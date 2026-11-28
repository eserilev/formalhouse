import EpochProofs.Assumptions
import EpochProofs.EthLib.ChainBalances
import EpochProofs.EthLib.Epoch

/-!
# The epoch input of an EthLib run has the invariants of the epoch proofs

`RunToEpochInput` describes a run of EthLib slots and blocks that ends where `process_epoch` starts.
The run starts at a genesis state, or at a state with the facts of `ChainStart`. The run can cross
any fork. `RunToEpochInput.invariants` proves `EpochInputInvariants` at the end of the run.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64 _root_.EthLib.Consensus
open Formalhouse (PresetMatchesEthLib)

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The statements -/

/-- A state that a run can start from, at any fork. A genesis state is such a state. -/
structure ChainStart (config : Config) (start : ForkedBeaconState preset) : Prop where
  /-- The facts that each step keeps. -/
  facts : ChainFacts config start.state
  /-- From Fulu, each effective balance is at most `4/3` of the balance. Each epoch transition makes
  this true. The proofs use it only for an epoch input in the epoch of the start. -/
  balanceFloor : .fusaka ≤ start.fork → ∀ (i : Nat) (validator : Validator) (balance : UInt64),
    start.state.validators.data[i]? = some validator →
    start.state.balances.data[i]? = some balance →
    3 * validator.effectiveBalance.toNat ≤ 4 * balance.toNat

/-- A genesis state is a start state. -/
theorem ChainStart.genesis {genesis : ForkedBeaconState preset}
    (isGenesis : Genesis config checks genesis) : ChainStart config genesis :=
  ⟨.genesis isGenesis, fun fulu =>
    absurd (genesis_fork isGenesis) (Nat.not_lt_of_le (Nat.le_trans (by decide) fulu))⟩

/-- An EthLib run from `start` to `input`, the state that `process_epoch` gets. Each step of the run
is a slot, with the epoch and fork upgrades of that slot, or a signed block. -/
structure RunToEpochInput (config : Config) (checks : SignatureChecks)
    (start : ForkedBeaconState preset) {fork : Fork} (input : BeaconState preset fork) where
  /-- The start is a genesis state, or it has the facts of a chain state. -/
  startsAt : Genesis config checks start ∨ ChainStart config start
  /-- The state at the last slot of the epoch, after its block. -/
  beforeLastSlot : BeaconState preset fork
  /-- The slots and blocks up to that state. -/
  run : Run config checks start ⟨fork, beforeLastSlot⟩
  /-- `process_slot` at the last slot gives the epoch input. -/
  lastSlot : processSlot beforeLastSlot = .ok input
  /-- The next slot is a `u64`. -/
  nextSlotFits : input.slot.toNat + 1 < 2 ^ 64
  /-- The epoch input is at the last slot of an epoch. -/
  atEpochEnd : (input.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0

/-- The bounds on the amounts at the epoch input. -/
structure SupplyAtInput [Spec.CurrentPreset] (input : Spec.BeaconState) : Prop where
  /-- Each balance is below `2^62`, all effective balances are below `2^60`, and the recent slashed
  balances are below `2^64 / 3`. -/
  balances : Spec.BalancesFarFromOverflow input
  /-- At most 139 million ETH is active. -/
  active : ∀ total, Spec.get_total_active_balance Spec.P input = .ok total →
    total ≤ 139000000000000000

/-- The largest effective balance before Electra is `MIN_ACTIVATION_BALANCE`. This holds on mainnet
and minimal. -/
def MaxEffectiveBalanceIsActivationBalance (preset : Preset) : Prop :=
  preset.MAX_EFFECTIVE_BALANCE = preset.MIN_ACTIVATION_BALANCE

theorem maxEffectiveBalance_mainnet : MaxEffectiveBalanceIsActivationBalance Preset.mainnet := by
  unfold MaxEffectiveBalanceIsActivationBalance
  decide

theorem maxEffectiveBalance_minimal : MaxEffectiveBalanceIsActivationBalance Preset.minimal := by
  unfold MaxEffectiveBalanceIsActivationBalance
  decide

/-! ## The preset values -/

section Values

variable [Spec.CurrentPreset] (presetMatches : PresetMatchesEthLib preset config)
include presetMatches

theorem slotsPerEpoch_eq : preset.SLOTS_PER_EPOCH.toNat = Spec.P.SLOTS_PER_EPOCH := by
  rw [← presetMatches.values]
  rfl

theorem increment_eq : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 1000000000 :=
  congrArg Spec.Preset.EFFECTIVE_BALANCE_INCREMENT presetMatches.values

theorem minActivationBalance_eq : preset.MIN_ACTIVATION_BALANCE.toNat = 32000000000 :=
  congrArg Spec.Preset.MIN_ACTIVATION_BALANCE presetMatches.values

theorem maxEffectiveBalanceElectra_eq :
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat = 2048000000000 :=
  congrArg Spec.Preset.MAX_EFFECTIVE_BALANCE_ELECTRA presetMatches.values

/-- The bands of the effective balance update. -/
theorem bands_eq : preset.downwardBand = 250000000 ∧ preset.upwardBand = 1250000000 := by
  have increment := increment_eq presetMatches
  have quotient : preset.HYSTERESIS_QUOTIENT.toNat = 4 :=
    congrArg Spec.Preset.HYSTERESIS_QUOTIENT presetMatches.values
  have down : preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat = 1 :=
    congrArg Spec.Preset.HYSTERESIS_DOWNWARD_MULTIPLIER presetMatches.values
  have up : preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat = 5 :=
    congrArg Spec.Preset.HYSTERESIS_UPWARD_MULTIPLIER presetMatches.values
  constructor <;> simp [Preset.downwardBand, Preset.upwardBand, increment, quotient, down, up]

theorem capOrder (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset) :
    CapOrder preset := by
  refine ⟨maxEffectiveBalance ▸ UInt64.le_refl _, UInt64.le_iff_toNat_le.mpr ?_⟩
  rw [minActivationBalance_eq presetMatches, maxEffectiveBalanceElectra_eq presetMatches]
  decide

theorem maxEffectiveBalancesAligned
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset) :
    MaxEffectiveBalancesAligned preset := by
  unfold MaxEffectiveBalanceIsActivationBalance at maxEffectiveBalance
  have aligned {value : UInt64} (h : value.toNat % 1000000000 = 0) :
      value % preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, increment_eq presetMatches, h]
    rfl
  refine ⟨?_, aligned ?_, aligned ?_⟩
  · rw [maxEffectiveBalance]
    exact aligned (by rw [minActivationBalance_eq presetMatches])
  · rw [minActivationBalance_eq presetMatches]
  · rw [maxEffectiveBalanceElectra_eq presetMatches]

theorem slashingQuotient_eq {fork : Fork} (fulu : .fusaka ≤ fork) :
    (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = 4096 := by
  have value : preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat = 4096 :=
    congrArg Spec.Preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA presetMatches.values
  cases fork <;> first | exact absurd fulu (by decide) | exact value

end Values

/-! ## The sync committee penalty -/

/-- If at most 139 million ETH is active, the sync committee penalties of one block are at most
`syncLoss` for each validator. -/
theorem syncReward_bound [Spec.CurrentPreset] [Spec.CurrentPreset.Valid]
    (presetMatches : PresetMatchesEthLib preset config) {fork : Fork}
    {state : BeaconState preset fork} (total : activeBalanceTotal state ≤ 139000000000000000) :
    preset.SYNC_COMMITTEE_SIZE.toNat * syncRewardAt state ≤ Spec.syncLoss := by
  have increment := increment_eq presetMatches
  have factor : preset.BASE_REWARD_FACTOR.toNat = 64 :=
    congrArg Spec.Preset.BASE_REWARD_FACTOR presetMatches.values
  unfold syncRewardAt Spec.syncLoss
  rw [increment, factor, slotsPerEpoch_eq presetMatches]
  have weight : SYNC_REWARD_WEIGHT.toNat = 2 ∧ WEIGHT_DENOMINATOR.toNat = 64 := ⟨rfl, rfl⟩
  rw [weight.1, weight.2]
  generalize activeBalanceTotal state = active at total ⊢
  have low : active.sqrt * active.sqrt ≤ active := Nat.sqrt_le active
  have high : active < (active.sqrt + 1) * (active.sqrt + 1) := Nat.lt_succ_sqrt active
  generalize active.sqrt = root at low high ⊢
  have rootLe : root ≤ 372827037 := by
    refine Nat.le_of_not_lt fun above => ?_
    have := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt above)
    omega
  have product : 1000000000 * 64 / root * (active / 1000000000) ≤ 64 * (root + 2) := by
    rcases Nat.eq_zero_or_pos root with zero | positive
    · simp [zero]
    have one := Nat.div_mul_le_self (1000000000 * 64) root
    have two := Nat.div_mul_le_self active 1000000000
    generalize 1000000000 * 64 / root = a at one ⊢
    generalize active / 1000000000 = b at two ⊢
    have three : (a * root) * (b * 1000000000) ≤ 1000000000 * 64 * active :=
      Nat.mul_le_mul one two
    have four : (a * b) * root * 1000000000 ≤ 64 * active * 1000000000 := by
      calc (a * b) * root * 1000000000 = (a * root) * (b * 1000000000) := by ring
        _ ≤ 1000000000 * 64 * active := three
        _ = 64 * active * 1000000000 := by ring
    have five : (a * b) * root ≤ 64 * active := Nat.le_of_mul_le_mul_right four (by decide)
    have six : 64 * active ≤ (64 * (root + 2)) * root := by
      have : active ≤ root * root + 2 * root := by nlinarith
      nlinarith
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans five six) positive
  generalize 1000000000 * 64 / root * (active / 1000000000) = scaled at product ⊢
  have scaledLe : scaled * 2 / 64 ≤ 745654078 := by omega
  calc preset.SYNC_COMMITTEE_SIZE.toNat *
        (scaled * 2 / 64 / Spec.P.SLOTS_PER_EPOCH / preset.SYNC_COMMITTEE_SIZE.toNat)
      ≤ scaled * 2 / 64 / Spec.P.SLOTS_PER_EPOCH := Nat.mul_div_le _ _
    _ ≤ 745654078 / Spec.P.SLOTS_PER_EPOCH := Nat.div_le_div_right scaledLe

/-! ## The effective balances at the epoch input -/

section Run

variable [Spec.CurrentPreset] [Spec.CurrentPreset.Valid] {start : ForkedBeaconState preset} {fork : Fork}
  {input : BeaconState preset fork}

omit [Spec.CurrentPreset.Valid] in
/-- The slot step that enters an epoch leaves each effective balance at most `4/3` of the
balance. -/
theorem balanceFloor_of_slot (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    {before after : ForkedBeaconState preset} (facts : ChainFacts config before.state)
    (ok : advanceSlotAcross config checks before = .ok after)
    (entersEpoch : after.state.slot % preset.SLOTS_PER_EPOCH = 0) (i : Nat) (validator : Validator)
    (balance : UInt64) (found : after.state.validators.data[i]? = some validator)
    (read : after.state.balances.data[i]? = some balance) :
    3 * validator.effectiveBalance.toNat ≤ 4 * balance.toNat := by
  have caps := capOrder presetMatches maxEffectiveBalance
  have aligned := (facts.chainStep caps (.slot ok)).invariant.aligned
    (maxEffectiveBalancesAligned presetMatches maxEffectiveBalance) validator
    (Array.mem_of_getElem? found)
  have aligned := congrArg UInt64.toNat aligned
  rw [UInt64.toNat_mod, increment_eq presetMatches] at aligned
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  have slot : after.state.slot = advanced.slot := processUpgrades_slot upgraded
  have bands := bands_eq presetMatches
  have hysteresis := Hysteresis.upgrade (forked := ⟨before.fork, advanced⟩)
    (hysteresis_of_advanceSlot ⟨by rw [increment_eq presetMatches]; decide,
      by rw [increment_eq presetMatches, bands.2]; decide⟩ advancedOk (slot ▸ entersEpoch))
    maxEffectiveBalance caps.compounding (advanceSlot_capped advancedOk facts.shaped.capped)
    upgraded
  have down := hysteresis.down i validator balance found read
  have zero : (0 : UInt64).toNat = 0 := rfl
  rw [bands.1] at down
  omega

/-- At the epoch input, the balance of each validator that is not withdrawable is at least `1/256`
of its effective balance. -/
theorem RunToEpochInput.effectiveBalance_le (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset) (fulu : .fusaka ≤ fork)
    (run : RunToEpochInput config checks start input) (registry : input.RegistryWithinLimit)
    (total : activeBalanceTotal input ≤ 139000000000000000) (i : Nat) (validator : Validator)
    (balance : UInt64) (found : input.validators.data[i]? = some validator)
    (read : input.balances.data[i]? = some balance)
    (notWithdrawable : getCurrentEpoch input < validator.withdrawableEpoch) :
    validator.effectiveBalance.toNat ≤ 256 * balance.toNat := by
  have caps := capOrder presetMatches maxEffectiveBalance
  have slots := slotsPerEpoch_eq presetMatches
  have slotsGt := Spec.P_slots_gt_one
  obtain ⟨startsAt, last, steps, lastSlot, -, -⟩ := run
  have startFacts : ChainStart config start := startsAt.elim .genesis id
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok lastSlot
  change last.RegistryWithinLimit at registry
  change activeBalanceTotal last ≤ _ at total
  change last.validators.data[i]? = some validator at found
  change last.balances.data[i]? = some balance at read
  change getCurrentEpoch last < _ at notWithdrawable
  -- The start of the epoch.
  obtain ⟨first, tail, firstFacts, epochSame, firstFloor⟩ : ∃ (first : ForkedBeaconState preset)
      (_ : Run config checks first ⟨fork, last⟩), ChainFacts config first.state ∧
      getCurrentEpoch last = getCurrentEpoch first.state ∧
      (first.fork = fork → ∀ (i : Nat) (validator : Validator) (balance : UInt64),
        first.state.validators.data[i]? = some validator →
        first.state.balances.data[i]? = some balance →
        3 * validator.effectiveBalance.toNat ≤ 4 * balance.toNat) := by
    have forward := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps steps.chainSteps)
    by_cases same : getCurrentEpoch last = getCurrentEpoch start.state
    · exact ⟨start, steps, startFacts.facts, same, fun forkSame =>
        startFacts.balanceFloor (forkSame ▸ fulu)⟩
    · have later : (getCurrentEpoch start.state).toNat < (getCurrentEpoch last).toNat := by
        have : (getCurrentEpoch last).toNat ≠ (getCurrentEpoch start.state).toNat :=
          fun h => same (UInt64.toNat_inj.mp h)
        dsimp only at forward
        omega
      obtain ⟨before, after, pre, ok, rest, -, beforeEpoch, afterEpoch⟩ :=
        steps.cross_split ((getCurrentEpoch last).toNat - 1) (by omega) (by dsimp only; omega)
      have beforeFacts := startFacts.facts.run caps pre
      refine ⟨after, rest, beforeFacts.chainStep caps (.slot ok),
        UInt64.toNat_inj.mp (by omega), fun _ =>
        balanceFloor_of_slot presetMatches maxEffectiveBalance beforeFacts ok ?_⟩
      -- The step enters an epoch, so the slot is the first of an epoch.
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      have slot : after.state.slot.toNat = before.state.slot.toNat + 1 := by
        rw [processUpgrades_slot upgraded]
        exact advanceSlot_slot advancedOk
      rw [getCurrentEpoch_toNat] at beforeEpoch afterEpoch
      rw [slot] at afterEpoch
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, slot]
      have divides : preset.SLOTS_PER_EPOCH.toNat ∣ before.state.slot.toNat + 1 := by
        by_contra notDivides
        rw [Nat.succ_div_of_not_dvd notDivides] at afterEpoch
        omega
      exact Nat.mod_eq_zero_of_dvd divides
  have far : getCurrentEpoch first.state < FAR_FUTURE_EPOCH := by
    rw [← epochSame]
    refine UInt64.lt_iff_toNat_lt.mpr ?_
    rw [getCurrentEpoch_toNat, slots]
    exact Spec.slot_div_lt_far slotsGt last.slot.toNat_lt
  have forkSame : fork = first.fork := Run.fork_same_epoch tail epochSame
  obtain ⟨_, first⟩ := first
  dsimp only at forkSame
  subst forkSame
  -- The total active balance is the one at the epoch input.
  have reward : preset.SYNC_COMMITTEE_SIZE.toNat * syncRewardAt first ≤ Spec.syncLoss := by
    refine syncReward_bound presetMatches ?_
    rw [← Run.activeBalanceTotal_same_epoch tail epochSame]
    exact total
  obtain ⟨-, -, added, floors⟩ :=
    Run.balanceInEpoch caps (first := ⟨fork, first⟩) fulu firstFacts far reward tail epochSame
  have lastFacts := firstFacts.run caps tail
  by_cases inside : i < first.validators.data.size
  · have small : i < 2 ^ 64 := by
      have := (Array.getElem?_eq_some_iff.mp found).1
      exact Nat.lt_of_lt_of_le this (Nat.le_trans registry
        (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
    have index : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' small
    have startFound := Array.getElem?_eq_getElem inside
    obtain ⟨now, nowFound, -, floor⟩ := floors registry (UInt64.ofNat i) first.validators.data[i]
      (by rw [index]; exact startFound)
    rw [index] at nowFound floor
    obtain rfl := Option.some.inj (nowFound.symm.trans found)
    have floor := floor.resolve_left (by
      rw [← epochSame]
      exact UInt64.not_le.mpr notWithdrawable)
    -- The balance at the start of the epoch.
    have balanceInside : i < first.balances.data.size := by
      rw [firstFacts.invariant.balancesMatch]
      exact inside
    have startBalance := Array.getElem?_eq_getElem balanceInside
    have atStart := firstFloor rfl i _ _ startFound startBalance
    -- The effective balance is the one at the start of the epoch.
    have effective := tail.effectiveKept_of_same_epoch epochSame i inside
    simp only [effectiveAt, found, startFound, Option.map_some, Option.getD_some] at effective
    have balanceNow : actualBalanceAt ⟨fork, last⟩ i = balance.toNat := by
      simp [actualBalanceAt, read]
    have balanceStart : actualBalanceAt ⟨fork, first⟩ i = first.balances.data[i].toNat := by
      simp [actualBalanceAt, startBalance]
    rw [balanceNow, balanceStart, minActivationBalance_eq presetMatches, ← effective] at floor
    rw [← effective] at atStart
    have penalty : slashingPenaltyBound preset fork now.effectiveBalance.toNat
        first.validators.data[i].slashed now.slashed ≤ now.effectiveBalance.toNat / 4096 := by
      unfold slashingPenaltyBound
      rw [slashingQuotient_eq presetMatches fulu]
      split <;> omega
    -- The effective balance is a multiple of the increment, and at most 2048 ETH.
    have member := Array.mem_of_getElem? found
    have aligned := congrArg UInt64.toNat (lastFacts.invariant.aligned
      (maxEffectiveBalancesAligned presetMatches maxEffectiveBalance) now member)
    rw [UInt64.toNat_mod, increment_eq presetMatches] at aligned
    have aligned : now.effectiveBalance.toNat % 1000000000 = 0 := aligned
    have capped : now.effectiveBalance.toNat ≤ 2048000000000 := by
      have cap := UInt64.le_iff_toNat_le.mp (lastFacts.shaped.capped now member)
      have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) fulu
      simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance] at cap
      have high := maxEffectiveBalanceElectra_eq presetMatches
      have low := minActivationBalance_eq presetMatches
      split at cap <;> omega
    have blocks : tail.blockCount ≤ Spec.P.SLOTS_PER_EPOCH := by
      have count := tail.blockCount_le_epochs (by rw [slots]; exact Spec.P_slots_pos)
      rw [epochSame, slots, Nat.add_sub_cancel_left, Nat.one_mul] at count
      exact count
    by_cases none : now.effectiveBalance.toNat = 0
    · omega
    · have fits := Spec.lossFits_mainnet blocks (Nat.le_refl _) aligned (Nat.pos_of_ne_zero none)
        capped
      unfold Spec.syncLoss at floor
      generalize tail.blockCount * (745654078 / Spec.P.SLOTS_PER_EPOCH) = loss at floor fits
      simp only [Nat.min_def] at floor fits
      split at floor <;> split at fits <;> omega
  · have zero := added i (Nat.le_of_not_lt inside)
    simp only [effectiveAt, found, Option.map_some, Option.getD_some] at zero
    omega

/-! ## The invariants at the epoch input -/

omit [Spec.CurrentPreset] [Spec.CurrentPreset.Valid] in
/-- The epoch input of a run has the facts of a chain state. -/
theorem RunToEpochInput.facts (caps : CapOrder preset)
    (run : RunToEpochInput config checks start input) : ChainFacts config input :=
  ((run.startsAt.elim ChainStart.genesis id).facts.run caps run.run).processSlot run.lastSlot

omit [Spec.CurrentPreset.Valid] in
/-- The facts of a chain state give the reachable-state invariants, except `EligibleBalancesAboveFloor` and the balance
bounds. -/
theorem ChainFacts.toSpecState (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset) (fulu : .fusaka ≤ fork)
    (facts : ChainFacts config input) :
    Spec.CheckpointsInOrder Spec.P (toSpecState input) ∧ Spec.ListLengthsMatch (toSpecState input) ∧
    (toSpecState input).slot < 2 ^ 64 ∧ Spec.EffectiveBalancesValid Spec.P (toSpecState input) ∧
    Spec.ExitEpochsAreUint64 (toSpecState input) ∧ Spec.PubkeysUnique (toSpecState input) ∧
    Spec.ConsolidationsInRange (toSpecState input) ∧ Spec.WithdrawableEpochsFitUint64 (toSpecState input) ∧
    Spec.NoWithdrawableEpochWithoutExit (toSpecState input) := by
  have caps := capOrder presetMatches maxEffectiveBalance
  have alignedMax := maxEffectiveBalancesAligned presetMatches maxEffectiveBalance
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) fulu
  have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) fulu
  have far (e : UInt64) : e.toNat ≤ Spec.FAR_FUTURE_EPOCH := Nat.le_of_lt_succ e.toNat_lt
  have validators : (EthLib.toSpecState input).validators =
      input.validators.data.toList.map toSpecValidator := rfl
  have ofMember : ∀ v ∈ (EthLib.toSpecState input).validators,
      ∃ w ∈ input.validators.data, v = toSpecValidator w := by
    intro v member
    rw [validators] at member
    obtain ⟨w, inside, rfl⟩ := List.mem_map.mp member
    exact ⟨w, by simpa using inside, rfl⟩
  have slots := slotsPerEpoch_eq presetMatches
  refine ⟨?_, ?_, input.slot.toNat_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨UInt64.le_iff_toNat_le.mp facts.invariant.ordered.1,
      UInt64.le_iff_toNat_le.mp facts.invariant.ordered.2⟩, ?_⟩
    have settled := UInt64.le_iff_toNat_le.mp facts.invariant.settled
    change input.currentJustifiedCheckpoint.epoch.toNat <
        input.slot.toNat / Spec.P.SLOTS_PER_EPOCH ∨
      input.currentJustifiedCheckpoint.epoch.toNat = 0
    rw [← slots, ← getCurrentEpoch_toNat]
    unfold getPreviousEpoch at settled
    rw [toNat_saturatingSub] at settled
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  · have balances := facts.shaped.balancesMatch
    have participation := facts.shaped.participationMatches altair
    have inactivity := facts.shaped.inactivityScoresMatch altair
    unfold BalancesMatch at balances
    unfold ParticipationMatches at *
    simp [Spec.ListLengthsMatch, EthLib.toSpecState, fieldOr, altair, readList]
    exact ⟨balances, inactivity, participation.1, participation.2⟩
  · intro v member
    obtain ⟨w, inside, rfl⟩ := ofMember v member
    have aligned := congrArg UInt64.toNat (facts.invariant.aligned alignedMax w inside)
    have capped := UInt64.le_iff_toNat_le.mp (facts.shaped.capped w inside)
    have order := UInt64.le_iff_toNat_le.mp caps.compounding
    refine ⟨?_, ?_⟩
    · rw [← presetMatches.values]
      rw [UInt64.toNat_mod] at aligned
      exact aligned
    · rw [← presetMatches.values]
      simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
        getMaxEffectiveBalance] at capped
      change w.effectiveBalance.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      split at capped <;> omega
  · intro v member
    obtain ⟨w, inside, rfl⟩ := ofMember v member
    exact far _
  · have keys := facts.keys
    unfold PubkeysDistinct validatorKeys at keys
    unfold Spec.PubkeysUnique
    rw [validators, List.map_map]
    exact keys
  · intro c member
    simp only [EthLib.toSpecState, fieldOr, electra, ↓reduceDIte, readList,
      List.mem_map] at member
    obtain ⟨d, inside, rfl⟩ := member
    have both := facts.shaped.inside electra d (by simpa using inside)
    simpa [validators, toSpecPendingConsolidation] using both
  · intro v member
    obtain ⟨w, inside, rfl⟩ := ofMember v member
    exact far _
  · intro v member noExit
    obtain ⟨w, inside, rfl⟩ := ofMember v member
    have none := withdrawableEpoch_of_no_exit facts.invariant w inside (UInt64.toNat_inj.mp noExit)
    simp only [toSpecValidator, none]
    rfl

/-- A validator that is eligible for rewards at the epoch input is not withdrawable. -/
theorem notWithdrawable_of_rewardsEligible (presetMatches : PresetMatchesEthLib preset config)
    (facts : ChainFacts config input) {validator : Validator}
    (member : validator ∈ input.validators.data)
    (eligible : Spec.rewardsEligible (input.slot.toNat / Spec.P.SLOTS_PER_EPOCH - 1)
      (toSpecValidator validator) = .ok true) :
    getCurrentEpoch input < validator.withdrawableEpoch := by
  have delay : config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat =
      Spec.P.MIN_VALIDATOR_WITHDRAWABILITY_DELAY :=
    congrArg Spec.Preset.MIN_VALIDATOR_WITHDRAWABILITY_DELAY presetMatches.values
  have epoch : (getCurrentEpoch input).toNat = input.slot.toNat / Spec.P.SLOTS_PER_EPOCH := by
    rw [getCurrentEpoch_toNat, slotsPerEpoch_eq presetMatches]
  have below : (getCurrentEpoch input).toNat < Spec.FAR_FUTURE_EPOCH := by
    rw [epoch]
    exact Spec.slot_div_lt_far Spec.P_slots_gt_one input.slot.toNat_lt
  have waits : Spec.ValidatorExitToWithdrawableDelay Spec.P (toSpecValidator validator) := by
    by_cases none : validator.exitEpoch = FAR_FUTURE_EPOCH
    · left
      simp only [toSpecValidator, withdrawableEpoch_of_no_exit facts.invariant _ member none]
      decide
    · right
      rw [← delay]
      exact facts.exitDelay validator member none
  refine UInt64.not_le.mp fun withdrawable => ?_
  exact Spec.rewardsEligible_of_withdrawable waits (UInt64.le_iff_toNat_le.mp withdrawable) below
    (show 1 ≤ Spec.P.MIN_VALIDATOR_WITHDRAWABILITY_DELAY by pdecide) (by rw [epoch]; omega) eligible

/-- The epoch input of a run has the reachable-state invariants. -/
theorem RunToEpochInput.invariants (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset) (fulu : .fusaka ≤ fork)
    (run : RunToEpochInput config checks start input) (registry : input.RegistryWithinLimit)
    (supply : SupplyAtInput (toSpecState input)) :
    Spec.EpochInputInvariants (toSpecState input) := by
  have facts := run.facts (capOrder presetMatches maxEffectiveBalance)
  obtain ⟨ffg, rows, slot, effective, exits, keys, consolidations, withdrawable, valid⟩ :=
    facts.toSpecState presetMatches maxEffectiveBalance fulu
  have slotsNonzero : preset.SLOTS_PER_EPOCH ≠ 0 := presetMatches.divisorsNonzero.slots
  -- The total active balance is below the bound.
  have total : activeBalanceTotal input ≤ 139000000000000000 := by
    have current : Spec.get_current_epoch Spec.P (toSpecState input) =
        .ok (getCurrentEpoch input).toNat := by
      rw [← presetMatches.values]
      exact get_current_epoch_eq slotsNonzero input
    obtain ⟨specTotal, specOk, -⟩ := Spec.get_total_active_balance_bounds Spec.P _ _ current
      (Nat.lt_trans supply.balances.2.1 (by decide))
    have same := get_total_active_balance_same (config := config) slotsNonzero registry
    rw [presetMatches.values, specOk] at same
    cases ethLibTotal : getTotalActiveBalance input with
    | error => rw [ethLibTotal] at same; cases same
    | ok value =>
      rw [ethLibTotal] at same
      cases same with
      | returned same =>
        have bound := supply.active specTotal specOk
        rw [← getTotalActiveBalance_toNat ethLibTotal, ← same]
        exact bound
  refine ⟨⟨⟨⟨ffg, rows, ?_⟩, slot, effective, exits, supply.balances⟩, keys, consolidations⟩,
    withdrawable, valid⟩
  intro i inside eligible
  have inside' : i < input.validators.data.size := by simpa [toSpecState, readList] using inside
  have balanceInside : i < input.balances.data.size := by
    rw [facts.invariant.balancesMatch]
    exact inside'
  have validator : (toSpecState input).validators[i] =
      toSpecValidator input.validators.data[i] := by
    simp [toSpecState, readList]
  have balance : (toSpecState input).balances.getD i 0 = input.balances.data[i].toNat := by
    simp [toSpecState, readList, List.getD_eq_getElem?_getD, balanceInside]
  rw [validator] at eligible ⊢
  rw [balance]
  exact run.effectiveBalance_le presetMatches maxEffectiveBalance fulu registry total i _ _
    (Array.getElem?_eq_getElem inside') (Array.getElem?_eq_getElem balanceInside)
    (notWithdrawable_of_rewardsEligible presetMatches facts (Array.getElem_mem inside') eligible)

omit [Spec.CurrentPreset.Valid] in
/-- The epoch input of a run is at an epoch boundary, when Lighthouse's list of historical summaries
has room. -/
theorem RunToEpochInput.atLastSlotOfEpoch (presetMatches : PresetMatchesEthLib preset config)
    (run : RunToEpochInput config checks start input)
    (historicalSummariesBelowLimit : (toSpecState input).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT) :
    Spec.AtLastSlotOfEpoch (toSpecState input) :=
  ⟨by rw [← slotsPerEpoch_eq presetMatches]; exact run.atEpochEnd, run.nextSlotFits,
    historicalSummariesBelowLimit⟩

end Run

end EpochProofs.EthLib
