import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EpochProofs.EthLib.BuilderPayments
import EpochProofs.EthLib.Deposits
import EpochProofs.EthLib.HistoricalSummaries
import EpochProofs.EthLib.Inactivity
import EpochProofs.EthLib.Justification
import EpochProofs.EthLib.PtcWindow
import EpochProofs.EthLib.Registry
import EpochProofs.EthLib.Resets
import EpochProofs.EthLib.Rewards
import EpochProofs.EthLib.Slashings
import EpochProofs.EthLib.SyncCommittee
import EpochProofs.Spec.FuluEpoch

/-!
# `process_epoch`: the reference and EthLib agree

`process_epoch_gloas` and `process_epoch_fulu` are the main theorems. Each one says that the
reference and EthLib return the same state, or both fail. Three differences remain. Each one is a
hypothesis about the input state:

- `EpochRoom.deposits`: the registry has room for the deposits of one epoch. EthLib fails if a
  registry position does not fit (`Deposits.lean`).
- `EpochRoom.historicalSummaries`: the list of historical summaries is not full. EthLib fails on a
  full list, and the reference appends (`HistoricalSummaries.lean`).
- `hslotLimit` (only Gloas): the epoch of the new PTCs does not end at slot `2**64`. The reference
  always fails on such a state (`process_epoch_gloas_fails_at_slot_limit`), and EthLib does not
  compute that end. `process_epoch_gloas_of_ok` does not need `hslotLimit`. A slot far below `2**64`
  gives it (`slotLimit_of_slot_far`).

The reference reads the total active balance before the rewards. EthLib reads it only where it needs
it. If the sum overflows, both fail, because `processSlashings` of EthLib always reads it.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- The registry has room for the deposits of one epoch. One epoch reads at most
`MAX_PENDING_DEPOSITS_PER_EPOCH` deposits of the queue, and each one adds at most one validator. The
registry stays within `VALIDATOR_REGISTRY_LIMIT`. -/
def RoomForDeposits (electra : .pectra ≤ fork) (s : BeaconState preset fork) : Prop :=
  s.validators.data.size +
    min (s.pendingDeposits electra).data.size preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤
      preset.VALIDATOR_REGISTRY_LIMIT.toNat

/-- The lists of the input state have room for the items that one epoch adds. -/
structure EpochRoom (electra : .pectra ≤ fork) (s : BeaconState preset fork) : Prop where
  /-- The registry has room for the deposits of one epoch. -/
  deposits : RoomForDeposits electra s
  /-- The list of historical summaries is below `HISTORICAL_ROOTS_LIMIT`. -/
  historicalSummaries :
    (s.historicalSummaries (Nat.le_trans (by decide) electra)).data.size <
      preset.HISTORICAL_ROOTS_LIMIT.toNat

/-! ## What the steps keep -/

/-- The fields that the epoch theorems follow from step to step. -/
structure FieldsKept (s st : BeaconState preset fork) : Prop where
  slot : st.slot = s.slot
  registrySize : st.validators.data.size = s.validators.data.size
  pendingDeposits : st.pendingDeposits = s.pendingDeposits
  historicalSummaries : st.historicalSummaries = s.historicalSummaries

namespace FieldsKept

variable {s st st' : BeaconState preset fork}

theorem refl (s : BeaconState preset fork) : FieldsKept s s := ⟨rfl, rfl, rfl, rfl⟩

theorem trans (h : FieldsKept s st) (h' : FieldsKept st st') : FieldsKept s st' :=
  ⟨h'.slot.trans h.slot, h'.registrySize.trans h.registrySize,
    h'.pendingDeposits.trans h.pendingDeposits, h'.historicalSummaries.trans h.historicalSummaries⟩

theorem registryWithinLimit (h : FieldsKept s st) (hs : s.RegistryWithinLimit) :
    st.RegistryWithinLimit := by
  rw [BeaconState.RegistryWithinLimit, h.registrySize]
  exact hs

theorem justification (h : processJustificationAndFinalization s = .ok st) : FieldsKept s st := by
  rw [processJustificationAndFinalization_eq h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inactivity {altair : .altair ≤ fork}
    (h : processInactivityUpdates config s altair = .ok st) :
    FieldsKept s st := by
  rw [processInactivityUpdates_frame h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem rewards (h : processRewardsAndPenalties config s = .ok st) : FieldsKept s st := by
  rw [processRewardsAndPenalties_frame h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem slashings (h : processSlashings s = .ok st) : FieldsKept s st := by
  rw [processSlashings_frame h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem eth1DataReset {beforeHeze : fork < .hegota}
    (h : processEth1DataReset beforeHeze s = .ok st) :
    FieldsKept s st := by
  rw [processEth1DataReset_frame h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem builderPayments {gloas : .glamsterdam ≤ fork}
    (h : liftAccessor (processBuilderPendingPayments s gloas) = .ok st) : FieldsKept s st := by
  rw [processBuilderPendingPayments_eq (liftAccessor_ok.mp h)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem effectiveBalances (h : processEffectiveBalanceUpdates s = .ok st) : FieldsKept s st := by
  have hsize := (sameSizes_processEffectiveBalanceUpdates h).1
  have hframe := processEffectiveBalanceUpdates_frame h
  exact ⟨by rw [hframe], hsize, by rw [hframe], by rw [hframe]⟩

theorem slashingsReset (h : processSlashingsReset s = .ok st) : FieldsKept s st := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem randaoMixesReset (h : processRandaoMixesReset s = .ok st) : FieldsKept s st := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq h
  exact ⟨rfl, rfl, rfl, rfl⟩

end FieldsKept

theorem historicalSummaries_keeps {capella : .shapella ≤ fork} {s st : BeaconState preset fork}
    (h : processHistoricalSummariesUpdate s capella = .ok st) :
    st.slot = s.slot ∧ st.validators = s.validators := by
  obtain ⟨-, h⟩ := processHistoricalSummariesUpdate_eq h
  split at h
  · obtain ⟨-, -, -, -, -, h⟩ := h
    exact ⟨congrArg (·.slot) h, congrArg (·.validators) h⟩
  · subst h
    exact ⟨rfl, rfl⟩

theorem syncCommittee_keeps {altair : .altair ≤ fork} {s st : BeaconState preset fork}
    (h : processSyncCommitteeUpdates s altair = .ok st) :
    st.slot = s.slot ∧ st.validators = s.validators := by
  unfold processSyncCommitteeUpdates at h
  simp only [bind_ok_iff] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem proposerLookahead_keeps {fulu : .fusaka ≤ fork} {s st : BeaconState preset fork}
    (h : liftAccessor (processProposerLookahead s fulu) = .ok st) :
    st.slot = s.slot ∧ st.validators = s.validators := by
  have h := liftAccessor_ok.mp h
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-! ## The total active balance -/

/-- The registry step keeps the total active balance, also if the churn limits fail. -/
theorem registry_keeps_total {s st : BeaconState preset fork}
    (h : processRegistryUpdates config s = .ok st) :
    getTotalActiveBalance st = getTotalActiveBalance s := by
  have hactive := (stepKeeps_processRegistryUpdates h).2
  have hkept := (processRegistryUpdates_kept h).1
  have hsize := (sameSizes_processRegistryUpdates h).1
  refine total_active_balance_congr hactive.1 (List.ext_getElem? fun i => ?_)
  have hstatus := hactive.2 _ (getCurrentEpoch_le_activityFixedEpoch s) i
  simp only [List.getElem?_map, Array.getElem?_toList]
  unfold isActiveAt at hstatus
  cases hold : s.validators.data[i]? with
  | none =>
    have hnone : st.validators.data[i]? = none := by
      rw [Array.getElem?_eq_none_iff] at hold ⊢
      rw [hsize]
      exact hold
    rw [hnone]
  | some v =>
    obtain ⟨w, hw, -, hbalance, -⟩ := hkept i v hold
    rw [hw, hold] at hstatus
    simp only [Option.map_some, Option.getD_some] at hstatus
    rw [hw, Option.map_some, Option.map_some, hstatus, hbalance]

theorem spec_total_eq (hslots : preset.SLOTS_PER_EPOCH ≠ 0) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) {total : UInt64} (h : getTotalActiveBalance s = .ok total) :
    Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s) =
      .ok total.toNat := by
  obtain ⟨_, hspec, rfl⟩ := (get_total_active_balance_same hslots hregistry).returns h
  exact hspec

theorem slashings_reads_total {s st : BeaconState preset fork} (h : processSlashings s = .ok st) :
    ∃ total, getTotalActiveBalance s = .ok total := by
  unfold processSlashings at h
  obtain ⟨total, htotal, -⟩ := bind_ok_iff.mp h
  exact ⟨total, liftAccessor_ok.mp htotal⟩

theorem SameOutcome.of_never_ok {ε α β : Type} {M : α → β → Prop} {x : Except ε α}
    {e : Spec.SpecError} (h : ∀ a, x ≠ .ok a) : SameOutcome M x (.error e) := by
  cases x with
  | ok a => exact absurd rfl (h a)
  | error => exact .failed

theorem SameOutcome.withResult {ε α β : Type} {M : α → β → Prop} {x : Except ε α}
    {y : Spec.SpecM β} (h : SameOutcome M x y) :
    SameOutcome (fun a b => M a b ∧ x = .ok a) x y := by
  cases h with
  | returned h => exact .returned ⟨h, rfl⟩
  | failed => exact .failed

/-! ## The steps up to the pending deposits -/

/-- The EthLib steps up to the pending deposits. -/
def throughDeposits (config : Config) (checks : SignatureChecks) (altair : .altair ≤ fork)
    (electra : .pectra ≤ fork) (beforeHeze : fork < .hegota) (s : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let state ← processJustificationAndFinalization s
  let state ← processInactivityUpdates config state altair
  let state ← processRewardsAndPenalties config state
  let state ← processRegistryUpdates config state
  let state ← processSlashings state
  let state ← processEth1DataReset beforeHeze state
  processPendingDeposits config checks state electra

/-- The reference steps up to the pending deposits, on the churn limits of the fork. -/
def specThroughDeposits (p : Spec.Preset) (exitChurn depositChurn : Nat → Spec.SpecM Nat)
    (apply_pending_deposit : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (state : Spec.BeaconState) : Spec.SpecM Spec.BeaconState := do
  let state ← Spec.process_justification_and_finalization p state
  let state ← Spec.process_inactivity_updates p state
  let state ← Spec.process_rewards_and_penalties p (← Spec.get_total_active_balance p state) state
  let state ←
    specRegistryUpdates p (exitChurn (← Spec.get_total_active_balance p state)) state
  let state ← Spec.process_slashings p (← Spec.get_total_active_balance p state) state
  let state ← Spec.process_eth1_data_reset p state
  specPendingDeposits p (depositChurn (← Spec.get_total_active_balance p state))
    apply_pending_deposit state

/-- A churn limit of EthLib and one of the reference have the same value. The reference takes the
total active balance as an argument. -/
def SameChurn (limit : BeaconState preset fork → Except AccessorError UInt64)
    (specLimit : Nat → Spec.SpecM Nat) : Prop :=
  ∀ s total, getTotalActiveBalance s = .ok total →
    ∃ churn, limit s = .ok churn ∧ specLimit total.toNat = .ok churn.toNat

/-- What the steps up to the pending deposits leave. -/
structure AfterDeposits (s st : BeaconState preset fork) : Prop where
  slot : st.slot = s.slot
  registry : st.RegistryWithinLimit
  historicalSummaries : st.historicalSummaries = s.historicalSummaries

theorem through_deposits_same (hdiv : DivisorsNonzero preset config) (altair : .altair ≤ fork)
    (electra : .pectra ≤ fork) (fulu : .fusaka ≤ fork) (beforeHeze : fork < .hegota)
    {checks : SignatureChecks} {o : Spec.Oracle} (ho : OracleMatches preset checks o)
    {exitChurn depositChurn : Nat → Spec.SpecM Nat}
    {s : BeaconState preset fork}
    (hexit : SameChurn (exitChurnLimit config (preset := preset) (fork := fork)) exitChurn)
    (hdeposit : SameChurn (depositChurnLimit config (preset := preset) (fork := fork)) depositChurn)
    (hroom : EpochRoom electra s) :
    SameOutcome (fun st b => b = toSpecState st ∧ AfterDeposits s st)
      (throughDeposits config checks altair electra beforeHeze s)
      (specThroughDeposits (toSpecPreset preset config) exitChurn depositChurn
        (Spec.apply_pending_deposit (toSpecPreset preset config) o) (toSpecState s)) := by
  have hregistry : s.RegistryWithinLimit := Nat.le_trans (Nat.le_add_right _ _) hroom.deposits
  unfold throughDeposits specThroughDeposits
  refine .bind (justification_same altair hdiv.slots hregistry) ?_
  rintro s₁ _ rfl h₁
  have k₁ := FieldsKept.justification h₁
  refine .bind (inactivity_updates_same hdiv altair (k₁.registryWithinLimit hregistry)) ?_
  rintro s₂ _ rfl h₂
  have k₂ := k₁.trans (.inactivity h₂)
  have r₂ := k₂.registryWithinLimit hregistry
  cases htotal : getTotalActiveBalance s₂ with
  | error e =>
    have hspec := get_total_active_balance_same (config := config) hdiv.slots r₂
    rw [htotal] at hspec
    generalize Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s₂) = t
      at hspec ⊢
    cases hspec
    refine .of_never_ok fun st h => ?_
    obtain ⟨s₃, h₃, h⟩ := bind_ok_iff.mp h
    obtain ⟨s₄, h₄, h⟩ := bind_ok_iff.mp h
    obtain ⟨s₅, h₅, -⟩ := bind_ok_iff.mp h
    obtain ⟨total, h⟩ := slashings_reads_total h₅
    have htotal₃ : getTotalActiveBalance s₃ = getTotalActiveBalance s₂ := by
      rw [processRewardsAndPenalties_frame h₃]
      exact total_active_balance_congr rfl rfl
    rw [registry_keeps_total h₄, htotal₃, htotal] at h
    cases h
  | ok total =>
    rw [spec_total_eq hdiv.slots r₂ htotal, bind_ok]
    refine .bind (rewards_and_penalties_same hdiv electra r₂ htotal) ?_
    rintro s₃ _ rfl h₃
    have k₃ := k₂.trans (.rewards h₃)
    have r₃ := k₃.registryWithinLimit hregistry
    have htotal₃ : getTotalActiveBalance s₃ = .ok total := by
      rw [← htotal, processRewardsAndPenalties_frame h₃]
      exact total_active_balance_congr rfl rfl
    rw [spec_total_eq hdiv.slots r₃ htotal₃, bind_ok]
    obtain ⟨churn, -, hspecChurn⟩ := hexit s₃ total htotal₃
    refine .bind (registry_updates_same hdiv electra r₃ (fun st h => by
      obtain ⟨churn', hchurn', hspecChurn'⟩ := hexit st total (h.trans htotal₃)
      rw [hchurn', UInt64.toNat_inj.mp (Except.ok.inj (hspecChurn'.symm.trans hspecChurn))])
      hspecChurn) ?_
    rintro s₄ _ ⟨rfl, h₄⟩ -
    have k₄ : FieldsKept s s₄ :=
      k₃.trans ⟨h₄.slot, h₄.size, h₄.pendingDeposits, h₄.historicalSummaries⟩
    rw [← bind_assoc (m := Spec.SpecM)]
    refine .bind (slashings_same hdiv electra (k₄.registryWithinLimit hregistry)) ?_
    rintro s₅ _ rfl h₅
    have k₅ := k₄.trans (.slashings h₅)
    refine .bind (eth1_data_reset_same hdiv beforeHeze s₅) ?_
    rintro s₆ _ rfl h₆
    have k₆ := k₅.trans (.eth1DataReset h₆)
    have htotal₆ : getTotalActiveBalance s₆ = .ok total := by
      rw [← htotal₃, ← h₄.total, processEth1DataReset_frame h₆, processSlashings_frame h₅]
      exact total_active_balance_congr rfl rfl
    rw [spec_total_eq hdiv.slots (k₆.registryWithinLimit hregistry) htotal₆, bind_ok]
    obtain ⟨churn, hchurn, hspecChurn⟩ := hdeposit s₆ total htotal₆
    refine (pending_deposits_same hdiv fulu electra beforeHeze ho
      (by rw [k₆.registrySize, k₆.pendingDeposits]; exact hroom.deposits)
      hchurn hspecChurn).withResult.mono ?_
    rintro st _ ⟨⟨rfl, hlimit⟩, h⟩
    exact ⟨rfl, (payloadInputsLaws.processPendingDeposits h).slot.trans k₆.slot, hlimit,
      (processPendingDeposits_history h).2.2.trans k₆.historicalSummaries⟩

/-! ## The steps after the pending deposits -/

/-- The EthLib steps from the effective balances to the proposer lookahead. -/
def throughLookahead (altair : .altair ≤ fork) (capella : .shapella ≤ fork) (fulu : .fusaka ≤ fork)
    (s : BeaconState preset fork) : Except TransitionError (BeaconState preset fork) := do
  let state ← processEffectiveBalanceUpdates s
  let state ← processSlashingsReset state
  let state ← processRandaoMixesReset state
  let state ← processHistoricalSummariesUpdate state capella
  let state ← processSyncCommitteeUpdates (processParticipationFlagUpdates state altair) altair
  liftAccessor (processProposerLookahead state fulu)

/-- The reference steps from the effective balances to the proposer lookahead, with the sync
committee and lookahead steps of the fork. -/
def specThroughLookahead (p : Spec.Preset) (o : Spec.Oracle)
    (syncCommitteeUpdates proposerLookahead : Spec.BeaconState → Spec.SpecM Spec.BeaconState)
    (state : Spec.BeaconState) : Spec.SpecM Spec.BeaconState := do
  let state ← Spec.process_effective_balance_updates p state
  let state ← Spec.process_slashings_reset p state
  let state ← Spec.process_randao_mixes_reset p state
  let state ← Spec.process_historical_summaries_update p o state
  let state := Spec.process_participation_flag_updates state
  let state ← syncCommitteeUpdates state
  proposerLookahead state

theorem through_lookahead_same (hdiv : DivisorsNonzero preset config) (altair : .altair ≤ fork)
    (capella : .shapella ≤ fork) (electra : .pectra ≤ fork) (fulu : .fusaka ≤ fork)
    {checks : SignatureChecks} {o : Spec.Oracle} (ho : OracleMatches preset checks o)
    {syncCommitteeUpdates proposerLookahead : Spec.BeaconState → Spec.SpecM Spec.BeaconState}
    (hsync : ∀ st : BeaconState preset fork, st.RegistryWithinLimit →
      SameOutcome SameState (processSyncCommitteeUpdates st altair)
        (syncCommitteeUpdates (toSpecState st)))
    (hlookahead : ∀ st : BeaconState preset fork, st.RegistryWithinLimit →
      SameOutcome SameState (processProposerLookahead st fulu) (proposerLookahead (toSpecState st)))
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit)
    (hhistory : (s.historicalSummaries capella).data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    SameOutcome (fun st b => b = toSpecState st ∧ st.slot = s.slot ∧ st.RegistryWithinLimit)
      (throughLookahead altair capella fulu s)
      (specThroughLookahead (toSpecPreset preset config) o syncCommitteeUpdates proposerLookahead
        (toSpecState s)) := by
  unfold throughLookahead specThroughLookahead
  refine .bind (effective_balance_updates_same hdiv electra s) ?_
  rintro s₁ _ rfl h₁
  have k₁ := FieldsKept.effectiveBalances h₁
  refine .bind (slashings_reset_same hdiv s₁) ?_
  rintro s₂ _ rfl h₂
  have k₂ := k₁.trans (.slashingsReset h₂)
  refine .bind (randao_mixes_reset_same hdiv s₂) ?_
  rintro s₃ _ rfl h₃
  have k₃ := k₂.trans (.randaoMixesReset h₃)
  refine .bind (historical_summaries_update_same hdiv ho capella s₃
    (by rw [k₃.historicalSummaries]; exact hhistory)) ?_
  rintro s₄ _ rfl h₄
  obtain ⟨hslot₄, hvalidators₄⟩ := historicalSummaries_keeps h₄
  have r₄ : s₄.RegistryWithinLimit := by
    rw [BeaconState.RegistryWithinLimit, hvalidators₄]
    exact k₃.registryWithinLimit hregistry
  simp only [participation_flag_updates_eq altair s₄]
  refine .bind (hsync _ r₄) ?_
  rintro s₅ _ rfl h₅
  obtain ⟨hslot₅, hvalidators₅⟩ := syncCommittee_keeps h₅
  have r₅ : s₅.RegistryWithinLimit := by
    rw [BeaconState.RegistryWithinLimit, hvalidators₅]
    exact r₄
  refine (hlookahead s₅ r₅).liftAccessor.withResult.mono ?_
  rintro st _ ⟨rfl, h⟩
  obtain ⟨hslot, hvalidators⟩ := proposerLookahead_keeps h
  refine ⟨rfl, hslot.trans (hslot₅.trans (hslot₄.trans k₃.slot)), ?_⟩
  rw [BeaconState.RegistryWithinLimit, hvalidators]
  exact r₅

theorem consolidations_keeps {electra : .pectra ≤ fork} (hdiv : DivisorsNonzero preset config)
    {s st : BeaconState preset fork} (h : processPendingConsolidations s electra = .ok st) :
    FieldsKept s st := by
  obtain ⟨_, -, -, _, _, rfl⟩ := (pending_consolidations_same hdiv electra s).returns h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Gloas -/

theorem gloas_exit_churn (hdiv : DivisorsNonzero preset config) :
    SameChurn (exitChurnLimit config (preset := preset) (fork := .glamsterdam))
      (Spec.get_exit_churn_limit (toSpecPreset preset config)) :=
  fun _ _ htotal => exit_churn_limit_eq hdiv htotal

theorem gloas_deposit_churn (hdiv : DivisorsNonzero preset config) :
    SameChurn (depositChurnLimit config (preset := preset) (fork := .glamsterdam))
      (Spec.get_activation_churn_limit (toSpecPreset preset config)) :=
  fun _ _ htotal => activation_churn_limit_eq hdiv htotal

/-- The Gloas steps of EthLib before the PTC window. -/
def gloasThroughLookahead (config : Config) (checks : SignatureChecks)
    (s : BeaconState preset .glamsterdam) :
    Except TransitionError (BeaconState preset .glamsterdam) := do
  let state ← throughDeposits config checks (by decide) (by decide) (by decide) s
  let state ← processPendingConsolidations state (by decide)
  let state ← liftAccessor (processBuilderPendingPayments state (by decide))
  throughLookahead (by decide) (by decide) (by decide) state

/-- The Gloas steps of the reference before the PTC window. -/
def specGloasThroughLookahead (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState) :
    Spec.SpecM Spec.BeaconState := do
  let state ← specThroughDeposits p (Spec.get_exit_churn_limit p)
    (Spec.get_activation_churn_limit p) (Spec.apply_pending_deposit p o) state
  let state ← Spec.process_pending_consolidations p state
  let state ← do
    let total ← Spec.get_total_active_balance p state
    Spec.process_builder_pending_payments p total state
  specThroughLookahead p o (Spec.process_sync_committee_updates p o)
    (Spec.process_proposer_lookahead p o) state

theorem processEpoch_gloas_eq (checks : SignatureChecks) (s : BeaconState preset .glamsterdam) :
    processEpoch config checks s =
      gloasThroughLookahead config checks s >>= fun state =>
        liftAccessor (processPtcWindow state (by decide)) := by
  have altair : _root_.EthLib.Base.Fork.altair ≤ .glamsterdam := by decide
  have electra : _root_.EthLib.Base.Fork.pectra ≤ .glamsterdam := by decide
  have capella : _root_.EthLib.Base.Fork.shapella ≤ .glamsterdam := by decide
  have fulu : _root_.EthLib.Base.Fork.fusaka ≤ .glamsterdam := by decide
  have gloas : _root_.EthLib.Base.Fork.glamsterdam ≤ .glamsterdam := by decide
  have beforeHeze : _root_.EthLib.Base.Fork.glamsterdam < .hegota := by decide
  simp only [processEpoch, processEpochAltair, processPendingBalances, gloasThroughLookahead,
    throughDeposits, throughLookahead, altair, electra, capella, fulu, gloas, beforeHeze, dite_true,
    bind_assoc]

theorem spec_process_epoch_eq (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState) :
    Spec.process_epoch p o state =
      specGloasThroughLookahead p o state >>= Spec.process_ptc_window p o := by
  simp only [Spec.process_epoch, specGloasThroughLookahead, specThroughDeposits,
    specThroughLookahead, specRegistryUpdates_gloas, specPendingDeposits_gloas, bind_assoc]

theorem gloas_through_lookahead_same (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) {s : BeaconState preset .glamsterdam}
    (hroom : EpochRoom (by decide) s) :
    SameOutcome (fun st b => b = toSpecState st ∧ st.slot = s.slot ∧ st.RegistryWithinLimit)
      (gloasThroughLookahead config checks s)
      (specGloasThroughLookahead (toSpecPreset preset config) o (toSpecState s)) := by
  unfold gloasThroughLookahead specGloasThroughLookahead
  refine .bind (through_deposits_same hdiv (by decide) (by decide) (by decide) (by decide) ho
    (gloas_exit_churn hdiv) (gloas_deposit_churn hdiv) hroom) ?_
  rintro s₁ _ ⟨rfl, h₁⟩ -
  refine .bind (pending_consolidations_same hdiv _ s₁) ?_
  rintro s₂ _ ⟨rfl, -⟩ h₂
  have k₂ := consolidations_keeps hdiv h₂
  have r₂ := k₂.registryWithinLimit h₁.registry
  rw [← bind_assoc (m := Spec.SpecM)]
  refine .bind (builder_pending_payments_same hdiv.slots _ r₂) ?_
  rintro s₃ _ rfl h₃
  have k₃ := k₂.trans (.builderPayments h₃)
  refine (through_lookahead_same hdiv (by decide) (by decide) (by decide) (by decide) ho
    (fun st hst => sync_committee_updates_gloas hdiv hbounds ho _ (by decide) hst)
    (fun st hst => proposer_lookahead_gloas hdiv.slots hbounds ho _ (by decide) hst)
    (k₃.registryWithinLimit h₁.registry) ?_).mono ?_
  · rw [k₃.historicalSummaries, h₁.historicalSummaries]
    exact hroom.historicalSummaries
  · rintro st _ ⟨rfl, hslot, hst⟩
    exact ⟨rfl, hslot.trans (k₃.slot.trans h₁.slot), hst⟩

/-- Gloas: the reference and EthLib return the same state, or both fail.

`hslotLimit` excludes at most one epoch: 2^59 - 3 on mainnet. There the reference always fails. -/
theorem process_epoch_gloas (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset .glamsterdam)
    (hroom : EpochRoom (by decide) s)
    (hslotLimit : ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≠ 2 ^ 64) :
    Spec.SameResultOrBothFail
      (Spec.process_epoch (toSpecPreset preset config) o (toSpecState s))
      (toSpecResult toSpecState (processEpoch config checks s)) := by
  apply SameOutcome.sameResultOrBothFail
  rw [processEpoch_gloas_eq, spec_process_epoch_eq]
  refine .bind (gloas_through_lookahead_same hdiv hbounds ho hroom) ?_
  rintro st _ ⟨rfl, hslot, hst⟩ -
  refine (ptc_window_same hdiv.slots hbounds ho _ hst ?_).liftAccessor
  have hepoch : getCurrentEpoch st = getCurrentEpoch s := by
    rw [getCurrentEpoch, getCurrentEpoch, hslot]
  rw [hepoch]
  exact hslotLimit

/-- Gloas: on the epoch that `process_epoch_gloas` excludes, the reference fails. -/
theorem process_epoch_gloas_fails_at_slot_limit (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset .glamsterdam)
    (hroom : EpochRoom (by decide) s)
    (hslotLimit : ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat = 2 ^ 64) :
    ∃ e, Spec.process_epoch (toSpecPreset preset config) o (toSpecState s) = .error e := by
  have h := gloas_through_lookahead_same hdiv hbounds ho hroom
  rw [spec_process_epoch_eq]
  generalize specGloasThroughLookahead (toSpecPreset preset config) o (toSpecState s) = y at h ⊢
  generalize gloasThroughLookahead config checks s = x at h
  cases h with
  | failed => exact ⟨_, rfl⟩
  | @returned st _ h =>
    obtain ⟨rfl, hslot, -⟩ := h
    refine ptc_window_fails_at_slot_limit hdiv.slots _ st ?_
    have hepoch : getCurrentEpoch st = getCurrentEpoch s := by
      rw [getCurrentEpoch, getCurrentEpoch, hslot]
    rw [hepoch]
    exact hslotLimit

/-- Gloas: if the reference returns a state, then EthLib returns the same state. This needs no
`hslotLimit`. -/
theorem process_epoch_gloas_of_ok (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset .glamsterdam)
    (hroom : EpochRoom (by decide) s) {state : Spec.BeaconState}
    (h : Spec.process_epoch (toSpecPreset preset config) o (toSpecState s) = .ok state) :
    toSpecResult toSpecState (processEpoch config checks s) = .ok state := by
  refine (process_epoch_gloas hdiv hbounds ho s hroom (fun hslotLimit => ?_) state).mp h
  obtain ⟨e, he⟩ := process_epoch_gloas_fails_at_slot_limit hdiv hbounds ho s hroom hslotLimit
  rw [he] at h
  cases h

/-- A slot far below `2**64` is not in the epoch that `process_epoch_gloas` excludes. -/
theorem slotLimit_of_slot_far (s : BeaconState preset fork)
    (h : s.slot.toNat + (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat <
      2 ^ 64) :
    ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≠ 2 ^ 64 := by
  refine Nat.ne_of_lt (Nat.lt_of_le_of_lt ?_ h)
  rw [Nat.add_assoc, Nat.add_mul, getCurrentEpoch_toNat]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

/-! ## Fulu -/

theorem fulu_exit_churn (hdiv : DivisorsNonzero preset config) :
    SameChurn (exitChurnLimit config (preset := preset) (fork := .fusaka))
      (Spec.get_activation_exit_churn_limit (toSpecPreset preset config)
        (toSpecFuluConfig config)) :=
  fun _ _ htotal => activation_exit_churn_limit_eq hdiv htotal

theorem fulu_deposit_churn (hdiv : DivisorsNonzero preset config) :
    SameChurn (depositChurnLimit config (preset := preset) (fork := .fusaka))
      (Spec.get_activation_exit_churn_limit (toSpecPreset preset config)
        (toSpecFuluConfig config)) :=
  fun _ _ htotal => activation_exit_churn_limit_eq hdiv htotal

/-- No epoch step writes the latest payload header, which is a separate field in Fulu. -/
theorem epoch_keeps_payload_header {checks : SignatureChecks} {s st : BeaconState preset fork}
    (h : processEpoch config checks s = .ok st) :
    st.latestExecutionPayloadHeader = s.latestExecutionPayloadHeader := by
  refine (processEpoch_trace h).transport (fun a b : BeaconState preset fork =>
    b.latestExecutionPayloadHeader = a.latestExecutionPayloadHeader) (fun _ => rfl)
    (fun {_ _ _} one two => Eq.trans two one) fun stage _ a b hstage => ?_
  have hstep := EpochStage.action_cases.mp hstage
  cases stage <;> simp only [EpochStage.Edge] at hstep
  case justification => exact justification_keeps_payload_header hstep
  case inactivity =>
    split at hstep
    · rw [processInactivityUpdates_frame hstep]
    · rw [hstep]
  case rewards => rw [processRewardsAndPenalties_frame hstep]
  case registry =>
    exact (payloadInputsLaws.processRegistryUpdates hstep).latestExecutionPayloadHeader
  case slashings => rw [processSlashings_frame hstep]
  case eth1Reset =>
    split at hstep
    · rw [processEth1DataReset_frame hstep]
    · rw [hstep]
  case pendingDeposits =>
    split at hstep
    · exact (payloadInputsLaws.processPendingDeposits hstep).latestExecutionPayloadHeader
    · rw [hstep]
  case pendingConsolidations =>
    split at hstep
    · exact (payloadInputsLaws.processPendingConsolidations hstep).latestExecutionPayloadHeader
    · rw [hstep]
  case payments =>
    split at hstep
    · rw [processBuilderPendingPayments_eq hstep]
    · rw [hstep]
  case effectiveBalances => rw [processEffectiveBalanceUpdates_frame hstep]
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq hstep
    rfl
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq hstep
    rfl
  case history =>
    split at hstep
    · exact (payloadInputsLaws.processHistoricalSummariesUpdate hstep).latestExecutionPayloadHeader
    · exact (payloadInputsLaws.processHistoricalRootsUpdate hstep).latestExecutionPayloadHeader
  case participation =>
    split at hstep
    · subst hstep
      rfl
    · exact
        (payloadInputsLaws.processParticipationRecordUpdates hstep).latestExecutionPayloadHeader
  case syncCommittees =>
    split at hstep
    · exact (payloadInputsLaws.processSyncCommitteeUpdates hstep).latestExecutionPayloadHeader
    · rw [hstep]
  case proposerLookahead =>
    split at hstep
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at hstep
      obtain ⟨_, _, _, _, rfl⟩ := hstep
      rfl
    · rw [hstep]
  case ptcWindow =>
    split at hstep
    · exact (payloadInputsLaws.processPtcWindow hstep).latestExecutionPayloadHeader
    · rw [hstep]

/-- Fulu: the reference and EthLib return the same state, or both fail. -/
theorem process_epoch_fulu (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset .fusaka)
    (hroom : EpochRoom (by decide) s) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState s with
          state := ← Spec.process_epoch_fulu (toSpecPreset preset config) (toSpecFuluConfig config)
            o (toSpecFuluState s).state })
      (toSpecResult toSpecFuluState (processEpoch config checks s)) := by
  have hepoch : SameOutcome SameState (processEpoch config checks s)
      (Spec.process_epoch_fulu (toSpecPreset preset config) (toSpecFuluConfig config) o
        (toSpecState s)) := by
    have altair : _root_.EthLib.Base.Fork.altair ≤ .fusaka := by decide
    have electra : _root_.EthLib.Base.Fork.pectra ≤ .fusaka := by decide
    have capella : _root_.EthLib.Base.Fork.shapella ≤ .fusaka := by decide
    have fulu : _root_.EthLib.Base.Fork.fusaka ≤ .fusaka := by decide
    have gloas : ¬_root_.EthLib.Base.Fork.glamsterdam ≤ .fusaka := by decide
    have beforeHeze : _root_.EthLib.Base.Fork.fusaka < .hegota := by decide
    have hsplit : processEpoch config checks s =
        throughDeposits config checks altair electra beforeHeze s >>= fun state =>
          processPendingConsolidations state electra >>= fun state =>
            throughLookahead altair capella fulu state := by
      simp only [processEpoch, processEpochAltair, processPendingBalances, throughDeposits,
        throughLookahead, altair, electra, capella, fulu, gloas, beforeHeze, dite_true, dite_false,
        bind_assoc, pure_bind, bind_pure]
    have hspecSplit : Spec.process_epoch_fulu (toSpecPreset preset config) (toSpecFuluConfig config)
        o (toSpecState s) =
        specThroughDeposits (toSpecPreset preset config)
          (Spec.get_activation_exit_churn_limit (toSpecPreset preset config)
            (toSpecFuluConfig config))
          (Spec.get_activation_exit_churn_limit (toSpecPreset preset config)
            (toSpecFuluConfig config))
          (Spec.apply_pending_deposit (toSpecPreset preset config) o) (toSpecState s) >>=
        fun state => Spec.process_pending_consolidations (toSpecPreset preset config) state >>=
          fun state => specThroughLookahead (toSpecPreset preset config) o
            (Spec.process_sync_committee_updates_fulu (toSpecPreset preset config) o)
            (Spec.process_proposer_lookahead_fulu (toSpecPreset preset config) o) state := by
      simp only [Spec.process_epoch_fulu, specThroughDeposits, specThroughLookahead,
        specRegistryUpdates_fulu, specPendingDeposits_fulu, bind_assoc]
    rw [hsplit, hspecSplit]
    refine .bind (through_deposits_same hdiv altair electra fulu beforeHeze ho
      (fulu_exit_churn hdiv) (fulu_deposit_churn hdiv) hroom) ?_
    rintro s₁ _ ⟨rfl, h₁⟩ -
    refine .bind (pending_consolidations_same hdiv electra s₁) ?_
    rintro s₂ _ ⟨rfl, -⟩ h₂
    have k₂ := consolidations_keeps hdiv h₂
    refine (through_lookahead_same hdiv altair capella electra fulu ho
      (fun st hst => sync_committee_updates_fulu hdiv hbounds ho altair electra hst)
      (fun st hst => proposer_lookahead_fulu hdiv.slots hbounds ho fulu gloas hst)
      (k₂.registryWithinLimit h₁.registry) ?_).mono fun _ _ h => h.1
    rw [k₂.historicalSummaries, h₁.historicalSummaries]
    exact hroom.historicalSummaries
  apply SameOutcome.sameResultOrBothFail
  rw [← bind_pure (processEpoch config checks s)]
  refine .bind hepoch ?_
  rintro s' _ rfl hs'
  refine .pure ?_
  rw [toSpecFuluState, toSpecFuluState, epoch_keeps_payload_header hs']

/-! ## Mainnet and minimal -/

/-- Gloas, mainnet: `process_epoch_gloas` without preset hypotheses. -/
theorem process_epoch_gloas_mainnet {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.mainnet checks o) (s : BeaconState Preset.mainnet .glamsterdam)
    (hroom : EpochRoom (by decide) s) (hslotLimit : (getCurrentEpoch s).toNat ≠ 2 ^ 59 - 3) :
    Spec.SameResultOrBothFail (Spec.process_epoch Spec.Preset.mainnet o (toSpecState s))
      (toSpecResult toSpecState (processEpoch Config.mainnet checks s)) := by
  rw [← toSpecPreset_mainnet]
  refine process_epoch_gloas divisorsNonzero_mainnet committeeBounds_mainnet ho s hroom ?_
  show ((getCurrentEpoch s).toNat + 1 + 2) * 32 ≠ 2 ^ 64
  omega

/-- Gloas, minimal: `process_epoch_gloas` without preset hypotheses. -/
theorem process_epoch_gloas_minimal {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.minimal checks o) (s : BeaconState Preset.minimal .glamsterdam)
    (hroom : EpochRoom (by decide) s) (hslotLimit : (getCurrentEpoch s).toNat ≠ 2 ^ 61 - 3) :
    Spec.SameResultOrBothFail (Spec.process_epoch Spec.Preset.minimal o (toSpecState s))
      (toSpecResult toSpecState (processEpoch Config.minimal checks s)) := by
  rw [← toSpecPreset_minimal]
  refine process_epoch_gloas divisorsNonzero_minimal committeeBounds_minimal ho s hroom ?_
  show ((getCurrentEpoch s).toNat + 1 + 2) * 8 ≠ 2 ^ 64
  omega

/-- Gloas, mainnet: `process_epoch_gloas_of_ok` without preset hypotheses. -/
theorem process_epoch_gloas_of_ok_mainnet {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.mainnet checks o) (s : BeaconState Preset.mainnet .glamsterdam)
    (hroom : EpochRoom (by decide) s) {state : Spec.BeaconState}
    (h : Spec.process_epoch Spec.Preset.mainnet o (toSpecState s) = .ok state) :
    toSpecResult toSpecState (processEpoch Config.mainnet checks s) = .ok state := by
  rw [← toSpecPreset_mainnet] at h
  exact process_epoch_gloas_of_ok divisorsNonzero_mainnet committeeBounds_mainnet ho s hroom h

/-- Gloas, minimal: `process_epoch_gloas_of_ok` without preset hypotheses. -/
theorem process_epoch_gloas_of_ok_minimal {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.minimal checks o) (s : BeaconState Preset.minimal .glamsterdam)
    (hroom : EpochRoom (by decide) s) {state : Spec.BeaconState}
    (h : Spec.process_epoch Spec.Preset.minimal o (toSpecState s) = .ok state) :
    toSpecResult toSpecState (processEpoch Config.minimal checks s) = .ok state := by
  rw [← toSpecPreset_minimal] at h
  exact process_epoch_gloas_of_ok divisorsNonzero_minimal committeeBounds_minimal ho s hroom h

/-- Fulu, mainnet: `process_epoch_fulu` without preset hypotheses. -/
theorem process_epoch_fulu_mainnet {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.mainnet checks o) (s : BeaconState Preset.mainnet .fusaka)
    (hroom : EpochRoom (by decide) s) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState s with
          state := ← Spec.process_epoch_fulu Spec.Preset.mainnet Spec.FuluConfig.mainnet o
            (toSpecFuluState s).state })
      (toSpecResult toSpecFuluState (processEpoch Config.mainnet checks s)) := by
  rw [← toSpecPreset_mainnet, ← toSpecFuluConfig_mainnet]
  exact process_epoch_fulu divisorsNonzero_mainnet committeeBounds_mainnet ho s hroom

/-- Fulu, minimal: `process_epoch_fulu` without preset hypotheses. -/
theorem process_epoch_fulu_minimal {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches Preset.minimal checks o) (s : BeaconState Preset.minimal .fusaka)
    (hroom : EpochRoom (by decide) s) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState s with
          state := ← Spec.process_epoch_fulu Spec.Preset.minimal Spec.FuluConfig.minimal o
            (toSpecFuluState s).state })
      (toSpecResult toSpecFuluState (processEpoch Config.minimal checks s)) := by
  rw [← toSpecPreset_minimal, ← toSpecFuluConfig_minimal]
  exact process_epoch_fulu divisorsNonzero_minimal committeeBounds_minimal ho s hroom

end EpochProofs.EthLib
