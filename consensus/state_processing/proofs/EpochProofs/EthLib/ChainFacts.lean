import EthLib.Consensus.Proofs.Transition.Totality.ShapeBlock
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import Batteries.Tactic.OpenPrivate

/-!
# Facts that every step of an EthLib chain keeps

A genesis state has these facts, and each slot and block keeps them.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Consensus

open private Kept.delay Kept.processBlock Kept.advanceSlot Kept.upgradeNext
  from EthLib.Consensus.Proofs.Transition.ActivationExitOrder

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Each validator with an exit epoch can withdraw `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` epochs
after it, or later. -/
def ExitsWaitForWithdrawal (config : Config) {fork : Fork} (state : BeaconState preset fork) :
    Prop :=
  ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
    validator.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
      validator.withdrawableEpoch.toNat

/-- Facts about a state that a genesis state has, and that each slot and block keeps. -/
structure ChainFacts (config : Config) {fork : Fork} (state : BeaconState preset fork) : Prop where
  /-- The checkpoints are in order, and each validator exits before it can withdraw. -/
  invariant : Invariant state
  /-- The lists have one entry for each validator. Each effective balance is below its limit. Each
  pending consolidation names two validators. -/
  shaped : Shaped state
  /-- No two validators have the same public key. -/
  keys : PubkeysDistinct state
  /-- Each validator with an exit epoch waits for the withdrawal delay. -/
  exitDelay : ExitsWaitForWithdrawal config state

/-- A slot or a block keeps the facts. -/
theorem ChainFacts.chainStep (caps : CapOrder preset) {before after : ForkedBeaconState preset}
    (facts : ChainFacts config before.state) (step : ChainStep config checks before after) :
    ChainFacts config after.state := by
  refine ⟨?_, ?_, (validatorKeys_prefix_and_distinct_of_chainSteps (.single step)).2 facts.keys, ?_⟩
  · cases step with
    | slot ok => exact (advanceSlotAcross_invariant facts.invariant ok).1
    | block engine signed validateResult ok =>
      exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant facts.invariant
  · cases step with
    | slot ok =>
      obtain ⟨_, advanced, upgraded⟩ := bind_ok_iff.mp ok
      exact processUpgrades_shaped (forked := ⟨_, _⟩) caps.activation caps.compounding upgraded
        (advanceSlot_shaped advanced facts.shaped)
    | block engine signed validateResult ok =>
      exact processBlock_shaped caps.compounding (applySignedBlock_ok ok).2.1 facts.shaped
  · cases step with
    | slot ok =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
      exact processUpgrades_induction
        (property := fun state => ExitsWaitForWithdrawal config state.state)
        (fun prior ok => Kept.delay (Kept.upgradeNext ok) prior)
        (show ExitsWaitForWithdrawal config
          (⟨before.fork, advanced⟩ : ForkedBeaconState preset).state from
          Kept.delay (Kept.advanceSlot facts.invariant advancedOk) facts.exitDelay) upgraded
    | block engine signed validateResult ok =>
      exact Kept.delay (Kept.processBlock (applySignedBlock_ok ok).2.1) facts.exitDelay

/-- A run keeps the facts. -/
theorem ChainFacts.run (caps : CapOrder preset) {first last : ForkedBeaconState preset}
    (facts : ChainFacts config first.state) (run : Run config checks first last) :
    ChainFacts config last.state := by
  induction run with
  | nil => exact facts
  | snoc _ step ih => exact ih.chainStep caps step.chainStep

/-- A genesis state has a fork before Altair. -/
theorem genesis_fork {genesis : ForkedBeaconState preset}
    (isGenesis : Genesis config checks genesis) : genesis.fork < .altair := by
  obtain ⟨_, _, _, ok⟩ := isGenesis
  exact (initializeBeaconStateFromEth1_ok ok).1

/-- A genesis state has the facts. -/
theorem ChainFacts.genesis {genesis : ForkedBeaconState preset}
    (isGenesis : Genesis config checks genesis) : ChainFacts config genesis.state := by
  have early := genesis_fork isGenesis
  refine ⟨Genesis.invariant isGenesis, ⟨(Genesis.invariant isGenesis).balancesMatch,
    fun altair => absurd early (Nat.not_lt_of_le altair),
    fun altair => absurd early (Nat.not_lt_of_le altair),
    Genesis.effectiveBalance_capped isGenesis,
    fun electra => absurd early (Nat.not_lt_of_le (Nat.le_trans (by decide) electra))⟩, ?_, ?_⟩
  · obtain ⟨_, _, _, ok⟩ := isGenesis
    exact (validatorKeys_prefix_and_distinct_of_genesis_chainSteps ok .refl).2
  · intro validator member
    obtain ⟨i, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    exact Run.exit_withdrawable_delay .nil isGenesis i _ (by simp [inside])

/-- `processSlot` keeps the facts. -/
theorem ChainFacts.processSlot {fork : Fork} {state after : BeaconState preset fork}
    (facts : ChainFacts config state) (ok : processSlot state = .ok after) :
    ChainFacts config after := by
  have invariant := (frame_processSlot ok).invariant facts.invariant
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok ok
  exact ⟨invariant, ⟨facts.shaped.balancesMatch, facts.shaped.participationMatches,
    facts.shaped.inactivityScoresMatch, facts.shaped.capped, facts.shaped.inside⟩, facts.keys,
    facts.exitDelay⟩

/-- A validator that has no exit epoch has no withdrawable epoch. -/
theorem withdrawableEpoch_of_no_exit {fork : Fork} {state : BeaconState preset fork}
    (invariant : Invariant state) : ∀ validator ∈ state.validators.data,
      validator.exitEpoch = FAR_FUTURE_EPOCH → validator.withdrawableEpoch = FAR_FUTURE_EPOCH := by
  intro validator member noExit
  have ordered := UInt64.le_iff_toNat_le.mp (noExit ▸ invariant.exitsOrdered validator member)
  have bound := validator.withdrawableEpoch.toNat_lt
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  exact UInt64.toNat_inj.mp (by omega)

end EpochProofs.EthLib
