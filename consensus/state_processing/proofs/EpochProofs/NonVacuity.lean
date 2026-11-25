import EpochProofs.Headline
import EpochProofs.NonVacuitySpec

/-!
# The hypotheses of the headline theorems can hold together

A theorem with hypotheses that cannot hold together proves nothing. The headline theorems had
this bug: the committee conditions held at every state `s` with `CommFrame t s`. `CommFrame`
fixes only the slot, the list lengths and the RANDAO length, so it admits `t` with every
validator list emptied, where a sync committee candidate fails to exist. That hypothesis was false
for every input. It now holds at the one state that the epoch passes to the committee steps
(`Spec.AtCommitteeStepState`, `Spec.FuluAtCommitteeStepState`).

This file gives a witness: `witnessState`, a minimal-preset state at the last slot of epoch 0
with eight active compounding validators (`witnessValidator`) at `2048 ETH`; `witnessStateFulu`,
the same state without the Gloas fields; and `witnessEtheorem`, `witnessEtheoremFulu`, the
Etheorem states that map to them. Lean computes the epoch steps on it.

- `gloas_bundles_at_witness`: the chain, Etheorem divergence and oracle bundles of the Gloas
  headline theorems (`Assumptions.lean`) hold together at `witnessEtheorem`, with an oracle that
  agrees with Etheorem, given that SHA-256 returns 32 bytes.
- `fulu_bundles_at_witness`: the chain and oracle bundles of the Fulu headline theorems hold at
  `witnessEtheoremFulu`, given also the Etheorem bridge bundle (`FuluEtheoremBridgeConditions`).
- `gloas_spec_witness`, `fulu_spec_witness`: at the same state, the start-state facts
  (`FuluStartOk`), unique pubkeys and the reachable-state facts that the run gives
  (`ReachableInvariants`) hold too, the epoch reaches its committee steps (so the committee
  conditions are not vacuous), and the spec `process_epoch` returns `ok`.
- `agrees_pyspec_hyps_at_witness`, `agrees_pyspec_hyps_at_witness_fulu`: the state hypotheses
  that the `_agrees_pyspec` theorems use hold at `witnessState`, `witnessStateFulu`, and
  `lighthouse_model_gloas_epoch_agrees_pyspec_at_witness` applies the Gloas one there.
- `selFin_full`: the selection facts in `CommitteeStepPreconds` hold for every hash when every
  candidate has the maximum effective balance.

Not covered: the runs (`GloasEpochRun`, `FuluEpochRun`, whose supply bounds range over every
run), the Fulu Etheorem bridge conditions (`FuluEtheoremBridgeConditions`), the hash backend
(`sha`), the cache facts and the Rust glue.
-/

namespace EpochProofs.Witness

open EpochProofs.Spec

/-! ## The assumption structures

The witnesses above are reference states. Here they are the `toSpecState` of Etheorem states, so
they give the bundles of `Assumptions.lean` directly. -/

section GloasEState

attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩


/-- A validator of the witness: active from epoch 0, never exits, compounding credentials, the
maximum effective balance. -/
def witnessEtheoremValidator (k : Nat) : EthCLSpecs.Gloas.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The witness as an Etheorem state on the minimal preset: the last slot of epoch 0, eight
validators, every other field at its default. -/
def witnessEtheorem : EthCLSpecs.Gloas.BeaconState :=
  { (default : EthCLSpecs.Gloas.BeaconState) with
    slot := 7
    validators := ⟨#[witnessEtheoremValidator 0, witnessEtheoremValidator 1,
      witnessEtheoremValidator 2,
      witnessEtheoremValidator 3, witnessEtheoremValidator 4, witnessEtheoremValidator 5,
      witnessEtheoremValidator 6, witnessEtheoremValidator 7]⟩
    balances := ⟨Array.replicate 8 2048000000000⟩
    previousEpochParticipation := ⟨Array.replicate 8 0⟩
    currentEpochParticipation := ⟨Array.replicate 8 0⟩
    inactivityScores := ⟨Array.replicate 8 0⟩ }


theorem witnessEtheorem_abs : Etheorem.toSpecState witnessEtheorem = witnessState := by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The oracle hypotheses hold for an oracle that accepts every key (`etheoremOracle_agrees`). -/
theorem oracle_witness : ∃ o, Etheorem.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.etheoremOracle keyOracle, Etheorem.etheoremOracle_agrees _, fun _ => rfl⟩

/-- The chain, Etheorem divergence and oracle bundles of the Gloas headline theorems hold
together at `witnessEtheorem` on the minimal preset, given the fact about the hash backend that
the oracle bundle takes as it is: SHA-256 returns 32 bytes. -/
theorem gloas_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Formalhouse.GloasChainAssumptions o (Etheorem.toSpecState witnessEtheorem) ∧
      Etheorem.GloasEtheoremDivergenceAssumptions witnessEtheorem ∧
      Etheorem.GloasOracleMatchesEtheorem o := by
  obtain ⟨o, ho, hk⟩ := oracle_witness
  have hc := witnessState_atCommitteeStepState o (fun v _ => hk _)
  rw [witnessEtheorem_abs]
  refine ⟨o, {
    syncCandidate := fun t h => (hc t h).2.syncActive
    proposerCandidate := fun t h => (hc t h).2.proposers
    enoughActiveForPtc := fun t h => (hc t h).2.ptc32
    syncSelectionEnds := fun t h => (hc t h).2.selSync
    proposerSelectionEnds := fun t h => (hc t h).2.selProp
    ptcSelectionEnds := fun t h => (hc t h).2.selPtc
    physicalLimits := witnessState_physicalLimits
    slotFarFromOverflow := by decide +kernel
    historicalSummariesBelowLimit := witnessState_atEpochBoundary.2.2
    committeeStepStateFacts := fun t h => ⟨(hc t h).1.regLen, (hc t h).1.keys⟩ },
    ⟨by rw [witnessEtheorem_abs]; decide +kernel⟩, ⟨ho, hsha⟩⟩

end GloasEState

section FuluEState

attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- `witnessEtheoremValidator` as a Fulu validator. -/
def witnessEtheoremValidatorFulu (k : Nat) : EthCLSpecs.Fulu.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The Fulu witness as an Etheorem Fulu state. -/
def witnessEtheoremFulu : EthCLSpecs.Fulu.BeaconState :=
  { (default : EthCLSpecs.Fulu.BeaconState) with
    slot := 7
    validators := ⟨#[witnessEtheoremValidatorFulu 0, witnessEtheoremValidatorFulu 1,
      witnessEtheoremValidatorFulu 2,
      witnessEtheoremValidatorFulu 3, witnessEtheoremValidatorFulu 4,
        witnessEtheoremValidatorFulu 5,
      witnessEtheoremValidatorFulu 6, witnessEtheoremValidatorFulu 7], by decide⟩
    balances := ⟨Array.replicate 8 2048000000000, by decide⟩
    previousEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    currentEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    inactivityScores := ⟨Array.replicate 8 0, by decide⟩ }

theorem witnessEtheoremFulu_abs : Etheorem.Fulu.toSpecState witnessEtheoremFulu = witnessStateFulu :=
    by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

theorem fulu_oracle_witness :
    ∃ o, Etheorem.Fulu.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.Fulu.etheoremOracle keyOracle, Etheorem.Fulu.etheoremOracle_agrees _, fun _ => rfl⟩

/-- The chain and oracle bundles of the Fulu headline theorems hold at `witnessEtheoremFulu` on
the minimal preset, with the Etheorem bridge bundle, given that bundle and SHA-256 returning 32
bytes. The bridge conditions are facts about Etheorem's intermediate states, taken as they
are. -/
theorem fulu_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Etheorem.Fulu.FuluEtheoremBridgeConditions P o witnessEtheoremFulu →
      Formalhouse.FuluChainAssumptions o (Etheorem.Fulu.toSpecState witnessEtheoremFulu) ∧
        Etheorem.Fulu.FuluEtheoremBridgeConditions P o witnessEtheoremFulu ∧
        Etheorem.Fulu.FuluOracleMatchesEtheorem o := by
  obtain ⟨o, ho, hk⟩ := fulu_oracle_witness
  refine ⟨o, fun hconds => ⟨?_, hconds, ⟨ho, hsha⟩⟩⟩
  rw [witnessEtheoremFulu_abs]
  have hc := witnessStateFulu_atCommitteeStepState o (fun v _ => hk _)
  exact {
    syncCandidate := fun t h => (hc t h).2.syncActive
    proposerCandidate := fun t h => (hc t h).2.proposers
    syncSelectionEnds := fun t h => (hc t h).2.selSync
    proposerSelectionEnds := fun t h => (hc t h).2.selProp
    physicalLimits := witnessStateFulu_physicalLimits
    slotFarFromOverflow := by decide +kernel
    historicalSummariesBelowLimit := witnessStateFulu_atEpochBoundary.2.2
    committeeStepStateFacts := fun t h => ⟨(hc t h).1.regLen, (hc t h).1.keys⟩ }

end FuluEState

end EpochProofs.Witness
