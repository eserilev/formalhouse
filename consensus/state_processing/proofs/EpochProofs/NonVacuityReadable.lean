import EpochProofs.NonVacuity
import EpochProofs.HeadlinePresets

/-!
# The hypotheses of the headline theorems can hold together

The witness of `NonVacuity.lean` (`witnessState`, and the Etheorem states `witnessEtheorem`,
`witnessEtheoremFulu` that map to it: minimal preset, last slot of epoch 0, eight active
validators at 2048 ETH) also satisfies the bundles of `FormalhouseReadable.lean`.

- `agrees_pyspec_hyps_at_witness`, `agrees_pyspec_hyps_at_witness_fulu`: the state hypotheses
  that the `_agrees_pyspec` theorems use (`ReachableInvariants`, `AtEpochBoundary`, so also
  `HistoricalSummariesBelowLimit`) hold at `witnessState`, `witnessStateFulu`. The Gloas one then
  applies there (`lighthouse_model_gloas_epoch_agrees_pyspec_at_witness`).
- `gloas_bundles_at_witness`, `fulu_bundles_at_witness`: the chain, Etheorem (Gloas divergence, Fulu bridge) and
  oracle bundles hold together at `witnessEtheorem` (`witnessEtheoremFulu`), given the facts that
  `NonVacuity.lean` also takes as they are (the Fulu Etheorem conditions, SHA-256 output
  size).

Not covered, as in `NonVacuity.lean`: the runs (`GloasEpochRun`, `FuluEpochRun`, whose supply
bounds range over every run), the cache facts and the Rust glue.
-/

namespace EpochProofs.Witness

open EpochProofs.Spec EpochProofs.Formalhouse

section Minimal

attribute [local instance] minimalCfg fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- The state hypotheses of the Gloas agreement theorem hold at `witnessState`. -/
theorem agrees_pyspec_hyps_at_witness :
    ReachableInvariants witnessState ∧ AtEpochBoundary witnessState ∧
      HistoricalSummariesBelowLimit witnessState :=
  ⟨witnessState_reachableInvariants, witnessState_atEpochBoundary,
    witnessState_atEpochBoundary.2.2⟩

/-- The state hypotheses of the Fulu agreement theorem hold at `witnessStateFulu`. -/
theorem agrees_pyspec_hyps_at_witness_fulu :
    ReachableInvariants witnessStateFulu ∧ AtEpochBoundary witnessStateFulu ∧
      HistoricalSummariesBelowLimit witnessStateFulu :=
  ⟨witnessStateFulu_reachableInvariants, witnessStateFulu_atEpochBoundary,
    witnessStateFulu_atEpochBoundary.2.2⟩

/-- At `witnessState`, the Lean model of Lighthouse's Gloas epoch and the transcription agree,
for every oracle. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_at_witness (o : Oracle) :
    SameResultOrBothFail (process_epoch_lighthouse o witnessState)
      (process_epoch P o witnessState) :=
  lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants o witnessState_reachableInvariants
    witnessState_atEpochBoundary

end Minimal

section GloasEState

attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The Gloas chain, Etheorem divergence and oracle bundles hold together at
`witnessEtheorem`. -/
theorem gloas_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, GloasChainAssumptions o (toSpecState witnessEtheorem) ∧
      GloasEtheoremDivergenceAssumptions witnessEtheorem ∧ GloasOracleMatchesEtheorem o := by
  obtain ⟨o, ha⟩ := gloasFinalHypotheses_witness hsha
  refine ⟨o, ⟨fun t h => ?_, fun t h => ?_, ha.rows, ha.slot, ha.boundary.2.2, ha.vectors,
    fun t h => (ha.committees t h).1⟩, ⟨ha.etheoremRoom⟩, ⟨ha.oracle, ha.sha⟩⟩
  · have hp := (ha.committees t h).2
    exact ⟨hp.syncActive, hp.proposers, hp.ptc32⟩
  · have hp := (ha.committees t h).2
    exact ⟨hp.selSync, hp.selProp, hp.selPtc⟩

end GloasEState

section FuluEState

attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The Fulu chain, Etheorem divergence and oracle bundles hold together at
`witnessEtheoremFulu`, given the Fulu Etheorem conditions. -/
theorem fulu_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Etheorem.Fulu.FuluEpochConds P o witnessEtheoremFulu →
      FuluChainAssumptions o (toSpecStateFulu witnessEtheoremFulu) ∧
        FuluEtheoremBridgeConditions o witnessEtheoremFulu ∧
        FuluOracleMatchesEtheorem o := by
  obtain ⟨o, ho, hk⟩ := fulu_oracle_witness
  refine ⟨o, fun hconds => ⟨?_, ⟨hconds⟩, ⟨ho, hsha⟩⟩⟩
  rw [toSpecStateFulu, witnessEtheoremFulu_abs]
  have hc := witnessStateFulu_atCommitteeStepState o (fun v _ => hk _)
  refine ⟨fun t h => ?_, fun t h => ?_, witnessStateFulu_physicalLimits, by decide +kernel,
    witnessStateFulu_atEpochBoundary.2.2, witnessStateFulu_fuluVectors, fun t h => (hc t h).1⟩
  · have hp := (hc t h).2
    exact ⟨hp.syncActive, hp.proposers⟩
  · have hp := (hc t h).2
    exact ⟨hp.selSync, hp.selProp⟩

end FuluEState

end EpochProofs.Witness
