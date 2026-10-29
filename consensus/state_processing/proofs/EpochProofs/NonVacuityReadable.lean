import EpochProofs.NonVacuity
import EpochProofs.HeadlinePresets

/-!
# The hypotheses of the readable theorems can hold together

The witness of `NonVacuity.lean` (`wt`, `we`, `wef`: minimal preset, last slot of epoch 0, eight
active validators at 2048 ETH) also satisfies the bundles of `FormalhouseReadable.lean`.

- `sameOk_witness`, `sameOk_witness_fulu`: the state hypotheses that the SameOk theorems use
  (the reachable-state invariants, `TailPre`, so also `HistRoom`) hold at `wt`, `wtf`. The SameOk
  theorems then apply there (`sameOk_at_witness`).
- `gloasChain_witness`, `fuluChain_witness`: `GloasChainAssumptions` (`FuluChainAssumptions`),
  `EtheoremFaithful` and `OracleMatchesEtheorem` hold at `we` (`wef`), given the facts that
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

/-- The state hypotheses of the Gloas SameOk theorem hold at `wt`. -/
theorem sameOk_witness : EpochInputOk'' EpochSupply wt ∧ TailPre wt ∧ HistRoom wt :=
  ⟨wt_epochInputOk, wt_tailPre, wt_tailPre.2.2⟩

/-- The state hypotheses of the Fulu SameOk theorem hold at `wtf`. -/
theorem sameOk_witness_fulu : EpochInputOk'' EpochSupply wtf ∧ TailPre wtf ∧ HistRoom wtf :=
  ⟨wtf_epochInputOk, wt_tailPre, wt_tailPre.2.2⟩

/-- At `wt`, Lighthouse's Gloas epoch and the transcription agree, for every oracle. -/
theorem sameOk_at_witness (o : Oracle) :
    SameOk (process_epoch_lh_order o wt) (process_epoch P o wt) :=
  gloas_sameOk_of_invariants o wt_epochInputOk wt_tailPre

end Minimal

section GloasEState

attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The Gloas chain, Etheorem and oracle bundles hold together at `we`. -/
theorem gloasChain_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, GloasChainAssumptions o (Etheorem.absEState we) ∧ EtheoremFaithful we ∧
      OracleMatchesEtheorem o := by
  obtain ⟨o, ha⟩ := gloasAssumptions_witness hsha
  exact ⟨o, ⟨fun t h => (ha.committees t h).2, ha.rows, ha.slot, ha.boundary.2.2, ha.vectors,
    fun t h => (ha.committees t h).1⟩, ⟨ha.etheoremRoom⟩, ⟨ha.oracle, ha.sha⟩⟩

end GloasEState

section FuluEState

attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The Fulu chain, Etheorem and oracle bundles hold together at `wef`, given the Fulu Etheorem
conditions. -/
theorem fuluChain_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Etheorem.Fulu.FuluEpochConds P o wef →
      FuluChainAssumptions o (Etheorem.Fulu.absEState wef) ∧ EtheoremFaithfulFulu o wef ∧
        OracleMatchesEtheoremFulu o := by
  obtain ⟨o, ho, hk⟩ := fulu_oracle_witness
  refine ⟨o, fun hconds => ⟨?_, ⟨hconds⟩, ⟨ho, hsha⟩⟩⟩
  have hc := wef_abs ▸ wtf_fuluCommAt o (fun v _ => hk _)
  exact ⟨fun t h => (hc t h).2, wef_abs ▸ wtf_rowBounds, by rw [wef_abs]; decide +kernel,
    wef_abs ▸ wt_tailPre.2.2, wef_abs ▸ wtf_fuluVectors, fun t h => (hc t h).1⟩

end FuluEState

end EpochProofs.Witness
