import EpochProofs.FormalhouseReadable

/-!
# The headline theorems

The results of this project, stated with the names of `FormalhouseReadable.lean`, where each
name has a docstring.

- `lighthouse_model_*`: about the Lean model of Lighthouse's epoch processing
  (`process_epoch_lighthouse`). `lighthouse_rust_*`: about the composed Aeneas translation of the
  Rust (`Compose.epoch`), given the glue facts.
- `*_eq_etheorem`: the epoch succeeds and its result equals Etheorem's `processEpoch`.
  `*_agrees_pyspec`: the epoch and the hand-written pyspec transcription give the same state, or
  both fail.

`Spec.P` is the preset (`Spec.PresetCfg`) and `Spec.FC` the Fulu config (`Spec.FuluCfg`). Every
theorem holds for any preset and config. The Etheorem ones ask that they agree with Etheorem's
(`hpreset`) and, for Gloas, that Lighthouse's `2^24` limit on `historical_summaries` is at most
Etheorem's (`hhistLimit`). `HeadlinePresets.lean` instantiates them for mainnet and minimal, where
both hold.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec
open Aeneas.Std (U64)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {o : Spec.Oracle} {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig}
  {uc : Spec.UpgradeConfig} {init : Spec.FuluState} {s : Spec.BeaconState}

section Gloas
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {e : EtheoremState}

/-- Gloas: at every epoch boundary of a run from Fulu across the Gloas fork, the Lean model of
Lighthouse's epoch succeeds and equals Etheorem's, and its cache reads give the spec values. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {progressiveCache : ProgressiveBalancesInner} {totalActiveBalance : U64} {M : Type}
    {pubkeyIndex} {pubkeyMap : M}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e)) :
    GloasLighthouseEqualsEtheorem o e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
        (toSpecState e) := by
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := hcaches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_final hpreset
    hhistLimit o fo c uc init e hrun.input (gloasFinalHypotheses_of hrun hchain hetheorem horacle)
    progressiveCache hcaches.progressive totalActiveBalance b hagree htotal laws b' hpre hpk0 hupd
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

/-- Gloas, for the composed Rust: the same, for `Compose.epoch` on a Rust state that views as
the epoch input, given the glue facts. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {progressiveCache : ProgressiveBalancesInner} {totalActiveBalance : U64} {M : Type}
    {pubkeyIndex} {pubkeyMap : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts G o view st (toSpecState e)) :
    GloasRustEqualsEtheorem G view st e := by
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨pview, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := hcaches.pubkeyCache
  exact formalhouse_gloas_epoch_rust hpreset hhistLimit o fo c uc init e hrun.input
    (gloasFinalHypotheses_of hrun hchain hetheorem horacle) progressiveCache hcaches.progressive
    totalActiveBalance b hagree htotal laws b' hpre hpk0 hupd G view st hrust.viewEq hrust.glue

end Gloas

section Fulu
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {e : EtheoremFuluState}

/-- Fulu: at every epoch boundary of a Fulu run, the Lean model of Lighthouse's epoch succeeds
and equals Etheorem's. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheoremFulu Spec.P Spec.FC)
    (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o) :
    FuluLighthouseEqualsEtheorem o e :=
  formalhouse_fulu_epoch_final hpreset o fo c init e hrun.input
    (fuluFinalHypotheses_of hrun hchain hetheorem horacle)

/-- Fulu, for the composed Rust. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheoremFulu Spec.P Spec.FC)
    {σ E : Type} {G : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState} {st : σ}
    (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o)
    (hrust : FuluRustGlueFacts G o view st (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem G view st e :=
  formalhouse_fulu_epoch_rust hpreset o fo c init e hrun.input
    (fuluFinalHypotheses_of hrun hchain hetheorem horacle) G view st hrust.viewEq hrust.glue

end Fulu

/-- Gloas, against the hand-written pyspec transcription: at every epoch boundary of a run, the
Lean model of Lighthouse's epoch and the spec's give the same state, or both fail. No pyspec
precondition. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec (hrun : GloasEpochRun o fo c uc init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse o s) (Spec.process_epoch Spec.P o s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants o hrun.invariants
    (hrun.atEpochBoundary hhist)

/-- Fulu, against the hand-written pyspec transcription. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec (hrun : FuluEpochRun o fo c init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu o s)
      (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  Spec.lighthouse_fulu_epoch_sameOk o s hrun.invariants (hrun.atEpochBoundary hhist)

end EpochProofs.Formalhouse
