import EpochProofs.FormalhouseReadable

/-!
# The headline theorems

The results of this project, stated with the names of `FormalhouseReadable.lean`, where each
name has a docstring.

- `lighthouse_model_*`: about the Lean model of Lighthouse's epoch processing
  (`process_epoch_lighthouse`). `lighthouse_rust_*`: about the composed Aeneas translation of the
  Rust (`Compose.epoch`), given the glue facts.
- `*_eq_etheorem`: the epoch succeeds and its result equals Etheorem's `processEpoch`.
  `*_agrees_pyspec`: the epoch and this project's hand-written Lean transcription of the pyspec
  (`Spec.process_epoch`) give the same state, or both fail.

`Spec.P` is the preset (`Spec.PresetCfg`) and `Spec.FC` the Fulu config (`Spec.FuluCfg`). Every
theorem holds for any preset and config. The Etheorem ones ask that they agree with Etheorem's
(`hpreset`) and, for Gloas, that Lighthouse's `2^24` limit on `historical_summaries` is at most
Etheorem's (`hhistLimit`). `HeadlinePresets.lean` instantiates them for mainnet and minimal, where
both hold.

The run is described by `oracle` (BLS, SHA-256 and `hash_tree_root`, `Spec.Oracle`),
`fuluOracle` and `blockConfig` (the Fulu block processing parameters), `upgradeConfig` (the Gloas
fork upgrade) and `fuluStart`, the Fulu state the run starts from. For the Rust theorems, `σ` is
the type of the Rust state, `view` maps it to the transcription's state, and `rustGlue` holds the
untranslated Rust between the translated functions (`E` is a type it uses).
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec
open Aeneas.Std (U64)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle}
  {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}

section Gloas
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {e : EtheoremState}

/-- Gloas: at every epoch boundary of a run from Fulu across the Gloas fork, the Lean model of
Lighthouse's epoch succeeds and equals Etheorem's, and its cache reads give the spec values. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {progressiveCache : ProgressiveBalancesInner} {totalActiveBalance : U64} {PubkeyMap : Type}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := hcaches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_final hpreset
    hhistLimit oracle fuluOracle blockConfig upgradeConfig fuluStart e hrun.input
    (gloasFinalHypotheses_of hrun hchain hetheorem horacle) progressiveCache hcaches.progressive
    totalActiveBalance b hagree htotal laws b' hpre hpk0 hupd
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

/-- Gloas, for the composed Rust: the same, for `Compose.epoch` on a Rust state that views as
the epoch input, given the glue facts. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {progressiveCache : ProgressiveBalancesInner} {totalActiveBalance : U64} {PubkeyMap : Type}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState e)) :
    GloasRustEqualsEtheorem rustGlue view rustState e := by
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨pview, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := hcaches.pubkeyCache
  exact formalhouse_gloas_epoch_rust hpreset hhistLimit oracle fuluOracle blockConfig
    upgradeConfig fuluStart e hrun.input (gloasFinalHypotheses_of hrun hchain hetheorem horacle)
    progressiveCache hcaches.progressive totalActiveBalance b hagree htotal laws b' hpre hpk0
    hupd rustGlue view rustState hrust.viewEq hrust.glue

end Gloas

section Fulu
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {e : EtheoremFuluState}

/-- Fulu: at every epoch boundary of a Fulu run, the Lean model of Lighthouse's epoch succeeds
and equals Etheorem's. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheoremFulu Spec.P Spec.FC)
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    FuluLighthouseModelEqualsEtheorem oracle e :=
  formalhouse_fulu_epoch_final hpreset oracle fuluOracle blockConfig fuluStart e hrun.input
    (fuluFinalHypotheses_of hrun hchain hetheorem horacle)

/-- Fulu, for the composed Rust. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheoremFulu Spec.P Spec.FC)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    (hrust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem rustGlue view rustState e :=
  formalhouse_fulu_epoch_rust hpreset oracle fuluOracle blockConfig fuluStart e hrun.input
    (fuluFinalHypotheses_of hrun hchain hetheorem horacle) rustGlue view rustState hrust.viewEq
    hrust.glue

end Fulu

/-- Gloas, against the hand-written pyspec transcription: at every epoch boundary of a run, the
Lean model of Lighthouse's epoch and the transcription's give the same state, or both fail. No
pyspec precondition. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants oracle hrun.invariants
    (hrun.atEpochBoundary hhistBelowLimit)

/-- Fulu, against the hand-written pyspec transcription. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  Spec.lighthouse_fulu_epoch_sameOk oracle s hrun.invariants
    (hrun.atEpochBoundary hhistBelowLimit)

end EpochProofs.Formalhouse
