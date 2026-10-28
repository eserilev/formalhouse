import EpochProofs.Headline

/-!
# The headline theorems on mainnet and minimal

Each instantiates a theorem of `Headline.lean` with the preset, its `PresetCfg.Ok` and
`PresetCfg.Bounds` facts, the Fulu config, and the Etheorem preset with the agreement facts
(`hpreset`; `hhistLimit` by `decide`).
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EpochProofs.Etheorem
open Aeneas.Std (U64)

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
/-- `lighthouse_model_gloas_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type} {pubkeyIndex} {pubkeyMap : M}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e)) :
    GloasLighthouseEqualsEtheorem o e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
        (toSpecState e) :=
  lighthouse_model_gloas_epoch_eq_etheorem epochPresetAgrees_mainnet (by decide) hrun hchain
    hetheorem horacle hcaches

/-- `lighthouse_rust_gloas_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type} {pubkeyIndex} {pubkeyMap : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts G o view st (toSpecState e)) :
    GloasRustEqualsEtheorem G view st e :=
  lighthouse_rust_gloas_epoch_eq_etheorem epochPresetAgrees_mainnet (by decide) hrun hchain
    hetheorem horacle hcaches hrust
end

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
/-- `lighthouse_model_fulu_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {o fo c init} {e : EtheoremFuluState} (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o) :
    FuluLighthouseEqualsEtheorem o e :=
  lighthouse_model_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_mainnet hrun hchain hetheorem
    horacle

/-- `lighthouse_rust_fulu_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {o fo c init} {e : EtheoremFuluState} {σ E : Type} {G : Compose.EpochGlueFulu σ E}
    {view : σ → Spec.BeaconState} {st : σ} (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o)
    (hrust : FuluRustGlueFacts G o view st (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem G view st e :=
  lighthouse_rust_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_mainnet hrun hchain hetheorem
    horacle hrust
end

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet {o : Spec.Oracle}
    {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig} {uc : Spec.UpgradeConfig}
    {init : Spec.FuluState} {s : Spec.BeaconState} (hrun : GloasEpochRun o fo c uc init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse o s) (Spec.process_epoch Spec.P o s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhist

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet {o : Spec.Oracle}
    {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig} {init : Spec.FuluState}
    {s : Spec.BeaconState} (hrun : FuluEpochRun o fo c init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu o s)
      (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhist

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
/-- `lighthouse_model_gloas_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type} {pubkeyIndex} {pubkeyMap : M}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e)) :
    GloasLighthouseEqualsEtheorem o e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
        (toSpecState e) :=
  lighthouse_model_gloas_epoch_eq_etheorem epochPresetAgrees_minimal (by decide) hrun hchain
    hetheorem horacle hcaches

/-- `lighthouse_rust_gloas_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type} {pubkeyIndex} {pubkeyMap : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyIndex pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts G o view st (toSpecState e)) :
    GloasRustEqualsEtheorem G view st e :=
  lighthouse_rust_gloas_epoch_eq_etheorem epochPresetAgrees_minimal (by decide) hrun hchain
    hetheorem horacle hcaches hrust
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
/-- `lighthouse_model_fulu_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {o fo c init} {e : EtheoremFuluState} (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o) :
    FuluLighthouseEqualsEtheorem o e :=
  lighthouse_model_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_minimal hrun hchain hetheorem
    horacle

/-- `lighthouse_rust_fulu_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {o fo c init} {e : EtheoremFuluState} {σ E : Type} {G : Compose.EpochGlueFulu σ E}
    {view : σ → Spec.BeaconState} {st : σ} (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremDivergenceAssumptions o e) (horacle : FuluOracleMatchesEtheorem o)
    (hrust : FuluRustGlueFacts G o view st (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem G view st e :=
  lighthouse_rust_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_minimal hrun hchain hetheorem
    horacle hrust
end

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal {o : Spec.Oracle}
    {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig} {uc : Spec.UpgradeConfig}
    {init : Spec.FuluState} {s : Spec.BeaconState} (hrun : GloasEpochRun o fo c uc init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse o s) (Spec.process_epoch Spec.P o s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhist

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal {o : Spec.Oracle}
    {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig} {init : Spec.FuluState}
    {s : Spec.BeaconState} (hrun : FuluEpochRun o fo c init s)
    (hhist : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu o s)
      (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhist

end Minimal

end EpochProofs.Formalhouse
