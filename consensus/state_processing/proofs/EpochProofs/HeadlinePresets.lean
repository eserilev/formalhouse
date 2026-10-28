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
    {oracle fuluOracle blockConfig upgradeConfig fuluStart} {e : EtheoremState}
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
        (toSpecState e) :=
  lighthouse_model_gloas_epoch_eq_etheorem epochPresetAgrees_mainnet (by decide) hrun hchain
    hetheorem horacle hcaches

/-- `lighthouse_rust_gloas_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig upgradeConfig fuluStart} {e : EtheoremState}
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
    GloasRustEqualsEtheorem rustGlue view rustState e :=
  lighthouse_rust_gloas_epoch_eq_etheorem epochPresetAgrees_mainnet (by decide) hrun hchain
    hetheorem horacle hcaches hrust
end

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
/-- `lighthouse_model_fulu_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig fuluStart} {e : EtheoremFuluState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    FuluLighthouseModelEqualsEtheorem oracle e :=
  lighthouse_model_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_mainnet hrun hchain hetheorem
    horacle

/-- `lighthouse_rust_fulu_epoch_eq_etheorem` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem_mainnet [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig fuluStart} {e : EtheoremFuluState} {σ E : Type}
    {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    (hrust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem rustGlue view rustState e :=
  lighthouse_rust_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_mainnet hrun hchain hetheorem
    horacle hrust
end

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse oracle s) 
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig} {fuluStart : Spec.FuluState}
    {s : Spec.BeaconState} (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

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
    {oracle fuluOracle blockConfig upgradeConfig fuluStart} {e : EtheoremState}
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
        (toSpecState e) :=
  lighthouse_model_gloas_epoch_eq_etheorem epochPresetAgrees_minimal (by decide) hrun hchain
    hetheorem horacle hcaches

/-- `lighthouse_rust_gloas_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig upgradeConfig fuluStart} {e : EtheoremState}
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
    GloasRustEqualsEtheorem rustGlue view rustState e :=
  lighthouse_rust_gloas_epoch_eq_etheorem epochPresetAgrees_minimal (by decide) hrun hchain
    hetheorem horacle hcaches hrust
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
/-- `lighthouse_model_fulu_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig fuluStart} {e : EtheoremFuluState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    FuluLighthouseModelEqualsEtheorem oracle e :=
  lighthouse_model_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_minimal hrun hchain hetheorem
    horacle

/-- `lighthouse_rust_fulu_epoch_eq_etheorem` on minimal. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem_minimal [HasherTag] [CryptoBackend]
    {oracle fuluOracle blockConfig fuluStart} {e : EtheoremFuluState} {σ E : Type}
    {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecStateFulu e))
    (hchain : FuluChainAssumptions oracle (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    (hrust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecStateFulu e)) :
    FuluRustEqualsEtheorem rustGlue view rustState e :=
  lighthouse_rust_fulu_epoch_eq_etheorem Fulu.epochPresetAgrees_minimal hrun hchain hetheorem
    horacle hrust
end

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse oracle s) 
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig} {fuluStart : Spec.FuluState}
    {s : Spec.BeaconState} (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : HistoricalSummariesBelowLimit s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Minimal

end EpochProofs.Formalhouse
