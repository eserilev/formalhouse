import EpochProofs.HeadlineSpec

/-!
# The theorems about the pyspec transcription, on mainnet and minimal
-/

namespace EpochProofs.Formalhouse

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal {oracle : Spec.Oracle}
    {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
    {fuluStart : Spec.FuluState} {s : Spec.BeaconState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Minimal

end EpochProofs.Formalhouse
