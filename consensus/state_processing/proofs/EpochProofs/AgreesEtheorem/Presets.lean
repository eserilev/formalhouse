import EpochProofs.AgreesEtheorem.Headline

/-!
# The equivalence theorems on mainnet and minimal

Each instantiates a theorem of `AgreesEtheorem/Headline.lean` with the preset, its
`PresetCfg.Ok` and `PresetCfg.Bounds` facts, the Fulu config, and the Etheorem preset with the
agreement facts (`hpreset` by `presetMatchesEtheorem_mainnet` and `_minimal`; `hhistLimit` by
`decide`).
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

section
open EpochProofs.Etheorem
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

/-- `lighthouse_model_gloas_epoch_agrees_etheorem` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_etheorem_mainnet [HasherTag] [CryptoBackend]
    {oracle : Spec.Oracle} {e : EtheoremState}
    (hstate : GloasEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_model_gloas_epoch_agrees_etheorem presetMatchesEtheorem_mainnet (by decide) hstate
    hetheorem horacle
end

section
open EpochProofs.Etheorem.Fulu
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig

/-- `lighthouse_model_fulu_epoch_agrees_etheorem` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_etheorem_mainnet [HasherTag] [CryptoBackend]
    {oracle : Spec.Oracle} {e : EtheoremState}
    (hstate : FuluEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_model_fulu_epoch_agrees_etheorem presetMatchesEtheorem_mainnet hstate hetheorem
    horacle
end

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

section
open EpochProofs.Etheorem
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig

/-- `lighthouse_model_gloas_epoch_agrees_etheorem` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_etheorem_minimal [HasherTag] [CryptoBackend]
    {oracle : Spec.Oracle} {e : EtheoremState}
    (hstate : GloasEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_model_gloas_epoch_agrees_etheorem presetMatchesEtheorem_minimal (by decide) hstate
    hetheorem horacle
end

section
open EpochProofs.Etheorem.Fulu
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig

/-- `lighthouse_model_fulu_epoch_agrees_etheorem` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_etheorem_minimal [HasherTag] [CryptoBackend]
    {oracle : Spec.Oracle} {e : EtheoremState}
    (hstate : FuluEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_model_fulu_epoch_agrees_etheorem presetMatchesEtheorem_minimal hstate hetheorem
    horacle
end

end Minimal

end EpochProofs.Formalhouse
