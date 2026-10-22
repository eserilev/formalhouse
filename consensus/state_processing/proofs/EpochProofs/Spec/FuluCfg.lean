import EpochProofs.Spec.Fulu
import EpochProofs.Spec.PresetCfg

/-!
# The Fulu config as a parameter

The Fulu proofs read the Fulu config from the class `FuluCfg`, as the preset from `PresetCfg`.
-/

namespace EpochProofs.Spec

/-- The Fulu config that the generic proofs read. -/
class FuluCfg where
  f : FuluConfig

/-- The Fulu config of the current `FuluCfg`. -/
@[reducible] def FC [c : FuluCfg] : FuluConfig := c.f

@[reducible] def fuluMainnetCfg : FuluCfg := ⟨FuluConfig.mainnet⟩
@[reducible] def fuluMinimalCfg : FuluCfg := ⟨FuluConfig.minimal⟩

end EpochProofs.Spec
