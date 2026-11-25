import EpochProofs.Spec.Fulu
import EpochProofs.Spec.CurrentPreset

/-!
# The Fulu config as a parameter

The Fulu proofs read the Fulu config from the class `CurrentFuluConfig`, as the preset from `CurrentPreset`.
-/

namespace EpochProofs.Spec

/-- The Fulu config that the generic proofs read. -/
class CurrentFuluConfig where
  f : FuluConfig

/-- The Fulu config of the current `CurrentFuluConfig`. -/
@[reducible] def FC [c : CurrentFuluConfig] : FuluConfig := c.f

@[reducible] def currentFuluConfigMainnet : CurrentFuluConfig := ⟨FuluConfig.mainnet⟩
@[reducible] def currentFuluConfigMinimal : CurrentFuluConfig := ⟨FuluConfig.minimal⟩

end EpochProofs.Spec
