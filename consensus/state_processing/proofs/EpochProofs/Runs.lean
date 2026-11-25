import EpochProofs.Sanity.Invariants.ForkUpgrade
import EpochProofs.Sanity.Invariants.LighthouseEpoch

/-!
# The runs that reach an input of `process_epoch`

`GloasEpochRun` and `FuluEpochRun` describe a chain, with a name for each state and step on it.
`fulu_then_gloas_reachable_invariants` proves the invariants at a Gloas epoch input after the fork.
-/

namespace EpochProofs.Formalhouse

section Runs

variable [Spec.PresetCfg] [Spec.FuluCfg]

/-- A run of Fulu blocks from `start` to an input of the Fulu `process_epoch`. -/
structure FuluRunToEpoch (oracle : Spec.Oracle) (fuluOracle : Spec.FuluOracle)
    (config : Spec.FuluBlockConfig) (start : Spec.FuluState) where
  /-- The state after the last block. -/
  afterBlocks : Spec.FuluState
  /-- The state after the slots that follow the last block. -/
  beforeLastSlot : Spec.FuluState
  /-- The state that `process_epoch` gets. -/
  epochInput : Spec.FuluState
  /-- The slot that `process_slots` runs to. -/
  targetSlot : Spec.Slot
  /-- Blocks reach `afterBlocks`. -/
  blocks : Spec.ReachableFulu oracle fuluOracle config start afterBlocks
  /-- The target slot is a `u64`. -/
  targetSlotFits : targetSlot < 2 ^ 64
  /-- The slots from there reach `beforeLastSlot`. -/
  slots : Spec.SlotReachFulu oracle fuluOracle afterBlocks targetSlot beforeLastSlot
  /-- That state is before the target slot. -/
  beforeTarget : beforeLastSlot.state.slot < targetSlot
  /-- `process_slot` on the last slot of the epoch gives the epoch input. -/
  lastSlot : Spec.process_slot_fulu Spec.P oracle fuluOracle beforeLastSlot = .ok epochInput
  /-- The epoch input is at the last slot of an epoch. -/
  atEpochEnd : (epochInput.state.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0

/-- A Fulu run whose last epoch ends with the Gloas fork. -/
structure FuluRunToGloasFork (oracle : Spec.Oracle) (fuluOracle : Spec.FuluOracle)
    (config : Spec.FuluBlockConfig) (upgradeConfig : Spec.UpgradeConfig) (start : Spec.FuluState)
    extends FuluRunToEpoch oracle fuluOracle config start where
  /-- The state after the last Fulu `process_epoch`. -/
  afterEpoch : Spec.BeaconState
  /-- The first Gloas state. -/
  gloasStart : Spec.BeaconState
  /-- The last Fulu epoch. -/
  lastEpoch : Spec.process_epoch_fulu Spec.P Spec.FC oracle epochInput.state = .ok afterEpoch
  /-- `upgrade_to_gloas` at the next slot. -/
  upgrade : Spec.upgrade_to_gloas Spec.P oracle upgradeConfig
    { epochInput with state := { afterEpoch with slot := afterEpoch.slot + 1 } } = .ok gloasStart

/-- A run of Gloas blocks from `start` to the input `epochInput` of the Gloas `process_epoch`. -/
structure GloasRunToEpoch (oracle : Spec.Oracle) (maxBlobsPerBlock : Spec.Epoch → Spec.Uint64)
    (gloasForkEpoch : Spec.Epoch) (start epochInput : Spec.BeaconState) where
  /-- The state after the last block. -/
  afterBlocks : Spec.BeaconState
  /-- The state after the slots that follow the last block. -/
  beforeLastSlot : Spec.BeaconState
  /-- The slot that `process_slots` runs to. -/
  targetSlot : Spec.Slot
  /-- Blocks reach `afterBlocks`. -/
  blocks : Spec.Reachable oracle maxBlobsPerBlock gloasForkEpoch start afterBlocks
  /-- The target slot is a `u64`. -/
  targetSlotFits : targetSlot < 2 ^ 64
  /-- The slots from there reach `beforeLastSlot`. -/
  slots : Spec.SlotReachG oracle afterBlocks targetSlot beforeLastSlot
  /-- That state is before the target slot. -/
  beforeTarget : beforeLastSlot.slot < targetSlot
  /-- `process_slot` on the last slot of the epoch gives the epoch input. -/
  lastSlot : Spec.process_slot Spec.P oracle beforeLastSlot = .ok epochInput
  /-- The epoch input is at the last slot of an epoch. -/
  atEpochEnd : (epochInput.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0

/-- A chain that starts in Fulu, crosses the Gloas fork, and reaches the input `epochInput` of a
Gloas `process_epoch`. The total stake stays below its bounds. -/
structure GloasEpochRun (oracle : Spec.Oracle) (fuluOracle : Spec.FuluOracle)
    (config : Spec.FuluBlockConfig) (upgradeConfig : Spec.UpgradeConfig) (start : Spec.FuluState)
    (epochInput : Spec.BeaconState) where
  /-- The start state has the invariants of a genesis state. -/
  startInvariants : Spec.FuluStartOk start.state
  /-- At most 139 million ETH is active before each Fulu block. -/
  fuluActiveBalance : Spec.SupplyBoundFulu oracle fuluOracle config start
  /-- The Fulu part, up to the first Gloas state. -/
  fulu : FuluRunToGloasFork oracle fuluOracle config upgradeConfig start
  /-- The blob limit of each epoch. -/
  maxBlobsPerBlock : Spec.Epoch → Spec.Uint64
  /-- The epoch of the Gloas fork that block processing reads. -/
  gloasForkEpoch : Spec.Epoch
  /-- At most 139 million ETH is active before each Gloas block. -/
  gloasActiveBalance : Spec.SupplyBound oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart
  /-- The balance bounds hold at each Gloas epoch input. -/
  gloasBalanceBounds : Spec.EpochEcon oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart
    Spec.EpochBalanceBounds
  /-- The Gloas part. -/
  gloas : GloasRunToEpoch oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart epochInput

/-- A Fulu chain that reaches the input `epochInput` of a Fulu `process_epoch`. The total stake
stays below its bounds. -/
structure FuluEpochRun (oracle : Spec.Oracle) (fuluOracle : Spec.FuluOracle)
    (config : Spec.FuluBlockConfig) (start : Spec.FuluState) (epochInput : Spec.BeaconState) where
  /-- The start state has the invariants of a genesis state. -/
  startInvariants : Spec.FuluStartOk start.state
  /-- At most 139 million ETH is active before each block. -/
  activeBalance : Spec.SupplyBoundFulu oracle fuluOracle config start
  /-- The balance bounds hold at each epoch input. -/
  balanceBounds : Spec.EpochEconFulu oracle fuluOracle config start Spec.EpochBalanceBounds
  /-- The blocks and slots up to the epoch input. -/
  path : FuluRunToEpoch oracle fuluOracle config start
  /-- The path ends at the epoch input. -/
  reachesInput : path.epochInput.state = epochInput

end Runs

end EpochProofs.Formalhouse

namespace EpochProofs.Spec

open Formalhouse (FuluRunToGloasFork GloasRunToEpoch)

/-- A Fulu run that crosses the Gloas fork: every input of the Gloas `process_epoch` after the
fork has the facts of `EpochInputOk''`. `Econ` holds at each Gloas epoch input of the run. -/
theorem fulu_then_gloas_reachable_invariants [PresetCfg] [PresetCfg.Ok] [FuluCfg] [FuluCfg.Ok]
    {oracle : Oracle} {fuluOracle : FuluOracle} {config : FuluBlockConfig}
    {upgradeConfig : UpgradeConfig} {start : FuluState}
    {maxBlobsPerBlock : Epoch → Uint64} {gloasForkEpoch : Epoch} {epochInput : BeaconState}
    (startInvariants : FuluStartOk start.state)
    (fuluActiveBalance : SupplyBoundFulu oracle fuluOracle config start)
    (fulu : FuluRunToGloasFork oracle fuluOracle config upgradeConfig start)
    (gloasActiveBalance : SupplyBound oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart)
    (Econ : BeaconState → Prop)
    (econ : EpochEcon oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart Econ)
    (gloas : GloasRunToEpoch oracle maxBlobsPerBlock gloasForkEpoch fulu.gloasStart epochInput) :
    EpochInputOk'' Econ epochInput :=
  gloas_reachable_invariants oracle _ _ fulu.gloasStart
    (fulu_gloas_fork_startOk oracle fuluOracle config upgradeConfig start startInvariants
      fuluActiveBalance _ _ _ _ _ _ fulu.blocks fulu.targetSlotFits fulu.slots fulu.beforeTarget
      fulu.lastSlot fulu.atEpochEnd fulu.lastEpoch fulu.upgrade)
    gloasActiveBalance Econ econ _ _ _ _ gloas.blocks gloas.targetSlotFits gloas.slots
    gloas.beforeTarget gloas.lastSlot gloas.atEpochEnd

end EpochProofs.Spec
