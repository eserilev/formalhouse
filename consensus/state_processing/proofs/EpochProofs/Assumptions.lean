import EpochProofs.Sanity.PtcIndices
import EpochProofs.Sanity.Invariants.BalanceFloor
import EpochProofs.Sanity.Invariants.LighthouseEpoch
import EpochProofs.Sanity.Invariants.ForkUpgrade
import EpochProofs.Sanity.Invariants.FuluReachable
import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Sanity.Invariants.TotalityRows
import EpochProofs.Sanity.Invariants.TotalityFulu
import EpochProofs.CacheBridge.ProgressiveBalances
import EpochProofs.CacheBridge.EpochCache
import EpochProofs.Trusted.CacheUpkeep
import EpochProofs.Compose.Epoch
import EpochProofs.Compose.Fulu

/-!
# The assumptions of the main theorems

- The run, `GloasEpochRun` and `FuluEpochRun`: the state is an input of `process_epoch` on a chain
  from a start state with the facts of a genesis state. The total stake stays below its bounds.
- The chain, `GloasChainAssumptions` and `FuluChainAssumptions`: what the epoch needs to succeed.
- The caches, `GloasCacheAssumptions`: where each cache that the Gloas epoch reads came from. The
  Fulu model reads the spec values, so the Fulu theorems take no cache facts.
- The untranslated Rust, `GloasRustGlueFacts` and `FuluRustGlueFacts`: what the code that Aeneas
  does not translate does.
-/

namespace EpochProofs.Formalhouse

open Aeneas Aeneas.Std Result

/-! ## The runs -/

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

/-! ## The chain -/

section Chain

variable [Spec.PresetCfg]

/-- What the Gloas epoch needs from the chain, beyond the run, to succeed. -/
structure GloasChainAssumptions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the three committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochToCommittees Spec.P oracle state = .ok committeeInput →
      Spec.CommitteeStepPreconds oracle committeeInput ∧
      Spec.SelectionStateFacts oracle committeeInput
  /-- The supply and time bounds. -/
  physicalLimits : Spec.PhysicalLimits state
  /-- The slot is far below `2^64`. The pyspec `get_block_root` raises near `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

variable [Spec.FuluCfg]

/-- What the Fulu epoch needs from the chain, beyond the run, to succeed. -/
structure FuluChainAssumptions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the two committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochToCommitteesFulu Spec.P Spec.FC oracle state = .ok committeeInput →
      Spec.FuluCommitteeStepPreconds oracle committeeInput ∧
      Spec.SelectionStateFacts oracle committeeInput
  /-- The supply and time bounds. -/
  physicalLimits : Spec.PhysicalLimits state
  /-- The slot is far below `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

end Chain

/-! ## The caches

Where each cache that the Gloas epoch reads came from (README, "The caches"). The Fulu model
reads the spec values directly, so the Fulu theorems take no cache facts. -/

section Caches

open EpochProofs.CacheBridge

variable [Spec.PresetCfg]

/-- What the proofs assume about the caches that the Gloas epoch reads. Lean does not check it. -/
structure GloasCacheAssumptions {PubkeyMap : Type}
    (progressiveCache : CacheProofs.PB.LhCache) (cachedTotal : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey)
    (pubkeyMap : PubkeyMap) (state : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was correct at a state `start` of this epoch, and each write
  since then ran its cache update (`CacheUpkeep`). -/
  progressiveBalances :
    ∃ (start : CacheProofs.Spec.BeaconState) (startCache : CacheProofs.PB.LhCache),
      CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start startCache ∧
      CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start
        (pbState state (state.slot / Spec.P.SLOTS_PER_EPOCH)) startCache progressiveCache
  /-- The epoch cache holds the total active balance of an earlier state `built`. That state has
  the same effective balances and the same active validators. -/
  epochCache : ∃ built : Spec.BeaconState,
    Spec.ActiveAgree (state.slot / Spec.P.SLOTS_PER_EPOCH) built state ∧
    cachedTotal.val = ((built.validators.filter
      (Spec.is_active_validator · (state.slot / Spec.P.SLOTS_PER_EPOCH))).map
        (·.effective_balance)).sum
  /-- The pubkey cache was correct at an earlier state `built`. Then `update_pubkey_cache` added
  the pubkeys that came after it. The map behaves as a finite map (`IndexMapLaws`). -/
  pubkeyCache : ∃ lookup : PubkeyMap → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps lookup ∧
    ∃ (built : Spec.BeaconState) (builtMap : PubkeyMap) (builtLength length : Usize),
      built.validators.map (·.pubkey) <+: state.validators.map (·.pubkey) ∧
      CacheProofs.Coherent lookup builtMap builtLength (built.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps builtMap builtLength
        ((state.validators.map (·.pubkey)).drop builtLength.val) = ok (some (pubkeyMap, length))

end Caches

/-! ## The untranslated Rust -/

section Glue

variable [Spec.PresetCfg]

/-- The Rust state `st` holds the epoch input `s`, and the untranslated Rust does what the proofs
assume (`Compose.EpochLinks`). One field is a fact about the state: `SinglePassLinks.depositRoom`,
the new validators of the epoch fit under the `2^40` limit of Lighthouse's validator list. -/
structure GloasRustGlueFacts {σ E : Type} (G : Compose.EpochGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  viewEq : view st = s
  /-- What the proofs assume about the untranslated Rust. -/
  glue : Compose.EpochLinks G o view st

variable [Spec.FuluCfg]

/-- The Rust state `st` holds the epoch input `s`, and the untranslated Rust of the Fulu epoch does
what the proofs assume (`Compose.EpochLinksFulu`). As for Gloas, `SinglePassLinks.depositRoom` is a
fact about the state. -/
structure FuluRustGlueFacts {σ E : Type} (G : Compose.EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  viewEq : view st = s
  /-- What the proofs assume about the untranslated Rust. -/
  glue : Compose.EpochLinksFulu G o view st

end Glue

end EpochProofs.Formalhouse
