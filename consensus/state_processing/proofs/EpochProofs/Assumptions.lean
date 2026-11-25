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
- The caches, `GloasCacheProvenance` and its variants: where each cache that the Gloas epoch reads
  came from. The Fulu model reads the spec values, so the Fulu theorems take no cache facts.
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

/-- The assumptions about the chain at a Gloas epoch input (README, "Assumptions about the
chain"), beyond the run. `t` ranges over the one state that the spec epoch passes to its
committee steps (`epochToCommittees`, a function of `s`). Without the first three, the pyspec
raises. -/
structure GloasChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec precondition: a validator is active at the next epoch, a sync committee
  candidate. -/
  syncCandidate : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- Pyspec precondition: an unslashed validator is active two epochs ahead, a proposer
  candidate. -/
  proposerCandidate : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []
  /-- Pyspec precondition: at least `SLOTS_PER_EPOCH` validators are active two epochs
  ahead. With fewer, the first slot of that epoch has an empty PTC and `compute_ptc`
  asserts. -/
  enoughActiveForPtc : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.P.SLOTS_PER_EPOCH ≤
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)).length
  /-- Hash output: the sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
      seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- Hash output: the proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t (Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1
      true
  /-- Hash output: each PTC selection of the epoch two ahead ends within `2^64` passes. -/
  ptcSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ slot,
    slot / Spec.P.SLOTS_PER_EPOCH = t.slot / Spec.P.SLOTS_PER_EPOCH + 2 → ∀ l,
    Spec.ptcIndices Spec.P o t (slot / Spec.P.SLOTS_PER_EPOCH) slot = .ok l →
      ∀ seed, Spec.SelFin Spec.P o t l seed Spec.P.PTC_SIZE false
  /-- Physical limits (`PhysicalLimits`): inactivity scores below `2^22`, the effective
  balance sum, funds, exit queue and validator count bounds, and the participation bound. -/
  physicalLimits : Spec.PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. The pyspec `get_block_root` raises
  above. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries, Lighthouse's list limit. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit s
  /-- Reachable-state facts not yet carried to the epoch, at `t` (`SelectionStateFacts`): at most
  `2^40` validators, valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.SelectionStateFacts o t

variable [Spec.FuluCfg]

/-- The assumptions about the chain at a Fulu epoch input, beyond the run. `t` ranges over the
one state that the spec epoch passes to its committee steps (`epochToCommitteesFulu`). In Fulu, a
slashed proposer candidate counts, and there is no PTC. -/
structure FuluChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec precondition: a validator is active at the next epoch, a sync committee
  candidate. -/
  syncCandidate : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- Pyspec precondition: a validator is active two epochs ahead, a proposer candidate. A
  slashed validator counts. -/
  proposerCandidate : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []
  /-- Hash output: the sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
      seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- Hash output: the proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1 true
  /-- Physical limits: the inactivity scores, supply, funds, exits and validator count. -/
  physicalLimits : Spec.PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit s
  /-- Reachable-state facts not yet carried, at `t` (`SelectionStateFacts`): registry size,
  valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.SelectionStateFacts o t

end Chain

/-! ## The caches

Where each cache that the Gloas epoch reads came from (README, "The caches"). The Fulu model
reads the spec values directly, so the Fulu theorems take no cache facts. -/

section Caches

open EpochProofs.CacheBridge

variable [Spec.PresetCfg]

/-- Where each cache that the Gloas epoch reads came from. -/
structure GloasCacheProvenance {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache (`LhCache`, the `Inner` of Lighthouse's
  `ProgressiveBalancesCache`) is correct for the epoch input at its current epoch. -/
  progressive : CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT
    (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) progressiveCache
  /-- The epoch cache total was built at a state `b` of the same epoch that agrees with the
  epoch input on which validators are active (`ActiveAgree`): it is the active effective
  balance sum of `b`. -/
  epochCache : ∃ b : Spec.BeaconState, Spec.ActiveAgree (s.slot / Spec.P.SLOTS_PER_EPOCH) b s ∧
    totalActiveBalance.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator)
        (s.slot / Spec.P.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance))
  /-- The pubkey cache `pubkeyMap` is a cache built at an earlier state `b'`, whose pubkeys are a
  prefix of the input's, and then completed by `update_pubkey_cache` (`insertAll`), over a map
  with the `IndexMapLaws`. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize),
      b'.validators.map (·.pubkey) <+: s.validators.map (·.pubkey) ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (pubkeyMap, len))

/-- `GloasCacheProvenance` with the progressive balances cache kept up to date since a state of
the epoch, instead of correct at the input. -/
structure GloasCacheProvenanceUpkeep {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was correct at a state `start` of the epoch (after a fresh
  build, or after the epoch transition), and every write since ran its cache update
  (`CacheUpkeep`). -/
  progressive : ∃ (start : CacheProofs.Spec.BeaconState) (cache0 : CacheProofs.PB.LhCache),
    CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start cache0 ∧
    CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start
      (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) cache0 progressiveCache
  /-- As `GloasCacheProvenance.epochCache`. -/
  epochCache : ∃ b : Spec.BeaconState, Spec.ActiveAgree (s.slot / Spec.P.SLOTS_PER_EPOCH) b s ∧
    totalActiveBalance.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator)
        (s.slot / Spec.P.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance))
  /-- As `GloasCacheProvenance.pubkeyCache`. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize),
      b'.validators.map (·.pubkey) <+: s.validators.map (·.pubkey) ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (pubkeyMap, len))

/-- The cache facts stated at the epoch input itself: each cache is the one built from the
input. -/
structure GloasCacheProvenanceAtInput {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- As `GloasCacheProvenance.progressive`. -/
  progressive : CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT
    (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) progressiveCache
  /-- The epoch cache total is the active effective balance sum of the input. -/
  epochCache : totalActiveBalance.val = CacheProofs.EpochCache.activeSum
    (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator)
      (s.slot / Spec.P.SLOTS_PER_EPOCH))
    (s.validators.map (·.effective_balance))
  /-- The pubkey cache is correct for the pubkeys of the input. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ len : Usize, CacheProofs.Coherent view pubkeyMap len (s.validators.map (·.pubkey))

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
