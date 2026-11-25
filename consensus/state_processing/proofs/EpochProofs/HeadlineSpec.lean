import EpochProofs.Assumptions
import EpochProofs.CacheBridge.Capstone
import EpochProofs.CacheBridge.Committees
import EpochProofs.CacheBridge.BuildPath
import EpochProofs.CacheBridge.Upkeep
import EpochProofs.CachePubkey
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder
import EpochProofs.Sanity.RewardsAndPenalties

/-!
# The theorems about the pyspec transcription

- `lighthouse_model_gloas_epoch_agrees_pyspec` and `lighthouse_model_fulu_epoch_agrees_pyspec`: the
  Lean model of Lighthouse's epoch and the transcription give the same state, or both fail.
- `ptc_committees_from_cache`: the committees that the PTC window step reads from a committee cache
  are the spec committees.
- `GloasCacheReadsCorrect`: what it means that the other cache reads give the spec values.
-/

namespace EpochProofs.Formalhouse

open EpochProofs.CacheBridge
open Aeneas Aeneas.Std Result
open CacheProofs.PB (LhCache lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle}
  {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}

/-! ## Facts about an epoch input of a run -/

/-- The reachable-state invariants at a Gloas epoch input
(`fulu_then_gloas_reachable_invariants`). -/
theorem GloasEpochRun.invariants (h : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig
    fuluStart s) : Spec.ReachableInvariants s := by
  exact Spec.fulu_then_gloas_reachable_invariants oracle fuluOracle blockConfig upgradeConfig
    fuluStart h.startInvariants h.fuluActiveBalance _ _ _ _ _ _ h.fulu.blocks
    h.fulu.targetSlotFits h.fulu.slots h.fulu.beforeTarget h.fulu.lastSlot h.fulu.atEpochEnd
    h.fulu.lastEpoch h.fulu.upgrade _ _ h.gloasActiveBalance _ h.gloasBalanceBounds _ _ _ _
    h.gloas.blocks h.gloas.targetSlotFits h.gloas.slots h.gloas.beforeTarget h.gloas.lastSlot
    h.gloas.atEpochEnd

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Gloas epoch input is the last slot of an epoch, and the next slot fits in `u64`. With
`HistoricalSummariesBelowLimit`, this is `AtEpochBoundary`. -/
theorem GloasEpochRun.atEpochBoundary (h : GloasEpochRun oracle fuluOracle blockConfig
    upgradeConfig fuluStart s) (hhist : Spec.HistoricalSummariesBelowLimit s) :
    Spec.AtEpochBoundary s := by
  have hs : s.slot = h.gloas.beforeLastSlot.slot :=
    (Spec.process_slot_frame _ oracle _ _ h.gloas.lastSlot).2
  exact ⟨h.gloas.atEpochEnd,
    by rw [hs]; exact Nat.lt_of_le_of_lt h.gloas.beforeTarget h.gloas.targetSlotFits, hhist⟩

/-- The reachable-state invariants at a Fulu epoch input (`fulu_reachable_invariants`). -/
theorem FuluEpochRun.invariants (h : FuluEpochRun oracle fuluOracle blockConfig fuluStart s) :
    Spec.ReachableInvariants s := by
  obtain ⟨hstart, hactive, hbounds, path, rfl⟩ := h
  exact Spec.fulu_reachable_invariants oracle fuluOracle blockConfig fuluStart hstart hactive _
    hbounds _ _ _ _ path.blocks path.targetSlotFits path.slots path.beforeTarget path.lastSlot
    path.atEpochEnd

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Fulu epoch input is the last slot of an epoch, and the next slot fits in `u64`. -/
theorem FuluEpochRun.atEpochBoundary (h : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhist : Spec.HistoricalSummariesBelowLimit s) : Spec.AtEpochBoundary s := by
  obtain ⟨-, -, -, path, rfl⟩ := h
  have hs : path.epochInput.state.slot = path.beforeLastSlot.state.slot :=
    (Spec.process_slot_fulu_frame _ oracle fuluOracle _ _ path.lastSlot).2.1
  exact ⟨path.atEpochEnd,
    by rw [hs]; exact Nat.lt_of_le_of_lt path.beforeTarget path.targetSlotFits, hhist⟩

/-! ## The cache reads -/

section Caches

variable [Spec.PresetCfg.Bounds]

/-- The cache reads of the Gloas epoch give the spec values. The committee cache read of the PTC
window step is a separate theorem, `ptc_committees_from_cache`. -/
structure GloasCacheReadsCorrect {PubkeyMap : Type} (progressiveCache : LhCache)
    (cachedTotal : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey)
    (pubkeyMap : PubkeyMap) (state : Spec.BeaconState) : Prop where
  /-- For each flag, the current epoch total is the spec total. -/
  currentEpochFlagBalances : ∀ flag : Usize, flag.val < 3 → ∃ total : U64,
    lhCurrentEpochFlagAttestingBalance progressiveCache flag = ok (.Ok total) ∧
    (Spec.get_unslashed_participating_indices Spec.P state flag.val
        (state.slot / Spec.P.SLOTS_PER_EPOCH) >>=
      Spec.get_total_balance Spec.P state) = .ok total.val
  /-- For each flag, after the first epoch, the previous epoch total is the spec total. -/
  previousEpochFlagBalances : ∀ flag : Usize, flag.val < 3 →
    0 < state.slot / Spec.P.SLOTS_PER_EPOCH → ∃ total : U64,
      lhPreviousEpochFlagAttestingBalance progressiveCache flag = ok (.Ok total) ∧
      (Spec.get_unslashed_participating_indices Spec.P state flag.val
          (state.slot / Spec.P.SLOTS_PER_EPOCH - 1) >>=
        Spec.get_total_balance Spec.P state) = .ok total.val
  /-- The total active balance, floored at one increment, is the spec total. -/
  totalActiveBalance : ∀ increment : U64, increment.val = Spec.P.EFFECTIVE_BALANCE_INCREMENT →
    ∃ total, types.state.total_active_balance.floor_total_active_balance cachedTotal increment =
      ok total ∧ Spec.get_total_active_balance Spec.P state = .ok total.val
  /-- The pubkey cache gives the first validator with the pubkey, as the spec lookup does. -/
  pubkeyLookup : ∀ pubkey, ∃ result, pubkeyMapOps.get_index pubkeyMap pubkey = ok result ∧
    result.map (·.val) =
      if pubkey ∈ state.validators.map (·.pubkey)
      then some ((state.validators.map (·.pubkey)).idxOf pubkey) else none

omit [Spec.PresetCfg.Bounds] in
/-- At every Gloas epoch input of a run, the cache reads give the spec values, when the cache
assumptions hold. -/
theorem gloas_cache_reads_correct {PubkeyMap : Type} {progressiveCache : LhCache}
    {cachedTotal : U64} {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap s) :
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap s := by
  have hin := run.invariants
  obtain ⟨start, startCache, hstart, hupdates⟩ := caches.progressiveBalances
  obtain ⟨built, hagree, htotal⟩ := caches.epochCache
  obtain ⟨lookup, laws, earlier, builtMap, builtLength, length, hprefix, hbuilt, hinsert⟩ :=
    caches.pubkeyCache
  rw [← activeSum_eq_active_balances] at htotal
  obtain ⟨h1, h2, h3⟩ := lh_cache_reads_mainnet s hin.1.1.1.2.1 hin.1.1.2.2.2.2 progressiveCache
    (coherent_of_upkeep hstart hupdates) cachedTotal
    (epoch_cache_total_carry cachedTotal.val htotal hagree)
  refine ⟨h1, h2, h3, fun pubkey => ?_⟩
  obtain ⟨result, hget, hresult⟩ := CacheProofs.get_coherent_of_nodup laws
    (pubkey_cache_carry laws hprefix hbuilt hinsert) hin.1.2.1 pubkey
  rw [Spec.idxOf_pubkey_eq] at hresult
  exact ⟨result, hget, by convert hresult⟩

/-- The committee cache that `process_ptc_window` builds at `state` for `epoch`, and the committees
that it reads from that cache. Review checks that Lighthouse reads them in this way. -/
structure PtcCommitteeCache (oracle : Spec.Oracle) (state : Spec.BeaconState) (epoch : Nat) where
  /-- The seed of the shuffling. -/
  seed : Spec.Bytes32
  /-- The shuffled validator indices. -/
  shuffling : Slice Usize
  /-- The number of committees in each slot. -/
  committeesPerSlot : Usize
  /-- The slots of an epoch. -/
  slotsPerEpoch : Usize
  /-- The first slot of `epoch`. -/
  startSlot : Nat
  /-- Entry `k` holds the members of all committees of slot `startSlot + k`. -/
  committees : Slice (alloc.vec.Vec Usize)
  /-- The seed is the spec seed. -/
  seedCorrect : Spec.get_seed Spec.P oracle state epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed
  /-- The slots of an epoch are the spec value. -/
  slotsPerEpochCorrect : slotsPerEpoch.val = Spec.P.SLOTS_PER_EPOCH
  /-- The first slot is the spec value. -/
  startSlotCorrect : Spec.compute_start_slot_at_epoch Spec.P epoch = .ok startSlot
  /-- A validator is active. -/
  someValidatorActive : 0 < (Spec.get_active_validator_indices state epoch).length
  /-- `shuffle_list` accepts at most `2^24` indices. -/
  shuffleAcceptsActive : (Spec.get_active_validator_indices state epoch).length ≤ 2 ^ 24
  /-- The products of the committee ranges do not overflow. -/
  committeeProductFits : (Spec.get_active_validator_indices state epoch).length *
    (committeesPerSlot.val * slotsPerEpoch.val) ≤ Usize.max
  /-- The cache holds the spec shuffling and the spec committee count. -/
  built : CommitteeCacheBuilt cachePresetOf oracle state epoch seed shuffling committeesPerSlot
  /-- One entry for each slot of the epoch. -/
  oneEntryPerSlot : committees.val.length = Spec.P.SLOTS_PER_EPOCH
  /-- Each entry joins the committees that `get_beacon_committee` returns for its slot. -/
  readFromCache :
    CommitteesFromCache shuffling committeesPerSlot slotsPerEpoch epoch startSlot committees

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The committees that the PTC window step reads from its committee cache are the spec
committees. -/
theorem ptc_committees_from_cache {oracle : Spec.Oracle} {state : Spec.BeaconState} {epoch : Nat}
    (cache : PtcCommitteeCache oracle state epoch) (k : Nat)
    (inEpoch : k < cache.committees.val.length) (expected : List Spec.ValidatorIndex)
    (specCommittees :
      Spec.ptcIndices Spec.P oracle state epoch (cache.startSlot + k) = .ok expected) :
    (cache.committees.val[k]).val.map (·.val) = expected :=
  hcomm_of_cache Spec.P _ committeePresetLink_P oracle state epoch cache.seed cache.seedCorrect
    cache.shuffling _ _ cache.built cache.slotsPerEpochCorrect cache.someValidatorActive
    cache.shuffleAcceptsActive cache.committeeProductFits _ cache.startSlotCorrect _
    cache.oneEntryPerSlot cache.readFromCache k inEpoch expected specCommittees

end Caches

/-! ## Against the pyspec transcription -/

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The Lean model of Lighthouse's Gloas epoch agrees with the transcription's `process_epoch`,
at a state with the reachable-state invariants at an epoch boundary. These hypotheses hold
together (`NonVacuity.lean`). -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants (o : Spec.Oracle)
    {s : Spec.BeaconState} (hin : Spec.ReachableInvariants s) (hpre : Spec.AtEpochBoundary s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse o s)
      (Spec.process_epoch Spec.P o s) := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, -, hcons⟩, -, hvalid⟩ := hin
  exact Spec.SameResultOrBothFail.trans
    (Spec.process_epoch_lighthouse_sameResultOrBothFail o s hpre)
    (Spec.process_epoch_lh_full_sameResultOrBothFail' o s hb hslot heb hexit hsup hvalid hcons)

/-- Gloas, against the hand-written pyspec transcription: at every epoch boundary of a run, the
Lean model of Lighthouse's epoch and the transcription's give the same state, or both fail. No
pyspec precondition. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants oracle hrun.invariants
    (hrun.atEpochBoundary hhistBelowLimit)

/-- Fulu, against the hand-written pyspec transcription. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle s hrun.invariants
    (hrun.atEpochBoundary hhistBelowLimit)

omit [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- Why the agreement theorems keep `EpochBalanceBounds` (each balance below `2^62`): near
`2^64`, Lighthouse's order of rewards and penalties (`rewardsCombined`: all rewards, then all
penalties) overflows where the spec's (`rewardsSequential`: each reward, then its penalty) does
not. A balance of `2^64 - 3`, a source reward and penalty of 2, and a target reward of 2. -/
theorem rewards_overflow_example :
    Spec.rewardsSequential (2 ^ 64 - 3) [(2, 2), (2, 0)] = .ok (2 ^ 64 - 1) ∧
    (Spec.rewardsCombined (2 ^ 64 - 3) [(2, 2), (2, 0)]).isOk = false :=
  ⟨rfl, rfl⟩

end EpochProofs.Formalhouse
