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

/-- The progressive balances cache gives the spec's flag attesting balances: for each of the
three flags, the current epoch total and, after the first epoch, the previous epoch total. -/
def ProgressiveBalancesReadsCorrect (progressiveCache : LhCache) (s : Spec.BeaconState) :
    Prop :=
  (∀ f : Usize, f.val < 3 → ∃ x : U64,
    lhCurrentEpochFlagAttestingBalance progressiveCache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val (s.slot / Spec.P.SLOTS_PER_EPOCH) >>=
      Spec.get_total_balance Spec.P s) = .ok x.val) ∧
  (∀ f : Usize, f.val < 3 → 0 < s.slot / Spec.P.SLOTS_PER_EPOCH →
    ∃ x : U64, lhPreviousEpochFlagAttestingBalance progressiveCache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val
        (s.slot / Spec.P.SLOTS_PER_EPOCH - 1) >>=
      Spec.get_total_balance Spec.P s) = .ok x.val)

/-- The epoch cache's total active balance, floored at one increment as Lighthouse reads it, is
the spec's `get_total_active_balance`. -/
def EpochCacheTotalCorrect (totalActiveBalance : U64) (s : Spec.BeaconState) : Prop :=
  ∀ inc : U64, inc.val = Spec.P.EFFECTIVE_BALANCE_INCREMENT →
    ∃ r, types.state.total_active_balance.floor_total_active_balance totalActiveBalance inc =
      ok r ∧ Spec.get_total_active_balance Spec.P s = .ok r.val

/-- The pubkey cache lookup (`pubkeyMapOps.get_index pubkeyMap`) of every pubkey returns the first
validator with that pubkey, and `none` exactly when no validator has it. -/
def PubkeyLookupCorrect {M : Type}
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop :=
  ∀ pk, ∃ r, pubkeyMapOps.get_index pubkeyMap pk = ok r ∧
    (r.map (·.val)).bind (fun i => s.validators[i]?) =
      s.validators[(s.validators.map (·.pubkey)).idxOf pk]? ∧
    (r.isSome ↔ pk ∈ s.validators.map (·.pubkey)) ∧
    ∀ i, r.map (·.val) = some i → i = (s.validators.map (·.pubkey)).idxOf pk

/-- The cache reads of the Gloas epoch give the spec values: the progressive balances cache, the
epoch cache total and the pubkey cache. The committee cache read of the PTC window step is
`ptc_committees_from_cache`, a separate theorem. -/
def GloasCacheReadsCorrect {M : Type} (progressiveCache : LhCache) (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop :=
  ProgressiveBalancesReadsCorrect progressiveCache s ∧
    EpochCacheTotalCorrect totalActiveBalance s ∧ PubkeyLookupCorrect pubkeyMapOps pubkeyMap s

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The committee cache read of the PTC window step: for any state `st` at which Lighthouse
builds the committee cache of `epoch`, a cache with its build facts (`CommitteeCacheBuilt`) and
the way Lighthouse joins its committees (`CommitteesFromCache`) give the spec's `ptcIndices`. -/
theorem ptc_committees_from_cache (o : Spec.Oracle) (st : Spec.BeaconState) (epoch : Nat)
    (seed : Spec.Bytes32)
    (hseed : Spec.get_seed Spec.P o st epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (shuffling : Slice Usize) (cps spe : Usize)
    (hbuilt : CommitteeCacheBuilt cachePresetOf o st epoch seed shuffling cps)
    (hspe : spe.val = Spec.P.SLOTS_PER_EPOCH)
    (hn : 0 < (Spec.get_active_validator_indices st epoch).length)
    (hn24 : (Spec.get_active_validator_indices st epoch).length ≤ 2 ^ 24)
    (hfit : (Spec.get_active_validator_indices st epoch).length * (cps.val * spe.val) ≤
      Usize.max)
    (start : Nat) (hstart : Spec.compute_start_slot_at_epoch Spec.P epoch = .ok start)
    (committees : Slice (alloc.vec.Vec Usize))
    (hclen : committees.val.length = Spec.P.SLOTS_PER_EPOCH)
    (hglue : CommitteesFromCache shuffling cps spe epoch start committees) :
    ∀ k (hk : k < committees.val.length) l,
      Spec.ptcIndices Spec.P o st epoch (start + k) = .ok l →
        (committees.val[k]).val.map (·.val) = l :=
  hcomm_of_cache Spec.P _ committeePresetLink_P o st epoch seed hseed shuffling cps spe hbuilt
    hspe hn hn24 hfit start hstart committees hclen hglue

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
