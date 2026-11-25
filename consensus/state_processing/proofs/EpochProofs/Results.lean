import EpochProofs.Assumptions
import EpochProofs.CacheBridge.Capstone
import EpochProofs.CacheBridge.Committees
import EpochProofs.CacheBridge.BuildPath
import EpochProofs.CacheBridge.Upkeep
import EpochProofs.CachePubkey
import EpochProofs.EthLib.Epoch
import EpochProofs.EthLib.VectorLengths
import EpochProofs.Sanity.EpochStepFrames
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder
import EpochProofs.Sanity.RewardsAndPenalties

/-!
# The main theorems

- `lighthouse_model_*`: about the Lean model of Lighthouse's epoch (`process_epoch_lighthouse`).
- `lighthouse_rust_*`: about the composed translation of the Rust (`Compose.epoch`). They take facts
  about the Rust that Aeneas does not translate.
- `*_eq_ethlib`: at every epoch input of a run, the epoch succeeds, and its result is the result of
  EthLib's `processEpoch`.
- `*_agrees_ethlib`: at an epoch input, the epoch and EthLib give the same state, or both fail.
- `*_agrees_pyspec`: the epoch and the hand-written transcription of the pyspec give the same state,
  or both fail.
- `lighthouse_rust_*_of_ethlib_ok`: if EthLib succeeds, the Rust succeeds with the same state.
- `ptc_committees_from_cache`: the committees that the PTC window step reads from a committee cache
  are the spec committees.

`toSpecState` reads an EthLib state as a state of the transcription. No two EthLib Gloas states give
the same transcription state (`toSpecState_injective`).
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
    fuluStart s) : Spec.ReachableInvariants s :=
  Spec.fulu_then_gloas_reachable_invariants h.startInvariants h.fuluActiveBalance h.fulu
    h.gloasActiveBalance _ h.gloasBalanceBounds h.gloas

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

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok] [Spec.PresetCfg.Bounds] in
/-- Caches that are correct at the epoch input itself satisfy the cache assumptions. -/
theorem GloasCacheAssumptions.ofCorrectAtInput {PubkeyMap : Type} {progressiveCache : LhCache}
    {cachedTotal : U64} {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (progressive : CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) progressiveCache)
    (total : cachedTotal.val = ((s.validators.filter
      (Spec.is_active_validator · (s.slot / Spec.P.SLOTS_PER_EPOCH))).map
        (·.effective_balance)).sum)
    {lookup : PubkeyMap → Spec.BLSPubkey → Option Usize}
    (laws : CacheProofs.IndexMapLaws pubkeyMapOps lookup) {length : Usize}
    (pubkeys : CacheProofs.Coherent lookup pubkeyMap length (s.validators.map (·.pubkey))) :
    GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap s where
  progressiveBalances := ⟨_, _, progressive, .refl _⟩
  epochCache := ⟨s, .refl _ _, total⟩
  pubkeyCache := ⟨lookup, laws, s, pubkeyMap, length, length, List.prefix_refl _, pubkeys, by
    rw [pubkeys.1, List.drop_length]
    rfl⟩

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
together (`AssumptionsHoldForExample.lean`). -/
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

/-! ## Against EthLib -/

section EthLib

open EpochProofs.EthLib
open _root_.EthLib.Consensus (BeaconState Config Preset SignatureChecks processEpoch)

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The room for deposits, and the room in Lighthouse's list of historical summaries, give the room
that EthLib needs. -/
theorem epochRoom (presetMatches : PresetMatchesEthLib preset config)
    {fork : _root_.EthLib.Base.Fork} {electra : .pectra ≤ fork} {state : BeaconState preset fork}
    (roomForDeposits : RoomForDeposits electra state)
    (historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit (toSpecState state)) :
    EpochRoom electra state := by
  refine ⟨roomForDeposits,
    Nat.lt_of_lt_of_le ?_ presetMatches.historicalRootsLimit⟩
  have h := historicalSummariesBelowLimit
  rw [Spec.HistoricalSummariesBelowLimit,
    toSpecState_historical_summaries _ (Nat.le_trans (by decide) electra)] at h
  simpa [readList] using h

/-! ### Gloas -/

section Gloas

variable [Spec.PresetCfg.Bounds] {state : BeaconState preset .glamsterdam}

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The new PTCs do not end at slot `2^64` when the slot is far below it. -/
theorem slotLimit_of_slotFarFromOverflow (presetMatches : PresetMatchesEthLib preset config)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64) :
    ((_root_.EthLib.Consensus.getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≠ 2 ^ 64 := by
  apply slotLimit_of_slot_far
  have hslots : preset.SLOTS_PER_EPOCH.toNat ≤ 32 :=
    Nat.le_trans (Nat.le_of_eq (congrArg Spec.Preset.SLOTS_PER_EPOCH presetMatches.values))
      Spec.PresetCfg.Bounds.slots_le
  have hlookahead : preset.MIN_SEED_LOOKAHEAD.toNat = 1 :=
    congrArg Spec.Preset.MIN_SEED_LOOKAHEAD presetMatches.values
  have hslot : state.slot.toNat + 8192 < 2 ^ 64 := slotFarFromOverflow
  rw [hlookahead]
  omega

omit [Spec.PresetCfg.Bounds] [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The conditions of the committee steps, from the chain assumptions at the epoch input. -/
theorem GloasChainAssumptions.atCommitteeStepState
    (presetMatches : PresetMatchesEthLib preset config)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state)) :
    Spec.AtCommitteeStepState oracle (toSpecState state) := by
  intro committeeInput hsteps
  obtain ⟨hpreconditions, hselection⟩ := chain.committeeSteps committeeInput hsteps
  have hbalances :=
    Spec.epochToCommittees_effective_balances oracle _ _ hsteps invariants.1.1.2.2.1
  obtain ⟨hlookahead, hptc⟩ := Spec.epochToCommittees_windows _ _ _ _ hsteps
  obtain ⟨-, -, -, -, -, -, -, h1, -, -, h2, -⟩ :=
    vectorLengths_toSpecState (config := config) state
  rw [presetMatches.values, Spec.P_min_seed] at h1 h2
  exact ⟨⟨hselection.regLen, fun v hv => (hbalances.1 v hv).2, by rw [hlookahead, h1],
    by rw [hptc, h2], hselection.keys⟩, hpreconditions⟩

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- Gloas: at an epoch input, the Lean model of Lighthouse's epoch and EthLib's `processEpoch` give
the same state, or both fail. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch config checks state)) := by
  refine (lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants oracle invariants
    atEpochBoundary).trans ?_
  have h := process_epoch_gloas presetMatches.divisorsNonzero presetMatches.committeeBounds
    oracleMatches state (epochRoom presetMatches roomForDeposits atEpochBoundary.2.2)
    (slotLimit_of_slotFarFromOverflow presetMatches slotFarFromOverflow)
  rwa [presetMatches.values] at h

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- Gloas: at an epoch input where the chain assumptions hold, the Lean model of Lighthouse's epoch
and EthLib's `processEpoch` succeed with the same state. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_of_invariants
    (presetMatches : PresetMatchesEthLib preset config)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    ∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result := by
  have hcommittees := chain.atCommitteeStepState presetMatches invariants
  have hvectors := vectorLengths_toSpecState (config := config) state
  rw [presetMatches.values] at hvectors
  -- The transcription succeeds, so the model succeeds.
  obtain ⟨specResult, hspec⟩ := Spec.process_epoch_total_rows oracle (toSpecState state)
    invariants.1.1.1.2.1 chain.slotFarFromOverflow atEpochBoundary.1 hvectors invariants.1.1.1.1
    invariants.1.1.2.2.1 invariants.1.2.2 invariants.1.1.2.2.2.2.2.2 chain.physicalLimits
    (Spec.committeesOk_of oracle _ chain.slotFarFromOverflow hcommittees)
  have hmodel := (lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants oracle invariants
    atEpochBoundary specResult).mpr hspec
  -- The model and EthLib agree.
  have hethlib := (lighthouse_model_gloas_epoch_agrees_ethlib presetMatches invariants
    atEpochBoundary chain.slotFarFromOverflow roomForDeposits oracleMatches specResult).mp hmodel
  cases hresult : processEpoch config checks state with
  | error e => rw [hresult] at hethlib; cases hethlib
  | ok result =>
    rw [hresult] at hethlib
    cases hethlib
    exact ⟨result, hmodel, rfl⟩

/-- Gloas: at every epoch input of a run that starts in Fulu and crosses the fork, the Lean model of
Lighthouse's epoch succeeds. EthLib's `processEpoch` succeeds with the same state. Each cache read
of the epoch gives the spec value. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib {PubkeyMap : Type} {progressiveCache : LhCache}
    {cachedTotal : U64} {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap} (presetMatches : PresetMatchesEthLib preset config)
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  ⟨lighthouse_model_gloas_epoch_eq_ethlib_of_invariants presetMatches run.invariants
    (run.atEpochBoundary chain.historicalSummariesBelowLimit) chain roomForDeposits oracleMatches,
    gloas_cache_reads_correct run caches⟩

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- Gloas, for the composed Rust: if EthLib's `processEpoch` succeeds at an epoch input, the Rust
returns `Ok` with the same state. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok
    (presetMatches : PresetMatchesEthLib preset config)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState preset .glamsterdam}
    (ethLibSucceeds : processEpoch config checks state = .ok result) :
    ∃ rustResult, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result := by
  have hmodel := (lighthouse_model_gloas_epoch_agrees_ethlib presetMatches invariants
    atEpochBoundary slotFarFromOverflow roomForDeposits oracleMatches (toSpecState result)).mpr
    (by rw [ethLibSucceeds]; rfl)
  have hvectors := vectorLengths_toSpecState (config := config) state
  rw [presetMatches.values] at hvectors
  exact Compose.epoch_spec rustGlue oracle view rustState rust.glue
    (by rw [rust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) atEpochBoundary.2.1)
    (by rw [rust.viewEq]; exact hvectors) _ (by rw [rust.viewEq]; exact hmodel)

/-- Gloas, for the composed Rust: at every epoch input of a run, the Rust returns `Ok`, and EthLib's
`processEpoch` succeeds with the same state. Each cache read of the epoch gives the spec value. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib {PubkeyMap : Type} {progressiveCache : LhCache}
    {cachedTotal : U64} {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap} (presetMatches : PresetMatchesEthLib preset config)
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    (∃ rustResult result, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch config checks state = .ok result ∧ view rustResult = toSpecState result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) := by
  obtain ⟨⟨result, -, hresult⟩, hreads⟩ := lighthouse_model_gloas_epoch_eq_ethlib presetMatches run
    chain roomForDeposits oracleMatches caches
  obtain ⟨rustResult, hrust, hview⟩ := lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatches
    run.invariants (run.atEpochBoundary chain.historicalSummariesBelowLimit)
    chain.slotFarFromOverflow roomForDeposits oracleMatches rust hresult
  exact ⟨⟨rustResult, result, hrust, hresult, hview⟩, hreads⟩

end Gloas

/-! ### Fulu -/

section Fulu

variable {state : BeaconState preset .fusaka}

/-- The conditions of the Fulu committee steps, from the chain assumptions at the epoch input. -/
theorem FuluChainAssumptions.atCommitteeStepState
    (presetMatches : PresetMatchesEthLib preset config)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state)) :
    Spec.FuluAtCommitteeStepState oracle (toSpecState state) := by
  intro committeeInput hsteps
  obtain ⟨hpreconditions, hselection⟩ := chain.committeeSteps committeeInput hsteps
  have hbalances :=
    Spec.epochToCommitteesFulu_effective_balances oracle _ _ hsteps invariants.1.1.2.2.1
  obtain ⟨hlookahead, -⟩ := Spec.epochToCommitteesFulu_windows _ _ _ hsteps
  obtain ⟨-, -, -, -, -, -, -, h⟩ :=
    fuluVectorLengths_toSpecState (config := config) (by decide) state
  rw [presetMatches.values, Spec.P_min_seed] at h
  exact ⟨⟨hselection.regLen, fun v hv => (hbalances.1 v hv).2, by rw [hlookahead, h],
    hselection.keys⟩, hpreconditions⟩

/-- Fulu: at an epoch input, the Lean model of Lighthouse's epoch and EthLib's `processEpoch` give
the same state, or both fail. The state includes the payload header, which the epoch keeps. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch config checks state)) := by
  have h := process_epoch_fulu presetMatches.divisorsNonzero presetMatches.committeeBounds
    oracleMatches state (epochRoom presetMatches roomForDeposits atEpochBoundary.2.2)
  rw [presetMatches.values, fuluConfigMatches] at h
  exact (Spec.SameResultOrBothFail.bind (Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle _
    invariants atEpochBoundary) fun _ _ => .refl _).trans h

/-- Fulu: at an epoch input where the chain assumptions hold, the Lean model of Lighthouse's epoch
and EthLib's `processEpoch` succeed with the same state, and EthLib keeps the payload header. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_of_invariants [Spec.PresetCfg.Bounds]
    (presetMatches : PresetMatchesEthLib preset config)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  have hcommittees := chain.atCommitteeStepState presetMatches invariants
  have hvectors := fuluVectorLengths_toSpecState (config := config) (by decide) state
  rw [presetMatches.values] at hvectors
  -- The transcription succeeds, so the model succeeds.
  obtain ⟨specResult, hspec⟩ := Spec.process_epoch_fulu_total oracle (toSpecState state)
    invariants.1.1.1.2.1 chain.slotFarFromOverflow atEpochBoundary.1 hvectors invariants.1.1.1.1
    invariants.1.1.2.2.1 invariants.1.2.2 invariants.1.1.2.2.2.2.2.2 chain.physicalLimits
    (Spec.committeesOkFulu_of oracle _ chain.slotFarFromOverflow hcommittees)
  have hmodel := (Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle _ invariants
    atEpochBoundary specResult).mpr hspec
  -- The model and EthLib agree.
  have hethlib := (lighthouse_model_fulu_epoch_agrees_ethlib presetMatches fuluConfigMatches
    invariants atEpochBoundary roomForDeposits oracleMatches
    { toSpecFuluState state with state := specResult }).mp
    (by rw [hmodel]; rfl)
  cases hresult : processEpoch config checks state with
  | error e => rw [hresult] at hethlib; cases hethlib
  | ok result =>
    rw [hresult] at hethlib
    have hstate : toSpecState result = specResult :=
      congrArg Spec.FuluState.state (Except.ok.inj hethlib)
    exact ⟨result, by rw [hstate, hmodel], rfl, epoch_keeps_payload_header hresult⟩

/-- Fulu: at every epoch input of a run, the Lean model of Lighthouse's epoch succeeds. EthLib's
`processEpoch` succeeds with the same state, and keeps the payload header. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib [Spec.PresetCfg.Bounds]
    (presetMatches : PresetMatchesEthLib preset config)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_model_fulu_epoch_eq_ethlib_of_invariants presetMatches fuluConfigMatches run.invariants
    (run.atEpochBoundary chain.historicalSummariesBelowLimit) chain roomForDeposits oracleMatches

/-- Fulu, for the composed Rust: if EthLib's `processEpoch` succeeds at an epoch input, the Rust
returns `Ok` with the same state. EthLib keeps the payload header. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok [Spec.PresetCfg.Bounds]
    (presetMatches : PresetMatchesEthLib preset config)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState preset .fusaka}
    (ethLibSucceeds : processEpoch config checks state = .ok result) :
    (∃ rustResult, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  have hmodel : Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) =
      .ok (toSpecState result) := by
    have h := (lighthouse_model_fulu_epoch_agrees_ethlib presetMatches fuluConfigMatches invariants
      atEpochBoundary roomForDeposits oracleMatches (toSpecFuluState result)).mpr
      (by rw [ethLibSucceeds]; rfl)
    obtain ⟨specResult, hspec, h⟩ := Spec.specM_bind_ok h
    have hstate : specResult = toSpecState result :=
      congrArg Spec.FuluState.state (Except.ok.inj h)
    rw [hspec, hstate]
  obtain ⟨-, -, -, -, hbits, -, -, hlookahead⟩ :=
    fuluVectorLengths_toSpecState (config := config) (by decide) state
  rw [presetMatches.values] at hlookahead
  exact ⟨Compose.epochFulu_spec rustGlue oracle view rustState rust.glue
    (by rw [rust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) atEpochBoundary.2.1)
    (by rw [rust.viewEq]; exact hbits) (by rw [rust.viewEq]; exact hlookahead) _
    (by rw [rust.viewEq]; exact hmodel), epoch_keeps_payload_header ethLibSucceeds⟩

/-- Fulu, for the composed Rust: at every epoch input of a run, the Rust returns `Ok`, and EthLib's
`processEpoch` succeeds with the same state, and keeps the payload header. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib [Spec.PresetCfg.Bounds]
    (presetMatches : PresetMatchesEthLib preset config)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    ∃ rustResult result, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch config checks state = .ok result ∧ view rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  obtain ⟨result, -, hresult, -⟩ := lighthouse_model_fulu_epoch_eq_ethlib presetMatches
    fuluConfigMatches run chain roomForDeposits oracleMatches
  obtain ⟨⟨rustResult, hrust, hview⟩, hheader⟩ := lighthouse_rust_fulu_epoch_of_ethlib_ok
    presetMatches fuluConfigMatches run.invariants
    (run.atEpochBoundary chain.historicalSummariesBelowLimit) roomForDeposits oracleMatches rust
    hresult
  exact ⟨rustResult, result, hrust, hresult, hview, hheader⟩

end Fulu

end EthLib

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
