import EpochProofs.FormalhouseRust
import EpochProofs.FormalhouseUpkeep
import EpochProofs.Sanity.RewardsAndPenalties

/-!
# Formalhouse: named conclusions and hypotheses for the final theorems

The final theorems of `FormalhouseFinal.lean`, `FormalhouseUpkeep.lean` and
`FormalhouseRust.lean` state their conclusions inline and take about twenty loose hypotheses.
This file names the conclusions and bundles the hypotheses by the groups of the README's
"What is trusted", so that `Headline.lean` can state the results in a few lines. Every theorem
here is proved from the existing ones by unfolding. No proof is changed.

Conclusions:

- `LighthouseEqualsEtheorem`: Lighthouse's epoch returns `ok`, Etheorem's `processEpoch`
  succeeds, and the two states are equal. `RustEqualsEtheorem`: the same for the composed Rust.
- `GloasCacheReadsCorrect`: the progressive balances reads, the epoch cache total and the pubkey
  cache lookup give the spec values.

Hypotheses:

- `GloasEpochRun`, `FuluEpochRun`: the state is an epoch input of a run from a start state with
  the genesis invariants. The run carries its supply bounds.
- `GloasCacheFacts`: where each cache came from (README, "The caches").
- `GloasChainAssumptions`, `FuluChainAssumptions`: the pyspec preconditions, the physical
  limits and the reachable-state facts not yet carried to the epoch (README, "Assumptions about
  the chain").
- `EtheoremFaithful`, `EtheoremFaithfulFulu`: what is needed only because Etheorem differs from
  the pyspec (its alpha.11 list limits).
- `OracleMatchesEtheorem`, `OracleMatchesEtheoremFulu`: the spec Oracle agrees with Etheorem.
- `RustEpoch`, `RustEpochFulu`: the Rust state views as the epoch input, and the glue facts hold.

Two facts of the old hypotheses are now proved from the run: unique pubkeys (Gloas), and that
the input is the last slot of an epoch with the next slot in `u64` (`TailPre` without
`HistRoom`).
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.CacheBridge
open EpochProofs.Spec (SameOk HistRoom TailPre)

/-! ## Runs -/

section Runs

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]

/-- `s` is an input of the Gloas `process_epoch` in a run that starts in Fulu, from a state with
the invariants of a genesis state (`FuluStartOk`), and crosses the Gloas fork. The run carries
its supply bounds (`GloasEpochInput`). -/
structure GloasEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- The run, with its supply bounds. -/
  input : GloasEpochInput o fo c uc init s

/-- `s` is an input of the Fulu `process_epoch` in a run of Fulu blocks from a state with the
invariants of a genesis state, with the supply bounds of the run. -/
structure FuluEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- At most 139M ETH is active before each block. -/
  supply : Spec.SupplyBoundFulu o fo c init
  /-- `EpochSupply` at each epoch input of the run. -/
  econ : Spec.EpochEconFulu o fo c init Spec.EpochSupply
  /-- The run. -/
  input : FuluEpochInput o fo c init s

/-- The reachable-state invariants at a Gloas epoch input. -/
theorem GloasEpochRun.invariants {o fo c uc init s} (h : GloasEpochRun o fo c uc init s) :
    Spec.EpochInputOk'' Spec.EpochSupply s := by
  obtain ⟨fs, t, t1, s2, g, slot, mbp, gfe, s0, u, slotG, hsupply, hr, hslot64, hreach, hlt, ht,
    hz, he, hup, hsupplyG, hecon, hrg, hslotG, hreachG, hltG, hu, hzG⟩ := h.input.run
  exact Spec.fulu_then_gloas_reachable_invariants o fo c uc init h.start hsupply fs t t1 s2 g
    slot hr hslot64 hreach hlt ht hz he hup mbp gfe hsupplyG Spec.EpochSupply hecon s0 u s slotG
    hrg hslotG hreachG hltG hu hzG

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Gloas epoch input is the last slot of an epoch, and the next slot fits in `u64`. With
`HistRoom`, this is `TailPre`. -/
theorem GloasEpochRun.tailPre {o fo c uc init s} (h : GloasEpochRun o fo c uc init s)
    (hroom : HistRoom s) : TailPre s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, u, slotG, -, -, -, -, -, -, -, -, -, -, -, -, hslotG, -, hltG,
    hu, hzG⟩ := h.input.run
  have hs : s.slot = u.slot := (Spec.process_slot_frame _ o _ _ hu).2
  exact ⟨hzG, by rw [hs]; exact Nat.lt_of_le_of_lt hltG hslotG, hroom⟩

/-- The reachable-state invariants at a Fulu epoch input. -/
theorem FuluEpochRun.invariants {o fo c init s} (h : FuluEpochRun o fo c init s) :
    Spec.EpochInputOk'' Spec.EpochSupply s := by
  obtain ⟨fs, t, t1, slot, hr, hslot64, hreach, hlt, ht, hz, rfl⟩ := h.input.reach
  exact Spec.fulu_reachable_invariants o fo c init h.start h.supply _ h.econ fs t t1 slot hr
    hslot64 hreach hlt ht hz

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Fulu epoch input is the last slot of an epoch, and the next slot fits in `u64`. -/
theorem FuluEpochRun.tailPre {o fo c init s} (h : FuluEpochRun o fo c init s)
    (hroom : HistRoom s) : TailPre s := by
  obtain ⟨fs, t, t1, slot, -, hslot64, -, hlt, ht, hz, rfl⟩ := h.input.reach
  have hs : t1.state.slot = t.state.slot := (Spec.process_slot_fulu_frame _ o fo _ _ ht).2.1
  exact ⟨hz, by rw [hs]; exact Nat.lt_of_le_of_lt hlt hslot64, hroom⟩

/-- The SameOk comparison of the Gloas epoch with the transcription, at a state with the
reachable-state invariants and `TailPre`. These hypotheses hold together
(`NonVacuityReadable.lean`). -/
theorem gloas_sameOk_of_invariants (o : Spec.Oracle) {s : Spec.BeaconState}
    (hin : Spec.EpochInputOk'' Spec.EpochSupply s) (hpre : TailPre s) :
    SameOk (Spec.process_epoch_lh_order o s) (Spec.process_epoch Spec.P o s) := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, -, hcons⟩, -, hvalid⟩ := hin
  exact Spec.SameOk.trans (Spec.process_epoch_lh_order_sameOk o s hpre)
    (Spec.process_epoch_lh_full_sameOk' o s hb hslot heb hexit hsup hvalid hcons)

/-- The SameOk comparison of the Gloas epoch with the transcription, on a run. -/
theorem gloas_sameOk_of_run {o fo c uc init s} (run : GloasEpochRun o fo c uc init s)
    (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order o s) (Spec.process_epoch Spec.P o s) :=
  gloas_sameOk_of_invariants o run.invariants (run.tailPre hroom)

/-- The SameOk comparison of the Fulu epoch with the transcription, on a run. -/
theorem fulu_sameOk_of_run {o fo c init s} (run : FuluEpochRun o fo c init s)
    (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order_fulu o s) (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  Spec.lighthouse_fulu_epoch_sameOk o s run.invariants (run.tailPre hroom)

end Runs

/-- Why the SameOk theorems keep `EpochSupply` (each balance below `2^62`): near `2^64`,
Lighthouse's order of rewards and penalties (`rewardsCombined`: all rewards, then all penalties)
overflows where the spec's (`rewardsSequential`: each reward, then its penalty) does not. A
balance of `2^64 - 3`, a source reward and penalty of 2, and a target reward of 2. -/
theorem rewards_overflow_example :
    Spec.rewardsSequential (2 ^ 64 - 3) [(2, 2), (2, 0)] = .ok (2 ^ 64 - 1) ∧
    (Spec.rewardsCombined (2 ^ 64 - 3) [(2, 2), (2, 0)]).isOk = false :=
  ⟨rfl, rfl⟩

/-! ## Gloas -/

section Gloas

open EpochProofs.Etheorem
open Aeneas Aeneas.Std Result
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance)

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

/-- The current epoch of `s`. -/
abbrev curEpoch (s : Spec.BeaconState) : Nat := s.slot / Spec.P.SLOTS_PER_EPOCH

/-! ### Conclusions -/

/-- Lighthouse's Gloas epoch processing returns `ok s'`, Etheorem's Gloas `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def LighthouseEqualsEtheorem (o : Spec.Oracle) (e : EState) : Prop :=
  ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s'

/-- The composed Rust Gloas epoch (`Compose.epoch`) returns `Ok st'` on the Rust state `st`,
Etheorem's Gloas `processEpoch` succeeds, and its result maps to the view of `st'`. -/
def RustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlue σ E) (view : σ → Spec.BeaconState)
    (st : σ) (e : EState) : Prop :=
  ∃ st', Compose.epoch G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = view st'

/-- The progressive balances cache gives the spec's flag attesting balances: for each of the
three flags, the current epoch total and, after the first epoch, the previous epoch total. -/
def ProgressiveBalancesReadsCorrect (cache : LhCache) (s : Spec.BeaconState) : Prop :=
  (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val (curEpoch s) >>=
      Spec.get_total_balance Spec.P s) = .ok x.val) ∧
  (∀ f : Usize, f.val < 3 → 0 < curEpoch s →
    ∃ x : U64, lhPreviousEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val (curEpoch s - 1) >>=
      Spec.get_total_balance Spec.P s) = .ok x.val)

/-- The epoch cache's total active balance, floored at one increment as Lighthouse reads it, is
the spec's `get_total_active_balance`. -/
def EpochCacheTotalCorrect (total : U64) (s : Spec.BeaconState) : Prop :=
  ∀ inc : U64, inc.val = Spec.P.EFFECTIVE_BALANCE_INCREMENT →
    ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
      Spec.get_total_active_balance Spec.P s = .ok r.val

/-- The pubkey cache lookup of every pubkey returns the first validator with that pubkey, and
`none` exactly when no validator has it. -/
def PubkeyLookupCorrect {M : Type} (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey)
    (m : M) (s : Spec.BeaconState) : Prop :=
  ∀ pk, ∃ r, inst.get_index m pk = ok r ∧
    (r.map (·.val)).bind (fun i => s.validators[i]?) =
      s.validators[(s.validators.map (·.pubkey)).idxOf pk]? ∧
    (r.isSome ↔ pk ∈ s.validators.map (·.pubkey)) ∧
    ∀ i, r.map (·.val) = some i → i = (s.validators.map (·.pubkey)).idxOf pk

/-- The cache reads of the Gloas epoch give the spec values. -/
def GloasCacheReadsCorrect {M : Type} (cache : LhCache) (total : U64)
    (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (m : M)
    (s : Spec.BeaconState) : Prop :=
  ProgressiveBalancesReadsCorrect cache s ∧ EpochCacheTotalCorrect total s ∧
    PubkeyLookupCorrect inst m s

/-! ### Cache provenance -/

/-- The progressive balances cache is coherent with the epoch state. -/
def ProgressiveCacheCoherent (cache : LhCache) (s : Spec.BeaconState) : Prop :=
  Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT (pbState s (curEpoch s)) cache

/-- The progressive balances cache was coherent at a state `start` of the epoch, and every write
since ran its cache hook (`CacheUpkeep`, U1 to U4 in `Trusted/CacheUpkeep.lean`). -/
def ProgressiveCacheKept (cache : LhCache) (s : Spec.BeaconState) : Prop :=
  ∃ (start : CacheProofs.Spec.BeaconState) (cache0 : LhCache),
    Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start cache0 ∧
    CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start (pbState s (curEpoch s)) cache0 cache

/-- The epoch cache total was built at a state `b` of the same epoch that agrees with the epoch
input on which validators are active (`ActiveAgree`). -/
def EpochCacheBuilt (total : U64) (s : Spec.BeaconState) : Prop :=
  ∃ b : Spec.BeaconState, Spec.ActiveAgree (curEpoch s) b s ∧
    total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator) (curEpoch s))
      (b.validators.map (·.effective_balance))

/-- The pubkey cache `m` is a cache built at an earlier state `b'` (whose pubkeys are a prefix of
the input's, `PkPrefix`) and then completed by `update_pubkey_cache` (`insertAll`), over a map
with the `IndexMapLaws`. -/
def PubkeyCacheBuilt {M : Type} (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey)
    (m : M) (s : Spec.BeaconState) : Prop :=
  ∃ view : M → Spec.BLSPubkey → Option Usize, CacheProofs.IndexMapLaws inst view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize), Spec.PkPrefix b' s ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll inst m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (m, len))

/-- Where each cache that the Gloas epoch reads came from (README, "The caches"). -/
structure GloasCacheFacts {M : Type} (cache : LhCache) (total : U64)
    (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (m : M)
    (s : Spec.BeaconState) : Prop where
  progressive : ProgressiveCacheCoherent cache s
  epochCache : EpochCacheBuilt total s
  pubkeyCache : PubkeyCacheBuilt inst m s

/-- `GloasCacheFacts` with the progressive balances cache kept up to date since a state of the
epoch (`ProgressiveCacheKept`). -/
structure GloasCacheFactsUpkeep {M : Type} (cache : LhCache) (total : U64)
    (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (m : M)
    (s : Spec.BeaconState) : Prop where
  progressive : ProgressiveCacheKept cache s
  epochCache : EpochCacheBuilt total s
  pubkeyCache : PubkeyCacheBuilt inst m s

/-- The cache facts stated at the epoch input itself. -/
structure GloasCacheFactsAtInput {M : Type} (cache : LhCache) (total : U64)
    (inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (m : M)
    (s : Spec.BeaconState) : Prop where
  progressive : ProgressiveCacheCoherent cache s
  epochCache : total.val = CacheProofs.EpochCache.activeSum
    (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) (curEpoch s))
    (s.validators.map (·.effective_balance))
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize, CacheProofs.IndexMapLaws inst view ∧
    ∃ len : Usize, CacheProofs.Coherent view m len (s.validators.map (·.pubkey))

/-! ### Other hypotheses -/

/-- The assumptions about the chain at a Gloas epoch input (README, "Assumptions about the
chain"), beyond the run. -/
structure GloasChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec preconditions, at the state `t` that the spec epoch passes to its committee steps
  (`epochToCommittees`): a sync committee candidate, an unslashed active validator two epochs
  ahead (F4), at least `SLOTS_PER_EPOCH` active validators two epochs ahead (F12). Without them
  the pyspec raises. With them, that each spec selection ends within `2^64` passes (a fact about
  hash outputs). -/
  preconditions : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → Spec.CommPreconds o t
  /-- Physical limits: inactivity scores below `2^22` (F5), and the supply, funds, exit and
  validator count bounds of `RowBounds`. -/
  rows : Spec.RowBounds s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slot : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries, Lighthouse's list limit. -/
  histRoom : HistRoom s
  /-- Reachable-state fact not yet carried to the epoch: the SSZ vectors have their lengths. -/
  vectors : s.VectorLengths Spec.P
  /-- Reachable-state facts not yet carried to the epoch, at the same state `t`: at most `2^40`
  validators, effective balances at most 2048 ETH, the lookahead and PTC window lengths, valid
  pubkeys. -/
  committees : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → Spec.CommConds o t

/-- Conditions needed only because Etheorem differs from the pyspec. -/
structure EtheoremFaithful (e : EState) : Prop where
  /-- F6, F10: Etheorem's alpha.11 list limits, which beta.4 removed: room in the registry for
  one epoch of deposits, and in `builder_pending_withdrawals`. -/
  room : EpochCondsIn e

/-- The spec Oracle agrees with Etheorem's SHA-256, roots and BLS checks, and SHA-256 returns 32
bytes. -/
structure OracleMatchesEtheorem (o : Spec.Oracle) : Prop where
  agrees : OracleAgrees o
  sha32 : ∀ b : ByteArray, (sha b).size = 32

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
hold (`EpochLinks`: the contracts of `Trusted/`, the fields each wrapper borrows, the values
passed to the translated code). -/
structure RustEpoch {σ E : Type} (G : Compose.EpochGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  view_eq : view st = s
  links : Compose.EpochLinks G o view st

/-! ### From the bundles to the old hypotheses -/

/-- The old `GloasAssumptions`, from the new bundles. Unique pubkeys and the first two parts of
`TailPre` come from the run. -/
theorem gloasAssumptions_of {o fo c uc init} {e : EState}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (orc : OracleMatchesEtheorem o) : GloasAssumptions o init e where
  start := run.start
  pubkeys := run.invariants.1.2.1
  vectors := chain.vectors
  boundary := run.tailPre chain.histRoom
  slot := chain.slot
  rows := chain.rows
  committees := fun t ht => ⟨chain.committees t ht, chain.preconditions t ht⟩
  etheoremRoom := ef.room
  oracle := orc.agrees
  sha := orc.sha32

/-! ### The readable theorems -/

/-- The general fact behind the PTC window step: for any state `st` at which Lighthouse builds
the committee cache of `epoch`, a cache with its build facts (`CommitteeCacheBuilt`) and the way
Lighthouse joins its committees (`CommitteesFromCache`) give the spec's `ptcIndices`. -/
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

/-- `formalhouse_gloas_epoch_final` with named hypotheses and conclusions. -/
theorem gloas_epoch_readable (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EState} {cache : LhCache} {total : U64} {M : Type}
    {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (orc : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) := by
  obtain ⟨b, hagree, htotal⟩ := caches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := caches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_final hpa hhr o fo c
    uc init e run.input (gloasAssumptions_of run chain ef orc) cache caches.progressive total b
    hagree htotal laws b' hpre hpk0 hupd
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

/-- `formalhouse_gloas_epoch_final_upkeep` with named hypotheses and conclusions. -/
theorem gloas_epoch_upkeep_readable (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EState} {cache : LhCache} {total : U64} {M : Type}
    {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (orc : OracleMatchesEtheorem o)
    (caches : GloasCacheFactsUpkeep cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) := by
  obtain ⟨start, cache0, hcoh0, hup⟩ := caches.progressive
  exact gloas_epoch_readable hpa hhr run chain ef orc
    ⟨coherent_of_upkeep hcoh0 hup, caches.epochCache, caches.pubkeyCache⟩

/-- `formalhouse_gloas_epoch_at_input` with named hypotheses and conclusions. -/
theorem gloas_epoch_at_input_readable (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EState} {cache : LhCache} {total : U64} {M : Type}
    {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (orc : OracleMatchesEtheorem o)
    (caches : GloasCacheFactsAtInput cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) := by
  obtain ⟨view, laws, len, hpk⟩ := caches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_at_input hpa hhr o fo
    c uc init e run.input (gloasAssumptions_of run chain ef orc) cache caches.progressive total
    caches.epochCache laws hpk
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

/-- `formalhouse_gloas_epoch_rust` with named hypotheses and conclusions. -/
theorem gloas_epoch_rust_readable (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EState} {cache : LhCache} {total : U64} {M : Type}
    {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {m : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (orc : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e))
    (rust : RustEpoch G o view st (absEState e)) :
    RustEqualsEtheorem G view st e := by
  obtain ⟨b, hagree, htotal⟩ := caches.epochCache
  obtain ⟨pview, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := caches.pubkeyCache
  exact formalhouse_gloas_epoch_rust hpa hhr o fo c uc init e run.input
    (gloasAssumptions_of run chain ef orc) cache caches.progressive total b hagree htotal laws b'
    hpre hpk0 hupd G view st rust.view_eq rust.links

end Gloas

/-! ## Fulu -/

section Fulu

open EpochProofs.Etheorem.Fulu
open Aeneas Aeneas.Std Result

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

/-- Lighthouse's Fulu epoch processing returns `ok s'`, Etheorem's Fulu `processEpoch` succeeds
on the same state, and its result maps to `s'`. -/
def LighthouseEqualsEtheoremFulu (o : Spec.Oracle) (e : EState) : Prop :=
  ∃ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s'

/-- The composed Rust Fulu epoch (`Compose.epochFulu`) returns `Ok st'`, Etheorem's Fulu
`processEpoch` succeeds, and its result maps to the view of `st'`. -/
def RustEqualsEtheoremFulu {σ E : Type} (G : Compose.EpochGlueFulu σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EState) : Prop :=
  ∃ st', Compose.epochFulu G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = view st'

/-- The assumptions about the chain at a Fulu epoch input, beyond the run. -/
structure FuluChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec preconditions, at the state `t` that the spec epoch passes to its committee steps
  (`epochToCommitteesFulu`): an active validator at the next epoch and two epochs ahead. With
  them, that each spec selection ends within `2^64` passes. Fulu has no F4 and no F12. -/
  preconditions : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.FuluCommPreconds o t
  /-- Physical limits (`RowBounds`, F5). -/
  rows : Spec.RowBounds s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slot : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries. -/
  histRoom : HistRoom s
  /-- Reachable-state fact not yet carried: the Fulu SSZ vectors have their lengths. -/
  vectors : s.FuluVectorLengths Spec.P
  /-- Reachable-state facts not yet carried, at the same state `t`: registry size, effective
  balances, lookahead length, valid pubkeys. -/
  committees : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.FuluCommConds o t

/-- The conditions of the Etheorem Fulu bridge (`FuluEpochConds`): Etheorem's alpha.11 list
limits (F10, the historical summaries room), and the facts about intermediate states that the bridge reads (the finalized epoch is below
`FAR_FUTURE_EPOCH`, list lengths agree, the Electra proposer loop ends before its last pass). -/
structure EtheoremFaithfulFulu (o : Spec.Oracle) (e : EState) : Prop where
  conds : FuluEpochConds Spec.P o e

/-- The spec Oracle agrees with Etheorem's Fulu functions, and SHA-256 returns 32 bytes. -/
structure OracleMatchesEtheoremFulu (o : Spec.Oracle) : Prop where
  agrees : OracleAgrees o
  sha32 : ∀ b : ByteArray, (sha b).size = 32

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
Fulu epoch hold (`EpochLinksFulu`). -/
structure RustEpochFulu {σ E : Type} (G : Compose.EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  view_eq : view st = s
  links : Compose.EpochLinksFulu G o view st

/-- The old `FuluAssumptions`, from the new bundles. -/
theorem fuluAssumptions_of {o fo c init} {e : EState}
    (run : FuluEpochRun o fo c init (absEState e))
    (chain : FuluChainAssumptions o (absEState e)) (ef : EtheoremFaithfulFulu o e)
    (orc : OracleMatchesEtheoremFulu o) : FuluAssumptions o fo c init e where
  start := run.start
  supply := run.supply
  econ := run.econ
  boundary := run.tailPre chain.histRoom
  slot := chain.slot
  vectors := chain.vectors
  rows := chain.rows
  committees := fun t ht => ⟨chain.committees t ht, chain.preconditions t ht⟩
  etheorem := ef.conds
  oracle := orc.agrees
  sha := orc.sha32

/-- `formalhouse_fulu_epoch_final` with named hypotheses and conclusion. -/
theorem fulu_epoch_readable (hpa : EpochPresetAgrees Spec.P Spec.FC) {o fo c init} {e : EState}
    (run : FuluEpochRun o fo c init (absEState e))
    (chain : FuluChainAssumptions o (absEState e)) (ef : EtheoremFaithfulFulu o e)
    (orc : OracleMatchesEtheoremFulu o) :
    LighthouseEqualsEtheoremFulu o e :=
  formalhouse_fulu_epoch_final hpa o fo c init e run.input (fuluAssumptions_of run chain ef orc)

/-- `formalhouse_fulu_epoch_rust` with named hypotheses and conclusion. -/
theorem fulu_epoch_rust_readable (hpa : EpochPresetAgrees Spec.P Spec.FC) {o fo c init}
    {e : EState} {σ E : Type} {G : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {st : σ} (run : FuluEpochRun o fo c init (absEState e))
    (chain : FuluChainAssumptions o (absEState e)) (ef : EtheoremFaithfulFulu o e)
    (orc : OracleMatchesEtheoremFulu o) (rust : RustEpochFulu G o view st (absEState e)) :
    RustEqualsEtheoremFulu G view st e :=
  formalhouse_fulu_epoch_rust hpa o fo c init e run.input (fuluAssumptions_of run chain ef orc)
    G view st rust.view_eq rust.links

end Fulu

end EpochProofs.Formalhouse
