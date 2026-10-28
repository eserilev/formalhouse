import EpochProofs.FormalhouseRust
import EpochProofs.FormalhouseUpkeep
import EpochProofs.Sanity.RewardsAndPenalties

/-!
# Formalhouse: named conclusions and hypotheses for the headline theorems

The final theorems of `FormalhouseFinal.lean`, `FormalhouseUpkeep.lean` and
`FormalhouseRust.lean` state their conclusions inline and take about twenty loose hypotheses.
This file names the conclusions and bundles the hypotheses by the groups of the README's
"What is trusted", so that `Headline.lean` can state the results in a few lines. No proof of the
final theorems is changed.

Readable names: a few names of the rest of the project that the headline statements and
bundles use get an alias here (`abbrev`, so each unfolds to the original): `EtheoremState`, `toSpecState`,
`SameResultOrBothFail`, `process_epoch_lighthouse`, `HistoricalSummariesBelowLimit`,
`PhysicalLimits`, `EpochBalanceBounds`, `ReachableInvariants`, `AtEpochBoundary`,
`LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT`, `ProgressiveBalancesInner`, `PresetMatchesEtheorem`, and
the Fulu ones.

Conclusions:

- `GloasLighthouseModelEqualsEtheorem`: the Lean model of Lighthouse's epoch returns `ok`,
  Etheorem's `processEpoch` succeeds, and the two states are equal.
  `GloasRustEqualsEtheorem`: the same for the composed Aeneas translation of the Rust.
  `FuluLighthouseModelEqualsEtheorem`, `FuluRustEqualsEtheorem`: the same for Fulu.
- `GloasCacheReadsCorrect`: the progressive balances reads, the epoch cache total and the pubkey
  cache lookup give the spec values.

Hypotheses (each `Gloas` bundle has a `Fulu` counterpart, except the cache one):

- `GloasEpochRun`: the state is an epoch input of a run from a start state with the genesis
  invariants. The run carries its supply bounds.
- `GloasCacheProvenance`: where each cache came from (README, "The caches").
- `GloasChainAssumptions`: the pyspec preconditions, the hash-output facts of the spec
  selections, the physical limits and the reachable-state facts not yet carried to the epoch
  (README, "Assumptions about the chain").
- `GloasEtheoremDivergenceAssumptions`: what is needed only because Etheorem differs from the
  pyspec (its alpha.11 list limits, F3). Fulu: `FuluEtheoremBridgeConditions`, the conditions of
  the Etheorem Fulu bridge, not all about Etheorem.
- `GloasOracleMatchesEtheorem`: the spec Oracle agrees with Etheorem.
- `GloasRustGlueFacts`: the Rust state views as the epoch input, and the glue facts hold.

`gloasFinalHypotheses_of` and `fuluFinalHypotheses_of` turn the bundles into the single
hypothesis structures (`GloasFinalHypotheses`, `FuluFinalHypotheses`) of the final theorems. Two
facts of the old hypotheses are now proved from the run: unique pubkeys (Gloas), and that the
input is the last slot of an epoch with the next slot in `u64` (`AtEpochBoundary` without
`HistoricalSummariesBelowLimit`).
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.CacheBridge
open EpochProofs.Spec (SameOk HistRoom TailPre)

/-! ## Readable names -/

section Names

variable [Spec.PresetCfg]

/-- `x` and `y` return the same `ok` value, or both fail (the errors may differ). This is
`SameOk`. -/
abbrev SameResultOrBothFail {α : Type} (x y : Spec.SpecM α) : Prop := SameOk x y

/-- The Lean model of Lighthouse's Gloas `process_epoch`, in Lighthouse's order: the single
pass, then the steps after it (`process_epoch_lh_order`). -/
abbrev process_epoch_lighthouse (o : Spec.Oracle) (s : Spec.BeaconState) :
    Spec.SpecM Spec.BeaconState :=
  Spec.process_epoch_lh_order o s

/-- The Lean model of Lighthouse's Fulu `process_epoch` (`process_epoch_lh_order_fulu`). -/
abbrev process_epoch_lighthouse_fulu [Spec.FuluCfg] (o : Spec.Oracle) (s : Spec.BeaconState) :
    Spec.SpecM Spec.BeaconState :=
  Spec.process_epoch_lh_order_fulu o s

/-- Lighthouse's limit on `historical_summaries`, `2^24` (`LH_HISTORICAL_ROOTS_LIMIT`). -/
abbrev LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT : Nat := Spec.LH_HISTORICAL_ROOTS_LIMIT

/-- Fewer than `2^24` historical summaries, Lighthouse's list limit (`HistRoom`). -/
abbrev HistoricalSummariesBelowLimit (s : Spec.BeaconState) : Prop := HistRoom s

/-- Physical limits at the epoch input (`RowBounds`): inactivity scores below `2^22` (F5), the
effective balance sum, funds, exit queue and validator count bounds, and the participation
bound. -/
abbrev PhysicalLimits (s : Spec.BeaconState) : Prop := Spec.RowBounds s

/-- The balance bounds at an epoch input (`EpochSupply`): each balance is below `2^62` Gwei, the
effective balances sum to less than `2^60` Gwei (about 1.15 billion ETH), and three times the
`slashings` sum is below `2^64`. -/
abbrev EpochBalanceBounds (s : Spec.BeaconState) : Prop := Spec.EpochSupply s

/-- The invariants proved at every epoch input of a run (`EpochInputOk''` with
`EpochBalanceBounds`). -/
abbrev ReachableInvariants [Spec.PresetCfg.Ok] (s : Spec.BeaconState) : Prop :=
  Spec.EpochInputOk'' Spec.EpochSupply s

/-- The state is at the last slot of an epoch, the next slot fits in `u64`, and (note) also
`HistoricalSummariesBelowLimit`: fewer than `2^24` historical summaries (`TailPre`). -/
abbrev AtEpochBoundary (s : Spec.BeaconState) : Prop := TailPre s

/-- `Inner` of Lighthouse's `ProgressiveBalancesCache` (`LhCache`). -/
abbrev ProgressiveBalancesInner : Type := CacheProofs.PB.LhCache

/-- An Etheorem Gloas state (`Etheorem.EState`). -/
abbrev EtheoremState [EthCLSpecs.Gloas.Preset] : Type := EpochProofs.Etheorem.EState

/-- An Etheorem Fulu state (`Etheorem.Fulu.EState`). -/
abbrev EtheoremFuluState [EthCLSpecs.Fulu.Preset] : Type := EpochProofs.Etheorem.Fulu.EState

/-- The state of the hand-written spec transcription (`EpochProofs/Spec/`) that an Etheorem Gloas
state maps to. Every field maps
(`Etheorem.absEState`). -/
abbrev toSpecState [EthCLSpecs.Gloas.Preset] (e : EtheoremState) : Spec.BeaconState :=
  EpochProofs.Etheorem.absEState e

/-- `toSpecState` for an Etheorem Fulu state (`Etheorem.Fulu.absEState`). -/
abbrev toSpecStateFulu [EthCLSpecs.Fulu.Preset] (e : EtheoremFuluState) : Spec.BeaconState :=
  EpochProofs.Etheorem.Fulu.absEState e

/-- The preset `p` has the values of Etheorem's Gloas preset that the epoch reads
(`Etheorem.EpochPresetAgrees`). -/
abbrev PresetMatchesEtheorem [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]
    (p : Spec.Preset) : Prop :=
  EpochProofs.Etheorem.EpochPresetAgrees p

/-- The preset `p` and Fulu config `f` have the values of Etheorem's Fulu preset and config that
the epoch reads (`Etheorem.Fulu.EpochPresetAgrees`). -/
abbrev PresetMatchesEtheoremFulu [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config]
    (p : Spec.Preset) (f : Spec.FuluConfig) : Prop :=
  EpochProofs.Etheorem.Fulu.EpochPresetAgrees p f

end Names

/-! ## Runs -/

section Runs

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]

/-- `s` is an input of the Gloas `process_epoch` in a run that starts in Fulu, from a state with
the invariants of a genesis state (`FuluStartOk`), and crosses the Gloas fork.

The run carries its supply bounds inside `input` (`GloasEpochInput`): before each Fulu block,
before each Gloas block, and `EpochBalanceBounds` at each Gloas epoch input. The Gloas bounds are
stated over the run from the Gloas fork state, which `input` quantifies over, so they cannot be
separate fields as in `FuluEpochRun`. -/
structure GloasEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- The run, with its supply bounds. -/
  input : GloasEpochInput o fo c uc init s

/-- `s` is an input of the Fulu `process_epoch` in a run of Fulu blocks from a state with the
invariants of a genesis state, with the supply bounds of the run (`activeBalanceBound`,
`epochBalanceBounds`). -/
structure FuluEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- The total active balance is at most 139M ETH before each block (`SupplyBoundFulu`). -/
  activeBalanceBound : Spec.SupplyBoundFulu o fo c init
  /-- `EpochBalanceBounds` at each epoch input of the run. -/
  epochBalanceBounds : Spec.EpochEconFulu o fo c init Spec.EpochSupply
  /-- The run. -/
  input : FuluEpochInput o fo c init s

/-- The reachable-state invariants at a Gloas epoch input. -/
theorem GloasEpochRun.invariants {o fo c uc init s} (h : GloasEpochRun o fo c uc init s) :
    ReachableInvariants s := by
  obtain ⟨fs, t, t1, s2, g, slot, mbp, gfe, s0, u, slotG, hsupply, hr, hslot64, hreach, hlt, ht,
    hz, he, hup, hsupplyG, hecon, hrg, hslotG, hreachG, hltG, hu, hzG⟩ := h.input.run
  exact Spec.fulu_then_gloas_reachable_invariants o fo c uc init h.start hsupply fs t t1 s2 g
    slot hr hslot64 hreach hlt ht hz he hup mbp gfe hsupplyG Spec.EpochSupply hecon s0 u s slotG
    hrg hslotG hreachG hltG hu hzG

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Gloas epoch input is the last slot of an epoch, and the next slot fits in `u64`. With
`HistoricalSummariesBelowLimit`, this is `AtEpochBoundary`. -/
theorem GloasEpochRun.atEpochBoundary {o fo c uc init s} (h : GloasEpochRun o fo c uc init s)
    (hhist : HistoricalSummariesBelowLimit s) : AtEpochBoundary s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, u, slotG, -, -, -, -, -, -, -, -, -, -, -, -, hslotG, -, hltG,
    hu, hzG⟩ := h.input.run
  have hs : s.slot = u.slot := (Spec.process_slot_frame _ o _ _ hu).2
  exact ⟨hzG, by rw [hs]; exact Nat.lt_of_le_of_lt hltG hslotG, hhist⟩

/-- The reachable-state invariants at a Fulu epoch input. -/
theorem FuluEpochRun.invariants {o fo c init s} (h : FuluEpochRun o fo c init s) :
    ReachableInvariants s := by
  obtain ⟨fs, t, t1, slot, hr, hslot64, hreach, hlt, ht, hz, rfl⟩ := h.input.reach
  exact Spec.fulu_reachable_invariants o fo c init h.start h.activeBalanceBound _
    h.epochBalanceBounds fs t t1 slot hr hslot64 hreach hlt ht hz

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Fulu epoch input is the last slot of an epoch, and the next slot fits in `u64`. -/
theorem FuluEpochRun.atEpochBoundary {o fo c init s} (h : FuluEpochRun o fo c init s)
    (hhist : HistoricalSummariesBelowLimit s) : AtEpochBoundary s := by
  obtain ⟨fs, t, t1, slot, -, hslot64, -, hlt, ht, hz, rfl⟩ := h.input.reach
  have hs : t1.state.slot = t.state.slot := (Spec.process_slot_fulu_frame _ o fo _ _ ht).2.1
  exact ⟨hz, by rw [hs]; exact Nat.lt_of_le_of_lt hlt hslot64, hhist⟩

/-- The Lean model of Lighthouse's Gloas epoch agrees with the transcription's `process_epoch`,
at a state with the reachable-state invariants at an epoch boundary. These hypotheses hold
together (`NonVacuityReadable.lean`). -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants (o : Spec.Oracle)
    {s : Spec.BeaconState} (hin : ReachableInvariants s) (hpre : AtEpochBoundary s) :
    SameResultOrBothFail (process_epoch_lighthouse o s) (Spec.process_epoch Spec.P o s) := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, -, hcons⟩, -, hvalid⟩ := hin
  exact Spec.SameOk.trans (Spec.process_epoch_lh_order_sameOk o s hpre)
    (Spec.process_epoch_lh_full_sameOk' o s hb hslot heb hexit hsup hvalid hcons)

end Runs

/-- Why the agreement theorems keep `EpochBalanceBounds` (each balance below `2^62`): near
`2^64`, Lighthouse's order of rewards and penalties (`rewardsCombined`: all rewards, then all
penalties) overflows where the spec's (`rewardsSequential`: each reward, then its penalty) does
not. A balance of `2^64 - 3`, a source reward and penalty of 2, and a target reward of 2. -/
theorem rewards_overflow_example :
    Spec.rewardsSequential (2 ^ 64 - 3) [(2, 2), (2, 0)] = .ok (2 ^ 64 - 1) ∧
    (Spec.rewardsCombined (2 ^ 64 - 3) [(2, 2), (2, 0)]).isOk = false :=
  ⟨rfl, rfl⟩

/-! ## Gloas -/

section Gloas

open EpochProofs.Etheorem
open Aeneas Aeneas.Std Result
open CacheProofs.PB (Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance)

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

/-- The current epoch of `s`. -/
abbrev curEpoch (s : Spec.BeaconState) : Nat := s.slot / Spec.P.SLOTS_PER_EPOCH

/-! ### Conclusions -/

/-- The Lean model of Lighthouse's Gloas epoch returns `ok s'`, Etheorem's Gloas `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def GloasLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremState) : Prop :=
  ∃ s', process_epoch_lighthouse o (toSpecState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s'

/-- The composed Rust Gloas epoch (`Compose.epoch`) returns `Ok st'` on the Rust state `st`,
Etheorem's Gloas `processEpoch` succeeds, and its result maps to the view of `st'`. -/
def GloasRustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlue σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EtheoremState) : Prop :=
  ∃ st', Compose.epoch G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = view st'

/-- The progressive balances cache gives the spec's flag attesting balances: for each of the
three flags, the current epoch total and, after the first epoch, the previous epoch total. -/
def ProgressiveBalancesReadsCorrect (progressiveCache : ProgressiveBalancesInner)
    (s : Spec.BeaconState) : Prop :=
  (∀ f : Usize, f.val < 3 → ∃ x : U64,
    lhCurrentEpochFlagAttestingBalance progressiveCache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val (curEpoch s) >>=
      Spec.get_total_balance Spec.P s) = .ok x.val) ∧
  (∀ f : Usize, f.val < 3 → 0 < curEpoch s →
    ∃ x : U64, lhPreviousEpochFlagAttestingBalance progressiveCache f = ok (.Ok x) ∧
    (Spec.get_unslashed_participating_indices Spec.P s f.val (curEpoch s - 1) >>=
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
def GloasCacheReadsCorrect {M : Type} (progressiveCache : ProgressiveBalancesInner)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop :=
  ProgressiveBalancesReadsCorrect progressiveCache s ∧
    EpochCacheTotalCorrect totalActiveBalance s ∧ PubkeyLookupCorrect pubkeyMapOps pubkeyMap s

/-! ### Cache provenance -/

/-- The progressive balances cache is coherent with the epoch state. -/
def ProgressiveCacheCoherent (progressiveCache : ProgressiveBalancesInner)
    (s : Spec.BeaconState) : Prop :=
  Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT (pbState s (curEpoch s)) progressiveCache

/-- The progressive balances cache was coherent at a state `start` of the epoch, and every write
since ran its cache hook (`CacheUpkeep`, U1 to U4 in `Trusted/CacheUpkeep.lean`). -/
def ProgressiveCacheKept (progressiveCache : ProgressiveBalancesInner)
    (s : Spec.BeaconState) : Prop :=
  ∃ (start : CacheProofs.Spec.BeaconState) (cache0 : ProgressiveBalancesInner),
    Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start cache0 ∧
    CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start (pbState s (curEpoch s)) cache0
      progressiveCache

/-- The epoch cache total was built at a state `b` of the same epoch that agrees with the epoch
input on which validators are active (`ActiveAgree`). -/
def EpochCacheBuilt (totalActiveBalance : U64) (s : Spec.BeaconState) : Prop :=
  ∃ b : Spec.BeaconState, Spec.ActiveAgree (curEpoch s) b s ∧
    totalActiveBalance.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator) (curEpoch s))
      (b.validators.map (·.effective_balance))

/-- The pubkey cache `pubkeyMap` is a cache built at an earlier state `b'` (whose pubkeys are a
prefix of the input's, `PkPrefix`) and then completed by `update_pubkey_cache` (`insertAll`),
over a map with the `IndexMapLaws`. -/
def PubkeyCacheBuilt {M : Type}
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop :=
  ∃ view : M → Spec.BLSPubkey → Option Usize, CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize), Spec.PkPrefix b' s ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (pubkeyMap, len))

/-- Where each cache that the Gloas epoch reads came from (README, "The caches"). -/
structure GloasCacheProvenance {M : Type} (progressiveCache : ProgressiveBalancesInner)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache is coherent with the epoch input. -/
  progressive : ProgressiveCacheCoherent progressiveCache s
  /-- The epoch cache total was built at a state of the same epoch with the same active set. -/
  epochCache : EpochCacheBuilt totalActiveBalance s
  /-- The pubkey cache was built at an earlier state and completed by `update_pubkey_cache`. -/
  pubkeyCache : PubkeyCacheBuilt pubkeyMapOps pubkeyMap s

/-- `GloasCacheProvenance` with the progressive balances cache kept up to date since a state of
the epoch (`ProgressiveCacheKept`) instead of coherent at the input. -/
structure GloasCacheProvenanceUpkeep {M : Type} (progressiveCache : ProgressiveBalancesInner)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was coherent at a state of the epoch, and every write since
  ran its cache hook. -/
  progressive : ProgressiveCacheKept progressiveCache s
  /-- As in `GloasCacheProvenance`. -/
  epochCache : EpochCacheBuilt totalActiveBalance s
  /-- As in `GloasCacheProvenance`. -/
  pubkeyCache : PubkeyCacheBuilt pubkeyMapOps pubkeyMap s

/-- The cache facts stated at the epoch input itself: each cache is the one built from the
input. -/
structure GloasCacheProvenanceAtInput {M : Type} (progressiveCache : ProgressiveBalancesInner)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache is coherent with the epoch input. -/
  progressive : ProgressiveCacheCoherent progressiveCache s
  /-- The epoch cache total is the active effective balance sum of the input. -/
  epochCache : totalActiveBalance.val = CacheProofs.EpochCache.activeSum
    (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) (curEpoch s))
    (s.validators.map (·.effective_balance))
  /-- The pubkey cache is coherent with the pubkeys of the input. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ len : Usize, CacheProofs.Coherent view pubkeyMap len (s.validators.map (·.pubkey))

/-! ### Other hypotheses -/

/-- The pyspec preconditions of the Gloas committee steps, at the state `t` that the epoch passes
to them. Without them the pyspec raises. The first three fields of `CommitteeStepPreconds`. -/
structure GloasCommitteeStepPyspecPreconds (t : Spec.BeaconState) : Prop where
  /-- A validator is active at the next epoch: a sync committee candidate. -/
  syncActive : Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- F4: an unslashed validator is active two epochs ahead: a proposer candidate. -/
  proposers : Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []
  /-- F12: at least `SLOTS_PER_EPOCH` validators are active two epochs ahead. With fewer, the
  first slot of that epoch has an empty PTC and `compute_ptc` asserts. -/
  enoughActiveForPtc : Spec.P.SLOTS_PER_EPOCH ≤
    (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)).length

/-- Hash-output facts of the Gloas committee steps, at the state `t` that the epoch passes to
them: each spec balance-weighted selection (sync committee, proposers, PTC) accepts its
candidates within `2^64` passes. The last three fields of `CommitteeStepPreconds`. -/
structure GloasCommitteeStepSelectionsEnd (o : Spec.Oracle) (t : Spec.BeaconState) : Prop where
  /-- The sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ seed, Spec.SelFin Spec.P o t
    (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
    seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- The proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ seed, Spec.SelFin Spec.P o t
    (Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1 true
  /-- Each PTC selection of the epoch two ahead ends within `2^64` passes. -/
  ptcSelectionEnds : ∀ slot,
    slot / Spec.P.SLOTS_PER_EPOCH = t.slot / Spec.P.SLOTS_PER_EPOCH + 2 → ∀ l,
    Spec.ptcIndices Spec.P o t (slot / Spec.P.SLOTS_PER_EPOCH) slot = .ok l →
      ∀ seed, Spec.SelFin Spec.P o t l seed Spec.P.PTC_SIZE false

/-- The assumptions about the chain at a Gloas epoch input (README, "Assumptions about the
chain"), beyond the run. `t` ranges over the one state that the spec epoch passes to its
committee steps (`epochToCommittees`, a function of `s`). -/
structure GloasChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec preconditions at `t`: a sync committee candidate, an unslashed active validator two
  epochs ahead (F4), at least `SLOTS_PER_EPOCH` active validators two epochs ahead (F12). -/
  pyspecPreconditions : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    GloasCommitteeStepPyspecPreconds t
  /-- Hash outputs at `t`: each spec selection ends within `2^64` passes. -/
  selectionsEnd : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    GloasCommitteeStepSelectionsEnd o t
  /-- Physical limits: inactivity scores below `2^22` (F5), and the supply, funds, exit and
  validator count bounds. -/
  physicalLimits : PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries, Lighthouse's list limit. -/
  historicalSummariesBelowLimit : HistoricalSummariesBelowLimit s
  /-- Reachable-state fact not yet carried to the epoch: the SSZ vectors have their lengths. -/
  vectorLengths : s.VectorLengths Spec.P
  /-- Reachable-state facts not yet carried to the epoch, at `t`: at most `2^40` validators,
  effective balances at most 2048 ETH, the lookahead and PTC window lengths, valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.CommitteeStepFacts o t

/-- Assumptions needed only because Etheorem diverges from the pyspec. Each one is about the
Etheorem state `e`, not the oracle. The Fulu counterpart is `FuluEtheoremBridgeConditions`, which
also holds conditions that are not about Etheorem. -/
structure GloasEtheoremDivergenceAssumptions (e : EtheoremState) : Prop where
  /-- F3: Etheorem's balance-weighted selections stop after `10^7` passes. They return all their
  items. -/
  selectionsFull : SelectionsFull e
  /-- F6, F10: room under Etheorem's alpha.11 list limits, which beta.4 removed: in the registry
  for one epoch of deposits (`depositRoom`), and in `builder_pending_withdrawals`
  (`builderRoom`). -/
  listLimitRoom : EpochCondsIn e

/-- The spec Oracle agrees with Etheorem's Gloas functions, and SHA-256 returns 32 bytes. -/
structure GloasOracleMatchesEtheorem (o : Spec.Oracle) : Prop where
  /-- The oracle's SHA-256, `hash_tree_root` and BLS functions are Etheorem's. -/
  agrees : OracleAgrees o
  /-- SHA-256 returns 32 bytes. -/
  sha32 : ∀ b : ByteArray, (sha b).size = 32

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
hold (`Compose.EpochLinks`: the contracts of `Trusted/`, the fields each wrapper borrows, the
values passed to the translated code). One field of the glue is a state fact, not a fact about
the Rust: `SinglePassLinks.depositRoom`, that the new validators of the epoch fit under the
`2^40` limit of Lighthouse's validator list. It is the Lighthouse counterpart of
`EpochCondsIn.depositRoom`, stated at the state after justification. -/
structure GloasRustGlueFacts {σ E : Type} (G : Compose.EpochGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state views as the epoch input. -/
  viewEq : view st = s
  /-- The glue facts. -/
  glue : Compose.EpochLinks G o view st

/-! ### From the bundles to the hypotheses of the final theorems -/

/-- `GloasFinalHypotheses`, from the bundles. Unique pubkeys and the first two parts of
`AtEpochBoundary` come from the run. -/
theorem gloasFinalHypotheses_of {o fo c uc init} {e : EtheoremState}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o) :
    GloasFinalHypotheses o init e where
  start := hrun.start
  pubkeys := hrun.invariants.1.2.1
  vectors := hchain.vectorLengths
  boundary := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  slot := hchain.slotFarFromOverflow
  rows := hchain.physicalLimits
  committees := fun t ht =>
    have hp := hchain.pyspecPreconditions t ht
    have hs := hchain.selectionsEnd t ht
    ⟨hchain.committeeStepStateFacts t ht,
      ⟨hp.syncActive, hp.proposers, hp.enoughActiveForPtc, hs.syncSelectionEnds,
        hs.proposerSelectionEnds, hs.ptcSelectionEnds⟩⟩
  selections := hetheorem.selectionsFull
  etheoremRoom := hetheorem.listLimitRoom
  oracle := horacle.agrees
  sha := horacle.sha32

/-! ### Other theorems -/

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

/-- `lighthouse_model_gloas_epoch_eq_etheorem` with the progressive balances cache kept up to
date since a state of the epoch (`formalhouse_gloas_epoch_final_upkeep`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_upkeep (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {pubkeyMap : M}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenanceUpkeep progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem o e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  obtain ⟨start, cache0, hcoh0, hup⟩ := hcaches.progressive
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hpre, hpk0, hupd⟩ := hcaches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_final_upkeep hpreset
    hhistLimit o fo c uc init e hrun.input (gloasFinalHypotheses_of hrun hchain hetheorem horacle)
    start cache0 progressiveCache hcoh0 hup totalActiveBalance b hagree htotal laws b' hpre hpk0
    hupd
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

/-- `lighthouse_model_gloas_epoch_eq_etheorem` with each cache the one built from the epoch
input (`formalhouse_gloas_epoch_at_input`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_at_input
    (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {o fo c uc init} {e : EtheoremState} {progressiveCache : ProgressiveBalancesInner}
    {totalActiveBalance : U64} {M : Type}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey} {pubkeyMap : M}
    (hrun : GloasEpochRun o fo c uc init (toSpecState e))
    (hchain : GloasChainAssumptions o (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e) (horacle : GloasOracleMatchesEtheorem o)
    (hcaches : GloasCacheProvenanceAtInput progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem o e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  obtain ⟨view, laws, len, hpk⟩ := hcaches.pubkeyCache
  obtain ⟨s', h1, ⟨⟨he, hc1, hc2, hc3⟩, -⟩, hpk⟩ := formalhouse_gloas_epoch_at_input hpreset
    hhistLimit o fo c uc init e hrun.input (gloasFinalHypotheses_of hrun hchain hetheorem horacle)
    progressiveCache hcaches.progressive totalActiveBalance hcaches.epochCache laws hpk
  exact ⟨⟨s', h1, he⟩, ⟨hc1, hc2⟩, hc3, hpk⟩

end Gloas

/-! ## Fulu -/

section Fulu

open EpochProofs.Etheorem.Fulu
open Aeneas Aeneas.Std Result

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

/-- The Lean model of Lighthouse's Fulu epoch returns `ok s'`, Etheorem's Fulu `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def FuluLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremFuluState) : Prop :=
  ∃ s', process_epoch_lighthouse_fulu o (toSpecStateFulu e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecStateFulu e' = s'

/-- The composed Rust Fulu epoch (`Compose.epochFulu`) returns `Ok st'`, Etheorem's Fulu
`processEpoch` succeeds, and its result maps to the view of `st'`. -/
def FuluRustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlueFulu σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EtheoremFuluState) : Prop :=
  ∃ st', Compose.epochFulu G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecStateFulu e' = view st'

/-- The pyspec preconditions of the Fulu committee steps, at the state `t` that the epoch passes
to them. The first two fields of `FuluCommitteeStepPreconds`. -/
structure FuluCommitteeStepPyspecPreconds (t : Spec.BeaconState) : Prop where
  /-- A validator is active at the next epoch: a sync committee candidate. -/
  syncActive : Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- A validator is active two epochs ahead: a proposer candidate. Unlike Gloas F4, a slashed
  validator counts. -/
  proposers : Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []

/-- Hash-output facts of the Fulu committee steps, at the state `t` that the epoch passes to
them: the sync committee and proposer selections accept their candidates within `2^64` passes.
The last two fields of `FuluCommitteeStepPreconds`. -/
structure FuluCommitteeStepSelectionsEnd (o : Spec.Oracle) (t : Spec.BeaconState) : Prop where
  /-- The sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ seed, Spec.SelFin Spec.P o t
    (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
    seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- The proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ seed, Spec.SelFin Spec.P o t
    (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1 true

/-- The assumptions about the chain at a Fulu epoch input, beyond the run. `t` ranges over the
one state that the spec epoch passes to its committee steps (`epochToCommitteesFulu`). -/
structure FuluChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec preconditions at `t`: an active validator at the next epoch and two epochs ahead.
  Fulu has no F4 and no F12. -/
  pyspecPreconditions : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    FuluCommitteeStepPyspecPreconds t
  /-- Hash outputs at `t`: each spec selection ends within `2^64` passes. -/
  selectionsEnd : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    FuluCommitteeStepSelectionsEnd o t
  /-- Physical limits (F5 and the supply, funds, exit and validator count bounds). -/
  physicalLimits : PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries. -/
  historicalSummariesBelowLimit : HistoricalSummariesBelowLimit s
  /-- Reachable-state fact not yet carried: the Fulu SSZ vectors have their lengths. -/
  vectorLengths : s.FuluVectorLengths Spec.P
  /-- Reachable-state facts not yet carried, at `t`: registry size, effective balances,
  lookahead length, valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.FuluCommitteeStepFacts o t

/-- The conditions of the Etheorem Fulu bridge (`FuluEpochConds`), at the states before the
steps that read them. Not all of them are about Etheorem:

- because Etheorem diverges from the pyspec: its alpha.11 registry limit (F10, `depositRoom`) and
  its selections returning all their items (F3, `syncFull`, `proposersFull`);
- spec conditions: the historical summaries room (`summariesRoom`; beta.4 keeps that cap);
- facts about the intermediate states that the bridge reads (`finalized`: the finalized epoch is
  below `FAR_FUTURE_EPOCH`; `depositLens`, `consolidationLens`: list lengths agree);
- a hash-output fact (`proposerFin`: the Electra proposer loop ends before its last pass). It
  mentions the spec oracle, so this bundle takes `o`, where the Gloas
  `GloasEtheoremDivergenceAssumptions` does not. -/
structure FuluEtheoremBridgeConditions (o : Spec.Oracle) (e : EtheoremFuluState) :
    Prop where
  /-- `FuluEpochConds`. -/
  bridgeConds : FuluEpochConds Spec.P o e

/-- The spec Oracle agrees with Etheorem's Fulu functions, and SHA-256 returns 32 bytes. -/
structure FuluOracleMatchesEtheorem (o : Spec.Oracle) : Prop where
  /-- The oracle's SHA-256, `hash_tree_root` and BLS functions are Etheorem's. -/
  agrees : OracleAgrees o
  /-- SHA-256 returns 32 bytes. -/
  sha32 : ∀ b : ByteArray, (sha b).size = 32

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
Fulu epoch hold (`Compose.EpochLinksFulu`). As for Gloas, the glue contains one state fact,
`SinglePassLinks.depositRoom`. -/
structure FuluRustGlueFacts {σ E : Type} (G : Compose.EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state views as the epoch input. -/
  viewEq : view st = s
  /-- The glue facts. -/
  glue : Compose.EpochLinksFulu G o view st

/-- `FuluFinalHypotheses`, from the bundles. -/
theorem fuluFinalHypotheses_of {o fo c init} {e : EtheoremFuluState}
    (hrun : FuluEpochRun o fo c init (toSpecStateFulu e))
    (hchain : FuluChainAssumptions o (toSpecStateFulu e))
    (hetheorem : FuluEtheoremBridgeConditions o e) (horacle : FuluOracleMatchesEtheorem o) :
    FuluFinalHypotheses o fo c init e where
  start := hrun.start
  supply := hrun.activeBalanceBound
  econ := hrun.epochBalanceBounds
  boundary := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  slot := hchain.slotFarFromOverflow
  vectors := hchain.vectorLengths
  rows := hchain.physicalLimits
  committees := fun t ht =>
    have hp := hchain.pyspecPreconditions t ht
    have hs := hchain.selectionsEnd t ht
    ⟨hchain.committeeStepStateFacts t ht, ⟨hp.syncActive, hp.proposers, hs.syncSelectionEnds,
      hs.proposerSelectionEnds⟩⟩
  etheorem := hetheorem.bridgeConds
  oracle := horacle.agrees
  sha := horacle.sha32

end Fulu

end EpochProofs.Formalhouse
