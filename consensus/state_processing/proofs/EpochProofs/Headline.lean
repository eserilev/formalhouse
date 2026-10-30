import EpochProofs.Assumptions
import EpochProofs.Etheorem.Total
import EpochProofs.Etheorem.Epoch
import EpochProofs.CacheBridge.CapstoneCommittees
import EpochProofs.CacheBridge.BuildPath
import EpochProofs.CacheBridge.Upkeep
import EpochProofs.CachePubkey
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder
import EpochProofs.Sanity.RewardsAndPenalties

/-!
# The headline theorems

The results of this project. Each hypothesis is a bundle of `Assumptions.lean` (the preset,
Etheorem and oracle bundles are in `Assumptions/Etheorem.lean`), and each conclusion is defined
below.

- `lighthouse_model_*`: about the Lean model of Lighthouse's epoch processing
  (`process_epoch_lighthouse`). `lighthouse_rust_*`: about the composed Aeneas translation of the
  Rust (`Compose.epoch`), given the glue facts.
- `*_eq_etheorem`: the epoch succeeds and its result equals Etheorem's `processEpoch`.
  `*_agrees_pyspec`: the epoch and this project's hand-written Lean transcription of the pyspec
  (`Spec.process_epoch`) give the same state, or both fail.

`Spec.P` is the preset (`Spec.PresetCfg`) and `Spec.FC` the Fulu config (`Spec.FuluCfg`). Every
theorem holds for any preset and config. The Etheorem ones ask that they agree with Etheorem's
(`hpreset`) and, for Gloas, that Lighthouse's `2^24` limit on `historical_summaries` is at most
Etheorem's (`hhistLimit`). `HeadlinePresets.lean` instantiates them for mainnet and minimal, where
both hold.

The run is described by `oracle` (BLS, SHA-256 and `hash_tree_root`, `Spec.Oracle`),
`fuluOracle` and `blockConfig` (the Fulu block processing parameters), `upgradeConfig` (the Gloas
fork upgrade) and `fuluStart`, the Fulu state the run starts from. `e` is an Etheorem state, and
`toSpecState e` the same state in the transcription's types. For the Rust theorems, `σ` is the
type of the Rust state, `view` maps it to the transcription's state, and `rustGlue` holds the
untranslated Rust between the translated functions (`E` is a type it uses).

Each proof calls one named lemma per step: `lighthouse_epoch_total_etheorem` (the model returns
`ok` and equals Etheorem), `lighthouse_order_epoch_etheorem_reachable_cached_ptc` (the cache
reads), `pubkey_cache_deposit_lookup` (the pubkey cache), `Compose.epoch_spec` (the composed Rust
is the model), and for Fulu `process_epoch_fulu_total`,
`lighthouse_fulu_epoch_sameResultOrBothFail` and `process_epoch_fulu_etheorem`.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.CacheBridge
open Aeneas Aeneas.Std Result
open CacheProofs.PB (LhCache lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle}
  {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}

/-! ## From the bundles to the step lemmas -/

/-- The reachable-state invariants at a Gloas epoch input
(`fulu_then_gloas_reachable_invariants`). -/
theorem GloasEpochRun.invariants (h : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig
    fuluStart s) : Spec.ReachableInvariants s := by
  obtain ⟨fs, t, t1, s2, g, slot, mbp, gfe, gs, u, slotG, hsupply, hr, hslot64, hreach, hlt, ht,
    hz, he, hup, hsupplyG, hecon, hrg, hslotG, hreachG, hltG, hu, hzG⟩ := h.run
  exact Spec.fulu_then_gloas_reachable_invariants oracle fuluOracle blockConfig upgradeConfig
    fuluStart h.start hsupply fs t t1 s2 g slot hr hslot64 hreach hlt ht hz he hup mbp gfe
    hsupplyG Spec.EpochBalanceBounds hecon gs u s slotG hrg hslotG hreachG hltG hu hzG

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Gloas epoch input is the last slot of an epoch, and the next slot fits in `u64`. With
`HistoricalSummariesBelowLimit`, this is `AtEpochBoundary`. -/
theorem GloasEpochRun.atEpochBoundary (h : GloasEpochRun oracle fuluOracle blockConfig
    upgradeConfig fuluStart s) (hhist : Spec.HistoricalSummariesBelowLimit s) :
    Spec.AtEpochBoundary s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, u, slotG, -, -, -, -, -, -, -, -, -, -, -, -, hslotG, -,
    hltG, hu, hzG⟩ := h.run
  have hs : s.slot = u.slot := (Spec.process_slot_frame _ oracle _ _ hu).2
  exact ⟨hzG, by rw [hs]; exact Nat.lt_of_le_of_lt hltG hslotG, hhist⟩

/-- The reachable-state invariants at a Fulu epoch input (`fulu_reachable_invariants`). -/
theorem FuluEpochRun.invariants (h : FuluEpochRun oracle fuluOracle blockConfig fuluStart s) :
    Spec.ReachableInvariants s := by
  obtain ⟨fs, t, t1, slot, hr, hslot64, hreach, hlt, ht, hz, rfl⟩ := h.run
  exact Spec.fulu_reachable_invariants oracle fuluOracle blockConfig fuluStart h.start
    h.activeBalanceBound _ h.epochBalanceBounds fs t t1 slot hr hslot64 hreach hlt ht hz

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- A Fulu epoch input is the last slot of an epoch, and the next slot fits in `u64`. -/
theorem FuluEpochRun.atEpochBoundary (h : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhist : Spec.HistoricalSummariesBelowLimit s) : Spec.AtEpochBoundary s := by
  obtain ⟨fs, t, t1, slot, -, hslot64, -, hlt, ht, hz, rfl⟩ := h.run
  have hs : t1.state.slot = t.state.slot :=
    (Spec.process_slot_fulu_frame _ oracle fuluOracle _ _ ht).2.1
  exact ⟨hz, by rw [hs]; exact Nat.lt_of_le_of_lt hlt hslot64, hhist⟩

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok] in
/-- The chain bundle gives the committee conditions at the state that the epoch passes to the
committee steps. -/
theorem GloasChainAssumptions.atCommitteeStepState (h : GloasChainAssumptions oracle s) :
    Spec.AtCommitteeStepState oracle s := fun t ht =>
  ⟨h.committeeStepStateFacts t ht, ⟨h.syncCandidate t ht, h.proposerCandidate t ht,
    h.enoughActiveForPtc t ht, h.syncSelectionEnds t ht, h.proposerSelectionEnds t ht,
    h.ptcSelectionEnds t ht⟩⟩

omit [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] in
/-- The Fulu chain bundle gives the committee conditions at the state that the epoch passes to
the committee steps. -/
theorem FuluChainAssumptions.atCommitteeStepState (h : FuluChainAssumptions oracle s) :
    Spec.FuluAtCommitteeStepState oracle s := fun t ht =>
  ⟨h.committeeStepStateFacts t ht, ⟨h.syncCandidate t ht, h.proposerCandidate t ht,
    h.syncSelectionEnds t ht, h.proposerSelectionEnds t ht⟩⟩

/-! ## Gloas -/

section Gloas

open EpochProofs.Etheorem

variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {e : EtheoremState}

/-! ### Conclusions -/

/-- The Lean model of Lighthouse's Gloas epoch returns `ok s'`, Etheorem's Gloas `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def GloasLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremState) : Prop :=
  ∃ s', Spec.process_epoch_lighthouse o (toSpecState e) = .ok s' ∧
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

/-! ### Theorems -/

variable {progressiveCache : LhCache} {totalActiveBalance : U64} {PubkeyMap : Type}
  {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
  {pubkeyMap : PubkeyMap}

/-- Gloas, with each cache the one built from the epoch input: at every epoch boundary of a run
from Fulu across the Gloas fork, the Lean model of Lighthouse's epoch succeeds and equals
Etheorem's, and its cache reads give the spec values. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_at_input
    (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenanceAtInput progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  have hin := hrun.invariants
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  -- The model returns `ok s'`.
  obtain ⟨s', hs', -⟩ := lighthouse_epoch_total_etheorem hpreset hhistLimit oracle
    horacle.agrees horacle.sha32 e hin hpre hetheorem hchain.slotFarFromOverflow
    hchain.vectorLengths hchain.physicalLimits hchain.atCommitteeStepState
  -- Etheorem's result, and the progressive balances and epoch cache reads.
  obtain ⟨⟨he, hc1, hc2, hc3⟩, -⟩ := lighthouse_order_epoch_etheorem_reachable_cached_ptc
    hpreset hhistLimit oracle horacle.agrees horacle.sha32 e hin hpre hetheorem hs' progressiveCache
    hcaches.progressive totalActiveBalance hcaches.epochCache
  -- The pubkey cache lookup. Pubkeys are unique on a reachable state.
  obtain ⟨view, laws, len, hpk⟩ := hcaches.pubkeyCache
  exact ⟨⟨s', hs', he⟩, ⟨hc1, hc2⟩, hc3,
    fun pk => Spec.pubkey_cache_deposit_lookup laws (toSpecState e) hpk hin.1.2.1 pk⟩

/-- Gloas: at every epoch boundary of a run from Fulu across the Gloas fork, the Lean model of
Lighthouse's epoch succeeds and equals Etheorem's, and its cache reads give the spec values. The
epoch cache total and the pubkey cache were built at earlier states (`GloasCacheProvenance`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  -- Carry each cache build fact to the epoch input.
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hprefix, hpk0, hupd⟩ := hcaches.pubkeyCache
  exact lighthouse_model_gloas_epoch_eq_etheorem_at_input hpreset hhistLimit hrun hchain hetheorem
    horacle ⟨hcaches.progressive, epoch_cache_total_carry totalActiveBalance.val htotal hagree,
      view, laws, len, pubkey_cache_carry laws hprefix hpk0 hupd⟩

/-- `lighthouse_model_gloas_epoch_eq_etheorem` with the progressive balances cache kept up to
date since a state of the epoch (`GloasCacheProvenanceUpkeep`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_upkeep (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenanceUpkeep progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  -- The upkeep keeps the cache coherent up to the epoch input.
  obtain ⟨start, cache0, hcoh0, hup⟩ := hcaches.progressive
  exact lighthouse_model_gloas_epoch_eq_etheorem hpreset hhistLimit hrun hchain hetheorem horacle
    ⟨coherent_of_upkeep hcoh0 hup, hcaches.epochCache, hcaches.pubkeyCache⟩

/-- Gloas, for the composed Rust: the same, for `Compose.epoch` on a Rust state that views as
the epoch input, given the glue facts. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState e)) :
    GloasRustEqualsEtheorem rustGlue view rustState e := by
  obtain ⟨⟨s', hs', e', he', habs⟩, -⟩ := lighthouse_model_gloas_epoch_eq_etheorem hpreset
    hhistLimit hrun hchain hetheorem horacle hcaches
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  -- The composed Rust returns the model's state.
  obtain ⟨st', hep, hv⟩ := Compose.epoch_spec rustGlue oracle view rustState hrust.glue
    (by rw [hrust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hpre.2.1)
    (by rw [hrust.viewEq]; exact hchain.vectorLengths) s' (by rw [hrust.viewEq]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] [HasherTag] [CryptoBackend] [EthCLSpecs.Gloas.Preset]
  [EthCLSpecs.Gloas.Config] in
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

end Gloas

/-! ## Fulu -/

section Fulu

open EpochProofs.Etheorem.Fulu

variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {e : EtheoremState}

/-- The Lean model of Lighthouse's Fulu epoch returns `ok s'`, Etheorem's Fulu `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def FuluLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremState) : Prop :=
  ∃ s', Spec.process_epoch_lighthouse_fulu o (toSpecState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s'

/-- The composed Rust Fulu epoch (`Compose.epochFulu`) returns `Ok st'`, Etheorem's Fulu
`processEpoch` succeeds, and its result maps to the view of `st'`. -/
def FuluRustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlueFulu σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EtheoremState) : Prop :=
  ∃ st', Compose.epochFulu G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = view st'

/-- Fulu: at every epoch boundary of a Fulu run, the Lean model of Lighthouse's epoch succeeds
and equals Etheorem's. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState e))
    (hchain : FuluChainAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    FuluLighthouseModelEqualsEtheorem oracle e := by
  have hin := hrun.invariants
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  obtain ⟨⟨⟨hb, -, heb, -, hsup⟩, -, hcons⟩, -, -⟩ := hin
  -- The Fulu spec epoch returns `ok s'`.
  obtain ⟨s', hs'⟩ := Spec.process_epoch_fulu_total oracle (toSpecState e) hb.2.1
    hchain.slotFarFromOverflow hpre.1 hchain.vectorLengths hb.1 heb hcons hsup.2.2
    hchain.physicalLimits
    (Spec.committeesOkFulu_of oracle _ hchain.slotFarFromOverflow hchain.atCommitteeStepState)
  -- The model gives the same state, and Etheorem's result maps to it.
  have hlh := (Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle (toSpecState e)
    hrun.invariants hpre s').mpr hs'
  exact ⟨s', hlh, process_epoch_fulu_etheorem hpreset oracle horacle.agrees horacle.sha32 e
    hetheorem hs'⟩

/-- Fulu, for the composed Rust. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState e))
    (hchain : FuluChainAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    (hrust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState e)) :
    FuluRustEqualsEtheorem rustGlue view rustState e := by
  obtain ⟨s', hs', e', he', habs⟩ := lighthouse_model_fulu_epoch_eq_etheorem hpreset hrun hchain
    hetheorem horacle
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  have hvec := hchain.vectorLengths
  unfold Spec.BeaconState.FuluVectorLengths at hvec
  obtain ⟨-, -, -, -, hjb, -, -, hpl⟩ := hvec
  -- The composed Rust returns the model's state.
  obtain ⟨st', hep, hv⟩ := Compose.epochFulu_spec rustGlue oracle view rustState hrust.glue
    (by rw [hrust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hpre.2.1)
    (by rw [hrust.viewEq]; exact hjb) (by rw [hrust.viewEq]; exact hpl) s'
    (by rw [hrust.viewEq]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

end Fulu

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
