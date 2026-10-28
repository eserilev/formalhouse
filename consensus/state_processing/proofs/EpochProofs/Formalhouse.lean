import EpochProofs.Etheorem.Total
import EpochProofs.CacheBridge.CapstoneCommittees
import EpochProofs.CachePubkey

/-!
# Formalhouse: the Gloas epoch of Lighthouse

`formalhouse_gloas_epoch` joins the epoch results into one statement, for a preset that agrees
with Etheorem's (`EpochPresetAgrees`, proved for mainnet and minimal), at the last slot of an
epoch of a reachable run:

1. Lighthouse's epoch (`process_epoch_lh_order`: Lighthouse's step order, its genesis path and
   the checked Rust of each step) returns `ok` (`lighthouse_epoch_total_etheorem`).
2. Its result equals Etheorem's Gloas `processEpoch` (`lighthouse_epoch_total_etheorem`).
3. The cache reads that Lighthouse makes (progressive balances, epoch cache, PTC committees)
   equal the spec values, given only the build facts of each cache
   (`lighthouse_order_epoch_etheorem_reachable_cached_ptc`).
4. The pubkey cache lookup of the pending deposits equals the spec lookup
   (`pubkey_cache_deposit_lookup`).

`GloasEpochConds` lists every condition that the statement takes about the epoch start state.
The caches are arguments: Lighthouse holds them at run time, and each one comes with its build
fact.

Trusted, outside this statement (see README.md, "What is trusted"):
- the glue that the model writes by hand: the milhouse loop of `single_pass.rs` and the writes
  after it, the participation rotation, the PTC window shift, the sync committee keys and
  aggregate key, the PTC joining loop (`CommitteesFromCache`), the committee cache inputs, the
  pubkey cache update loop and `HashTrieMap`;
- the Lean spec, Etheorem at the pinned fork commit, Aeneas, Charon and Lean.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas
open EpochProofs.Etheorem EpochProofs.CacheBridge

section Generic

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds]

/-- The conditions of `formalhouse_gloas_epoch` on the epoch start state `e`, by kind. -/
structure GloasEpochConds (o : Spec.Oracle) (e : EState) : Prop where
  /-- Reachable-state invariants (`Sanity/Invariants`): the facts that every state reached
  by spec state transitions from a genesis-like state keeps. -/
  reachable : Spec.EpochInputOk'' Spec.EpochSupply (absEState e)
  /-- Reachable-state invariant: no two validators share a pubkey (`PubkeysUnique.lean`). -/
  pubkeys : Spec.PubkeysUnique (absEState e)
  /-- Reachable-state invariant: the SSZ vector fields have their lengths. The Lean state holds
  them as lists. -/
  vectors : (absEState e).VectorLengths Spec.P
  /-- The epoch boundary: the last slot of an epoch, the next slot fits in `u64`, and fewer than
  `2^24` historical summaries (a time bound: about 1.6M years). -/
  boundary : Spec.TailPre (absEState e)
  /-- Time bound: the slot is `8192` below `2^64`. The pyspec `get_block_root` raises above. -/
  slot : (absEState e).slot + 8192 < 2 ^ 64
  /-- Supply and time bounds (`RowBounds`): inactivity scores (F5), total effective balance,
  balance sum, exit queue, registry size, participation against the active balance. The pyspec
  raises without them too. -/
  rows : Spec.RowBounds (absEState e)
  /-- Etheorem's list limits from alpha.11 (F6, F10): room in the registry for the deposits of
  one epoch and in the builder pending withdrawals. beta.4 has no limit on these lists. -/
  etheoremRoom : EpochCondsIn e
  /-- At the state that the epoch passes to the committee steps (`Spec.epochToCommittees`):
  state facts (`CommConds`: registry size, effective balance cap,
  lookahead and PTC window lengths, valid keys) and true pyspec preconditions (`CommPreconds`:
  a sync candidate, a proposer candidate (F4), at least `SLOTS_PER_EPOCH` active validators
  (F12), and each
  balance weighted selection ends within `2^64` passes, a fact about the hash values). -/
  committees : Spec.CommAt o (absEState e)
  /-- A fact about Etheorem's output (F3): its selections return all their items. Etheorem
  stops after `10^7` passes. -/
  selections : SelectionsFull e
  /-- Oracle: the spec Oracle agrees with Etheorem's functions (SHA-256, the roots, the BLS
  key and signature checks). -/
  oracle : OracleAgrees o
  /-- Oracle: SHA-256 returns 32 bytes. `sha_size_pure` proves it for the pure SHA-256. -/
  sha : ∀ b : ByteArray, (sha b).size = 32

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- The Gloas epoch of Lighthouse returns `ok` and equals Etheorem's `processEpoch`, its cache
reads equal the spec values, and its pubkey cache lookup equals the spec lookup. -/
theorem formalhouse_gloas_epoch (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle) (e : EState) (hc : GloasEpochConds o e)
    (c : LhCache)
    (hcoh : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState (absEState e)
        ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)) c)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        ((absEState e).validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      ((absEState e).validators.map (·.effective_balance)))
    {M : Type} {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey}
    {view : M → Spec.BLSPubkey → Option Usize} (laws : CacheProofs.IndexMapLaws inst view)
    {m : M} {len : Usize}
    (hpk : CacheProofs.Coherent view m len ((absEState e).validators.map (·.pubkey))) :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      (((∃ e', (EthCLSpecs.Gloas.processEpoch
          (StateTransition := GloasRun)).run (EthCLLib.Proofs.pureState e) =
        .ok ((), EthCLLib.Proofs.pureState e') ∧ EpochProofs.Etheorem.absEState e' = s') ∧
      let s := EpochProofs.Etheorem.absEState e
      let cur := s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH
      (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance c f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
            f.val cur >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
      (∀ f : Usize, f.val < 3 → 0 < cur →
        ∃ x : U64, lhPreviousEpochFlagAttestingBalance c f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
            f.val (cur - 1) >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
      (∀ inc : U64, inc.val = EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT →
        ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
          EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.P s =
            .ok r.val)) ∧
      (∀ (st : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32),
        Spec.get_seed Spec.P o st epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed →
        ∀ (shuffling : Slice Usize) (cps spe : Usize),
        CommitteeCacheBuilt cachePresetOf o st epoch seed shuffling
          cps →
        spe.val = Spec.P.SLOTS_PER_EPOCH →
        0 < (Spec.get_active_validator_indices st epoch).length →
        (Spec.get_active_validator_indices st epoch).length ≤ 2 ^ 24 →
        (Spec.get_active_validator_indices st epoch).length * (cps.val * spe.val) ≤ Usize.max →
        ∀ (start : Nat), Spec.compute_start_slot_at_epoch Spec.P epoch = .ok start →
        ∀ (committees : Slice (alloc.vec.Vec Usize)),
        committees.val.length = Spec.P.SLOTS_PER_EPOCH →
        CommitteesFromCache shuffling cps spe epoch start committees →
        ∀ k (hk : k < committees.val.length) l,
          Spec.ptcIndices Spec.P o st epoch (start + k) = .ok l →
            (committees.val[k]).val.map (·.val) = l)) ∧
    ∀ pk, ∃ r, inst.get_index m pk = ok r ∧
      (r.map (·.val)).bind (fun i => (absEState e).validators[i]?) =
        (absEState e).validators[((absEState e).validators.map (·.pubkey)).idxOf pk]? ∧
      (r.isSome ↔ pk ∈ (absEState e).validators.map (·.pubkey)) ∧
      ∀ i, r.map (·.val) = some i → i = ((absEState e).validators.map (·.pubkey)).idxOf pk := by
  obtain ⟨s', hs', -⟩ := lighthouse_epoch_total_etheorem hpa hhr o hc.oracle hc.sha e hc.reachable
    hc.boundary hc.etheoremRoom hc.selections hc.slot hc.vectors hc.rows hc.committees
  exact ⟨s', hs', lighthouse_order_epoch_etheorem_reachable_cached_ptc hpa hhr o hc.oracle hc.sha e
    hc.reachable hc.boundary hc.etheoremRoom hc.selections hs' c hcoh total htotal,
    fun pk => Spec.pubkey_cache_deposit_lookup laws (absEState e) hpk hc.pubkeys pk⟩

end Generic

end EpochProofs.Formalhouse
