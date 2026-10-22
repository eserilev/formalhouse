import EpochProofs.FormalhouseFinal
import EpochProofs.CacheBridge.BuildPath

/-!
# Formalhouse: the cache build facts on the epoch path

`formalhouse_gloas_epoch_cachepath` restates `formalhouse_gloas_epoch_final` with two cache facts
moved from the epoch input to the state that built the cache:

- the epoch cache total holds the active sum of a state `b` of the same epoch, and the blocks
  between `b` and the epoch input keep the effective balances and the activity
  (`ActiveAgree`, which `state_transition_epochInv` keeps for each block);
- the pubkey cache holds the pubkeys of an earlier state `b'` whose pubkeys are a prefix of the
  epoch input's pubkeys (`PkPrefix`, see `Reachable.pkPrefix` and `SlotReachG.pkPrefix`), and
  `update_pubkey_cache` ran on it (`insertAll`).

The progressive balances cache stays a fact about the epoch input: `Coherent` with the state.
`initialize_progressive_balances_cache` rebuilds a cache of another epoch, and the block
operations update it with the functions that `CacheProofs.PB` proves. That each mutation calls
its update function is checked by review only.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.Etheorem EpochProofs.CacheBridge

section Gloas

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- `formalhouse_gloas_epoch_final` with the epoch cache total built at a state `b` of the same
epoch, and the pubkey cache built at an earlier state `b'` and completed by
`update_pubkey_cache`. -/
theorem formalhouse_gloas_epoch_cachepath (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e)
    (cache : LhCache)
    (hcoh : Coherent EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT
      (pbState (absEState e)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH)) cache)
    (total : U64) (b : Spec.BeaconState)
    (hagree : Spec.ActiveAgree ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH)
      b (absEState e))
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        (b.validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance)))
    {M : Type} {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey}
    {view : M → Spec.BLSPubkey → Option Usize} (laws : CacheProofs.IndexMapLaws inst view)
    (b' : Spec.BeaconState) (hpre : Spec.PkPrefix b' (absEState e))
    {m0 m : M} {len0 len : Usize}
    (hpk0 : CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)))
    (hupd : CacheProofs.insertAll inst m0 len0
      (((absEState e).validators.map (·.pubkey)).drop len0.val) = ok (some (m, len))) :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      (((∃ e', (EthCLSpecs.Gloas.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ EpochProofs.Etheorem.absEState e' = s') ∧
      let s := EpochProofs.Etheorem.absEState e
      let cur := s.slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH
      (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val cur >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ f : Usize, f.val < 3 → 0 < cur →
        ∃ x : U64, lhPreviousEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val (cur - 1) >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ inc : U64, inc.val = EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT →
        ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
          EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.Preset.mainnet s =
            .ok r.val)) ∧
      (∀ (st : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32),
        Spec.get_seed Spec.Preset.mainnet o st epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed →
        ∀ (shuffling : Slice Usize) (cps spe : Usize),
        CommitteeCacheBuilt CacheProofs.Spec.CommitteeCache.Preset.mainnet o st epoch seed shuffling
          cps →
        spe.val = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        0 < (Spec.get_active_validator_indices st epoch).length →
        (Spec.get_active_validator_indices st epoch).length ≤ 2 ^ 24 →
        (Spec.get_active_validator_indices st epoch).length * (cps.val * spe.val) ≤ Usize.max →
        ∀ (start : Nat), Spec.compute_start_slot_at_epoch Spec.Preset.mainnet epoch = .ok start →
        ∀ (committees : Slice (alloc.vec.Vec Usize)),
        committees.val.length = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        CommitteesFromCache shuffling cps spe epoch start committees →
        ∀ k (hk : k < committees.val.length) l,
          Spec.ptcIndices Spec.Preset.mainnet o st epoch (start + k) = .ok l →
            (committees.val[k]).val.map (·.val) = l)) ∧
    ∀ pk, ∃ r, inst.get_index m pk = ok r ∧
      (r.map (·.val)).bind (fun i => (absEState e).validators[i]?) =
        (absEState e).validators[((absEState e).validators.map (·.pubkey)).idxOf pk]? ∧
      (r.isSome ↔ pk ∈ (absEState e).validators.map (·.pubkey)) ∧
      ∀ i, r.map (·.val) = some i → i = ((absEState e).validators.map (·.pubkey)).idxOf pk :=
  formalhouse_gloas_epoch_final o fo c uc init e hin ha cache hcoh total
    (epoch_cache_total_carry total.val htotal hagree) laws
    (pubkey_cache_carry laws hpre hpk0 hupd)

end Gloas

end EpochProofs.Formalhouse
