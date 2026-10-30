import EpochProofs.CacheBridge.Capstone
import EpochProofs.Spec.PresetCfg
import EpochProofs.CacheBridge.Committees

/-!
# The Lighthouse epoch equals Etheorem, with the committee cache reads checked

`lighthouse_order_epoch_etheorem_reachable_cached` (`CacheBridge/Capstone.lean`) checks the
progressive balances and epoch cache reads. This file adds the committee cache read of the PTC
window step.

Lighthouse runs `process_ptc_window` on the state of the epoch at that step. It builds a
committee cache for the lookahead epoch from that state, and joins the cache committees of each
slot. When the cache satisfies its build facts (`CommitteeCacheBuilt`, from the Aeneas-checked
`committee_assignment::shuffling` and `committee_count_per_slot` by
`committeeCacheBuilt_of_rust`), the joined committees are `ptcIndices` of the epoch reference.
This replaces the committee hypothesis of `ptc_for_epoch_spec` (`lh_ptc_window_from_cache`).
-/

namespace EpochProofs.CacheBridge

section Generic

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [EthCLLib.Spec.HasherTag]
  [EthCLLib.Spec.CryptoBackend]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- `lighthouse_order_epoch_etheorem_reachable_cached`, and the PTC committees that Lighthouse
reads from a committee cache equal the spec `ptcIndices`: for any state `st` at which Lighthouse
builds the committee cache of `epoch`, a cache that satisfies its build facts and the way
Lighthouse joins its committees give the committees of `compute_ptc`. -/
theorem lighthouse_order_epoch_etheorem_reachable_cached_ptc [EpochProofs.Spec.PresetCfg]
    [EpochProofs.Spec.PresetCfg.Ok] [EpochProofs.Spec.PresetCfg.Bounds]
    (hpa : EpochProofs.Etheorem.PresetMatchesEtheorem Spec.P)
    (hhr : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle)
    (ho : EpochProofs.Etheorem.OracleAgrees o)
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) (e : EpochProofs.Etheorem.EtheoremState)
    (hin : Spec.ReachableInvariants (EpochProofs.Etheorem.toSpecState e))
    (hpre : Spec.AtEpochBoundary (EpochProofs.Etheorem.toSpecState e))
    (hcond : EpochProofs.Etheorem.GloasEtheoremDivergenceAssumptions e)
    {s' : Spec.BeaconState}
    (h : Spec.process_epoch_lighthouse o (EpochProofs.Etheorem.toSpecState e) = .ok s')
    (c : LhCache)
    (hc : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState (EpochProofs.Etheorem.toSpecState e)
        ((EpochProofs.Etheorem.toSpecState e).slot /
          EpochProofs.Spec.P.SLOTS_PER_EPOCH)) c)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        ((EpochProofs.Etheorem.toSpecState e).validators.map ecValidator)
        ((EpochProofs.Etheorem.toSpecState e).slot /
          EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      ((EpochProofs.Etheorem.toSpecState e).validators.map (·.effective_balance))) :
    ((∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := GloasRun)).run (EthCLLib.Proofs.pureState e) =
      .ok ((), EthCLLib.Proofs.pureState e') ∧ EpochProofs.Etheorem.toSpecState e' = s') ∧
    let s := EpochProofs.Etheorem.toSpecState e
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
          (committees.val[k]).val.map (·.val) = l) :=
  ⟨lighthouse_order_epoch_etheorem_reachable_cached hpa hhr o ho hsha e hin hpre hcond h c hc total
    htotal,
   fun st epoch seed hseed shuffling cps spe hbuilt hspe hn hn24 hfit start hstart committees
      hclen hglue =>
    hcomm_of_cache Spec.P _ committeePresetLink_P o st epoch seed hseed
      shuffling cps spe hbuilt hspe hn hn24 hfit start hstart committees hclen hglue⟩

end Generic

end EpochProofs.CacheBridge
