import EpochProofs.FormalhouseFinal
import EpochProofs.CacheBridge.Upkeep

/-!
# Formalhouse: the Gloas result with the cache upkeep

The final Gloas statement assumes a coherent progressive balances cache at the epoch input.
`formalhouse_gloas_epoch_final_upkeep` assumes it only at a state `start` of the epoch, plus the
named upkeep fact `CacheUpkeep`, which lists the Lighthouse hooks between the two states.
-/

set_option maxHeartbeats 1000000

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.Etheorem EpochProofs.CacheBridge

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- `formalhouse_gloas_epoch_final` with the progressive balances cache coherent at a state
`start` of the epoch (after a fresh build, or after the epoch transition) and the trusted upkeep
fact `CacheUpkeep` (U1 to U4 in `Trusted/CacheUpkeep.lean`) from `start` to the epoch input. -/
theorem formalhouse_gloas_epoch_final_upkeep (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e)
    (start : CacheProofs.Spec.BeaconState) (cache0 cache : LhCache)
    (hcoh0 : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT start cache0)
    (hup : CacheUpkeep EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT start
      (pbState (absEState e) ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      cache0 cache)
    (total : U64) (b : Spec.BeaconState)
    (hagree : Spec.ActiveAgree ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)
      b (absEState e))
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        (b.validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
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
      let cur := s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH
      (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
            f.val cur >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
      (∀ f : Usize, f.val < 3 → 0 < cur →
        ∃ x : U64, lhPreviousEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
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
      ∀ i, r.map (·.val) = some i → i = ((absEState e).validators.map (·.pubkey)).idxOf pk :=
  formalhouse_gloas_epoch_final hpa hhr o fo c uc init e hin ha cache
    (coherent_of_upkeep hcoh0 hup) total b hagree htotal laws b' hpre hpk0 hupd

end EpochProofs.Formalhouse
