import EpochProofs.CacheBridge.Capstone
import EpochProofs.Etheorem.Final

/-!
# The Lighthouse epoch equals Etheorem, with the cache reads checked

The Etheorem part of `CacheBridge/Capstone.lean`. This file is not in the build: Etheorem is not
a dependency at the moment.
-/

namespace EpochProofs.CacheBridge

section Generic

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [EthCLLib.Spec.HasherTag]
  [EthCLLib.Spec.CryptoBackend]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- Lighthouse's epoch processing equals Etheorem's Gloas `processEpoch` at an epoch boundary of
a reachable run, on mainnet (`lighthouse_order_epoch_etheorem_reachable`), and the cache reads
that it makes equal the spec values of the model (`lh_cache_reads_mainnet`). The caches satisfy
their build invariants at the epoch start state. -/
theorem lighthouse_order_epoch_etheorem_reachable_cached [EpochProofs.Spec.PresetCfg]
    [EpochProofs.Spec.PresetCfg.Ok] (hpa : EpochProofs.Etheorem.PresetMatchesEtheorem Spec.P)
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
    (∃ e', (EthCLSpecs.Gloas.processEpoch
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
          .ok r.val) :=
  ⟨EpochProofs.Etheorem.lighthouse_order_epoch_etheorem_reachable hpa hhr o ho hsha e hin hpre
    hcond h,
   lh_cache_reads_mainnet _ hin.1.1.1.2.1 hin.1.1.2.2.2.2 c hc total htotal⟩

end Generic

end EpochProofs.CacheBridge
