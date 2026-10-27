import EpochProofs.Equiv.PendingDeposits
import EpochProofs.Spec.PresetCfg
import EpochProofs.Sanity.Invariants.LighthouseTailDeposits

/-!
# The postponed flags cover every handled deposit

`PendingDepositsContext::new` in `single_pass.rs` reads `outcome.postponed[i]` for each
`i < outcome.next_deposit_index`, with an `ok_or` on a missing flag.
`process_pending_deposits_postponed_len` shows that `postponed` has exactly
`next_deposit_index` entries on mainnet, so that `ok_or` never fails.
-/

namespace EpochProofs.Spec

theorem depositDecisions_postponed_len [PresetCfg] (fs dbtc churn : Nat) (views : List DepositSpecView)
    (n : Nat) (b : Gwei) (pp : List Bool)
    (h : depositDecisions P fs dbtc churn views = .ok (n, b, pp)) :
    pp.length = n := by
  unfold depositDecisions at h
  obtain ⟨avail, -, h⟩ := specM_bind_ok h
  obtain ⟨r, hr, h⟩ := specM_bind_ok h
  obtain ⟨flags, hpp, hn⟩ := depositLoop_growth fs avail views ⟨0, 0, []⟩ r hr
  have key : n = r.state.next_deposit_index ∧ pp = r.state.postponed := by
    dsimp only at h
    split at h
    · obtain ⟨y, -, h⟩ := specM_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.2.symm⟩
    · simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.2.symm⟩
  rw [key.1, key.2, hpp, hn]
  simp

end EpochProofs.Spec

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem process_pending_deposits_postponed_len [EpochProofs.Spec.PresetCfg] (views : Slice LhDepositView)
    (finalized_slot current_epoch next_epoch deposit_balance_to_consume churn : U64)
    (c : LhDepositConstants) (hc : DepositConstantsMatch Spec.P c) :
    per_epoch_processing.pending_deposits.process_pending_deposits views finalized_slot
      current_epoch next_epoch deposit_balance_to_consume churn c ⦃ r =>
        ∀ o, r = .Ok o → o.postponed.val.length = o.next_deposit_index.val ⦄ := by
  obtain ⟨r, hr, hq⟩ := spec_imp_exists (process_pending_deposits_equiv Spec.P views
    finalized_slot current_epoch next_epoch deposit_balance_to_consume churn c hc)
  apply exists_imp_spec
  refine ⟨r, hr, ?_⟩
  intro o ho
  subst ho
  simp only [absDeposits] at hq
  exact Spec.depositDecisions_postponed_len _ _ _ _ _ _ _ hq.symm

end EpochProofs
