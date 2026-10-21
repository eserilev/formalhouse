import EpochProofs.Equiv.Slashings
import EpochProofs.Equiv.RegistryUpdates
import EpochProofs.Sanity.LighthouseNewValidator

/-!
# Lighthouse new validator effective balance equals its model

`deposit_balance.rs` in the `types` crate holds the two functions that `Validator::from_deposit`
and `Validator::get_max_effective_balance` call after Electra. Each theorem relates one of them
to its model in `Sanity/LighthouseNewValidator.lean`. The functions never fail.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem max_effective_balance_electra_equiv (is_compounding : Bool) (a b : U64) :
    types.validator.deposit_balance.max_effective_balance_electra is_compounding a b ⦃ r =>
      r.val = Spec.lhMaxEffectiveBalanceElectra is_compounding a.val b.val ⦄ := by
  unfold types.validator.deposit_balance.max_effective_balance_electra
    Spec.lhMaxEffectiveBalanceElectra
  by_cases hc : is_compounding <;> simp [hc]

theorem deposit_effective_balance_equiv (amount increment m : U64) :
    types.validator.deposit_balance.deposit_effective_balance amount increment m ⦃ r =>
      r.val = Spec.lhDepositEffectiveBalance amount.val increment.val m.val ⦄ := by
  unfold types.validator.deposit_balance.deposit_effective_balance Spec.lhDepositEffectiveBalance
  obtain ⟨r, hr, h⟩ := spec_imp_exists (safe_rem_spec amount increment)
  rw [hr]
  simp only [bind_tc_ok]
  cases r with
  | Ok rem =>
    obtain ⟨hv, hb⟩ := h.1 rem rfl
    simp only [bind_tc_ok, hb, if_false]
    have hs : (core.num.U64.saturating_sub amount rem).val = amount.val - amount.val % increment.val := by
      rw [u64_saturating_sub_val, hv]
    split
    · rename_i hlt
      have : amount.val - amount.val % increment.val < m.val := by
        rw [← hs]; exact hlt
      simp [this, hs]
    · rename_i hlt
      have : ¬ amount.val - amount.val % increment.val < m.val := by
        rw [← hs]; exact hlt
      simp [this]
  | Err e =>
    obtain ⟨-, hb⟩ := h.2 e rfl
    simp only [bind_tc_ok, hb, if_true]
    split
    · rename_i hlt
      have : amount.val < m.val := hlt
      simp [this]
    · rename_i hlt
      have : ¬ amount.val < m.val := hlt
      simp [this]

/-- The proof root `new_validator_effective_balance` is the effective balance of
`lhValidatorFromDeposit`. -/
theorem new_validator_effective_balance_equiv (amount : U64) (is_compounding : Bool)
    (increment a b : U64) :
    per_epoch_processing.pending_deposits.new_validator_effective_balance amount is_compounding
      increment a b ⦃ r =>
        r.val = Spec.lhDepositEffectiveBalance amount.val increment.val
          (Spec.lhMaxEffectiveBalanceElectra is_compounding a.val b.val) ⦄ := by
  unfold per_epoch_processing.pending_deposits.new_validator_effective_balance
  apply spec_bind (max_effective_balance_electra_equiv is_compounding a b)
  intro m hm
  rw [← hm]
  exact deposit_effective_balance_equiv amount increment m

end EpochProofs
