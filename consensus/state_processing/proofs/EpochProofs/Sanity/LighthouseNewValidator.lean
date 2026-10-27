import EpochProofs.Spec.Epoch
import EpochProofs.Spec.PresetCfg

/-!
# The Lighthouse new validator equals the spec

`Validator::from_deposit` computes the effective balance of a new validator with the two
functions of `deposit_balance.rs` (`Equiv/DepositBalance.lean`). The models below use these two
functions where the spec has `get_max_effective_balance` and the `min` of
`get_validator_from_deposit`. With a nonzero increment, each model equals its spec function.
-/

namespace EpochProofs.Spec

/-- `max_effective_balance_electra` of `deposit_balance.rs`. -/
def lhMaxEffectiveBalanceElectra (is_compounding : Bool)
    (max_effective_balance_electra min_activation_balance : Gwei) : Gwei :=
  if is_compounding then max_effective_balance_electra else min_activation_balance

/-- `deposit_effective_balance` of `deposit_balance.rs`. An increment of 0 does not round. -/
def lhDepositEffectiveBalance (amount increment max_effective_balance : Gwei) : Gwei :=
  let rounded := if increment = 0 then amount else amount - amount % increment
  if rounded < max_effective_balance then rounded else max_effective_balance

/-- `Validator::from_deposit` after Electra. -/
def lhValidatorFromDeposit (p : Preset) (pubkey : BLSPubkey) (withdrawal_credentials : Bytes32)
    (amount : Gwei) : Validator :=
  { pubkey
    withdrawal_credentials
    effective_balance := lhDepositEffectiveBalance amount p.EFFECTIVE_BALANCE_INCREMENT
      (lhMaxEffectiveBalanceElectra (is_compounding_withdrawal_credential withdrawal_credentials)
        p.MAX_EFFECTIVE_BALANCE_ELECTRA p.MIN_ACTIVATION_BALANCE)
    slashed := false
    activation_eligibility_epoch := FAR_FUTURE_EPOCH
    activation_epoch := FAR_FUTURE_EPOCH
    exit_epoch := FAR_FUTURE_EPOCH
    withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- `add_validator_to_registry` with `lhValidatorFromDeposit`. -/
def lhAddValidatorToRegistry (p : Preset) (state : BeaconState) (pubkey : BLSPubkey)
    (withdrawal_credentials : Bytes32) (amount : Gwei) : SpecM BeaconState := do
  let index := get_index_for_new_validator state
  let validator := lhValidatorFromDeposit p pubkey withdrawal_credentials amount
  let state := { state with validators := ← set_or_append_list state.validators index validator }
  let state := { state with balances := ← set_or_append_list state.balances index amount }
  let state := { state with
    previous_epoch_participation :=
      ← set_or_append_list state.previous_epoch_participation index 0 }
  let state := { state with
    current_epoch_participation := ← set_or_append_list state.current_epoch_participation index 0 }
  pure { state with
    inactivity_scores := ← set_or_append_list state.inactivity_scores index 0 }

/-- `apply_pending_deposit` with `lhAddValidatorToRegistry`. -/
def lhApplyPendingDeposit (p : Preset) (o : Oracle) (state : BeaconState)
    (deposit : PendingDeposit) : SpecM BeaconState := do
  let validator_pubkeys := state.validators.map (·.pubkey)
  if deposit.pubkey ∉ validator_pubkeys then
    if is_valid_deposit_signature p o deposit.pubkey deposit.withdrawal_credentials
        deposit.amount deposit.signature then
      lhAddValidatorToRegistry p state deposit.pubkey deposit.withdrawal_credentials
        deposit.amount
    else
      pure state
  else
    let validator_index := validator_pubkeys.idxOf deposit.pubkey
    pure { state with balances := ← increase_balance state.balances validator_index deposit.amount }

theorem lhDepositEffectiveBalance_eq_min (amount increment m : Gwei) (h : 0 < increment) :
    lhDepositEffectiveBalance amount increment m = min (amount - amount % increment) m := by
  unfold lhDepositEffectiveBalance
  simp only [Nat.pos_iff_ne_zero.mp h, if_false, Nat.min_def]
  by_cases h1 : amount - amount % increment < m
  · simp [h1, Nat.le_of_lt h1]
  · simp only [h1, if_false]
    by_cases h2 : amount - amount % increment ≤ m
    · simp only [h2, if_true]; exact Nat.le_antisymm (Nat.not_lt.mp h1) h2
    · simp [h2]

theorem get_validator_from_deposit_lh (p : Preset) (h : 0 < p.EFFECTIVE_BALANCE_INCREMENT)
    (pubkey : BLSPubkey) (withdrawal_credentials : Bytes32) (amount : Gwei) :
    get_validator_from_deposit p pubkey withdrawal_credentials amount =
      .ok (lhValidatorFromDeposit p pubkey withdrawal_credentials amount) := by
  have hm : amount % p.EFFECTIVE_BALANCE_INCREMENT ≤ amount := Nat.mod_le _ _
  simp only [get_validator_from_deposit, lhValidatorFromDeposit, uint64Mod, uint64Sub,
    Nat.pos_iff_ne_zero.mp h, if_false, hm, if_true, lhDepositEffectiveBalance_eq_min _ _ _ h,
    get_max_effective_balance, has_compounding_withdrawal_credential,
    lhMaxEffectiveBalanceElectra, pure, Except.pure, Bind.bind, Except.bind]
  rfl

theorem add_validator_to_registry_lh (p : Preset) (h : 0 < p.EFFECTIVE_BALANCE_INCREMENT)
    (state : BeaconState) (pubkey : BLSPubkey) (withdrawal_credentials : Bytes32) (amount : Gwei) :
    lhAddValidatorToRegistry p state pubkey withdrawal_credentials amount =
      add_validator_to_registry p state pubkey withdrawal_credentials amount := by
  simp only [lhAddValidatorToRegistry, add_validator_to_registry,
    get_validator_from_deposit_lh p h, Bind.bind, Except.bind]

theorem lhApplyPendingDeposit_eq (p : Preset) (h : 0 < p.EFFECTIVE_BALANCE_INCREMENT)
    (o : Oracle) : lhApplyPendingDeposit p o = apply_pending_deposit p o := by
  funext state deposit
  simp only [lhApplyPendingDeposit, apply_pending_deposit, add_validator_to_registry_lh p h]

theorem lhApplyPendingDeposit_mainnet [PresetCfg] (o : Oracle) :
    lhApplyPendingDeposit P o = apply_pending_deposit P o :=
  lhApplyPendingDeposit_eq P (by pdecide) o

end EpochProofs.Spec
