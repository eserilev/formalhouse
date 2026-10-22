import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Generated

/-!
# The contracts of the epoch tail writes

The writes after the single-pass loop in `single_pass.rs` are generic over small traits. Aeneas
translates the generic code, but not the implementations over the milhouse lists. The theorems
take one contract for each trait as a hypothesis. This file is the only statement the proofs trust
about these writes.

`DepositWritesContract` says what `StateDeposits` in `single_pass.rs` does, in spec terms:

- `write_queue` sets the pending deposits to the deposits from the given index on, followed by
  the postponed deposits, and sets `deposit_balance_to_consume`. It succeeds when the index is at
  most the queue length.
- `validator_index` returns the index of the first validator with the deposit pubkey. It changes
  no field of the state.
- `balance` and `set_balance` read and write one balance. A read out of range fails.
- `is_valid_signature` is the spec `is_valid_deposit_signature`.
- `add_validator` is the spec `add_validator_to_registry` and returns the new index. It fails
  when the spec fails.
- `update_effective_balance` is the effective balance update of one validator. It fails when the
  spec fails.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev LhDepositWrites (S D E : Type) := per_epoch_processing.deposit_writes.DepositWrites S D E

/-- Trusted: what the `DepositWrites` implementation in `single_pass.rs` does. `view` gives the
spec state that an implementation value holds, `absDep` the spec deposit of a deposit, and
`postOf` the postponed deposits that the value holds. -/
structure DepositWritesContract {S D E : Type} (inst : LhDepositWrites S D E) (o : Spec.Oracle)
    (view : S → Spec.BeaconState) (absDep : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) : Prop where
  write_queue : ∀ (s : S) (next : Usize) (dbtc : U64),
    next.val ≤ (view s).pending_deposits.length →
    ∃ s', inst.write_queue s next dbtc = ok (.Ok (), s') ∧
      view s' = { view s with
        pending_deposits := (view s).pending_deposits.drop next.val ++ postOf s
        deposit_balance_to_consume := dbtc.val }
  validator_index : ∀ (s : S) (d : D), ∃ r s', inst.validator_index s d = ok (.Ok r, s') ∧
    view s' = view s ∧
    r.map (·.val) = (if (absDep d).pubkey ∈ (view s).validators.map (·.pubkey) then
      some (((view s).validators.map (·.pubkey)).idxOf (absDep d).pubkey) else none)
  amount : ∀ (s : S) (d : D), ∃ a : U64, inst.amount s d = ok a ∧ a.val = (absDep d).amount
  balance : ∀ (s : S) (i : Usize),
    (∃ b : U64, inst.balance s i = ok (.Ok b) ∧ (view s).balances[i.val]? = some b.val) ∨
    ((view s).balances[i.val]? = none ∧ ∃ e, inst.balance s i = ok (.Err e))
  set_balance : ∀ (s : S) (i : Usize) (b : U64), i.val < (view s).balances.length →
    ∃ s', inst.set_balance s i b = ok (.Ok (), s') ∧
      view s' = { view s with balances := (view s).balances.set i.val b.val }
  is_valid_signature : ∀ (s : S) (d : D), inst.is_valid_signature s d =
    ok (Spec.is_valid_deposit_signature Spec.Preset.mainnet o (absDep d).pubkey
      (absDep d).withdrawal_credentials (absDep d).amount (absDep d).signature)
  add_validator : ∀ (s : S) (d : D),
    (∀ t', Spec.add_validator_to_registry Spec.Preset.mainnet (view s) (absDep d).pubkey
        (absDep d).withdrawal_credentials (absDep d).amount = .ok t' →
      ∃ (i : Usize) (s' : S), inst.add_validator s d = ok (.Ok i, s') ∧ view s' = t' ∧
        i.val = (view s).validators.length) ∧
    (∀ e, Spec.add_validator_to_registry Spec.Preset.mainnet (view s) (absDep d).pubkey
        (absDep d).withdrawal_credentials (absDep d).amount = .error e →
      ∃ (e' : E) (s' : S), inst.add_validator s d = ok (.Err e', s'))
  update_effective_balance : ∀ (s : S) (i : Usize),
    (∀ t', Spec.ebUpdateAt (view s) i.val = .ok t' →
      ∃ s', inst.update_effective_balance s i = ok (.Ok (), s') ∧ view s' = t') ∧
    (∀ e, Spec.ebUpdateAt (view s) i.val = .error e →
      ∃ (e' : E) (s' : S), inst.update_effective_balance s i = ok (.Err e', s'))

end EpochProofs
