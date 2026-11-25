import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Spec.PresetCfg
import EpochProofs.Generated

/-!
# The contracts of the epoch tail writes

The writes after the single-pass loop in `single_pass.rs` are generic over small traits. Aeneas
translates the generic code, but not the implementations over the milhouse lists. The theorems
take one contract for each trait as a hypothesis. This file is the only statement the proofs trust
about these writes.

`DepositWritesMatchSpec` says what `StateDeposits` in `single_pass.rs` does, in spec terms:

- `write_queue` sets the pending deposits to the deposits from the given index on, followed by
  the postponed deposits, and sets `deposit_balance_to_consume`. It succeeds when the index is at
  most the queue length.
- `validator_index` returns the index of the first validator with the deposit pubkey. It changes
  no field of the state.
- `balance` and `set_balance` read and write one balance. A read out of range fails.
- `is_valid_signature` is the spec `is_valid_deposit_signature`.
- `add_validator` is the spec `add_validator_to_registry` and returns the new index, below
  `VALIDATOR_REGISTRY_LIMIT = 2^40` validators (the milhouse list fails at the limit, the spec has
  no limit). It fails when the spec fails. Without the limit the contract was false for every
  implementation with a deposit: each call returns a `Usize` index one larger than the last, and
  the contract holds at every state it returns.
- `update_effective_balance` is the effective balance update of one validator. It fails when the
  spec fails.

`BuilderPaymentWritesMatchSpec` says what `StateBuilderPayments` does: `payments` reads the builder
pending payments, `push_withdrawal` appends a builder pending withdrawal and never fails (the list
is a `ProgressiveList` with no limit), and `set_payments` writes the payments when their number
is unchanged (the field is a `Vector`).

`EffectiveBalanceWritesMatchSpec` says what `StateEffectiveBalances` does: the effective balance
update of one validator, which fails when the spec fails.

`PtcWindowWritesMatchSpec` says what `PtcWindowWrites` does: `pop_front` drops entries from the
front when there are enough, `push` appends an item of the right size while the list is below its
limit, and `commit` writes the list back when it has the length of the window.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The Rust trait `DepositWrites`. -/
abbrev LhDepositWrites (S D E : Type) := per_epoch_processing.deposit_writes.DepositWrites S D E

/-- Trusted: what the `DepositWrites` implementation in `single_pass.rs` does. `toSpec` gives the
spec state that an implementation value holds, `depositToSpec` the spec deposit of a deposit, and
`postOf` the postponed deposits that the value holds. -/
structure DepositWritesMatchSpec [EpochProofs.Spec.CurrentPreset] {S D E : Type}
    (implementation : LhDepositWrites S D E) (oracle : Spec.Oracle)
    (toSpec : S → Spec.BeaconState) (depositToSpec : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) : Prop where
  write_queue : ∀ (s : S) (next : Usize) (dbtc : U64),
    next.val ≤ (toSpec s).pending_deposits.length →
    ∃ s', implementation.write_queue s next dbtc = ok (.Ok (), s') ∧
      toSpec s' = { toSpec s with
        pending_deposits := (toSpec s).pending_deposits.drop next.val ++ postOf s
        deposit_balance_to_consume := dbtc.val }
  validator_index : ∀ (s : S) (d : D), ∃ r s', implementation.validator_index s d = ok (.Ok r, s') ∧
    toSpec s' = toSpec s ∧
    r.map (·.val) = (if (depositToSpec d).pubkey ∈ (toSpec s).validators.map (·.pubkey) then
      some (((toSpec s).validators.map (·.pubkey)).idxOf (depositToSpec d).pubkey) else none)
  amount : ∀ (s : S) (d : D), ∃ a : U64, implementation.amount s d = ok a ∧ a.val =
    (depositToSpec d).amount
  balance : ∀ (s : S) (i : Usize),
    (∃ b : U64, implementation.balance s i = ok (.Ok b) ∧ (toSpec s).balances[i.val]? = some b.val)
      ∨
    ((toSpec s).balances[i.val]? = none ∧ ∃ e, implementation.balance s i = ok (.Err e))
  set_balance : ∀ (s : S) (i : Usize) (b : U64), i.val < (toSpec s).balances.length →
    ∃ s', implementation.set_balance s i b = ok (.Ok (), s') ∧
      toSpec s' = { toSpec s with balances := (toSpec s).balances.set i.val b.val }
  is_valid_signature : ∀ (s : S) (d : D), implementation.is_valid_signature s d =
    ok (Spec.is_valid_deposit_signature Spec.P oracle (depositToSpec d).pubkey
      (depositToSpec d).withdrawal_credentials (depositToSpec d).amount (depositToSpec d).signature)
  add_validator : ∀ (s : S) (d : D),
    ((toSpec s).validators.length < 2 ^ 40 →
      ∀ t', Spec.add_validator_to_registry Spec.P (toSpec s) (depositToSpec d).pubkey
        (depositToSpec d).withdrawal_credentials (depositToSpec d).amount = .ok t' →
        ∃ (i : Usize) (s' : S), implementation.add_validator s d = ok (.Ok i, s') ∧ toSpec s' = t' ∧
          i.val = (toSpec s).validators.length) ∧
    (∀ e, Spec.add_validator_to_registry Spec.P (toSpec s) (depositToSpec d).pubkey
        (depositToSpec d).withdrawal_credentials (depositToSpec d).amount = .error e →
      ∃ (e' : E) (s' : S), implementation.add_validator s d = ok (.Err e', s'))
  update_effective_balance : ∀ (s : S) (i : Usize),
    (∀ t', Spec.ebUpdateAt (toSpec s) i.val = .ok t' →
      ∃ s', implementation.update_effective_balance s i = ok (.Ok (), s') ∧ toSpec s' = t') ∧
    (∀ e, Spec.ebUpdateAt (toSpec s) i.val = .error e →
      ∃ (e' : E) (s' : S), implementation.update_effective_balance s i = ok (.Err e', s'))

/-- The Rust trait `BuilderPaymentWrites`. -/
abbrev LhPaymentWrites (S E : Type) := per_epoch_processing.list_writes.BuilderPaymentWrites S E

/-- Trusted: what the `BuilderPaymentWrites` implementation in `single_pass.rs` does. `wview` and
`pview` give the builder pending withdrawals and payments that an implementation value holds. -/
structure BuilderPaymentWritesMatchSpec {S E : Type} (implementation : LhPaymentWrites S E)
    (wview : S → List types.builder.builder_pending_withdrawal.BuilderPendingWithdrawal)
    (pview : S → List types.builder.builder_pending_payment.BuilderPendingPayment) : Prop where
  payments : ∀ (s : S), ∃ v : alloc.vec.Vec types.builder.builder_pending_payment.BuilderPendingPayment,
    implementation.payments s = ok (.Ok v) ∧ v.val = pview s
  push_withdrawal : ∀ (s : S) (w : types.builder.builder_pending_withdrawal.BuilderPendingWithdrawal),
    ∃ s', implementation.push_withdrawal s w = ok (.Ok (), s') ∧ wview s' = wview s ++ [w] ∧
      pview s' = pview s
  set_payments : ∀ (s : S)
    (v : alloc.vec.Vec types.builder.builder_pending_payment.BuilderPendingPayment),
    v.val.length = (pview s).length →
    ∃ s', implementation.set_payments s v = ok (.Ok (), s') ∧ pview s' = v.val ∧ wview s' = wview s

/-- The Rust trait `WindowWrites`. -/
abbrev LhWindowWrites (W T E : Type) := per_epoch_processing.list_writes.WindowWrites W T E

/-- Trusted: what a `WindowWrites` implementation in `single_pass.rs` does. `toSpec` gives the list
that a value holds, `committed` the window it wrote back to the state, `itemToSpec` the entry of an
item, `itemOk` the items that fit an entry, and `N` the window length. -/
structure PtcWindowWritesMatchSpec {W T E α : Type} (implementation : LhWindowWrites W T E)
    (toSpec : W → List α)
    (committed : W → List α) (itemToSpec : T → α) (itemOk : T → Prop) (N : Nat) : Prop where
  pop_front : ∀ (w : W) (n : Usize), n.val ≤ (toSpec w).length →
    ∃ w', implementation.pop_front w n = ok (.Ok (), w') ∧ toSpec w' = (toSpec w).drop n.val
  push : ∀ (w : W) (t : T), itemOk t → (toSpec w).length < N →
    ∃ w', implementation.push w t = ok (.Ok (), w') ∧ toSpec w' = toSpec w ++ [itemToSpec t]
  commit : ∀ (w : W), (toSpec w).length = N →
    ∃ w', implementation.commit w = ok (.Ok (), w') ∧ committed w' = toSpec w

/-- The Rust trait `EffectiveBalanceWrites`. -/
abbrev LhEffectiveBalanceWrites (S E : Type) :=
  per_epoch_processing.list_writes.EffectiveBalanceWrites S E

/-- Trusted: what the `EffectiveBalanceWrites` implementation in `single_pass.rs` does. -/
structure EffectiveBalanceWritesMatchSpec [EpochProofs.Spec.CurrentPreset] {S E : Type}
    (implementation : LhEffectiveBalanceWrites S E)
    (toSpec : S → Spec.BeaconState) : Prop where
  update_effective_balance : ∀ (s : S) (i : Usize),
    (∀ t', Spec.ebUpdateAt (toSpec s) i.val = .ok t' →
      ∃ s', implementation.update_effective_balance s i = ok (.Ok (), s') ∧ toSpec s' = t') ∧
    (∀ e, Spec.ebUpdateAt (toSpec s) i.val = .error e →
      ∃ (e' : E) (s' : S), implementation.update_effective_balance s i = ok (.Err e', s'))

end EpochProofs
