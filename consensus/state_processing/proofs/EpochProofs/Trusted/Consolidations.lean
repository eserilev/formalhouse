import EpochProofs.Equiv.PendingConsolidations
import EpochProofs.Sanity.ConsolidationTable

/-!
# The contracts of the pending consolidations code

`process_on_table` in `pending_consolidations.rs` is generic over the `ConsolidationState`
trait. Aeneas translates it, but not `StateConsolidations` in `single_pass.rs`, which reads and
writes the milhouse lists. `ConsolidationAccessMatchesSpec` says what each trait method does, in
spec terms:

- `next_epoch` is `get_current_epoch(state) + 1`, and fails when the spec addition fails.
- `pending` returns the source and target index of each pending consolidation, in order.
- `local_validator` returns the table row of a validator: whether it exists, whether it is
  slashed, its withdrawable epoch and its effective balance. Past the registry, it returns the
  row of a missing validator.
- `balance` returns the balance of a validator, or 0 past the registry.
- `set_balance` sets one balance, and does nothing past the registry.
- `pop_pending` drops the first `n` pending consolidations when there are at least `n`.

`IteratesLikeBTreeSet` says what `get_validators_in_consolidations` in `single_pass.rs` gives: the
`BTreeSet` of the source and target indices, iterated. A Rust `BTreeSet` iterates its members in
increasing order, each once. The `as usize` cast keeps the value, because `usize` has 64 bits.

These two statements are the only facts the proofs trust about this code.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The Rust trait `ConsolidationState`. -/
abbrev LhConsolidationState (S E : Type) :=
  per_epoch_processing.pending_consolidations.ConsolidationState S E

/-- The Rust `PendingPair`: the source and the target of a pending consolidation. -/
abbrev LhPendingPair := per_epoch_processing.pending_consolidations.PendingPair

/-- The spec next epoch of a state. -/
def specNextEpoch (p : Spec.Preset) (state : Spec.BeaconState) : Spec.SpecM Nat := do
  Spec.uint64Add (← Spec.get_current_epoch p state) 1

/-- The source and target index of each pending consolidation. -/
def pendingPairs (state : Spec.BeaconState) : List (Nat × Nat) :=
  state.pending_consolidations.map fun c => (c.source_index, c.target_index)

/-- Trusted: what the `ConsolidationState` implementation in `single_pass.rs` does. `toSpec` gives
the spec state that an implementation value holds. -/
structure ConsolidationAccessMatchesSpec {S E : Type} (implementation : LhConsolidationState S E)
    (p : Spec.Preset) (toSpec : S → Spec.BeaconState) : Prop where
  next_epoch : ∀ (s : S),
    (∀ n, specNextEpoch p (toSpec s) = .ok n →
      ∃ v : U64, implementation.next_epoch s = ok (.Ok v) ∧ v.val = n) ∧
    (∀ e, specNextEpoch p (toSpec s) = .error e → ∃ e', implementation.next_epoch s = ok (.Err e'))
  pending : ∀ (s : S), ∃ v : alloc.vec.Vec LhPendingPair, implementation.pending s = ok (.Ok v) ∧
    v.val.map (fun q => (q.source.val, q.target.val)) = pendingPairs (toSpec s)
  local_validator : ∀ (s : S) (i : Usize), ∃ lv, implementation.local_validator s i = ok lv ∧
    consolidationValidatorToSpec lv = Spec.localRow (toSpec s).validators i.val
  balance : ∀ (s : S) (i : Usize), ∃ b : U64, implementation.balance s i = ok b ∧
    b.val = ((toSpec s).balances[i.val]?).getD 0
  set_balance : ∀ (s : S) (i : Usize) (b : U64), ∃ s', implementation.set_balance s i b = ok s' ∧
    toSpec s' = { toSpec s with balances :=
      if i.val < (toSpec s).balances.length then (toSpec s).balances.set i.val b.val
      else (toSpec s).balances }
  pop_pending : ∀ (s : S) (n : Usize), n.val ≤ (toSpec s).pending_consolidations.length →
    ∃ s', implementation.pop_pending s n = ok (.Ok (), s') ∧
      toSpec s' = { toSpec s with
        pending_consolidations := (toSpec s).pending_consolidations.drop n.val }

/-- Trusted: `it` is the iteration of a Rust `BTreeSet` after inserting each of `inserted`. -/
def IteratesLikeBTreeSet (inserted : List Nat) (it : List Nat) : Prop :=
  it.Pairwise (· < ·) ∧ ∀ x, x ∈ it ↔ x ∈ inserted

end EpochProofs
