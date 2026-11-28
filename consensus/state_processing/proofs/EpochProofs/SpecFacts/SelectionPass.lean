import EpochProofs.Spec.Committees

/-!
# One pass of `compute_balance_weighted_selection`

`selectionPass` is the body of the `while` loop. `selection_loop_succ` unfolds one pass of the
loop. The Lighthouse proof follows the loop one pass at a time.
-/

namespace EpochProofs.Spec

/-- One pass of the selection loop: the accepted candidate, if any, and the new
`random_bytes`. -/
def selectionPass (p : Preset) (o : Oracle) (indices : List ValidatorIndex) (seed : Bytes32)
    (shuffle_indices : Bool) (total : Uint64) (effective_balances : List Gwei) (i : Uint64)
    (random_bytes : Bytes32) : SpecM (Option ValidatorIndex × Bytes32) := do
  let MAX_RANDOM_VALUE := 2 ^ 16 - 1
  let offset ← uint64Mul (← uint64Mod i 16) 2
  let random_bytes :=
    if offset == 0 then o.hash (seed.toList ++ uint_to_bytes 8 (i / 16)) else random_bytes
  let mut next_index ← uint64Mod i total
  if shuffle_indices then
    next_index ← compute_shuffled_index p o next_index total seed
  let weight ← uint64Mul (← listGet effective_balances next_index) MAX_RANDOM_VALUE
  let random_value ← bytes_to_uint64 ((random_bytes.toList.drop offset).take 2)
  let threshold ← uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA random_value
  if weight ≥ threshold then pure (some (← listGet indices next_index), random_bytes)
  else pure (none, random_bytes)

theorem selection_loop_succ (p : Preset) (o : Oracle) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Uint64) (shuffle_indices : Bool) (total : Uint64)
    (effective_balances : List Gwei) (fuel : Nat) (selected : List ValidatorIndex) (i : Uint64)
    (random_bytes : Bytes32) :
    compute_balance_weighted_selection_loop p o indices seed size shuffle_indices total
        effective_balances (fuel + 1) selected i random_bytes =
      if selected.length < size then do
        let r ← selectionPass p o indices seed shuffle_indices total effective_balances i
          random_bytes
        let i ← uint64Add i 1
        compute_balance_weighted_selection_loop p o indices seed size shuffle_indices total
          effective_balances fuel (selected ++ r.1.toList) i r.2
      else pure selected := by
  simp only [compute_balance_weighted_selection_loop, selectionPass]
  split
  · cases shuffle_indices <;>
      simp only [Bind.bind, Except.bind, pure, Except.pure, if_true, Bool.false_eq_true,
        if_false] <;>
      (repeat' split) <;> simp_all
  · rfl
end EpochProofs.Spec
