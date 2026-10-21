import EpochProofs.Equiv.BalanceWeightedSelection

/-!
# The selection fails with no candidates, in Lighthouse and in the spec

`compute_balance_weighted_selection_spec` gives "spec ok → Rust `Ok`, same value". With an
empty candidate list the spec fails its `assert total > 0`. This file shows that Lighthouse
fails there too, with `EmptyIndices`. A proposer lookahead with every candidate slashed (F4)
takes this path in both.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem compute_balance_weighted_selection_empty {H B : Type} (inst : ShuffleHashInst H)
    (ebi : EBInst B) (balances : B) (indices : Slice Usize) (seed : Array U8 32#usize)
    (size : Usize) (shuffle : Bool) (R : U8) (maxeb : U64) (hn : indices.val.length = 0) :
    types.state.balance_weighted_selection.compute_balance_weighted_selection inst ebi balances
      indices seed size shuffle R maxeb =
      ok (core.result.Result.Err
        types.state.balance_weighted_selection.SelectionError.EmptyIndices) := by
  unfold types.state.balance_weighted_selection.compute_balance_weighted_selection
  have : indices.length = 0 := by simpa [Slice.length] using hn
  simp [this]

theorem spec_compute_balance_weighted_selection_empty (p : Spec.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (seed : Spec.Bytes32) (size : Spec.Uint64) (shuffle : Bool) :
    Spec.compute_balance_weighted_selection p o state [] seed size shuffle =
      .error .assertionFailed := by
  simp [Spec.compute_balance_weighted_selection, throw, throwThe, MonadExceptOf.throw,
    Bind.bind, Except.bind]

end EpochProofs
