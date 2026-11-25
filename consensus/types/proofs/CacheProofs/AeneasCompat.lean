import Aeneas
import Mathlib

/-!
# Facts about the Aeneas library

Aeneas no longer has these lemmas. `Result` is not an inductive type in Lean, so `rfl` does not
compute on it.
-/

namespace Aeneas.Std.WP

open Aeneas.Std.Result

/-- If `m` meets the postcondition `p`, then `m` returns a value that satisfies `p`. -/
theorem spec_imp_exists {α : Type _} {m : Result α} {p : α → Prop} (h : spec m p) :
    ∃ r, m = ok r ∧ p r := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by simp)
  | div => exact absurd h (by simp)

end Aeneas.Std.WP

namespace Aeneas.Std

open Aeneas.Std.Result

/-- The Rust `?` operator passes an error on without a change, if the error types are equal. -/
theorem from_residual_same {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame E) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Aeneas.Std


/-! ## Integer square root: Lean has these lemmas, but they are private -/

namespace CacheProofs.IntegerSqrt

/-- Each guess of the square root loop ends with a root whose square is at most `n`. -/
theorem iter_sq_le (n guess : Nat) : Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n := by
  unfold Nat.sqrt.iter
  dsimp only
  split
  · exact iter_sq_le n _
  · rename_i h
    apply Nat.mul_le_of_le_div
    omega
termination_by guess

/-- If the first guess is large enough, the square of the next number after the root is more than `n`. -/
theorem lt_iter_succ_sq (n guess : Nat) (hn : n < (guess + 1) * (guess + 1)) :
    n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) := by
  unfold Nat.sqrt.iter
  dsimp only
  split
  · rename_i h
    apply lt_iter_succ_sq
    have hg : 0 < guess := Nat.lt_of_le_of_lt (Nat.zero_le _) h
    have h1 : n < guess * (n / guess + 1) := Nat.lt_mul_div_succ n hg
    have h2 : guess + n / guess + 1 ≤ 2 * ((guess + n / guess) / 2 + 1) := by omega
    generalize (guess + n / guess) / 2 + 1 = m at *
    generalize n / guess = q at *
    zify at *
    nlinarith [sq_nonneg ((guess : Int) - (q + 1))]
  · exact hn
termination_by guess

end CacheProofs.IntegerSqrt
