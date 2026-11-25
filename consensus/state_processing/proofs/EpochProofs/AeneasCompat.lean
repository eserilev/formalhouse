import Aeneas

/-!
# Facts about the Aeneas library

Aeneas no longer has these lemmas. `Result` is not an inductive type in Lean, so `rfl` does not
compute on it. `CacheProofs.AeneasCompat` has the same lemmas in the Aeneas namespaces. The names
here are in `EpochProofs`, so a file can import both.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Aeneas.Std.Result

/-- If `m` meets the postcondition `p`, then `m` returns a value that satisfies `p`. -/
theorem spec_imp_exists {α : Type _} {m : Result α} {p : α → Prop} (h : spec m p) :
    ∃ r, m = ok r ∧ p r := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by simp)
  | div => exact absurd h (by simp)

/-- The converse of `spec_imp_exists`. -/
theorem exists_imp_spec {α : Type _} {m : Result α} {p : α → Prop}
    (h : ∃ y, m = ok y ∧ p y) : spec m p := by
  obtain ⟨y, rfl, hp⟩ := h
  exact (spec_ok y).mpr hp

/-- The Rust `?` operator passes an error on without a change, if the error types are equal. -/
theorem from_residual_same {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame E) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `deref` of a vector keeps the elements. -/
theorem vec_deref_val {α : Type _} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp only [alloc.vec.Vec.deref, Slice.from_val]

/-- `do` pushes the code after `let x ← if c then ok a else ok b` into the two branches. This
gives the code `F` after the `if` for one value `e`. -/
theorem exists_ite_tail {α β : Type _} {c : Prop} [Decidable c] {a b : α} {F : α → Result β}
    {x : Result β} {R : β → Prop} (hx : x = F a)
    (h : ∀ e, e = (if c then a else b) → ∃ y, F e = ok y ∧ R y) :
    ∃ y, (if c then x else F b) = ok y ∧ R y := by
  subst hx
  by_cases hc : c
  · simpa only [hc, ite_true] using h a (by simp only [hc, ite_true])
  · simpa only [hc, ite_false] using h b (by simp only [hc, ite_false])

/-- `exists_ite_tail` for a postcondition. -/
theorem spec_ite_tail {α β : Type _} {c : Prop} [Decidable c] {a b : α} {F : α → Result β}
    {x : Result β} {p : β → Prop} (hx : x = F a)
    (h : ∀ e, e = (if c then a else b) → spec (F e) p) :
    spec (if c then x else F b) p := by
  subst hx
  by_cases hc : c
  · simpa only [hc, ite_true] using h a (by simp only [hc, ite_true])
  · simpa only [hc, ite_false] using h b (by simp only [hc, ite_false])

/-- Computes a `Result` program that only binds known results, then closes `ok x = ok ?y`. -/
syntax "ok_rfl" : tactic

macro_rules
  | `(tactic| ok_rfl) => `(tactic| (
      try simp only [bind_tc_ok, Aeneas.Std.bind_ok, lift, uncurry_apply_pair,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, if_true, if_false, reduceIte, Bool.false_eq_true]
      try rfl))

end EpochProofs
