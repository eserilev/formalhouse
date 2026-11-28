import EthLib.Consensus.Transition.Basic
import EpochProofs.SpecFacts.SinglePass

/-!
# Comparison of an EthLib result and a reference result

EthLib functions return `Except` with an EthLib error. Reference functions return `SpecM`. The two
never have the same error values, so the comparison ignores the error.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

/-- Either both computations return, and their values match, or both fail. -/
inductive SameOutcome {ε α β : Type} (Match : α → β → Prop) : Except ε α → Spec.SpecM β → Prop
  | returned {a : α} {b : β} (h : Match a b) : SameOutcome Match (.ok a) (.ok b)
  | failed {e : ε} {e' : Spec.SpecError} : SameOutcome Match (.error e) (.error e')

/-- An EthLib result, read as a reference result. `read` maps the value. The error that the
reference result holds has no meaning, because `SameResultOrBothFail` does not compare errors. -/
def toSpecResult {ε α β : Type} (read : α → β) : Except ε α → Spec.SpecM β
  | .ok a => .ok (read a)
  | .error _ => .error .assertionFailed

namespace SameOutcome

variable {ε α β γ δ : Type}

/-- If the matching relation is a map, `SameOutcome` gives `SameResultOrBothFail`. -/
theorem sameResultOrBothFail {read : α → β} {x : Except ε α} {y : Spec.SpecM β}
    (h : SameOutcome (fun a b => b = read a) x y) :
    Spec.SameResultOrBothFail y (toSpecResult read x) := by
  intro v
  cases h with
  | returned h => simp [toSpecResult, h]
  | failed => simp [toSpecResult]

theorem mono {M N : α → β → Prop} {x : Except ε α} {y : Spec.SpecM β}
    (h : SameOutcome M x y) (hMN : ∀ a b, M a b → N a b) : SameOutcome N x y := by
  cases h with
  | returned h => exact .returned (hMN _ _ h)
  | failed => exact .failed

/-- Two computations have the same outcome if their first parts have the same outcome, and their
second parts have the same outcome on each pair of matching values. -/
theorem bind {M : α → β → Prop} {N : γ → δ → Prop} {x : Except ε α} {y : Spec.SpecM β}
    {f : α → Except ε γ} {g : β → Spec.SpecM δ} (h : SameOutcome M x y)
    (hfg : ∀ a b, M a b → x = .ok a → SameOutcome N (f a) (g b)) :
    SameOutcome N (x >>= f) (y >>= g) := by
  cases h with
  | returned h => exact hfg _ _ h rfl
  | failed => exact .failed

/-- A last step of EthLib that only builds the result. -/
theorem bind_pure {M : α → β → Prop} {N : γ → β → Prop} {x : Except ε α} {y : Spec.SpecM β}
    {f : α → γ} (h : SameOutcome M x y) (hf : ∀ a b, M a b → N (f a) b) :
    SameOutcome N (x >>= fun a => Pure.pure (f a)) y := by
  cases h with
  | returned h => exact .returned (hf _ _ h)
  | failed => exact .failed

/-- If EthLib returns, then the reference returns a matching value. -/
theorem returns {M : α → β → Prop} {x : Except ε α} {y : Spec.SpecM β} (h : SameOutcome M x y)
    {a : α} (ha : x = .ok a) : ∃ b, y = .ok b ∧ M a b := by
  subst ha
  cases h with
  | returned h => exact ⟨_, rfl, h⟩

theorem pure {M : α → β → Prop} {a : α} {b : β} (h : M a b) :
    SameOutcome M (Pure.pure a : Except ε α) (Pure.pure b) := .returned h

/-- `if` on two conditions that hold together. -/
theorem ite {M : α → β → Prop} {c d : Prop} [Decidable c] [Decidable d] {x x' : Except ε α}
    {y y' : Spec.SpecM β} (hcd : c ↔ d) (hthen : c → SameOutcome M x y)
    (helse : ¬c → SameOutcome M x' y') :
    SameOutcome M (if c then x else x') (if d then y else y') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left (hcd.mp h)]
    exact hthen h
  · rw [ite_eq_right h, ite_eq_right (fun hd => h (hcd.mpr hd))]
    exact helse h

/-- A change of the error type does not change the outcome. -/
theorem mapError {ε' : Type} {M : α → β → Prop} {x : Except ε α} {y : Spec.SpecM β} (f : ε → ε')
    (h : SameOutcome M x y) : SameOutcome M (x.mapError f) y := by
  cases h with
  | returned h => exact .returned h
  | failed => exact .failed

theorem liftArith {M : α → β → Prop} {x : Except ArithError α} {y : Spec.SpecM β}
    (h : SameOutcome M x y) : SameOutcome M (_root_.EthLib.Consensus.liftArith x) y := mapError _ h

theorem liftAccessor {M : α → β → Prop} {x : Except AccessorError α} {y : Spec.SpecM β}
    (h : SameOutcome M x y) : SameOutcome M (_root_.EthLib.Consensus.liftAccessor x) y :=
  mapError _ h

end SameOutcome

/-- The reference number is the value of the EthLib `UInt64`. -/
abbrev SameNumber (a : UInt64) (n : Nat) : Prop := n = a.toNat

/-! ## Checked `uint64` arithmetic -/

theorem addChecked_same (a b : UInt64) :
    SameOutcome SameNumber (addChecked a b) (Spec.uint64Add a.toNat b.toNat) := by
  unfold addChecked Spec.uint64Add Spec.UINT64_SIZE
  split
  · rename_i h
    exact .returned (by rw [SameNumber, UInt64.toNat_add, Nat.mod_eq_of_lt h])
  · exact .failed

theorem subChecked_same (a b : UInt64) :
    SameOutcome SameNumber (subChecked a b) (Spec.uint64Sub a.toNat b.toNat) := by
  unfold subChecked Spec.uint64Sub
  refine .ite UInt64.le_iff_toNat_le (fun h => .returned ?_) (fun _ => .failed)
  rw [SameNumber, UInt64.toNat_sub_of_le _ _ h]

theorem mulChecked_same (a b : UInt64) :
    SameOutcome SameNumber (mulChecked a b) (Spec.uint64Mul a.toNat b.toNat) := by
  unfold mulChecked Spec.uint64Mul Spec.UINT64_SIZE
  split
  · rename_i h
    exact .returned (by rw [SameNumber, UInt64.toNat_mul, Nat.mod_eq_of_lt h])
  · exact .failed

theorem divChecked_same (a b : UInt64) :
    SameOutcome SameNumber (divChecked a b) (Spec.uint64Div a.toNat b.toNat) := by
  unfold divChecked Spec.uint64Div
  exact .ite (by rw [← UInt64.toNat_inj]; rfl) (fun _ => .failed)
    (fun _ => .returned (UInt64.toNat_div a b).symm)

theorem uint64Div_eq {a b : UInt64} (hb : b ≠ 0) :
    Spec.uint64Div a.toNat b.toNat = .ok (a / b).toNat := by
  have hb' : b.toNat ≠ 0 := fun h => hb (UInt64.toNat_inj.mp h)
  simp [Spec.uint64Div, hb', UInt64.toNat_div, Pure.pure, Except.pure]

theorem uint64Mod_eq {a b : UInt64} (hb : b ≠ 0) :
    Spec.uint64Mod a.toNat b.toNat = .ok (a % b).toNat := by
  have hb' : b.toNat ≠ 0 := fun h => hb (UInt64.toNat_inj.mp h)
  simp [Spec.uint64Mod, hb', UInt64.toNat_mod, Pure.pure, Except.pure]

theorem uint64Div_nat {a b : Nat} (hb : b ≠ 0) : Spec.uint64Div a b = .ok (a / b) :=
  ite_eq_right hb

theorem uint64Add_fits {a b : Nat} (h : a + b < 2 ^ 64) : Spec.uint64Add a b = .ok (a + b) :=
  ite_eq_left h

theorem uint64Add_overflows {a b : Nat} (h : ¬a + b < 2 ^ 64) :
    Spec.uint64Add a b = .error .overflow :=
  ite_eq_right h

theorem uint64Mul_fits {a b : Nat} (h : a * b < 2 ^ 64) : Spec.uint64Mul a b = .ok (a * b) :=
  ite_eq_left h

theorem uint64Mul_overflows {a b : Nat} (h : ¬a * b < 2 ^ 64) :
    Spec.uint64Mul a b = .error .overflow :=
  ite_eq_right h

theorem toNat_of_addChecked {a b c : UInt64}
    (h : _root_.EthLib.Consensus.liftArith (addChecked a b) = .ok c) :
    c.toNat = a.toNat + b.toNat := by
  obtain ⟨n, hn, rfl⟩ := (addChecked_same a b).liftArith.returns h
  by_cases hfits : a.toNat + b.toNat < 2 ^ 64
  · rw [uint64Add_fits hfits] at hn
    exact (Except.ok.inj hn).symm
  · rw [uint64Add_overflows hfits] at hn
    cases hn

theorem toNat_of_mulChecked {a b c : UInt64}
    (h : _root_.EthLib.Consensus.liftArith (mulChecked a b) = .ok c) :
    c.toNat = a.toNat * b.toNat := by
  obtain ⟨n, hn, rfl⟩ := (mulChecked_same a b).liftArith.returns h
  by_cases hfits : a.toNat * b.toNat < 2 ^ 64
  · rw [uint64Mul_fits hfits] at hn
    exact (Except.ok.inj hn).symm
  · rw [uint64Mul_overflows hfits] at hn
    cases hn

theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  rw [UInt64.min_def]
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem liftArith_bind {α β : Type} (x : Except ArithError α) (f : α → Except ArithError β) :
    _root_.EthLib.Consensus.liftArith (x >>= f) =
      _root_.EthLib.Consensus.liftArith x >>= fun a => _root_.EthLib.Consensus.liftArith (f a) := by
  cases x <;> rfl

theorem liftAccessor_bind {α β : Type} (x : Except AccessorError α)
    (f : α → Except AccessorError β) :
    _root_.EthLib.Consensus.liftAccessor (x >>= f) =
      _root_.EthLib.Consensus.liftAccessor x >>= fun a =>
        _root_.EthLib.Consensus.liftAccessor (f a) := by
  cases x <;> rfl

theorem pure_eq_ok {ε α : Type} (a : α) : (Pure.pure a : Except ε α) = .ok a := rfl

end EpochProofs.EthLib
