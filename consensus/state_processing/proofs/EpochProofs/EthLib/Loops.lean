import EpochProofs.EthLib.Results

/-!
# Loops of EthLib and loops of the reference

EthLib folds a list. The reference runs a `for` loop. The theorems here compare the two.
-/

namespace EpochProofs.EthLib

/-- A fold over the first parts of a list of pairs, and a `for` loop over the second parts. `R i`
relates the values after `i` steps. -/
theorem SameOutcome.forIn_pairs {ε α β κ κ' : Type} {f : α → κ → Except ε α}
    {body : κ' → β → Spec.SpecM (ForInStep β)} {R : Nat → α → β → Prop} :
    ∀ (pairs : List (κ × κ')) (k : Nat) {a : α} {b : β}, R k a b →
      (∀ i a b x y, pairs[i]? = some (x, y) → R (k + i) a b →
        SameOutcome (fun a' r => ∃ b', r = .yield b' ∧ R (k + i + 1) a' b') (f a x) (body y b)) →
      SameOutcome (R (k + pairs.length)) ((pairs.map (·.1)).foldlM f a)
        (forIn (pairs.map (·.2)) b body)
  | [], _, _, _, h, _ => .returned h
  | (x, y) :: pairs, k, a, b, h, hstep => by
    rw [List.map_cons, List.map_cons, List.foldlM_cons, List.forIn_cons]
    refine .bind (hstep 0 a b x y rfl h) ?_
    rintro a' _ ⟨b', rfl, h'⟩ -
    have := SameOutcome.forIn_pairs pairs (k + 1) h' fun i a b x y hi hR => by
      have hs := hstep (i + 1) a b x y (by simpa using hi)
      rw [← Nat.add_assoc, Nat.add_right_comm] at hs
      exact hs hR
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

/-- A fold and a `for` loop over the same positions. -/
theorem SameOutcome.forIn_range {ε α β : Type} {f : α → Nat → Except ε α}
    {body : Nat → β → Spec.SpecM (ForInStep β)} {R : Nat → α → β → Prop} (n : Nat) {a : α} {b : β}
    (h : R 0 a b)
    (hstep : ∀ i a b, i < n → R i a b →
      SameOutcome (fun a' r => ∃ b', r = .yield b' ∧ R (i + 1) a' b') (f a i) (body i b)) :
    SameOutcome (R n) ((List.range n).foldlM f a) (forIn (List.range n) b body) := by
  have := SameOutcome.forIn_pairs (f := f) (body := body) (R := R)
    ((List.range n).map fun i => (i, i)) 0 h (by
      intro i a b x y hi hR
      simp only [List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq] at hi
      obtain ⟨j, hj, rfl, rfl⟩ := hi
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      simp only [List.getElem_range, Nat.zero_add] at hR ⊢
      exact hstep i a b (by simpa using hlt) hR)
  simpa [Function.comp_def] using this

/-- A fold over the positions of a list, and a `for` loop over its elements and positions. -/
theorem SameOutcome.forIn_zipIdx {ε α β γ : Type} {f : α → Nat → Except ε α}
    {body : γ × Nat → β → Spec.SpecM (ForInStep β)} {R : Nat → α → β → Prop} (l : List γ) {a : α}
    {b : β} (h : R 0 a b)
    (hstep : ∀ i a b x, l[i]? = some x → R i a b →
      SameOutcome (fun a' r => ∃ b', r = .yield b' ∧ R (i + 1) a' b') (f a i) (body (x, i) b)) :
    SameOutcome (R l.length) ((List.range l.length).foldlM f a) (forIn l.zipIdx b body) := by
  have := SameOutcome.forIn_pairs (f := f) (body := body) (R := R)
    (l.zipIdx.map fun p => (p.2, p)) 0 h (by
      rintro i a b x ⟨y, j⟩ hi hR
      simp only [List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq] at hi
      obtain ⟨p, hp, rfl, rfl⟩ := hi
      simp only [List.getElem?_zipIdx, Option.map_eq_some_iff, Prod.mk.injEq, Nat.zero_add] at hp
      obtain ⟨_, hp, rfl, rfl⟩ := hp
      simp only [Nat.zero_add] at hR ⊢
      exact hstep i a b _ hp hR)
  simpa [Function.comp_def, List.zipIdx_map_snd, List.range_eq_range'] using this

end EpochProofs.EthLib
