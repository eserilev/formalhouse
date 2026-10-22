import EpochProofs.Sanity.Invariants.LighthouseTailModel
import EpochProofs.Sanity.PendingConsolidations
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Perm
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

/-!
# The consolidation moves on a table equal the moves on the full registry

`single_pass.rs` runs `process_pending_consolidations` on a table of the validators that
consolidations reference, then writes the table balances back. `stepLoop_table` shows that the
table run is the full-registry run, seen through the table. `writeBack_table` shows that the
write-back gives the full-registry balances.

`consolidationIndices_eq_of_sorted` shows that a strictly increasing list with the members of
the referenced indices is `consolidationIndices`. This is what the `BTreeSet` in
`single_pass.rs` gives.
-/

namespace EpochProofs.Spec

/-- The table row of an index past the registry. -/
def missingRow : LocalValidator := ⟨false, false, 0, 0⟩

/-- The table row of validator `i`. -/
def localRow (vs : List Validator) (i : Nat) : LocalValidator :=
  (vs[i]?.map globalLocal).getD missingRow

/-- The table rows of the validators in `idx`. -/
def tableRows (vs : List Validator) (idx : List Nat) : List LocalValidator :=
  idx.map (localRow vs)

/-- The table balances of the validators in `idx`. A balance past the registry is 0. -/
def tableBalances (bs : List Gwei) (idx : List Nat) : List Gwei :=
  idx.map fun i => bs[i]?.getD 0

/-- Writes the table balances `tb` back to `bs`, at the indices in `idx`. A write past the end
of `bs` does nothing. -/
def writeBack (bs : List Gwei) (idx : List Nat) (tb : List Gwei) : List Gwei :=
  (idx.zip tb).foldl (fun acc p => if p.1 < acc.length then acc.set p.1 p.2 else acc) bs

theorem localExists_tableRows {vs : List Validator} {idx : List Nat} {x : Nat} (hx : x ∈ idx) :
    localExists (tableRows vs idx) (idx.idxOf x) = localExists (vs.map globalLocal) x := by
  have hlt := List.idxOf_lt_length_of_mem hx
  unfold localExists tableRows
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt,
    List.getElem?_map]
  unfold localRow
  cases h : vs[x]? <;> simp [h, missingRow, globalLocal]

theorem tableRows_getElem? {vs : List Validator} {idx : List Nat} {x : Nat} (hx : x ∈ idx) :
    (tableRows vs idx)[idx.idxOf x]? = some (localRow vs x) := by
  have hlt := List.idxOf_lt_length_of_mem hx
  unfold tableRows
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

theorem tableBalances_getElem? {bs : List Gwei} {idx : List Nat} {x : Nat} (hx : x ∈ idx) :
    (tableBalances bs idx)[idx.idxOf x]? = some (bs[x]?.getD 0) := by
  have hlt := List.idxOf_lt_length_of_mem hx
  unfold tableBalances
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

theorem tableBalances_length (bs : List Gwei) (idx : List Nat) :
    (tableBalances bs idx).length = idx.length := by
  simp [tableBalances]

theorem tableBalances_set {bs : List Gwei} {idx : List Nat} (hnd : idx.Nodup) {x : Nat}
    (hx : x ∈ idx) (hxb : x < bs.length) (v : Gwei) :
    tableBalances (bs.set x v) idx = (tableBalances bs idx).set (idx.idxOf x) v := by
  have hlt := List.idxOf_lt_length_of_mem hx
  apply List.ext_getElem
  · simp [tableBalances]
  intro k h1 h2
  have hk : k < idx.length := by simpa [tableBalances] using h1
  simp only [tableBalances, List.getElem_map, List.getElem_set]
  by_cases hkx : idx.idxOf x = k
  · subst hkx
    simp [List.getElem_idxOf hlt, hxb]
  · simp only [hkx, if_false, List.getElem_map]
    have hne : idx[k] ≠ x := by
      intro he
      apply hkx
      have : idx[idx.idxOf x]'hlt = idx[k]'hk := by rw [List.getElem_idxOf hlt, he]
      exact ((List.getElem_inj hnd).mp this)
    rw [List.getElem?_set_ne (Ne.symm hne)]

/-- Every index that the moves touch is in the table. -/
def PairsIn (idx : List Nat) (pairs : List (Nat × Nat)) : Prop :=
  ∀ p ∈ pairs, p.1 ∈ idx ∧ p.2 ∈ idx

/-- The table view of a full-registry state of the loop. -/
def toTable (idx : List Nat) (s : List Gwei × Nat) : List Gwei × Nat :=
  (tableBalances s.1 idx, s.2)

/-- `B` differs from `B0` only at indices in `idx`, and has the same length. -/
def AgreeOut (B0 B : List Gwei) (idx : List Nat) : Prop :=
  B.length = B0.length ∧ ∀ i, i ∉ idx → B[i]? = B0[i]?

theorem consolidationStep_table {vs : List Validator} {idx : List Nat} (hnd : idx.Nodup)
    (ne : Nat) {B : List Gwei} (hB : B.length = vs.length) (n : Nat) {s t : Nat}
    (hs : s ∈ idx) (ht : t ∈ idx) :
    consolidationStep (tableRows vs idx) ne (tableBalances B idx, n) (idx.idxOf s, idx.idxOf t) =
      (consolidationStep (vs.map globalLocal) ne (B, n) (s, t)).map
        fun r => (toTable idx r.1, r.2) := by
  have hrs := tableRows_getElem? (vs := vs) hs
  have hbs := tableBalances_getElem? (bs := B) hs
  have hes := localExists_tableRows (vs := vs) hs
  have het := localExists_tableRows (vs := vs) ht
  have hlts := List.idxOf_lt_length_of_mem hs
  have hltt := List.idxOf_lt_length_of_mem ht
  by_cases hsx : s < vs.length
  case neg =>
    simp [consolidationStep, hes, localExists_global, hsx, Except.map, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]
  have hrow : localRow vs s = globalLocal vs[s] := by
    simp [localRow, List.getElem?_eq_getElem hsx]
  have hsb : s < B.length := by rw [hB]; exact hsx
  by_cases hsl : vs[s].slashed = true
  · simp [consolidationStep, hes, localExists_global, hsx, listGet, hrs, hrow, hsl, globalLocal,
      Except.map, bind, Except.bind, pure, Except.pure, toTable]
  by_cases hwe : vs[s].withdrawable_epoch > ne
  · simp [consolidationStep, hes, localExists_global, hsx, listGet, hrs, hrow, hsl, hwe,
      globalLocal, Except.map, bind, Except.bind, pure, Except.pure, toTable]
  have hlen1 : (tableBalances B idx).length = idx.length := tableBalances_length _ _
  have hset1 := tableBalances_set hnd hs hsb
    (saturating_sub B[s] (min B[s] vs[s].effective_balance))
  by_cases htx : t < vs.length
  case neg =>
    simp [consolidationStep, hes, het, localExists_global, hsx, htx, listGet, listSet, hrs, hrow,
      hsl, hwe, globalLocal, decrease_balance, hbs, List.getElem?_eq_getElem hsb, hsb, hlen1,
      hlts, Except.map, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]
  have htb : t < (B.set s (saturating_sub B[s] (min B[s] vs[s].effective_balance))).length := by
    simp [hB, htx]
  have hbt := tableBalances_getElem? (bs := B.set s (saturating_sub B[s]
    (min B[s] vs[s].effective_balance))) ht
  have hlen2 : ((tableBalances B idx).set (idx.idxOf s)
      (saturating_sub B[s] (min B[s] vs[s].effective_balance))).length = idx.length := by
    simp [hlen1]
  simp only [consolidationStep, hes, het, localExists_global, hsx, htx, decide_true,
    Bool.not_true, Bool.false_eq_true, if_false, listGet, hrs, hrow, List.getElem?_map,
    List.getElem?_eq_getElem hsx, Option.map_some, globalLocal, hsl, hwe, decrease_balance,
    increase_balance, listSet, hbs, List.getElem?_eq_getElem hsb, Option.getD_some, hsb, if_true,
    hlen1, hlts, hltt, hlen2, hbt, List.getElem?_eq_getElem htb, htb, bind, Except.bind, pure,
    Except.pure, Except.map, ← hset1, tableBalances_length]
  cases uint64Add _ _ with
  | error e => rfl
  | ok v =>
    simp only [toTable, tableBalances_set hnd ht htb]

/-- An `ok` step on the full registry changes no balance, or sets the source and then the
target balance. -/
theorem consolidationStep_full_ok {vs : List Validator} (ne : Nat) {B : List Gwei} (n : Nat)
    (s t : Nat) {r} (hB : B.length = vs.length)
    (hr : consolidationStep (vs.map globalLocal) ne (B, n) (s, t) = .ok r) :
    r.1.1 = B ∨ ∃ x y, r.1.1 = (B.set s x).set t y := by
  by_cases hsx : s < vs.length
  case neg =>
    simp [consolidationStep, localExists_global, hsx, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at hr
  have hsb : s < B.length := by rw [hB]; exact hsx
  by_cases hsl : vs[s].slashed = true
  · simp [consolidationStep, localExists_global, hsx, hsl, listGet, globalLocal, bind,
      Except.bind, pure, Except.pure] at hr
    left; subst hr; rfl
  by_cases hwe : vs[s].withdrawable_epoch > ne
  · simp [consolidationStep, localExists_global, hsx, hsl, hwe, listGet, globalLocal, bind,
      Except.bind, pure, Except.pure] at hr
    left; subst hr; rfl
  by_cases htx : t < vs.length
  case neg =>
    simp [consolidationStep, localExists_global, hsx, hsl, hwe, htx, listGet, listSet,
      globalLocal, decrease_balance, hsb, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hr
  right
  have htb : t < (B.set s (saturating_sub B[s] (min B[s] vs[s].effective_balance))).length := by
    simp [hB, htx]
  revert hr
  simp only [consolidationStep, localExists_global, hsx, htx, decide_true, Bool.not_true,
    Bool.false_eq_true, if_false, listGet, List.getElem?_map, List.getElem?_eq_getElem hsx,
    Option.map_some, globalLocal, hsl, hwe, decrease_balance, increase_balance, listSet,
    List.getElem?_eq_getElem hsb, hsb, if_true, List.getElem?_eq_getElem htb, htb, bind,
    Except.bind, pure, Except.pure]
  cases uint64Add _ _ with
  | error e => intro h; cases h
  | ok v =>
    intro h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨_, _, rfl⟩

/-- An `ok` step counts at most one more consolidation. -/
theorem consolidationStep_count {vs : List LocalValidator} (ne : Nat) (st : List Gwei × Nat)
    (c : Nat × Nat) {r} (hr : consolidationStep vs ne st c = .ok r) : r.1.2 ≤ st.2 + 1 := by
  unfold consolidationStep at hr
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
  split at hr
  · simp at hr
  cases hg : listGet vs c.1 with
  | error e => rw [hg] at hr; simp at hr
  | ok v =>
    rw [hg] at hr
    simp only at hr
    split at hr
    · cases hr; simp
    split at hr
    · cases hr; simp
    cases hb : listGet st.1 c.1 with
    | error e => rw [hb] at hr; simp at hr
    | ok b =>
      rw [hb] at hr
      simp only at hr
      cases hd : decrease_balance st.1 c.1 (min b v.effective_balance) with
      | error e => rw [hd] at hr; simp at hr
      | ok d =>
        rw [hd] at hr
        simp only at hr
        split at hr
        · simp at hr
        cases hi : increase_balance d c.2 (min b v.effective_balance) with
        | error e => rw [hi] at hr; simp at hr
        | ok d2 => rw [hi] at hr; simp only [Except.ok.injEq] at hr; cases hr; simp

/-- The count after a loop is at most the start count plus the number of steps. -/
theorem stepLoop_count {vs : List LocalValidator} (ne : Nat) (pairs : List (Nat × Nat))
    (st : List Gwei × Nat) {r} (hr : stepLoop (consolidationStep vs ne) st pairs = .ok r) :
    r.1.2 ≤ st.2 + pairs.length := by
  induction pairs generalizing st with
  | nil =>
    simp only [stepLoop, pure, Except.pure, Except.ok.injEq] at hr
    subst hr; simp
  | cons p ps ih =>
    unfold stepLoop at hr
    cases hstep : consolidationStep vs ne st p with
    | error e => rw [hstep] at hr; simp [bind, Except.bind] at hr
    | ok r1 =>
      rw [hstep] at hr
      simp only [bind, Except.bind] at hr
      have h1 := consolidationStep_count ne st p hstep
      split at hr
      · simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr; simp; omega
      · have := ih r1.1 hr
        simp; omega

theorem consolidationStep_length {vs : List Validator} (ne : Nat) {B : List Gwei} (n : Nat)
    (c : Nat × Nat) {r} (hB : B.length = vs.length)
    (hr : consolidationStep (vs.map globalLocal) ne (B, n) c = .ok r) :
    r.1.1.length = B.length := by
  rcases consolidationStep_full_ok ne n c.1 c.2 hB hr with h | ⟨x, y, h⟩ <;> simp [h]

theorem consolidationStep_agreeOut {vs : List Validator} {idx : List Nat} (ne : Nat)
    {B0 B : List Gwei} (n : Nat) {s t : Nat} (hs : s ∈ idx) (ht : t ∈ idx)
    (hB : B.length = vs.length) (hag : AgreeOut B0 B idx) {r}
    (hr : consolidationStep (vs.map globalLocal) ne (B, n) (s, t) = .ok r) :
    AgreeOut B0 r.1.1 idx := by
  refine ⟨(consolidationStep_length ne n _ hB hr).trans hag.1, fun i hi => ?_⟩
  have his : s ≠ i := fun h => hi (h ▸ hs)
  have hit : t ≠ i := fun h => hi (h ▸ ht)
  rw [← hag.2 i hi]
  rcases consolidationStep_full_ok ne n s t hB hr with h | ⟨x, y, h⟩
  · rw [h]
  · rw [h, List.getElem?_set_ne hit, List.getElem?_set_ne his]

/-- The table run is the full-registry run, seen through the table. -/
theorem stepLoop_table {vs : List Validator} {idx : List Nat} (hnd : idx.Nodup) (ne : Nat)
    (pairs : List (Nat × Nat)) (hin : PairsIn idx pairs) (B : List Gwei)
    (hB : B.length = vs.length) (n : Nat) :
    stepLoop (consolidationStep (tableRows vs idx) ne) (toTable idx (B, n))
        (pairs.map fun p => (idx.idxOf p.1, idx.idxOf p.2)) =
      (stepLoop (consolidationStep (vs.map globalLocal) ne) (B, n) pairs).map
        fun r => (toTable idx r.1, r.2) := by
  induction pairs generalizing B n with
  | nil => simp [stepLoop, pure, Except.pure, Except.map]
  | cons p ps ih =>
    obtain ⟨hs, ht⟩ := hin p (List.mem_cons_self ..)
    have hin' : PairsIn idx ps := fun q hq => hin q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, stepLoop]
    rw [show toTable idx (B, n) = (tableBalances B idx, n) from rfl,
      consolidationStep_table hnd ne hB n hs ht]
    cases hr : consolidationStep (vs.map globalLocal) ne (B, n) p with
    | error e => simp [Except.map, bind, Except.bind]
    | ok r =>
      obtain ⟨⟨B', n'⟩, stop⟩ := r
      have hlen := consolidationStep_length ne n p hB hr
      simp only [Except.map, bind, Except.bind]
      by_cases hstop : stop = true
      · simp [hstop, pure, Except.pure, toTable]
      · simp only [hstop, Bool.false_eq_true, if_false]
        exact ih hin' B' (by simp only at hlen; rw [hlen, hB]) n'

theorem stepLoop_agreeOut {vs : List Validator} {idx : List Nat} (ne : Nat)
    (pairs : List (Nat × Nat)) (hin : PairsIn idx pairs) (B0 B : List Gwei) (n : Nat)
    (hB : B.length = vs.length) (hag : AgreeOut B0 B idx) {r}
    (hr : stepLoop (consolidationStep (vs.map globalLocal) ne) (B, n) pairs = .ok r) :
    AgreeOut B0 r.1.1 idx := by
  induction pairs generalizing B n with
  | nil =>
    simp only [stepLoop, pure, Except.pure, Except.ok.injEq] at hr
    subst hr; exact hag
  | cons p ps ih =>
    obtain ⟨hs, ht⟩ := hin p (List.mem_cons_self ..)
    have hin' : PairsIn idx ps := fun q hq => hin q (List.mem_cons_of_mem _ hq)
    unfold stepLoop at hr
    cases hstep : consolidationStep (vs.map globalLocal) ne (B, n) p with
    | error e => rw [hstep] at hr; simp [bind, Except.bind] at hr
    | ok r1 =>
      rw [hstep] at hr
      simp only [bind, Except.bind] at hr
      have hag1 := consolidationStep_agreeOut (s := p.1) (t := p.2) ne n hs ht hB hag
        (by rw [← hstep])
      have hlen1 := consolidationStep_length ne n p hB hstep
      split at hr
      · simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr; exact hag1
      · exact ih hin' r1.1.1 r1.1.2 (by rw [hlen1, hB]) hag1 hr

theorem writeBack_getElem? (bs : List Gwei) (idx : List Nat) (hnd : idx.Nodup) (tb : List Gwei)
    (hlen : tb.length = idx.length) (i : Nat) :
    (writeBack bs idx tb)[i]? =
      if i ∈ idx ∧ i < bs.length then tb[idx.idxOf i]? else bs[i]? := by
  unfold writeBack
  induction idx generalizing bs tb with
  | nil => simp
  | cons x xs ih =>
    cases tb with
    | nil => simp at hlen
    | cons b bs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hnd' := (List.nodup_cons.mp hnd)
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih _ hnd'.2 _ hlen]
      by_cases hix : i = x
      · subst hix
        simp [hnd'.1]
        split <;> simp_all
      · have hxi : x ≠ i := Ne.symm hix
        have hidx : (x :: xs).idxOf i = xs.idxOf i + 1 := by
          simp [List.idxOf_cons, hxi]
        simp only [List.mem_cons, hix, false_or, hidx, List.getElem?_cons_succ]
        split <;> split <;> simp_all [List.getElem?_set_ne hxi]

/-- Writing back the table of a full-registry run gives that run's balances. -/
theorem writeBack_table {B0 B : List Gwei} {idx : List Nat} (hnd : idx.Nodup)
    (hag : AgreeOut B0 B idx) : writeBack B0 idx (tableBalances B idx) = B := by
  apply List.ext_getElem?
  intro i
  rw [writeBack_getElem? _ _ hnd _ (tableBalances_length _ _)]
  by_cases hi : i ∈ idx
  · by_cases hib : i < B0.length
    · simp only [hi, hib, and_self, if_true, tableBalances_getElem? hi]
      have : i < B.length := hag.1 ▸ hib
      simp [List.getElem?_eq_getElem this]
    · simp only [hi, hib, and_false, if_false]
      have hb0 : B0[i]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hib)
      have hb : B[i]? = none := List.getElem?_eq_none (by rw [hag.1]; exact Nat.le_of_not_lt hib)
      rw [hb0, hb]
  · simp only [hi, false_and, if_false]
    exact (hag.2 i hi).symm

theorem eraseDups_nodup : (l : List Nat) → l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup _⟩
    rw [List.mem_eraseDups]; simp
termination_by l => l.length
decreasing_by
  have := List.length_filter_le (fun b => !b == a) as
  simp only [List.length_cons]
  omega

/-- A strictly increasing list with the members of the referenced indices is
`consolidationIndices`. -/
theorem consolidationIndices_eq_of_sorted (s : BeaconState) (it : List Nat)
    (hsorted : it.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ it ↔ ∃ c ∈ s.pending_consolidations, x = c.source_index ∨ x = c.target_index) :
    it = consolidationIndices s := by
  unfold consolidationIndices
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; omega
  · exact hsorted.imp Nat.le_of_lt
  · have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega)
      (s.pending_consolidations.flatMap fun c => [c.source_index, c.target_index]).eraseDups
    exact this.imp (by simp)
  · refine List.Perm.trans ?_ (List.mergeSort_perm _ _).symm
    rw [List.perm_ext_iff_of_nodup (hsorted.nodup) (eraseDups_nodup _)]
    intro x
    rw [hmem, List.mem_eraseDups]
    simp [List.mem_flatMap, eq_comm]

theorem consolidationIndices_nodup (s : BeaconState) : (consolidationIndices s).Nodup := by
  unfold consolidationIndices
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (eraseDups_nodup _)

theorem mem_consolidationIndices (s : BeaconState) (x : Nat) :
    x ∈ consolidationIndices s ↔
      ∃ c ∈ s.pending_consolidations, x = c.source_index ∨ x = c.target_index := by
  unfold consolidationIndices
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_eraseDups]
  simp [List.mem_flatMap, eq_comm]

theorem pairsIn_consolidationIndices (s : BeaconState) :
    PairsIn (consolidationIndices s)
      (s.pending_consolidations.map fun c => (c.source_index, c.target_index)) := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact ⟨(mem_consolidationIndices s _).mpr ⟨c, hc, Or.inl rfl⟩,
    (mem_consolidationIndices s _).mpr ⟨c, hc, Or.inr rfl⟩⟩

end EpochProofs.Spec
