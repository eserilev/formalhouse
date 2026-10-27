import EpochProofs.Spec.Committees

/-!
# `compute_shuffled_permutation` in closed form

`sigma o seed n r` is one round of the swap-or-not shuffle on one index. `csiFold` runs rounds
`0, 1, ..., R - 1` on one index. `compute_shuffled_permutation_eq` proves that the reference
returns `[csiFold i for i in range(n)]` for `0 < n < 2^40` and `R ≤ 256`. So
`compute_shuffled_index_eq` gives `compute_shuffled_index(i) = csiFold i`.

Ported from `CacheProofs/Equiv/ShuffleSpec.lean` (the committee shuffle proof, #29), for the
`Oracle` hash of this reference.
-/

namespace EpochProofs.Spec

/-- `int.from_bytes(l, 'little')`. -/
def leNat (l : List UInt8) : Nat := l.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The pivot of round `r`. -/
def pivotOf (o : Oracle) (seed : List UInt8) (n r : Nat) : Nat :=
  leNat ((o.hash (seed ++ [UInt8.ofNat r])).toList.take 8) % n

/-- The bit of round `r` at `position`. -/
def bitOf (o : Oracle) (seed : List UInt8) (r position : Nat) : Nat :=
  ((o.hash (seed ++ [UInt8.ofNat r] ++ uint_to_bytes 4 (position / 256))).toList.getD
    (position % 256 / 8) 0).toNat / 2 ^ (position % 8) % 2

/-- One round of the shuffle on index `x`. -/
def sigma (o : Oracle) (seed : List UInt8) (n r x : Nat) : Nat :=
  let flip := (pivotOf o seed n r + n - x) % n
  if bitOf o seed r (max x flip) ≠ 0 then flip else x

/-- Rounds `0, ..., R - 1` on index `x`. -/
def csiFold (o : Oracle) (seed : List UInt8) (n R x : Nat) : Nat :=
  (List.range R).foldl (fun y r => sigma o seed n r y) x

theorem sigma_lt (o : Oracle) (seed : List UInt8) (n r x : Nat) (hn : 0 < n) (hx : x < n) :
    sigma o seed n r x < n := by
  unfold sigma
  dsimp only
  split
  · exact Nat.mod_lt _ hn
  · exact hx

theorem foldl_sigma_lt (o : Oracle) (seed : List UInt8) (n : Nat) (hn : 0 < n) (rs : List Nat)
    (x : Nat) (hx : x < n) : rs.foldl (fun y r => sigma o seed n r y) x < n := by
  induction rs generalizing x with
  | nil => exact hx
  | cons r rs ih => exact ih _ (sigma_lt _ _ _ _ _ hn hx)

theorem csiFold_lt (o : Oracle) (seed : List UInt8) (n R x : Nat) (hn : 0 < n) (hx : x < n) :
    csiFold o seed n R x < n :=
  foldl_sigma_lt _ _ _ hn _ _ hx

theorem leNat_lt (l : List UInt8) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    simp only [leNat, List.foldr_cons, List.length_cons] at *
    have := b.toNat_lt
    rw [Nat.pow_succ]
    have : 256 * l.foldr (fun b acc => b.toNat + 256 * acc) 0 ≤ 256 * (256 ^ l.length - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h1 : 1 ≤ 256 ^ l.length := Nat.one_le_pow _ _ (by decide)
    rw [Nat.mul_sub, Nat.mul_one] at this
    rw [Nat.mul_comm (256 ^ l.length)]
    omega

/-- The bit test of the reference, on `UInt8`. -/
theorem shift_mod_two (b : UInt8) (k : Nat) (hk : k < 8) :
    ((b >>> UInt8.ofNat k) % 2 != 0) = decide (b.toNat / 2 ^ k % 2 ≠ 0) := by
  have hk' : (UInt8.ofNat k).toNat = k := by
    simp only [UInt8.toNat_ofNat']; omega
  have h : ((b >>> UInt8.ofNat k) % 2).toNat = b.toNat / 2 ^ k % 2 := by
    rw [UInt8.toNat_mod, UInt8.toNat_shiftRight, hk', Nat.mod_eq_of_lt (by omega : k < 8),
      Nat.shiftRight_eq_div_pow]
    rfl
  cases hb : (b >>> UInt8.ofNat k) % 2 != 0 <;>
    simp only [bne_iff_ne, ne_eq, bne_eq_false_iff_eq] at hb <;>
    simp only [Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq,
      Decidable.not_not, ne_eq]
  · rw [← h, hb]; rfl
  · intro h0; apply hb; apply UInt8.toNat_inj.mp; rw [h, h0]; rfl

theorem foldl_set_sigma (f : Nat → Nat) (l : List Nat) (k : Nat) (hk : k ≤ l.length) :
    (List.range k).foldl (fun a i => a.set i (f (a.getD i 0))) l =
      (l.take k).map f ++ l.drop k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hlt : k < l.length := by omega
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.length_set, List.length_append, List.length_map, List.length_take,
        List.length_drop] at h1
      rw [List.getElem_set]
      split
      · rename_i hik
        subst hik
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega)]
        rw [List.getElem_append_left (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hlt), List.getElem?_eq_getElem hlt]
      · rename_i hik
        rw [List.getElem_append, List.getElem_append]
        by_cases hi : i < k
        · simp [hi, show i < k + 1 by omega, Nat.min_eq_left (Nat.le_of_lt hlt),
            Nat.min_eq_left hk]
        · have hi' : ¬ i < k + 1 := by omega
          simp [hi, hi', Nat.min_eq_left (Nat.le_of_lt hlt), Nat.min_eq_left hk]
          congr 1
          omega

theorem forIn_yield {ε α β : Type} (l : List α) (b : β)
    (f : α → β → Except ε (ForInStep β)) (g : β → α → β) (P : β → Prop) (hb : P b)
    (hf : ∀ x ∈ l, ∀ a, P a → f x a = .ok (.yield (g a x)) ∧ P (g a x)) :
    forIn l b f = .ok (l.foldl g b) := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := hf x (by simp) b hb
    rw [List.forIn_cons, h1]
    exact ih _ h2 (fun y hy a ha => hf y (by simp [hy]) a ha)

theorem foldl_map_sigma (o : Oracle) (seed : List UInt8) (n : Nat) (rs : List Nat)
    (l : List Nat) :
    rs.foldl (fun l r => l.map (sigma o seed n r)) l =
      l.map (fun x => rs.foldl (fun y r => sigma o seed n r y) x) := by
  induction rs generalizing l with
  | nil => simp
  | cons r rs ih => simp [ih, List.map_map, Function.comp_def]

/-- Valid shuffle state: `n` indices, each below `n`. -/
def ValidIndices (n : Nat) (l : List Nat) : Prop := l.length = n ∧ ∀ y ∈ l, y < n

theorem bytes_to_uint64_take8 (l : List UInt8) :
    bytes_to_uint64 (l.take 8) = .ok (leNat (l.take 8)) := by
  have h := leNat_lt (l.take 8)
  have hl : (l.take 8).length ≤ 8 := by simp [Nat.min_le_left]
  have : 256 ^ (l.take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hl
  simp only [bytes_to_uint64, leNat] at h ⊢
  rw [if_pos (by unfold UINT64_SIZE; omega)]
  rfl

theorem compute_shuffled_permutation_eq (p : Preset) (o : Oracle) (seed : Bytes32) (n : Nat)
    (hn : 0 < n) (hn40 : n ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256) :
    compute_shuffled_permutation p o n seed =
      .ok ((List.range n).map (csiFold o seed.toList n p.SHUFFLE_ROUND_COUNT)) := by
  unfold compute_shuffled_permutation
  dsimp only
  rw [forIn_yield _ _ _ (fun l r => l.map (sigma o seed.toList n r)) (ValidIndices n)]
  · show Except.ok _ = _
    rw [foldl_map_sigma]
    rfl
  · exact ⟨by simp, fun y hy => by simpa using hy⟩
  · intro r hr a ha
    rw [List.mem_range] at hr
    have hr' : r < 256 := Nat.lt_of_lt_of_le hr hR
    have hp : pivotOf o seed.toList n r < n := Nat.mod_lt _ hn
    have hrb : uint_to_bytes 1 r = [UInt8.ofNat r] := by
      simp [uint_to_bytes, Nat.mod_eq_of_lt hr']
    simp only [hr', not_true_eq_false, if_false, hrb, bytes_to_uint64_take8, uint64Mod,
      Nat.ne_of_gt hn, pure_bind, bind_pure_comp]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [forIn_yield _ _ _ (fun a i => a.set i (sigma o seed.toList n r (a.getD i 0)))
      (ValidIndices n) ha]
    · have hlen := ha.1
      refine ⟨?_, ?_⟩
      · rw [foldl_set_sigma _ _ _ (by omega), List.take_of_length_le (by omega),
          List.drop_of_length_le (by omega), List.append_nil]
        rfl
      · refine ⟨by simp [hlen], ?_⟩
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact sigma_lt _ _ _ _ _ hn (ha.2 x hx)
    · intro i hi b hb
      rw [List.mem_range] at hi
      have hib : i < b.length := by rw [hb.1]; exact hi
      have hidx : b.getD i 0 < n := hb.2 _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]; exact List.getElem_mem hib)
      have hget : listGet b i = .ok (b.getD i 0) := by
        simp [listGet, List.getElem?_eq_getElem hib, List.getD_eq_getElem?_getD]; rfl
      generalize hx : b.getD i 0 = x at hidx hget
      have hpiv : leNat ((o.hash (seed.toList ++ [UInt8.ofNat r])).toList.take 8) % n =
          pivotOf o seed.toList n r := rfl
      generalize hflip : (pivotOf o seed.toList n r + n - x) % n = flip
      have hflipn : flip < n := by rw [← hflip]; exact Nat.mod_lt _ hn
      have hpos : max x flip < n := Nat.max_lt.2 ⟨hidx, hflipn⟩
      have hbucket : max x flip / 256 < 2 ^ 32 := by omega
      have hsrc : max x flip % 256 / 8 <
          (o.hash (seed.toList ++ [UInt8.ofNat r] ++ uint_to_bytes 4 (max x flip / 256))).toList.length := by
        simp; omega
      have hbyte : listGet (o.hash (seed.toList ++ [UInt8.ofNat r] ++
            uint_to_bytes 4 (max x flip / 256))).toList (max x flip % 256 / 8) =
          .ok ((o.hash (seed.toList ++ [UInt8.ofNat r] ++
            uint_to_bytes 4 (max x flip / 256))).toList.getD (max x flip % 256 / 8) 0) := by
        unfold listGet; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsrc]; rfl
      have h1 : pivotOf o seed.toList n r + n < UINT64_SIZE := by unfold UINT64_SIZE; omega
      have hadd : uint64Add (pivotOf o seed.toList n r) n = .ok (pivotOf o seed.toList n r + n) := by
        simp only [uint64Add, h1, if_true]; rfl
      have hsub : uint64Sub (pivotOf o seed.toList n r + n) x =
          .ok (pivotOf o seed.toList n r + n - x) := by
        simp only [uint64Sub, show x ≤ pivotOf o seed.toList n r + n by omega, if_true]; rfl
      have hdiv : uint64Div (max x flip) 256 = .ok (max x flip / 256) := by
        simp only [uint64Div, show (256 : Nat) ≠ 0 by decide, if_false]; rfl
      simp only [hpiv, hadd, hget, hsub]
      simp only [hflip, hdiv, hbucket, not_true_eq_false, if_false, hbyte]
      have hk : max x flip % 8 < 8 := Nat.mod_lt _ (by decide)
      rw [shift_mod_two _ _ hk]
      have hset : listSet b i (if decide (((o.hash (seed.toList ++ [UInt8.ofNat r] ++
            uint_to_bytes 4 (max x flip / 256))).toList.getD (max x flip % 256 / 8) 0).toNat /
            2 ^ (max x flip % 8) % 2 ≠ 0) = true then flip else x) =
          .ok (b.set i (sigma o seed.toList n r x)) := by
        simp only [listSet, hib, if_true, sigma, ← hflip, bitOf, decide_eq_true_eq]
        rfl
      simp only [hset]
      refine ⟨rfl, by simp [hb.1], ?_⟩
      intro y hy
      rcases List.mem_or_eq_of_mem_set hy with h | h
      · exact hb.2 y h
      · rw [h]; exact sigma_lt _ _ _ _ _ hn hidx

theorem compute_shuffled_index_eq (p : Preset) (o : Oracle) (seed : Bytes32) (index n : Nat)
    (hi : index < n) (hn40 : n ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256) :
    compute_shuffled_index p o index n seed =
      .ok (csiFold o seed.toList n p.SHUFFLE_ROUND_COUNT index) := by
  unfold compute_shuffled_index
  rw [if_neg (Decidable.not_not.mpr hi), compute_shuffled_permutation_eq p o seed n (by omega) hn40 hR]
  simp [Bind.bind, Except.bind, listGet, hi]
  rfl

end EpochProofs.Spec
