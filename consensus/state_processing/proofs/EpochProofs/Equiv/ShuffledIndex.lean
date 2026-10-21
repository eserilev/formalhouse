import EpochProofs.Generated
import EpochProofs.Sanity.ShuffleClosedForm

/-!
# Lighthouse `compute_shuffled_index_with` equals the reference

`compute_shuffled_index_with_spec`: for `0 < n ≤ 2^24` and `index < n`, the Lighthouse function
returns `some (csiFold index)`. With `Spec.compute_shuffled_index_eq`, it returns the reference
`compute_shuffled_index`.

The hash is the trait instance `inst`. `HashLink inst o` says that `inst.hash` computes
`o.hash` and does not fail.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev ShuffleHashInst (H : Type) := swap_or_not_shuffle.shuffle_hash.ShuffleHash H

/-- The bytes of a Lighthouse byte list. -/
def u8s (l : List U8) : List UInt8 := l.map (fun b => UInt8.ofNat b.val)

/-- `inst.hash` computes `o.hash` and does not fail. -/
def HashLink {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle) : Prop :=
  ∀ s : Slice U8, ∃ d, inst.hash s = ok d ∧ u8s d.val = (o.hash (u8s s.val)).toList

theorem u8s_length (l : List U8) : (u8s l).length = l.length := by simp [u8s]

theorem u8_lt (b : U8) : b.val < 256 := by
  have := b.hBounds; simpa using this

theorem toNat_u8 (b : U8) : (UInt8.ofNat b.val).toNat = b.val := by
  simp only [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (u8_lt b)

theorem take_set_succ {α : Type} (l s : List α) (k : Nat) (hk : k < l.length) (hks : k < s.length)
    (h : l.take k = s.take k) : (l.set k s[k]).take (k + 1) = s.take (k + 1) := by
  rw [List.take_succ_eq_append_getElem (by simp; omega),
    List.take_succ_eq_append_getElem hks]
  simp only [List.take_set, List.getElem_set_self]
  rw [List.set_eq_of_length_le (by simp), h]

theorem pivot_preimage_loop_spec (seed : Array U8 32#usize) (buf : Array U8 33#usize)
    (k : Usize) (hk : k.val ≤ 32) (hpre : buf.val.take k.val = seed.val.take k.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.pivot_preimage_loop seed buf k ⦃ r =>
      r.val.take 32 = seed.val ∧ r.val.drop 32 = buf.val.drop 32 ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.pivot_preimage_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Array U8 33#usize × Usize) => 32 - x.2.val)
    (inv := fun (x : Array U8 33#usize × Usize) => x.2.val ≤ 32 ∧
      x.1.val.take x.2.val = seed.val.take x.2.val ∧ x.1.val.drop 32 = buf.val.drop 32)
  · rintro ⟨b, j⟩ ⟨hj, hb, hd⟩
    dsimp only at hj hb hd ⊢
    unfold swap_or_not_shuffle.compute_shuffled_index_with.pivot_preimage_loop.body
    split
    · rename_i hlt
      have hj32 : j.val < 32 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [k1_post, a_post, i_post, Array.set_val_eq]
        exact take_set_succ _ _ _ (by simp; omega) (by simp; omega) hb
      · simp only [a_post, Array.set_val_eq, List.drop_set_of_lt (by omega : j.val < 32), hd]
    · rename_i hge
      have hj32 : j.val = 32 := by scalar_tac
      simp only [spec_ok]
      rw [hj32] at hb
      refine ⟨?_, hd⟩
      rw [hb]; simp
  · exact ⟨hk, hpre, rfl⟩

theorem source_preimage_loop_spec (seed : Array U8 32#usize) (buf : Array U8 37#usize)
    (k : Usize) (hk : k.val ≤ 32) (hpre : buf.val.take k.val = seed.val.take k.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.source_preimage_loop seed buf k ⦃ r =>
      r.val.take 32 = seed.val ∧ r.val.drop 32 = buf.val.drop 32 ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.source_preimage_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Array U8 37#usize × Usize) => 32 - x.2.val)
    (inv := fun (x : Array U8 37#usize × Usize) => x.2.val ≤ 32 ∧
      x.1.val.take x.2.val = seed.val.take x.2.val ∧ x.1.val.drop 32 = buf.val.drop 32)
  · rintro ⟨b, j⟩ ⟨hj, hb, hd⟩
    dsimp only at hj hb hd ⊢
    unfold swap_or_not_shuffle.compute_shuffled_index_with.source_preimage_loop.body
    split
    · rename_i hlt
      have hj32 : j.val < 32 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [k1_post, a_post, i_post, Array.set_val_eq]
        exact take_set_succ _ _ _ (by simp; omega) (by simp; omega) hb
      · simp only [a_post, Array.set_val_eq, List.drop_set_of_lt (by omega : j.val < 32), hd]
    · rename_i hge
      have hj32 : j.val = 32 := by scalar_tac
      simp only [spec_ok]
      rw [hj32] at hb
      refine ⟨?_, hd⟩
      rw [hb]; simp
  · exact ⟨hk, hpre, rfl⟩

theorem take_drop_eq {α : Type} (l : List α) (k : Nat) (a b : List α) (ha : l.take k = a)
    (hb : l.drop k = b) : l = a ++ b := by
  rw [← ha, ← hb, List.take_append_drop]

@[step]
theorem pivot_preimage_spec (seed : Array U8 32#usize) (round : U8) :
    swap_or_not_shuffle.compute_shuffled_index_with.pivot_preimage seed round ⦃ r =>
      r.val = seed.val ++ [round] ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.pivot_preimage
  apply spec_bind (pivot_preimage_loop_spec seed _ 0#usize (by simp) (by simp))
  rintro b1 ⟨h1, h2⟩
  step*
  have hb := take_drop_eq _ _ _ _ h1 h2
  have hs : seed.val.length = 32 := by simp
  rw [r_post, Array.set_val_eq, hb]
  simp [Array.repeat, List.set_append_right _ _ (by omega : 32 ≥ seed.val.length), hs]

/-- The byte `k` of `uint_to_bytes(Uint32(x))`. -/
theorem cast_shift_byte (x : Usize) (y : Usize) (k : Nat) (hy : y.val = x.val / 2 ^ (8 * k)) :
    (UScalar.cast UScalarTy.U8 y).val = x.val / 256 ^ k % 256 := by
  rw [UScalar.cast_val_eq, hy]
  have : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
  rw [this]
  rfl

@[step]
theorem source_preimage_spec (seed : Array U8 32#usize) (round : U8) (bucket : Usize) :
    swap_or_not_shuffle.compute_shuffled_index_with.source_preimage seed round bucket ⦃ r =>
      r.val.map (·.val) = seed.val.map (·.val) ++ [round.val] ++
        (List.range 4).map (fun k => bucket.val / 256 ^ k % 256) ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.source_preimage
  apply spec_bind (source_preimage_loop_spec seed _ 0#usize (by simp) (by simp))
  rintro b1 ⟨h1, h2⟩
  step*
  all_goals try (rcases System.Platform.numBits_eq with h | h <;> (simp [h]; done))
  have hb := take_drop_eq _ _ _ _ h1 h2
  have hs : seed.val.length = 32 := by simp
  have e0 : i.val = bucket.val / 256 ^ 0 % 256 := by
    rw [i_post]; exact cast_shift_byte bucket bucket 0 (by simp)
  have e1 : i2.val = bucket.val / 256 ^ 1 % 256 := by
    rw [i2_post]; exact cast_shift_byte bucket i1 1 (by rw [i1_post1, Nat.shiftRight_eq_div_pow])
  have e2 : i4.val = bucket.val / 256 ^ 2 % 256 := by
    rw [i4_post]; exact cast_shift_byte bucket i3 2 (by rw [i3_post1, Nat.shiftRight_eq_div_pow])
  have e3 : i6.val = bucket.val / 256 ^ 3 % 256 := by
    rw [i6_post]; exact cast_shift_byte bucket i5 3 (by rw [i5_post1, Nat.shiftRight_eq_div_pow])
  simp only [r_post, buf5_post, buf4_post, buf3_post, buf2_post, Array.set_val_eq, hb]
  simp [Array.repeat, hs, List.range_succ, e0, e1, e2, e3]

theorem or_shift_step (acc x k : Nat) (hacc : acc < 2 ^ k) (hx : x < 256) (hk : k + 8 ≤ 64) :
    acc ||| (x <<< k % U64.size) = acc + x * 2 ^ k ∧ acc + x * 2 ^ k < 2 ^ (k + 8) := by
  have hpow : 2 ^ (k + 8) = 2 ^ k * 256 := by rw [pow_add]; norm_num
  have hxk : x * 2 ^ k < 2 ^ (k + 8) := by
    rw [hpow, Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left hx (by positivity)
  have h64 : 2 ^ (k + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hk
  have hsz : U64.size = 2 ^ 64 := by rw [U64.size_def]; simp [U64.numBits]
  rw [hsz, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.lor_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq]
  constructor
  · ring
  · have : acc + x * 2 ^ k < 2 ^ k + 255 * 2 ^ k := by
      have : x * 2 ^ k ≤ 255 * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hpow]; omega

theorem leNat_take8 (l : List U8) (h : 8 ≤ l.length) :
    Spec.leNat ((u8s l).take 8) =
      l[0].val + l[1].val * 2 ^ 8 + l[2].val * 2 ^ 16 + l[3].val * 2 ^ 24 + l[4].val * 2 ^ 32 +
        l[5].val * 2 ^ 40 + l[6].val * 2 ^ 48 + l[7].val * 2 ^ 56 := by
  match l, h with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest, _ =>
    simp [Spec.leNat, u8s]; ring

@[step]
theorem first_u64_spec (digest : Array U8 32#usize) :
    swap_or_not_shuffle.compute_shuffled_index_with.first_u64 digest ⦃ v =>
      v.val = Spec.leNat ((u8s digest.val).take 8) ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.first_u64
  step*
  have hc : ∀ (x : U8) (y : U64), y = UScalar.cast UScalarTy.U64 x → y.val = x.val := by
    intro x y hy; rw [hy, UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by have := x.hBounds; simp [UScalarTy.numBits] at *; omega)
  have hb : ∀ (x : U8), x.val < 256 := u8_lt
  have h0 : i1.val < 2 ^ 8 := by rw [hc _ _ i1_post]; exact hb i
  have s1 := or_shift_step _ _ 8 h0 (hb i2) (by norm_num)
  have e1 : i5.val = i1.val + i2.val * 2 ^ 8 := by
    rw [i5_post1, UScalar.val_or, i4_post1, hc _ _ i3_post]; exact s1.1
  have s2 := or_shift_step _ _ 16 (e1 ▸ s1.2) (hb i6) (by norm_num)
  have e2 : i9.val = i5.val + i6.val * 2 ^ 16 := by
    rw [i9_post1, UScalar.val_or, i8_post1, hc _ _ i7_post]; exact s2.1
  have s3 := or_shift_step _ _ 24 (e2 ▸ s2.2) (hb i10) (by norm_num)
  have e3 : i13.val = i9.val + i10.val * 2 ^ 24 := by
    rw [i13_post1, UScalar.val_or, i12_post1, hc _ _ i11_post]; exact s3.1
  have s4 := or_shift_step _ _ 32 (e3 ▸ s3.2) (hb i14) (by norm_num)
  have e4 : i17.val = i13.val + i14.val * 2 ^ 32 := by
    rw [i17_post1, UScalar.val_or, i16_post1, hc _ _ i15_post]; exact s4.1
  have s5 := or_shift_step _ _ 40 (e4 ▸ s4.2) (hb i18) (by norm_num)
  have e5 : i21.val = i17.val + i18.val * 2 ^ 40 := by
    rw [i21_post1, UScalar.val_or, i20_post1, hc _ _ i19_post]; exact s5.1
  have s6 := or_shift_step _ _ 48 (e5 ▸ s5.2) (hb i22) (by norm_num)
  have e6 : i25.val = i21.val + i22.val * 2 ^ 48 := by
    rw [i25_post1, UScalar.val_or, i24_post1, hc _ _ i23_post]; exact s6.1
  have s7 := or_shift_step _ _ 56 (e6 ▸ s6.2) (hb i26) (by norm_num)
  have e7 : (i25 ||| i28).val = i25.val + i26.val * 2 ^ 56 := by
    rw [UScalar.val_or, i28_post1, hc _ _ i27_post]; exact s7.1
  rw [e7, e6, e5, e4, e3, e2, e1, hc _ _ i1_post, leNat_take8 _ (by simp)]
  simp [i_post, i2_post, i6_post, i10_post, i14_post, i18_post, i22_post, i26_post]
  rfl

theorem hash_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle) (hH : HashLink inst o)
    (s : Slice U8) : inst.hash s ⦃ d => u8s d.val = (o.hash (u8s s.val)).toList ⦄ := by
  obtain ⟨d, hd, hdb⟩ := hH s
  rw [hd]; exact hdb

theorem u8s_append (a b : List U8) : u8s (a ++ b) = u8s a ++ u8s b := by simp [u8s]

theorem u8s_source (seed : Array U8 32#usize) (round : U8) (bucket : Usize) (l : List U8)
    (h : l.map (·.val) = seed.val.map (·.val) ++ [round.val] ++
        (List.range 4).map (fun k => bucket.val / 256 ^ k % 256)) :
    u8s l = u8s seed.val ++ [UInt8.ofNat round.val] ++ Spec.uint_to_bytes 4 bucket.val := by
  have : u8s l = (l.map (·.val)).map UInt8.ofNat := by simp [u8s]
  rw [this, h]
  simp [u8s, Spec.uint_to_bytes, Function.comp_def]

theorem cast_usize_of_lt (x : U64) (h : x.val < 2 ^ 32) :
    (UScalar.cast UScalarTy.Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb] <;> omega

theorem cast_u64_of_usize (x : Usize) :
    (UScalar.cast UScalarTy.U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := x.hBounds
  rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb] at * <;> omega

theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rcases System.Platform.numBits_eq with hb | hb <;> simp [Usize.max_def, Usize.numBits, hb]

theorem shuffle_round_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle)
    (hH : HashLink inst o) (seed : Array U8 32#usize) (index : Usize) (round : U8) (n : Usize)
    (hn : 0 < n.val) (hn24 : n.val ≤ 2 ^ 24) (hi : index.val < n.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.shuffle_round inst seed index round n ⦃ r =>
      r.val = Spec.sigma o (u8s seed.val) n.val round.val index.val ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.shuffle_round
  step*
  step with hash_spec inst o hH as ⟨a1, ha1⟩
  step*
  case hmax =>
    have hi1 : i1.val = n.val := by rw [i1_post, cast_u64_of_usize]
    have hi2 : i2.val < n.val := by rw [i2_post, hi1]; exact Nat.mod_lt _ hn
    have hp : pivot.val = i2.val := by rw [pivot_post]; exact cast_usize_of_lt _ (by omega)
    have := usize_max_ge
    omega
  have hi1 : i1.val = n.val := by rw [i1_post, cast_u64_of_usize]
  have hi2 : i2.val < n.val := by rw [i2_post, hi1]; exact Nat.mod_lt _ hn
  have hp : pivot.val = i2.val := by rw [pivot_post]; exact cast_usize_of_lt _ (by omega)
  have hpiv : pivot.val = Spec.pivotOf o (u8s seed.val) n.val round.val := by
    rw [hp, i2_post, hi1, i_post, ha1, s_post]
    simp only [Spec.pivotOf, Array.to_slice, a_post, u8s_append]
    rfl
  have hflip : flip.val = (Spec.pivotOf o (u8s seed.val) n.val round.val + n.val - index.val) % n.val := by
    rw [flip_post, i4_post, hpiv, i3_post1]
    congr 1
    omega
  obtain ⟨position, hposeq, hposv⟩ : ∃ q : Usize,
      (if index < flip then ok flip else ok index : Result Usize) = ok q ∧
        q.val = max index.val flip.val := by
    split
    · rename_i h
      have : index.val < flip.val := by scalar_tac
      exact ⟨flip, rfl, by omega⟩
    · rename_i h
      have : flip.val ≤ index.val := by scalar_tac
      exact ⟨index, rfl, by omega⟩
  rw [hposeq]
  simp only [bind_tc_ok]
  step*
  case hy => rcases System.Platform.numBits_eq with h | h <;> simp [h]
  step with hash_spec inst o hH as ⟨source, hsrc⟩
  have hi5 : i5.val = position.val / 256 := by rw [i5_post1, Nat.shiftRight_eq_div_pow]
  have hs1 : u8s s1.val = u8s seed.val ++ [UInt8.ofNat round.val] ++
      Spec.uint_to_bytes 4 (position.val / 256) := by
    rw [s1_post, ← hi5]; exact u8s_source seed round i5 a2.val a2_post
  rw [hs1] at hsrc
  have hsl : source.val.length = 32 := by simp
  have hidx : position.val % 256 / 8 < 32 := by omega
  have hbyte : (source.val[position.val % 256 / 8]'(by omega)).val =
      ((o.hash (u8s seed.val ++ [UInt8.ofNat round.val] ++
        Spec.uint_to_bytes 4 (position.val / 256))).toList.getD (position.val % 256 / 8) 0).toNat := by
    rw [← hsrc]
    simp [u8s, List.getD_eq_getElem?_getD, hidx]
  have hbit : Spec.bitOf o (u8s seed.val) round.val position.val =
      (source.val[position.val % 256 / 8]'(by omega)).val / 2 ^ (position.val % 8) % 2 := by
    rw [hbyte]; rfl
  step*
  all_goals
    have hb10 : i10.val = Spec.bitOf o (u8s seed.val) round.val position.val := by
      rw [hbit, i10_post, i9_post1, i8_post, Nat.shiftRight_eq_div_pow]
      simp only [byte_post, i7_post, i6_post]
    have hlt2 : i10.val < 2 := by rw [i10_post]; exact Nat.mod_lt _ (by decide)
    simp only [Spec.sigma, ← hflip, ← hposv, ← hb10]
    rename_i hc
  · have : i10.val = 1 := by rw [hc]; rfl
    simp [this]
  · have : i10.val ≠ 1 := fun h => hc (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have : i10.val = 0 := by omega
    simp [this]

theorem csiFold_succ (o : Spec.Oracle) (seed : List UInt8) (n r x : Nat) :
    Spec.csiFold o seed n (r + 1) x = Spec.sigma o seed n r (Spec.csiFold o seed n r x) := by
  simp [Spec.csiFold, List.range_succ, List.foldl_append]

theorem rounds_loop_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle)
    (hH : HashLink inst o) (n : Usize) (seed : Array U8 32#usize) (R : U8) (index : Usize)
    (round : U8) (x0 : Nat) (hn : 0 < n.val) (hn24 : n.val ≤ 2 ^ 24) (hr : round.val ≤ R.val)
    (hidx : index.val = Spec.csiFold o (u8s seed.val) n.val round.val x0) (hi : index.val < n.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with_loop inst n seed R
      index round ⦃ r => r.val = Spec.csiFold o (u8s seed.val) n.val R.val x0 ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × U8) => R.val - x.2.val)
    (inv := fun (x : Usize × U8) => x.2.val ≤ R.val ∧
      x.1.val = Spec.csiFold o (u8s seed.val) n.val x.2.val x0 ∧ x.1.val < n.val)
  · rintro ⟨j, rd⟩ ⟨hr, hj, hjn⟩
    dsimp only at hr hj hjn ⊢
    unfold swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with_loop.body
    split
    · rename_i hlt
      have hrR : rd.val < R.val := by scalar_tac
      step with shuffle_round_spec inst o hH seed j rd n hn hn24 hjn as ⟨j1, hj1⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hj1, round1_post, csiFold_succ, hj]
      · rw [hj1]; exact Spec.sigma_lt _ _ _ _ _ hn hjn
    · rename_i hge
      have : rd.val = R.val := by scalar_tac
      simp only [spec_ok]
      rw [hj, this]
  · exact ⟨hr, hidx, hi⟩

theorem compute_shuffled_index_with_spec {H : Type} (inst : ShuffleHashInst H)
    (o : Spec.Oracle) (hH : HashLink inst o) (index n : Usize) (seed : Array U8 32#usize)
    (R : U8) (hn24 : n.val ≤ 2 ^ 24) (hi : index.val < n.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with inst index n seed R
      ⦃ r => ∃ x : Usize, r = some x ∧
        x.val = Spec.csiFold o (u8s seed.val) n.val R.val index.val ⦄ := by
  unfold swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with
  have hn0 : n ≠ 0#usize := by intro h; rw [h] at hi; simp at hi
  have hge : ¬ index >= n := by scalar_tac
  simp only [hn0, if_false, hge]
  have hmax := usize_max_ge
  step*
  all_goals try (rcases System.Platform.numBits_eq with h | h <;> (simp [h]; done))
  case h1 =>
    exfalso
    rename_i hc
    have : i1.val = 2 ^ 24 := by
      rw [i1_post1, Nat.shiftLeft_eq]
      apply Nat.mod_eq_of_lt
      rcases System.Platform.numBits_eq with hb | hb <;> simp [Usize.size, Usize.numBits, hb]
    scalar_tac
  step with rounds_loop_spec inst o hH n seed R index 0#u8 index.val (by omega) hn24
      (by simp) (by simp [Spec.csiFold]) hi as ⟨r, hr⟩
  exact ⟨r, rfl, hr⟩

/-- The Lighthouse shuffle equals the reference `compute_shuffled_index`. -/
theorem compute_shuffled_index_with_eq {H : Type} (inst : ShuffleHashInst H) (p : Spec.Preset)
    (o : Spec.Oracle) (hH : HashLink inst o) (index n : Usize) (seed : Array U8 32#usize)
    (seedSpec : Spec.Bytes32) (hseed : u8s seed.val = seedSpec.toList) (R : U8)
    (hR : R.val = p.SHUFFLE_ROUND_COUNT) (hn24 : n.val ≤ 2 ^ 24) (hi : index.val < n.val) :
    swap_or_not_shuffle.compute_shuffled_index_with.compute_shuffled_index_with inst index n seed R
      ⦃ r => ∃ x : Usize, r = some x ∧
        Spec.compute_shuffled_index p o index.val n.val seedSpec = .ok x.val ⦄ := by
  apply spec_mono (compute_shuffled_index_with_spec inst o hH index n seed R hn24 hi)
  rintro r ⟨x, rfl, hx⟩
  refine ⟨x, rfl, ?_⟩
  have hR256 : p.SHUFFLE_ROUND_COUNT ≤ 256 := by
    rw [← hR]; exact Nat.le_of_lt (u8_lt R)
  have h40 : n.val ≤ 2 ^ 40 := by omega
  have := Spec.compute_shuffled_index_eq p o seedSpec index.val n.val hi h40 hR256
  rw [this, hx, hseed, hR]

end EpochProofs
