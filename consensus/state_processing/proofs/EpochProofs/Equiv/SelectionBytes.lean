import EpochProofs.Equiv.ShuffledIndex
import EpochProofs.Equiv.BuilderPendingPayments

/-!
# The byte strings of the balance-weighted selection

`hash_with_u64_spec`: `hash_with_u64(seed, x)` hashes `seed + uint_to_bytes(x)`.
`compute_seed_spec`: `compute_seed(domain, epoch, mix)` hashes
`domain + uint_to_bytes(epoch) + mix`, as `get_seed` does.
`random_value_spec`: `random_value(seed, i)` reads the 2 bytes at `i % 16 * 2` of
`sha256(seed + uint_to_bytes(i // 16))`.

The functions build each preimage in a fixed-size buffer with one `while` loop per part.
`copy_take` describes one pass of such a loop.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- One pass of a copy loop: `b[k] = src[k - lo]`. -/
theorem copy_take {α : Type} (b src pre : List α) (lo k : Nat) (hk : lo ≤ k)
    (hks : k - lo < src.length) (hlen : k < b.length)
    (h : b.take k = pre ++ src.take (k - lo)) :
    (b.set k src[k - lo]).take (k + 1) = pre ++ src.take (k + 1 - lo) := by
  have hpre : pre.length = lo := by
    have := congrArg List.length h
    simp only [List.length_take, List.length_append] at this
    omega
  rw [List.take_succ_eq_append_getElem (by simp; omega)]
  simp only [List.take_set, List.getElem_set_self]
  rw [List.set_eq_of_length_le (by simp), h, show k + 1 - lo = (k - lo) + 1 by omega,
    List.take_succ_eq_append_getElem hks, List.append_assoc]

theorem usize_sat_add_one (k : Usize) (h : k.val < 64) :
    (core.num.Usize.saturating_add k 1#usize).val = k.val + 1 :=
  usize_saturating_add_one k (by have := usize_max_ge; omega)

theorem usize_sat_sub (k c : Usize) (hc : c.val ≤ k.val) :
    (core.num.Usize.saturating_sub k c).val = k.val - c.val := by
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub]
  have hk := k.hBounds
  show (BitVec.ofNat _ (max 0 (k.val - c.val))).toNat = _
  rw [BitVec.toNat_ofNat, Nat.max_def]
  simp only [Nat.zero_le, if_true]
  exact Nat.mod_eq_of_lt (by omega)

/-- The invariant of a copy loop that writes `src` into `[lo, hi)` of the buffer `b0`. -/
def CopyInv {m n : Usize} (b0 : Array U8 m) (src : Array U8 n) (lo : Nat) (x : Array U8 m × Usize) :
    Prop :=
  lo ≤ x.2.val ∧ x.2.val ≤ lo + n.val ∧
    x.1.val.take x.2.val = b0.val.take lo ++ src.val.take (x.2.val - lo) ∧
    x.1.val.drop (lo + n.val) = b0.val.drop (lo + n.val)

theorem CopyInv.step {m n : Usize} (b0 : Array U8 m) (src : Array U8 n) (lo : Nat)
    (b : Array U8 m) (k : Usize) (hm : lo + n.val ≤ m.val) (h : CopyInv b0 src lo (b, k))
    (hlo : lo ≤ k.val) (hlt : k.val < lo + n.val) (k1 : Usize) (hk1 : k1.val = k.val + 1) :
    CopyInv b0 src lo (b.set k (src.val[k.val - lo]'(by simp; omega)), k1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only at h1 h2 h3 h4
  unfold CopyInv
  dsimp only
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp only [Array.set_val_eq, hk1]
    exact copy_take _ _ _ _ _ h1 (by simp; omega) (by simp; omega) h3
  · simp only [Array.set_val_eq, List.drop_set_of_lt (by omega : k.val < lo + n.val), h4]

theorem CopyInv.done {m n : Usize} (b0 : Array U8 m) (src : Array U8 n) (lo : Nat)
    (b : Array U8 m) (k : Usize) (h : CopyInv b0 src lo (b, k)) (hk : k.val = lo + n.val) :
    b.val.take (lo + n.val) = b0.val.take lo ++ src.val ∧
      b.val.drop (lo + n.val) = b0.val.drop (lo + n.val) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only at h1 h2 h3 h4
  rw [hk] at h3
  refine ⟨?_, h4⟩
  rw [h3, show lo + n.val - lo = n.val by omega,
    List.take_of_length_le (l := src.val) (by simp)]

theorem hash_with_u64_loop0_spec (seed : Array U8 32#usize) (b0 : Array U8 40#usize) (k0 : Usize)
    (hk0 : k0.val = 0) :
    types.state.balance_weighted_selection.hash_with_u64_loop0 seed b0 k0 ⦃ r =>
      r.2.val = 32 ∧ CopyInv b0 seed 0 r ⦄ := by
  unfold types.state.balance_weighted_selection.hash_with_u64_loop0
  apply loop.spec_decr_nat (measure := fun (x : Array U8 40#usize × Usize) => 32 - x.2.val)
    (inv := CopyInv b0 seed 0)
  · rintro ⟨b, k⟩ hinv
    dsimp only
    unfold types.state.balance_weighted_selection.hash_with_u64_loop0.body
    have hk := hinv.2.1
    have hk' := hinv.1
    dsimp only at hk hk'
    split
    · rename_i hlt
      have hkh : k.val < 32 := by scalar_tac
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, i_post]
      have := CopyInv.step b0 seed 0 b k (by simp) hinv (by omega) (by simpa using hkh) k1
        (by scalar_tac)
      
      simpa using this
    · have : k.val = 32 := by scalar_tac
      simp only [spec_ok]
      exact ⟨this, hinv⟩
  · exact ⟨by simp [hk0], by simp [hk0], by simp [hk0], rfl⟩

theorem hash_with_u64_loop1_spec (bytes : Array U8 8#usize) (b0 : Array U8 40#usize) (k0 : Usize)
    (hk0 : k0.val = 32) :
    types.state.balance_weighted_selection.hash_with_u64_loop1 bytes b0 k0 ⦃ r =>
      r.val.take (32 + 8) = b0.val.take 32 ++ bytes.val ∧
        r.val.drop (32 + 8) = b0.val.drop (32 + 8) ⦄ := by
  unfold types.state.balance_weighted_selection.hash_with_u64_loop1
  apply loop.spec_decr_nat (measure := fun (x : Array U8 40#usize × Usize) => 40 - x.2.val)
    (inv := CopyInv b0 bytes 32)
  · rintro ⟨b, k⟩ hinv
    dsimp only
    unfold types.state.balance_weighted_selection.hash_with_u64_loop1.body
    have hk := hinv.2.1
    have hk' := hinv.1
    dsimp only at hk hk'
    split
    · rename_i hlt
      have hkh : k.val < 40 := by scalar_tac
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, i1_post]
      have := CopyInv.step b0 bytes 32 b k (by simp) hinv (by omega) (by simpa using hkh) k1
        (by scalar_tac)
      have hi : i.val = k.val - 32 := by scalar_tac
      simp only [hi]
      simpa using this
    · have : k.val = 40 := by scalar_tac
      simp only [spec_ok]
      exact CopyInv.done b0 bytes 32 b k hinv (by simp; omega)
  · exact ⟨by simp [hk0], by simp [hk0], by simp [hk0], rfl⟩

theorem compute_seed_loop0_spec (domain_type : Array U8 4#usize) (b0 : Array U8 44#usize) (k0 : Usize)
    (hk0 : k0.val = 0) :
    types.state.balance_weighted_selection.compute_seed_loop0 domain_type b0 k0 ⦃ r =>
      r.2.val = 4 ∧ CopyInv b0 domain_type 0 r ⦄ := by
  unfold types.state.balance_weighted_selection.compute_seed_loop0
  apply loop.spec_decr_nat (measure := fun (x : Array U8 44#usize × Usize) => 4 - x.2.val)
    (inv := CopyInv b0 domain_type 0)
  · rintro ⟨b, k⟩ hinv
    dsimp only
    unfold types.state.balance_weighted_selection.compute_seed_loop0.body
    have hk := hinv.2.1
    have hk' := hinv.1
    dsimp only at hk hk'
    split
    · rename_i hlt
      have hkh : k.val < 4 := by scalar_tac
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, i_post]
      have := CopyInv.step b0 domain_type 0 b k (by simp) hinv (by omega) (by simpa using hkh) k1
        (by scalar_tac)
      
      simpa using this
    · have : k.val = 4 := by scalar_tac
      simp only [spec_ok]
      exact ⟨this, hinv⟩
  · exact ⟨by simp [hk0], by simp [hk0], by simp [hk0], rfl⟩

theorem compute_seed_loop1_spec (bytes : Array U8 8#usize) (b0 : Array U8 44#usize) (k0 : Usize)
    (hk0 : k0.val = 4) :
    types.state.balance_weighted_selection.compute_seed_loop1 bytes b0 k0 ⦃ r =>
      r.2.val = 12 ∧ CopyInv b0 bytes 4 r ⦄ := by
  unfold types.state.balance_weighted_selection.compute_seed_loop1
  apply loop.spec_decr_nat (measure := fun (x : Array U8 44#usize × Usize) => 12 - x.2.val)
    (inv := CopyInv b0 bytes 4)
  · rintro ⟨b, k⟩ hinv
    dsimp only
    unfold types.state.balance_weighted_selection.compute_seed_loop1.body
    have hk := hinv.2.1
    have hk' := hinv.1
    dsimp only at hk hk'
    split
    · rename_i hlt
      have hkh : k.val < 12 := by scalar_tac
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, i1_post]
      have := CopyInv.step b0 bytes 4 b k (by simp) hinv (by omega) (by simpa using hkh) k1
        (by scalar_tac)
      have hi : i.val = k.val - 4 := by scalar_tac
      simp only [hi]
      simpa using this
    · have : k.val = 12 := by scalar_tac
      simp only [spec_ok]
      exact ⟨this, hinv⟩
  · exact ⟨by simp [hk0], by simp [hk0], by simp [hk0], rfl⟩

theorem compute_seed_loop2_spec (mix : Array U8 32#usize) (b0 : Array U8 44#usize) (k0 : Usize)
    (hk0 : k0.val = 12) :
    types.state.balance_weighted_selection.compute_seed_loop2 mix b0 k0 ⦃ r =>
      r.val.take (12 + 32) = b0.val.take 12 ++ mix.val ∧
        r.val.drop (12 + 32) = b0.val.drop (12 + 32) ⦄ := by
  unfold types.state.balance_weighted_selection.compute_seed_loop2
  apply loop.spec_decr_nat (measure := fun (x : Array U8 44#usize × Usize) => 44 - x.2.val)
    (inv := CopyInv b0 mix 12)
  · rintro ⟨b, k⟩ hinv
    dsimp only
    unfold types.state.balance_weighted_selection.compute_seed_loop2.body
    have hk := hinv.2.1
    have hk' := hinv.1
    dsimp only at hk hk'
    split
    · rename_i hlt
      have hkh : k.val < 44 := by scalar_tac
      step*
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, i1_post]
      have := CopyInv.step b0 mix 12 b k (by simp) hinv (by omega) (by simpa using hkh) k1
        (by scalar_tac)
      have hi : i.val = k.val - 12 := by scalar_tac
      simp only [hi]
      simpa using this
    · have : k.val = 44 := by scalar_tac
      simp only [spec_ok]
      exact CopyInv.done b0 mix 12 b k hinv (by simp; omega)
  · exact ⟨by simp [hk0], by simp [hk0], by simp [hk0], rfl⟩

theorem cast_shift_byte64 (x y : U64) (k : Nat) (hy : y.val = x.val / 2 ^ (8 * k)) :
    (UScalar.cast UScalarTy.U8 y).val = x.val / 256 ^ k % 256 := by
  rw [UScalar.cast_val_eq, hy]
  have : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
  rw [this]
  rfl

@[step]
theorem le_bytes8_spec (x : U64) :
    types.state.balance_weighted_selection.le_bytes8 x ⦃ r =>
      u8s r.val = Spec.uint_to_bytes 8 x.val ⦄ := by
  unfold types.state.balance_weighted_selection.le_bytes8
  step*
  have e0 : i.val = x.val / 256 ^ 0 % 256 := by
    rw [i_post]; exact cast_shift_byte64 x x 0 (by simp)
  have e1 : i2.val = x.val / 256 ^ 1 % 256 := by
    rw [i2_post]; exact cast_shift_byte64 x i1 1 (by rw [i1_post1, Nat.shiftRight_eq_div_pow])
  have e2 : i4.val = x.val / 256 ^ 2 % 256 := by
    rw [i4_post]; exact cast_shift_byte64 x i3 2 (by rw [i3_post1, Nat.shiftRight_eq_div_pow])
  have e3 : i6.val = x.val / 256 ^ 3 % 256 := by
    rw [i6_post]; exact cast_shift_byte64 x i5 3 (by rw [i5_post1, Nat.shiftRight_eq_div_pow])
  have e4 : i8.val = x.val / 256 ^ 4 % 256 := by
    rw [i8_post]; exact cast_shift_byte64 x i7 4 (by rw [i7_post1, Nat.shiftRight_eq_div_pow])
  have e5 : i10.val = x.val / 256 ^ 5 % 256 := by
    rw [i10_post]; exact cast_shift_byte64 x i9 5 (by rw [i9_post1, Nat.shiftRight_eq_div_pow])
  have e6 : i12.val = x.val / 256 ^ 6 % 256 := by
    rw [i12_post]; exact cast_shift_byte64 x i11 6 (by rw [i11_post1, Nat.shiftRight_eq_div_pow])
  have e7 : i14.val = x.val / 256 ^ 7 % 256 := by
    rw [i14_post]; exact cast_shift_byte64 x i13 7 (by rw [i13_post1, Nat.shiftRight_eq_div_pow])
  simp [u8s, Array.make, Spec.uint_to_bytes, List.range_succ, e0, e1, e2, e3, e4, e5, e6, e7]

theorem u8s_take_drop (b b0 : List U8) (n : Nat) (pre src : List U8)
    (h1 : b.take n = pre ++ src) (h2 : b.drop n = b0.drop n) :
    u8s b = u8s pre ++ u8s src ++ u8s (b0.drop n) := by
  rw [← List.take_append_drop n b, h1, h2]
  simp [u8s]

theorem hash_with_u64_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle)
    (hH : HashLink inst o) (seed : Array U8 32#usize) (x : U64) :
    types.state.balance_weighted_selection.hash_with_u64 inst seed x ⦃ d =>
      u8s d.val = (o.hash (u8s seed.val ++ Spec.uint_to_bytes 8 x.val)).toList ⦄ := by
  unfold types.state.balance_weighted_selection.hash_with_u64
  step with le_bytes8_spec as ⟨bytes, hbytes⟩
  apply spec_bind (hash_with_u64_loop0_spec seed _ 0#usize (by simp))
  rintro ⟨b1, k⟩ ⟨hk, hinv⟩
  have h1 := CopyInv.done _ _ _ b1 k hinv (by simpa using hk)
  simp only [uncurry_apply_pair]
  apply spec_bind (hash_with_u64_loop1_spec bytes b1 k (by simpa using hk))
  rintro b2 ⟨h2, h3⟩
  simp only [lift, bind_tc_ok]
  apply spec_mono (hash_spec inst o hH _)
  intro d hd
  rw [hd]
  congr 2
  have hb1 : b1.val.take 32 = seed.val := by simpa using h1.1
  have : b2.val = b1.val.take 32 ++ bytes.val := by
    have e : b2.val.take (32 + 8) = b2.val := List.take_of_length_le (by simp)
    rw [← e, h2]
  simp only [Array.to_slice, this, hb1, u8s_append, hbytes]

theorem compute_seed_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle)
    (hH : HashLink inst o) (domain : Array U8 4#usize) (epoch : U64) (mix : Array U8 32#usize) :
    types.state.balance_weighted_selection.compute_seed inst domain epoch mix ⦃ d =>
      u8s d.val = (o.hash (u8s domain.val ++ Spec.uint_to_bytes 8 epoch.val ++
        u8s mix.val)).toList ⦄ := by
  unfold types.state.balance_weighted_selection.compute_seed
  step with le_bytes8_spec as ⟨bytes, hbytes⟩
  apply spec_bind (compute_seed_loop0_spec domain _ 0#usize (by simp))
  rintro ⟨b1, k⟩ ⟨hk, hinv⟩
  have h1 := CopyInv.done _ _ _ b1 k hinv (by simpa using hk)
  simp only [uncurry_apply_pair]
  apply spec_bind (compute_seed_loop1_spec bytes b1 k (by simpa using hk))
  rintro ⟨b2, k1⟩ ⟨hk1, hinv1⟩
  have h2 := CopyInv.done _ _ _ b2 k1 hinv1 (by simpa using hk1)
  simp only [uncurry_apply_pair]
  apply spec_bind (compute_seed_loop2_spec mix b2 k1 (by simpa using hk1))
  rintro b3 ⟨h3, h4⟩
  simp only [lift, bind_tc_ok]
  apply spec_mono (hash_spec inst o hH _)
  intro d hd
  rw [hd]
  congr 2
  have hb1 : b1.val.take 4 = domain.val := by simpa using h1.1
  have hb2 : b2.val.take 12 = b1.val.take 4 ++ bytes.val := by simpa using h2.1
  have : b3.val = b2.val.take 12 ++ mix.val := by
    have e : b3.val.take (12 + 32) = b3.val := List.take_of_length_le (by simp)
    rw [← e, h3]
  simp only [Array.to_slice, this, hb2, hb1, u8s_append, hbytes]

theorem random_value_spec {H : Type} (inst : ShuffleHashInst H) (o : Spec.Oracle)
    (hH : HashLink inst o) (seed : Array U8 32#usize) (i : Usize) :
    types.state.balance_weighted_selection.random_value inst seed i ⦃ v =>
      v.val = Spec.leNat (((o.hash (u8s seed.val ++ Spec.uint_to_bytes 8 (i.val / 16))).toList.drop
        (i.val % 16 * 2)).take 2) ⦄ := by
  unfold types.state.balance_weighted_selection.random_value
  step*
  step with hash_with_u64_spec inst o hH seed i2 as ⟨rb, hrb⟩
  step*
  have hc : ∀ (x : U8) (y : U64), y = UScalar.cast UScalarTy.U64 x → y.val = x.val := by
    intro x y hy; rw [hy, UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by have := x.hBounds; simp [UScalarTy.numBits] at *; omega)
  have hi2 : i2.val = i.val / 16 := by rw [i2_post, cast_u64_of_usize, i1_post]
  rw [hi2] at hrb
  have hoff : offset.val = i.val % 16 * 2 := by rw [offset_post, i3_post]
  have hoff30 : offset.val ≤ 30 := by omega
  have s1 := or_shift_step i5.val i7.val 8 (by rw [hc _ _ i5_post]; exact u8_lt i4) (u8_lt i7)
    (by norm_num)
  rw [UScalar.val_or, i9_post1, hc _ _ i8_post, s1.1, hc _ _ i5_post, ← hrb, ← hoff]
  have hlen : (u8s rb.val).length = 32 := by simp [u8s]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by rw [hlen]; omega)]
  simp [Spec.leNat, u8s, i4_post, i7_post, i6_post]
  ring

end EpochProofs
