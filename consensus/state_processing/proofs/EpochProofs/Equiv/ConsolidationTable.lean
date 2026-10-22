import EpochProofs.Trusted.Consolidations
import EpochProofs.Equiv.ListWrites

/-!
# Lighthouse pending consolidations glue equals the reference

`process_on_table_spec` relates `process_on_table` in `pending_consolidations.rs` to the spec
`process_pending_consolidations`. It assumes `ConsolidationStateContract` and that the table
indices are the `BTreeSet` iteration (`BTreeSetIter`). If the spec succeeds, Lighthouse succeeds
with the same state. If the spec fails, Lighthouse fails.

The pieces:

- `position_spec`: the binary search finds an index in a strictly increasing slice.
- `build_table_spec`: the table rows and balances are `tableRows` and `tableBalances`.
- `build_views_spec`: each pending consolidation becomes the pair of its table positions.
- `write_back_spec`: the write-back is `writeBack`.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-! ## Binary search -/

theorem usize_max_lt : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
  have := Nat.one_le_two_pow (n := UScalarTy.Usize.numBits)
  rw [Usize.max_def]; simp [Usize.numBits]

theorem usize_saturating_sub_val (a b : Usize) :
    (core.num.Usize.saturating_sub a b).val = a.val - b.val := by
  have hlt : a.val - b.val < 2 ^ UScalarTy.Usize.numBits := by
    have := a.hBounds; simp at this ⊢; omega
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val,
    BitVec.toNat_ofNat]
  simp only [UScalar.val] at hlt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem usize_saturating_add_val (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    (core.num.Usize.saturating_add a b).val = a.val + b.val := by
  have hmax := usize_max_lt
  have hmin : min (UScalar.max UScalarTy.Usize) (a.val + b.val) = a.val + b.val := by
    rw [UScalar.max_USize_eq]; omega
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add]
  rw [hmin]
  simp only [UScalar.val, BitVec.toNat_ofNat] at h hmin ⊢
  rw [Nat.mod_eq_of_lt (by omega)]

theorem position_loop_spec (sorted : Slice Usize) (x : Usize)
    (hs : (sorted.val.map (·.val)).Pairwise (· < ·)) (low high : Usize)
    (hlh : low.val ≤ high.val) (hhl : high.val ≤ sorted.val.length)
    (hlow : ∀ j (h : j < sorted.val.length), j < low.val → sorted.val[j].val < x.val)
    (hhigh : ∀ j (h : j < sorted.val.length), high.val ≤ j → x.val < sorted.val[j].val) :
    per_epoch_processing.pending_consolidations.position_loop sorted x low high ⦃ r =>
      (∀ k, r = some k → ∃ h : k.val < sorted.val.length, sorted.val[k.val].val = x.val) ∧
      (r = none → ∀ j (h : j < sorted.val.length), sorted.val[j].val ≠ x.val) ⦄ := by
  have hpair : ∀ i j (hi : i < sorted.val.length) (hj : j < sorted.val.length), i < j →
      sorted.val[i].val < sorted.val[j].val := by
    intro i j hi hj hij
    have := List.pairwise_iff_getElem.mp hs i j (by simpa using hi) (by simpa using hj) hij
    simpa using this
  unfold per_epoch_processing.pending_consolidations.position_loop
  apply loop.spec_decr_nat
    (measure := fun (y : Usize × Usize) => y.2.val - y.1.val)
    (inv := fun (y : Usize × Usize) => y.1.val ≤ y.2.val ∧ y.2.val ≤ sorted.val.length ∧
      (∀ j (h : j < sorted.val.length), j < y.1.val → sorted.val[j].val < x.val) ∧
      (∀ j (h : j < sorted.val.length), y.2.val ≤ j → x.val < sorted.val[j].val))
  · rintro ⟨lo, hi⟩ ⟨hlh1, hhl1, hlo1, hhi1⟩
    dsimp only at hlh1 hhl1 hlo1 hhi1 ⊢
    unfold per_epoch_processing.pending_consolidations.position_loop.body
    split
    · rename_i hlt
      have hlt' : lo.val < hi.val := by scalar_tac
      have hsub : (core.num.Usize.saturating_sub hi lo).val = hi.val - lo.val :=
        usize_saturating_sub_val hi lo
      simp only [lift, bind_tc_ok]
      have hdiv := Usize.div_spec (core.num.Usize.saturating_sub hi lo) (y := 2#usize) (by simp)
      obtain ⟨d, hd, hdv⟩ := spec_imp_exists hdiv
      rw [hd, bind_tc_ok]
      have hdv' : d.val = (hi.val - lo.val) / 2 := by rw [hdv, hsub]; rfl
      have hmidv : (core.num.Usize.saturating_add lo d).val = lo.val + (hi.val - lo.val) / 2 := by
        have hhim : hi.val ≤ Usize.max := by scalar_tac
        rw [usize_saturating_add_val lo d (by omega), hdv']
      generalize hmid : core.num.Usize.saturating_add lo d = mid at hmidv
      have hmidl : mid.val < sorted.val.length := by
        have : (hi.val - lo.val) / 2 < hi.val - lo.val := Nat.div_lt_self (by omega) (by omega)
        omega
      rw [slice_get_some sorted mid hmidl, bind_tc_ok]
      dsimp only
      split
      · rename_i heq
        simp only [spec_ok]
        refine ⟨fun k hk => ?_, fun h => by simp at h⟩
        simp only [Option.some.injEq] at hk
        subst hk
        exact ⟨hmidl, by rw [heq]⟩
      · rename_i hne
        have hne' : sorted.val[mid.val].val ≠ x.val := by
          intro h; apply hne; exact UScalar.eq_of_val_eq h
        split
        · rename_i hlt2
          have hlt2' : sorted.val[mid.val].val < x.val := by scalar_tac
          have hsat : (core.num.Usize.saturating_add mid 1#usize).val = mid.val + 1 :=
            usize_saturating_add_one mid (by have := sorted.property; scalar_tac)
          simp only [spec_ok, hsat]
          refine ⟨⟨by omega, hhl1, fun j hj hjl => ?_, hhi1⟩, by omega⟩
          by_cases hjm : j = mid.val
          · subst hjm; exact hlt2'
          · by_cases hjlo : j < lo.val
            · exact hlo1 j hj hjlo
            · have := hpair j mid.val hj hmidl (by omega); omega
        · rename_i hge2
          have hgt : x.val < sorted.val[mid.val].val := by
            have : ¬ sorted.val[mid.val].val < x.val := by scalar_tac
            omega
          simp only [spec_ok]
          refine ⟨⟨by omega, by omega, hlo1, fun j hj hjh => ?_⟩, by omega⟩
          by_cases hjm : j = mid.val
          · subst hjm; exact hgt
          · by_cases hjhi : hi.val ≤ j
            · exact hhi1 j hj hjhi
            · have := hpair mid.val j hmidl hj (by omega); omega
    · rename_i hge
      have hge' : hi.val ≤ lo.val := by scalar_tac
      simp only [spec_ok]
      refine ⟨fun k hk => by simp at hk, fun _ j hj => ?_⟩
      by_cases hjl : j < lo.val
      · have := hlo1 j hj hjl; omega
      · have := hhi1 j hj (by omega); omega
  · exact ⟨hlh, hhl, hlow, hhigh⟩

theorem position_spec (sorted : Slice Usize) (x : Usize)
    (hs : (sorted.val.map (·.val)).Pairwise (· < ·)) :
    per_epoch_processing.pending_consolidations.position sorted x ⦃ r =>
      (∀ k, r = some k → ∃ h : k.val < sorted.val.length, sorted.val[k.val].val = x.val) ∧
      (r = none → ∀ j (h : j < sorted.val.length), sorted.val[j].val ≠ x.val) ⦄ := by
  unfold per_epoch_processing.pending_consolidations.position
  exact position_loop_spec sorted x hs 0#usize (Slice.len sorted) (by simp) (by simp)
    (fun j _ hj => by simp at hj) (fun j hj hjl => by simp at hjl; omega)

/-! ## The table -/

theorem build_table_loop_spec {S E : Type} (inst : LhConsolidationState S E) (p : Spec.Preset)
    (view : S → Spec.BeaconState) (hc : ConsolidationStateContract inst p view) (s : S)
    (idx : Slice Usize) (vals : alloc.vec.Vec LhLocalValidator) (bals : alloc.vec.Vec U64)
    (k : Usize) (hk : k.val ≤ idx.val.length)
    (hv : vals.val.map absLocal =
      Spec.tableRows (view s).validators ((idx.val.take k.val).map (·.val)))
    (hb : bals.val.map (·.val) =
      Spec.tableBalances (view s).balances ((idx.val.take k.val).map (·.val))) :
    per_epoch_processing.pending_consolidations.build_table_loop inst s idx vals bals k ⦃ r =>
      r.1.val.map absLocal = Spec.tableRows (view s).validators (idx.val.map (·.val)) ∧
      r.2.val.map (·.val) = Spec.tableBalances (view s).balances (idx.val.map (·.val)) ⦄ := by
  unfold per_epoch_processing.pending_consolidations.build_table_loop
  apply loop.spec_decr_nat
    (measure := fun (y : alloc.vec.Vec LhLocalValidator × alloc.vec.Vec U64 × Usize) =>
      idx.val.length - y.2.2.val)
    (inv := fun (y : alloc.vec.Vec LhLocalValidator × alloc.vec.Vec U64 × Usize) =>
      y.2.2.val ≤ idx.val.length ∧
      y.1.val.map absLocal =
        Spec.tableRows (view s).validators ((idx.val.take y.2.2.val).map (·.val)) ∧
      y.2.1.val.map (·.val) =
        Spec.tableBalances (view s).balances ((idx.val.take y.2.2.val).map (·.val)))
  · rintro ⟨vs1, bs1, k1⟩ ⟨hk1, hv1, hb1⟩
    dsimp only at hk1 hv1 hb1 ⊢
    unfold per_epoch_processing.pending_consolidations.build_table_loop.body
    dsimp only
    split
    · rename_i hlt
      have hkl : k1.val < idx.val.length := by scalar_tac
      rw [slice_get_some idx k1 hkl, bind_tc_ok]
      dsimp only
      obtain ⟨lv, hlv, hlva⟩ := hc.local_validator s idx.val[k1.val]
      rw [hlv, bind_tc_ok]
      have hvlen : vs1.val.length = k1.val := by
        have := congrArg List.length hv1
        simpa [Spec.tableRows, Nat.min_eq_left hk1] using this
      have hblen : bs1.val.length = k1.val := by
        have := congrArg List.length hb1
        simpa [Spec.tableBalances, Nat.min_eq_left hk1] using this
      have hmax : k1.val < Usize.max := by have := idx.property; scalar_tac
      obtain ⟨vs2, hpv, hvs2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec vs1 lv (by omega))
      rw [hpv, bind_tc_ok]
      obtain ⟨b, hbal, hbv⟩ := hc.balance s idx.val[k1.val]
      rw [hbal, bind_tc_ok]
      obtain ⟨bs2, hpb, hbs2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec bs1 b (by omega))
      rw [hpb, bind_tc_ok]
      have hsat := usize_saturating_add_one k1 hmax
      simp only [lift, bind_tc_ok, uncurry_apply_pair, spec_ok]
      rw [hsat]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hvs2, List.map_append, hv1]
        simp only [Spec.tableRows, List.map_take, List.map_map, List.map_cons, List.map_nil, hlva]
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
      · rw [hbs2, List.map_append, hb1]
        simp only [Spec.tableBalances, List.map_take, List.map_map, List.map_cons, List.map_nil,
          hbv]
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hkl]
        rfl
    · rename_i hge
      have hkl : k1.val = idx.val.length := by scalar_tac
      simp only [spec_ok]
      rw [hkl, List.take_length] at hv1 hb1
      exact ⟨hv1, hb1⟩
  · exact ⟨hk, hv, hb⟩

theorem build_table_spec {S E : Type} (inst : LhConsolidationState S E) (p : Spec.Preset)
    (view : S → Spec.BeaconState) (hc : ConsolidationStateContract inst p view) (s : S)
    (idx : Slice Usize) :
    per_epoch_processing.pending_consolidations.build_table inst s idx ⦃ r =>
      r.1.val.map absLocal = Spec.tableRows (view s).validators (idx.val.map (·.val)) ∧
      r.2.val.map (·.val) = Spec.tableBalances (view s).balances (idx.val.map (·.val)) ⦄ := by
  unfold per_epoch_processing.pending_consolidations.build_table
  exact build_table_loop_spec inst p view hc s idx _ _ 0#usize (by simp)
    (by simp [Spec.tableRows, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
    (by simp [Spec.tableBalances, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])

/-! ## The views -/

theorem cast_usize_u64 (hus : Usize.max = U64.max) (x : U64) :
    (UScalar.cast UScalarTy.Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h1 := usize_max_lt
  have h2 : x.val ≤ U64.max := by scalar_tac
  have h3 : Usize.max + 1 = 2 ^ UScalarTy.Usize.numBits := by
    have := Nat.one_le_two_pow (n := System.Platform.numBits)
    rw [Usize.max_def]; simp [Usize.numBits]; try omega
  omega

/-- The table position of each pending consolidation. -/
def tablePairs (idx : List Nat) (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map fun q => (idx.idxOf q.1, idx.idxOf q.2)

theorem position_found (idx : Slice Usize) (hs : (idx.val.map (·.val)).Pairwise (· < ·))
    (x : Usize) (r : Option Usize)
    (hr : (∀ k, r = some k → ∃ h : k.val < idx.val.length, idx.val[k.val].val = x.val) ∧
      (r = none → ∀ j (h : j < idx.val.length), idx.val[j].val ≠ x.val))
    (hx : x.val ∈ idx.val.map (·.val)) :
    ∃ k, r = some k ∧ k.val = (idx.val.map (·.val)).idxOf x.val := by
  cases r with
  | none =>
    exfalso
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    simp only [List.length_map] at hj
    exact hr.2 rfl j hj (by simpa using hjx)
  | some k =>
    obtain ⟨hk, hkx⟩ := hr.1 k rfl
    refine ⟨k, rfl, ?_⟩
    have hnd : (idx.val.map (·.val)).Nodup := hs.nodup
    have hkm : k.val < (idx.val.map (·.val)).length := by simpa using hk
    have := List.Nodup.idxOf_getElem hnd k.val hkm
    simp only [List.getElem_map, hkx] at this
    exact this.symm

theorem build_views_loop_spec (hus : Usize.max = U64.max) (pairs : Slice LhPendingPair)
    (idx : Slice Usize) (hs : (idx.val.map (·.val)).Pairwise (· < ·))
    (hin : ∀ q ∈ pairs.val, q.source.val ∈ idx.val.map (·.val) ∧
      q.target.val ∈ idx.val.map (·.val))
    (views : alloc.vec.Vec LhConsolidationView) (i : Usize) (hi : i.val ≤ pairs.val.length)
    (hv : views.val.map absView = tablePairs (idx.val.map (·.val))
      ((pairs.val.take i.val).map fun q => (q.source.val, q.target.val))) :
    per_epoch_processing.pending_consolidations.build_views_loop pairs idx views i ⦃ r =>
      r.2 = none ∧ r.1.val.map absView = tablePairs (idx.val.map (·.val))
        (pairs.val.map fun q => (q.source.val, q.target.val)) ⦄ := by
  unfold per_epoch_processing.pending_consolidations.build_views_loop
  apply loop.spec_decr_nat
    (measure := fun (y : alloc.vec.Vec LhConsolidationView × Usize) =>
      pairs.val.length - y.2.val)
    (inv := fun (y : alloc.vec.Vec LhConsolidationView × Usize) =>
      y.2.val ≤ pairs.val.length ∧
      y.1.val.map absView = tablePairs (idx.val.map (·.val))
        ((pairs.val.take y.2.val).map fun q => (q.source.val, q.target.val)))
  · rintro ⟨vw1, i1⟩ ⟨hi1, hv1⟩
    dsimp only at hi1 hv1 ⊢
    unfold per_epoch_processing.pending_consolidations.build_views_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i1.val < pairs.val.length := by scalar_tac
      rw [slice_get_some pairs i1 hil, bind_tc_ok]
      dsimp only
      obtain ⟨hsrc, htgt⟩ := hin pairs.val[i1.val] (List.getElem_mem hil)
      simp only [lift, bind_tc_ok]
      generalize hcs : UScalar.cast UScalarTy.Usize pairs.val[i1.val].source = cs
      generalize hct : UScalar.cast UScalarTy.Usize pairs.val[i1.val].target = ct
      have hcsv : cs.val = pairs.val[i1.val].source.val := by rw [← hcs, cast_usize_u64 hus]
      have hctv : ct.val = pairs.val[i1.val].target.val := by rw [← hct, cast_usize_u64 hus]
      obtain ⟨o1, ho1, hpo1⟩ := spec_imp_exists (position_spec idx cs hs)
      rw [ho1, bind_tc_ok]
      obtain ⟨k1, rfl, hk1⟩ := position_found idx hs cs o1 hpo1 (by rw [hcsv]; exact hsrc)
      dsimp only
      obtain ⟨o2, ho2, hpo2⟩ := spec_imp_exists (position_spec idx ct hs)
      rw [ho2, bind_tc_ok]
      obtain ⟨k2, rfl, hk2⟩ := position_found idx hs ct o2 hpo2 (by rw [hctv]; exact htgt)
      dsimp only
      have hvlen : vw1.val.length = i1.val := by
        have := congrArg List.length hv1
        simpa [tablePairs, Nat.min_eq_left hi1] using this
      have hmax : i1.val < Usize.max := by have := pairs.property; scalar_tac
      obtain ⟨vw2, hpv, hvw2⟩ := spec_imp_exists
        (alloc.vec.Vec.push_spec vw1 ({ source := k1, target := k2 } : LhConsolidationView)
          (by omega))
      rw [hpv, bind_tc_ok]
      have hsat := usize_saturating_add_one i1 hmax
      simp only [lift, bind_tc_ok, spec_ok]
      try dsimp only
      rw [hsat]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hvw2, List.map_append, hv1]
      simp only [tablePairs, List.map_take, List.map_map, List.map_cons, List.map_nil]
      rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hil]
      simp [absView, hk1, hk2, hcsv, hctv]
    · rename_i hge
      have hil : i1.val = pairs.val.length := by scalar_tac
      simp only [spec_ok]
      rw [hil, List.take_length] at hv1
      exact ⟨by simp, hv1⟩
  · exact ⟨hi, hv⟩

theorem build_views_spec (hus : Usize.max = U64.max) (pairs : Slice LhPendingPair)
    (idx : Slice Usize) (hs : (idx.val.map (·.val)).Pairwise (· < ·))
    (hin : ∀ q ∈ pairs.val, q.source.val ∈ idx.val.map (·.val) ∧
      q.target.val ∈ idx.val.map (·.val)) :
    per_epoch_processing.pending_consolidations.build_views pairs idx ⦃ r =>
      ∃ views, r = .Ok views ∧ views.val.map absView = tablePairs (idx.val.map (·.val))
        (pairs.val.map fun q => (q.source.val, q.target.val)) ⦄ := by
  unfold per_epoch_processing.pending_consolidations.build_views
  dsimp only
  apply exists_imp_spec
  obtain ⟨r, hr, hnone, hviews⟩ := spec_imp_exists (build_views_loop_spec hus pairs idx hs hin
    (alloc.vec.Vec.with_capacity LhConsolidationView (Slice.len pairs)) 0#usize (by simp)
    (by simp [tablePairs, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]))
  rw [hr]
  obtain ⟨vw, o⟩ := r
  dsimp only at hnone hviews
  subst hnone
  exact ⟨_, rfl, vw, rfl, hviews⟩

/-! ## The write-back -/

theorem writeBack_snoc (bs : List Spec.Gwei) (l m : List Nat) (hl : l.length = m.length)
    (i b : Nat) :
    Spec.writeBack bs (l ++ [i]) (m ++ [b]) =
      if i < (Spec.writeBack bs l m).length then (Spec.writeBack bs l m).set i b
      else Spec.writeBack bs l m := by
  unfold Spec.writeBack
  rw [List.zip_append hl, List.foldl_append]
  rfl

theorem write_back_loop_spec {S E : Type} (inst : LhConsolidationState S E) (p : Spec.Preset)
    (view : S → Spec.BeaconState) (hc : ConsolidationStateContract inst p view)
    (idx : Slice Usize) (bals : Slice U64) (hlen : bals.val.length = idx.val.length)
    (s0 st : S) (k : Usize) (hk : k.val ≤ idx.val.length)
    (hv : view st = { view s0 with balances := (Spec.writeBack (view s0).balances
      ((idx.val.take k.val).map (·.val)) ((bals.val.take k.val).map (·.val))) }) :
    per_epoch_processing.pending_consolidations.write_back_loop inst st idx bals k ⦃ r =>
      view r = { view s0 with balances := (Spec.writeBack (view s0).balances
        (idx.val.map (·.val)) (bals.val.map (·.val))) } ⦄ := by
  unfold per_epoch_processing.pending_consolidations.write_back_loop
  apply loop.spec_decr_nat
    (measure := fun (y : S × Usize) => idx.val.length - y.2.val)
    (inv := fun (y : S × Usize) => y.2.val ≤ idx.val.length ∧
      view y.1 = { view s0 with balances := (Spec.writeBack (view s0).balances
        ((idx.val.take y.2.val).map (·.val)) ((bals.val.take y.2.val).map (·.val))) })
  · rintro ⟨st1, k1⟩ ⟨hk1, hv1⟩
    dsimp only at hk1 hv1 ⊢
    unfold per_epoch_processing.pending_consolidations.write_back_loop.body
    dsimp only
    split
    · rename_i hlt
      have hkl : k1.val < idx.val.length := by scalar_tac
      have hkb : k1.val < bals.val.length := by omega
      rw [slice_get_some idx k1 hkl, bind_tc_ok]
      dsimp only
      rw [slice_get_some bals k1 hkb, bind_tc_ok]
      dsimp only
      obtain ⟨st2, hset, hv2⟩ := hc.set_balance st1 idx.val[k1.val] bals.val[k1.val]
      rw [hset, bind_tc_ok]
      have hmax : k1.val < Usize.max := by have := idx.property; scalar_tac
      have hsat := usize_saturating_add_one k1 hmax
      simp only [lift, bind_tc_ok, uncurry_apply_pair, spec_ok]
      rw [hsat]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv2, hv1]
      simp only
      rw [List.take_succ_eq_append_getElem (l := idx.val) hkl,
        List.take_succ_eq_append_getElem (l := bals.val) hkb, List.map_append, List.map_append,
        List.map_singleton, List.map_singleton,
        writeBack_snoc _ _ _ (by simp [Nat.min_eq_left hk1, Nat.min_eq_left (by omega : k1.val ≤ bals.val.length)])]
    · rename_i hge
      have hkl : k1.val = idx.val.length := by scalar_tac
      simp only [spec_ok]
      rw [hv1, hkl, List.take_length, List.take_of_length_le (by omega)]
  · exact ⟨hk, hv⟩

theorem write_back_spec {S E : Type} (inst : LhConsolidationState S E) (p : Spec.Preset)
    (view : S → Spec.BeaconState) (hc : ConsolidationStateContract inst p view)
    (idx : Slice Usize) (bals : Slice U64) (hlen : bals.val.length = idx.val.length) (s : S) :
    per_epoch_processing.pending_consolidations.write_back inst s idx bals ⦃ r =>
      view r = { view s with balances := (Spec.writeBack (view s).balances
        (idx.val.map (·.val)) (bals.val.map (·.val))) } ⦄ := by
  unfold per_epoch_processing.pending_consolidations.write_back
  exact write_back_loop_spec inst p view hc idx bals hlen s s 0#usize (by simp)
    (by simp [Spec.writeBack])

/-! ## The whole step -/

theorem specNextEpoch_bind {α : Type} (p : Spec.Preset) (state : Spec.BeaconState)
    (f : Nat → Spec.SpecM α) :
    (do let next_epoch ← Spec.uint64Add (← Spec.get_current_epoch p state) 1; f next_epoch) =
      (specNextEpoch p state >>= f) := by
  simp only [specNextEpoch, bind_assoc]

theorem btreeSetIter_consolidationIndices (state : Spec.BeaconState) (it : List Nat)
    (h : BTreeSetIter (state.pending_consolidations.flatMap
      fun c => [c.source_index, c.target_index]) it) :
    it = Spec.consolidationIndices state := by
  apply Spec.consolidationIndices_eq_of_sorted state it h.1
  intro x
  rw [h.2]
  simp [List.mem_flatMap, eq_comm]

/-- Lighthouse's pending consolidations step equals the spec `process_pending_consolidations`:
if the spec succeeds, Lighthouse succeeds with the same state, and if the spec fails, Lighthouse
fails. -/
theorem process_on_table_spec {S E : Type} (inst : LhConsolidationState S E) (p : Spec.Preset)
    (view : S → Spec.BeaconState) (hc : ConsolidationStateContract inst p view)
    (hus : Usize.max = U64.max) (s : S) (idx : Slice Usize)
    (hidx : BTreeSetIter ((view s).pending_consolidations.flatMap
      fun c => [c.source_index, c.target_index]) (idx.val.map (·.val)))
    (hlen : (view s).balances.length = (view s).validators.length) :
    per_epoch_processing.pending_consolidations.process_on_table inst s idx ⦃ r =>
      (∀ t, Spec.process_pending_consolidations p (view s) = .ok t →
        r.1 = .Ok () ∧ view r.2 = t) ∧
      (∀ e, Spec.process_pending_consolidations p (view s) = .error e →
        ∃ e', r.1 = .Err e') ⦄ := by
  have hidxN := btreeSetIter_consolidationIndices (view s) _ hidx
  have hnd : (idx.val.map (·.val)).Nodup := hidx.1.nodup
  have hin : Spec.PairsIn (idx.val.map (·.val)) (pendingPairs (view s)) := by
    rw [hidxN]; exact Spec.pairsIn_consolidationIndices (view s)
  rw [Spec.process_pending_consolidations_eq p (view s) hlen, specNextEpoch_bind]
  unfold per_epoch_processing.pending_consolidations.process_on_table
  cases hse : specNextEpoch p (view s) with
  | error e =>
    obtain ⟨e', hn⟩ := (hc.next_epoch s).2 e hse
    rw [hn, bind_tc_ok]
    simp only [spec_ok]
    exact ⟨(fun t ht => by cases ht), fun _ _ => ⟨_, rfl⟩⟩
  | ok ne =>
    have hok : ∀ {β : Type} (f : Nat → Spec.SpecM β), ((Except.ok ne : Spec.SpecM Nat) >>= f) = f ne :=
      fun _ => rfl
    simp only [hok]
    obtain ⟨v, hn, hvv⟩ := (hc.next_epoch s).1 ne hse
    rw [hn, bind_tc_ok]
    dsimp only
    obtain ⟨pv, hp, hpv⟩ := hc.pending s
    rw [hp, bind_tc_ok]
    dsimp only
    obtain ⟨tbl, htbl, htv, htb⟩ := spec_imp_exists (build_table_spec inst p view hc s idx)
    rw [htbl, bind_tc_ok]
    obtain ⟨vals, bals⟩ := tbl
    dsimp only at htv htb
    simp only [uncurry_apply_pair]
    have hin' : ∀ q ∈ (alloc.vec.Vec.deref pv).val, q.source.val ∈ idx.val.map (·.val) ∧
        q.target.val ∈ idx.val.map (·.val) := by
      intro q hq
      have hqm : (q.source.val, q.target.val) ∈ pendingPairs (view s) := by
        rw [← hpv]; exact List.mem_map_of_mem hq
      exact hin _ hqm
    obtain ⟨rv, hrv, views, rfl, hviews⟩ := spec_imp_exists
      (build_views_spec hus (alloc.vec.Vec.deref pv) idx hidx.1 hin')
    rw [hrv, bind_tc_ok]
    dsimp only
    have hlenvb : bals.val.length = vals.val.length := by
      have h1 := congrArg List.length htv
      have h2 := congrArg List.length htb
      simp [Spec.tableRows, Spec.tableBalances] at h1 h2
      omega
    obtain ⟨r3, hr3, habs⟩ := spec_imp_exists (process_pending_consolidations_equiv
      (alloc.vec.Vec.deref views) (alloc.vec.Vec.deref vals) bals v hlenvb)
    rw [hr3, bind_tc_ok]
    have hviews' : (alloc.vec.Vec.deref views).val.map absView =
        (pendingPairs (view s)).map fun q =>
          ((idx.val.map (·.val)).idxOf q.1, (idx.val.map (·.val)).idxOf q.2) := by
      show views.val.map absView = _
      rw [hviews, ← hpv]
      simp [tablePairs, alloc.vec.Vec.deref]
    have hloop := Spec.stepLoop_table (vs := (view s).validators) hnd ne (pendingPairs (view s))
      hin (view s).balances hlen 0
    have htv' : (alloc.vec.Vec.deref vals).val.map absLocal =
        Spec.tableRows (view s).validators (idx.val.map (·.val)) := htv
    rw [htv', htb, hviews', hvv] at habs
    rw [show (Spec.tableBalances (view s).balances (idx.val.map (·.val)), 0) =
      Spec.toTable (idx.val.map (·.val)) ((view s).balances, 0) from rfl, hloop] at habs
    simp only [pendingPairs] at habs
    cases hfull : Spec.stepLoop (Spec.consolidationStep ((view s).validators.map Spec.globalLocal)
        ne) ((view s).balances, 0)
        ((view s).pending_consolidations.map fun c => (c.source_index, c.target_index)) with
    | error e =>
      rw [hfull] at habs
      cases r3 with
      | Ok res => simp [absConsolidations, Except.map, Functor.map] at habs
      | Err ce =>
        cases ce with
        | UnknownValidator pos =>
          dsimp only
          simp only [slice_get_any, bind_tc_ok]
          cases hpos : idx.val[pos.val]? <;>
            simp only [spec_ok] <;>
            exact ⟨(fun t ht => by cases ht), fun _ _ => ⟨_, rfl⟩⟩
        | Overflow =>
          simp only [spec_ok]
          exact ⟨(fun t ht => by cases ht), fun _ _ => ⟨_, rfl⟩⟩
    | ok rr =>
      rw [hfull] at habs
      cases r3 with
      | Err ce => simp [absConsolidations, Except.map, Functor.map] at habs
      | Ok res =>
        obtain ⟨nxt, nb⟩ := res
        simp only [absConsolidations, Except.map, Functor.map, Except.ok.injEq] at habs
        obtain ⟨hnb, hnxt⟩ := Prod.mk.inj habs
        simp only [uncurry_apply_pair]
        have hnblen : (alloc.vec.Vec.deref nb).val.length = idx.val.length := by
          have := congrArg List.length hnb
          simp [Spec.toTable, Spec.tableBalances] at this
          simpa [alloc.vec.Vec.deref] using this
        obtain ⟨s2, hwb, hv2⟩ := spec_imp_exists (write_back_spec inst p view hc idx
          (alloc.vec.Vec.deref nb) hnblen s)
        rw [hwb, bind_tc_ok]
        have hag := Spec.stepLoop_agreeOut (vs := (view s).validators)
          (idx := idx.val.map (·.val)) ne _ hin (view s).balances (view s).balances 0 hlen
          ⟨rfl, fun _ _ => rfl⟩ hfull
        have hnbv : (alloc.vec.Vec.deref nb).val.map (·.val) =
            Spec.tableBalances rr.1.1 (idx.val.map (·.val)) := by
          simpa [Spec.toTable, alloc.vec.Vec.deref] using hnb
        rw [hnbv, Spec.writeBack_table hnd hag] at hv2
        have hcount := Spec.stepLoop_count ne _ _ hfull
        have hle : nxt.val ≤ (view s2).pending_consolidations.length := by
          rw [hv2]; simp at hcount ⊢; omega
        obtain ⟨s3, hpop, hv3⟩ := hc.pop_pending s2 nxt hle
        rw [hpop]
        simp only [bind_tc_ok, spec_ok]
        refine ⟨fun t ht => ?_, fun e he => by cases he⟩
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at ht
        refine ⟨rfl, ?_⟩
        rw [hv3, hv2, ← ht, hnxt]

end EpochProofs

