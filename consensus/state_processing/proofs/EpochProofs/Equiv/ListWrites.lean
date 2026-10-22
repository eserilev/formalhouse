import EpochProofs.Trusted.EpochTail
import EpochProofs.Equiv.DepositWrites
import EpochProofs.Equiv.BuilderPendingPayments
import EpochProofs.Equiv.EpochCommittees
import EpochProofs.Sanity.PtcIndices

namespace EpochProofs

namespace Spec

theorem cbws_loop_length (p : Preset) (o : Oracle) (indices : List ValidatorIndex) (seed : Bytes32)
    (size : Uint64) (sh : Bool) (total : Uint64) (ebs : List Gwei) :
    ∀ (fuel : Nat) (selected : List ValidatorIndex) (i : Uint64) (rb : Bytes32)
      (res : List ValidatorIndex),
      compute_balance_weighted_selection_loop p o indices seed size sh total ebs fuel selected i
        rb = .ok res → selected.length ≤ size → res.length = size
  | 0, _, _, _, _, h, _ => by
    simp [compute_balance_weighted_selection_loop, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, selected, i, rb, res, h, hle => by
    unfold compute_balance_weighted_selection_loop at h
    split at h
    · rename_i hlt
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | contradiction
        | (apply cbws_loop_length p o indices seed size sh total ebs fuel _ _ _ res h
           simp_all only [pure, Except.pure, Except.ok.injEq]
           (try subst_vars)
           (try simp only [List.length_append, List.length_cons, List.length_nil])
           try omega)
    · rename_i hge
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      omega

theorem compute_balance_weighted_selection_length (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (size : Uint64) (sh : Bool)
    (res : List ValidatorIndex)
    (h : compute_balance_weighted_selection p o state indices seed size sh = .ok res) :
    res.length = size := by
  unfold compute_balance_weighted_selection at h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [pure, Except.pure, bind, Except.bind] at h
    split at h
    · contradiction
    · exact cbws_loop_length p o indices seed size sh _ _ _ [] 0 Bytes32.zero res h (by simp)

theorem compute_ptc_length (p : Preset) (o : Oracle) (state : BeaconState) (slot : Slot)
    (res : List ValidatorIndex) (h : compute_ptc p o state slot = .ok res) :
    res.length = p.PTC_SIZE := by
  rw [compute_ptc_eq] at h
  obtain ⟨epoch, -, h⟩ := specM_bind_ok h
  obtain ⟨sd, -, h⟩ := specM_bind_ok h
  obtain ⟨indices, -, h⟩ := specM_bind_ok h
  exact compute_balance_weighted_selection_length _ _ _ _ _ _ _ _ h

end Spec

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev LhLWError (E : Type) := per_epoch_processing.list_writes.ListWritesError E

/-! ## Builder pending payments -/

theorem push_withdrawals_loop_spec {S E : Type} (inst : LhPaymentWrites S E)
    (wview : S → List LhWithdrawal) (pview : S → List LhPayment)
    (hc : PaymentWritesContract inst wview pview) (ws : Slice LhWithdrawal)
    (w0 : List LhWithdrawal) (p0 : List LhPayment) (s : S) (i : Usize) (hi : i.val ≤ ws.length)
    (hw : wview s = w0 ++ ws.val.take i.val) (hp : pview s = p0) :
    per_epoch_processing.list_writes.push_withdrawals_loop inst s ws i ⦃ res =>
      ∃ s', res = (.Ok (), s') ∧ wview s' = w0 ++ ws.val ∧ pview s' = p0 ⦄ := by
  unfold per_epoch_processing.list_writes.push_withdrawals_loop
  apply loop.spec_decr_nat
    (measure := fun (x : S × Usize) => ws.length - x.2.val)
    (inv := fun (x : S × Usize) => x.2.val ≤ ws.length ∧
      wview x.1 = w0 ++ ws.val.take x.2.val ∧ pview x.1 = p0)
  · rintro ⟨s1, i1⟩ ⟨hi1, hw1, hp1⟩
    dsimp only at hi1 hw1 hp1 ⊢
    unfold per_epoch_processing.list_writes.push_withdrawals_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i1.val < ws.length := by scalar_tac
      have hiv : i1.val < ws.val.length := hil
      rw [slice_get_some ws i1 hiv, bind_tc_ok]
      dsimp only
      rw [withdrawal_clone, bind_tc_ok]
      obtain ⟨s2, hpush, hw2, hp2⟩ := hc.push_withdrawal s1 ws.val[i1.val]
      rw [hpush]
      simp only [bind_tc_ok, uncurry_apply_pair]
      have hmax : i1.val < Usize.max := by scalar_tac
      obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i1 hmax
      rw [hadd]
      simp only [bind_tc_ok, spec_ok]
      refine ⟨⟨by omega, ?_, by rw [hp2, hp1]⟩, by omega⟩
      rw [hw2, hw1, hi', List.take_succ_eq_append_getElem hiv, List.append_assoc]
    · rename_i hge
      have hiv : i1.val = ws.length := by scalar_tac
      simp only [spec_ok]
      refine ⟨s1, rfl, ?_, hp1⟩
      rw [hw1, hiv]
      simp
  · exact ⟨hi, hw, hp⟩

/-- `apply_builder_pending_payments` does what `lighthouseBuilderPendingPayments` models by hand,
under the trusted `PaymentWritesContract`. So `builder_pending_payments_equiv` now holds for the
Lighthouse code, not for a hand model. -/
theorem apply_builder_pending_payments_spec {S E : Type} (inst : LhPaymentWrites S E)
    (wview : S → List LhWithdrawal) (pview : S → List LhPayment)
    (hc : PaymentWritesContract inst wview pview) (s : S) (tab spe64 : U64) (spe : Usize)
    (hspe : spe.val ≤ (pview s).length) (pslice : Slice LhPayment) (hps : pslice.val = pview s) :
    per_epoch_processing.list_writes.apply_builder_pending_payments inst s tab spe64 spe 6#u64
      10#u64 ⦃ res => match res with
        | (.Ok _, s') => lighthouseBuilderPendingPayments tab spe64 spe pslice (wview s) =
            ok (.Ok (wview s', pview s'))
        | (.Err (.Arith e), _) => lighthouseBuilderPendingPayments tab spe64 spe pslice (wview s) =
            ok (.Err e)
        | (.Err (.State _), _) => False ⦄ := by
  obtain ⟨q, hq, -⟩ := spec_imp_exists (quorum_equiv
    { Spec.Preset.mainnet with SLOTS_PER_EPOCH := spe64.val } tab spe64 rfl)
  unfold per_epoch_processing.list_writes.apply_builder_pending_payments
    lighthouseBuilderPendingPayments
  rw [hq, bind_tc_ok]
  cases q with
  | Err e =>
    simp only [spec_ok, bind_tc_ok]
  | Ok quorum =>
    simp only [bind_tc_ok]
    obtain ⟨v, hv, hvv⟩ := hc.payments s
    rw [hv]
    simp only [bind_tc_ok]
    have hslice : alloc.vec.Vec.deref v = pslice := by
      apply Subtype.ext
      simp [alloc.vec.Vec.deref, hvv, hps]
    rw [hslice]
    obtain ⟨res, hres, h1, h2⟩ := spec_imp_exists
      (process_builder_pending_payments_spec pslice spe quorum)
    rw [hres, bind_tc_ok]
    obtain ⟨wd, up⟩ := res
    simp only [uncurry_apply_pair] at h1 h2 ⊢
    unfold per_epoch_processing.list_writes.push_withdrawals
    apply spec_bind (push_withdrawals_loop_spec inst wview pview hc (alloc.vec.Vec.deref wd)
      (wview s) (pview s) s 0#usize (by simp) (by simp) rfl)
    rintro ⟨r, s1⟩ ⟨s1x, hx, hw1, hp1⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hr, hs⟩ := hx
    subst hs
    cases r with
    | Err e => cases hr
    | Ok u =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
      have hlen : up.val.length = (pview s1).length := by
        rw [h2, hp1, hps]
        simp only [List.length_append, List.length_drop, List.length_replicate]
        omega
      obtain ⟨s2, hset, hp2, hw2⟩ := hc.set_payments s1 up hlen
      rw [hset]
      simp only [bind_tc_ok, uncurry_apply_pair, spec_ok]
      rw [hp2, hw2, hw1]
      simp [alloc.vec.Vec.deref]

/-- `apply_builder_pending_payments` equals the spec `process_builder_pending_payments` on the
builder lists, under the trusted `PaymentWritesContract`. -/
theorem apply_builder_pending_payments_equiv {S E : Type} (p : Spec.Preset)
    (inst : LhPaymentWrites S E) (wview : S → List LhWithdrawal) (pview : S → List LhPayment)
    (hc : PaymentWritesContract inst wview pview) (s : S) (tab spe64 : U64) (spe : Usize)
    (hslots : spe64.val = p.SLOTS_PER_EPOCH) (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hlen : (pview s).length = 2 * p.SLOTS_PER_EPOCH) (pslice : Slice LhPayment)
    (hps : pslice.val = pview s) :
    per_epoch_processing.list_writes.apply_builder_pending_payments inst s tab spe64 spe 6#u64
      10#u64 ⦃ res => match res with
        | (.Ok _, s') => Spec.process_builder_pending_payments p tab.val
            (absState (wview s, pview s)) = .ok (absState (wview s', pview s'))
        | (.Err _, _) => ∃ e, Spec.process_builder_pending_payments p tab.val
            (absState (wview s, pview s)) = .error e ⦄ := by
  obtain ⟨r, hr, habs⟩ := spec_imp_exists (builder_pending_payments_equiv p tab spe64 spe hslots
    hspe pslice (wview s) (by rw [hps, hlen]))
  apply spec_mono (apply_builder_pending_payments_spec inst wview pview hc s tab spe64 spe
    (by omega) pslice hps)
  rintro ⟨res, s'⟩ h
  rw [hps] at habs
  cases res with
  | Ok u =>
    rw [hr] at h
    cases h
    rw [← habs]
    rfl
  | Err e =>
    cases e with
    | Arith e =>
      rw [hr] at h
      cases h
      exact ⟨absArithError e, by rw [← habs]; rfl⟩
    | State e => exact h.elim


/-! ## The effective balance updates after the consolidations -/

/-- What an effective balance loop returns, in spec terms. -/
def EbPost {S E : Type} (view : S → Spec.BeaconState) (spec : Spec.SpecM Spec.BeaconState) :
    core.result.Result Unit (LhLWError E) × S → Prop
  | (.Ok _, s') => spec = .ok (view s')
  | (.Err _, _) => ∃ e, spec = .error e

theorem update_effective_balances_at_loop_spec {S E : Type} (inst : LhEffectiveBalanceWrites S E)
    (view : S → Spec.BeaconState) (hc : EffectiveBalanceContract inst view)
    (idx : Slice Usize) (t0 : Spec.BeaconState) (s : S) (j : Usize) (hj : j.val ≤ idx.length)
    (hp : ((idx.val.map (·.val)).take j.val).foldlM Spec.ebUpdateAt t0 = .ok (view s)) :
    per_epoch_processing.list_writes.update_effective_balances_at_loop inst s idx j
      ⦃ res => EbPost view ((idx.val.map (·.val)).foldlM Spec.ebUpdateAt t0) res ⦄ := by
  unfold per_epoch_processing.list_writes.update_effective_balances_at_loop
  apply loop.spec_decr_nat
    (measure := fun (x : S × Usize) => idx.length - x.2.val)
    (inv := fun (x : S × Usize) => x.2.val ≤ idx.length ∧
      ((idx.val.map (·.val)).take x.2.val).foldlM Spec.ebUpdateAt t0 = .ok (view x.1))
  · rintro ⟨s1, j1⟩ ⟨hj1, hp1⟩
    dsimp only at hj1 hp1 ⊢
    unfold per_epoch_processing.list_writes.update_effective_balances_at_loop.body
    dsimp only
    split
    · rename_i hlt
      have hjl : j1.val < idx.length := by scalar_tac
      have hjv : j1.val < idx.val.length := hjl
      rw [slice_get_some idx j1 hjv, bind_tc_ok]
      dsimp only
      set x := idx.val[j1.val] with hxv
      have hml : j1.val < (idx.val.map (·.val)).length := by simpa using hjv
      have hget : (idx.val.map (·.val))[j1.val] = x.val := by simp [hxv]
      cases heb : Spec.ebUpdateAt (view s1) x.val with
      | ok t' =>
        obtain ⟨s', hu, hv⟩ := (hc.update_effective_balance s1 x).1 t' heb
        rw [hu]
        simp only [bind_tc_ok, uncurry_apply_pair]
        have hmax : j1.val < Usize.max := by scalar_tac
        obtain ⟨j', hadd, hj'⟩ := usize_safe_add_one j1 hmax
        rw [hadd]
        simp only [bind_tc_ok, spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hj', foldlM_take_succ _ _ _ _ hml, hp1, hget]
        show Spec.ebUpdateAt (view s1) x.val = _
        rw [heb, hv]
      | error e =>
        obtain ⟨e', s', hu⟩ := (hc.update_effective_balance s1 x).2 e heb
        rw [hu]
        simp only [bind_tc_ok, uncurry_apply_pair, spec_ok]
        refine ⟨e, ?_⟩
        apply foldlM_error_of_take _ _ _ _ _ hml hp1
        rw [hget]
        exact heb
    · rename_i hge
      have hjv : j1.val = idx.length := by scalar_tac
      simp only [spec_ok]
      show _ = _
      have h1 : (idx.val.map (·.val)).take j1.val = idx.val.map (·.val) := by
        rw [hjv]; simp
      rw [← h1, hp1]
  · exact ⟨hj, hp⟩

/-- The effective balance updates after the consolidations are the model step
`(consolidationIndices s).foldlM ebUpdateAt`, under the trusted `EffectiveBalanceContract`, when
the Rust indices are the model indices. Lighthouse collects them from a `BTreeSet`, which iterates
in ascending order without duplicates, as `consolidationIndices` sorts and removes duplicates. -/
theorem update_effective_balances_at_spec {S E : Type} (inst : LhEffectiveBalanceWrites S E)
    (view : S → Spec.BeaconState) (hc : EffectiveBalanceContract inst view) (s : S)
    (idx : Slice Usize) (named : List Nat) (hidx : idx.val.map (·.val) = named) :
    per_epoch_processing.list_writes.update_effective_balances_at inst s idx
      ⦃ res => EbPost view (named.foldlM Spec.ebUpdateAt (view s)) res ⦄ := by
  unfold per_epoch_processing.list_writes.update_effective_balances_at
  rw [← hidx]
  exact update_effective_balances_at_loop_spec inst view hc idx (view s) s 0#usize (by simp)
    (by simp [pure, Except.pure])


/-! ## The PTC window shift -/

theorem push_items_loop_spec {W T E α : Type} (inst : LhWindowWrites W T E)
    (view committed : W → List α) (absItem : T → α) (itemOk : T → Prop) (N : Nat)
    (hc : WindowContract inst view committed absItem itemOk N) (items : Slice T) (base : List α)
    (w : W) (i : Usize) (hi : i.val ≤ items.length)
    (hv : view w = base ++ (items.val.take i.val).map absItem)
    (hok : ∀ t ∈ items.val, itemOk t) (hN : base.length + items.length ≤ N) :
    per_epoch_processing.list_writes.push_items_loop inst w items i ⦃ res =>
      ∃ w', res = (.Ok (), w') ∧ view w' = base ++ items.val.map absItem ⦄ := by
  unfold per_epoch_processing.list_writes.push_items_loop
  apply loop.spec_decr_nat
    (measure := fun (x : W × Usize) => items.length - x.2.val)
    (inv := fun (x : W × Usize) => x.2.val ≤ items.length ∧
      view x.1 = base ++ (items.val.take x.2.val).map absItem)
  · rintro ⟨w1, i1⟩ ⟨hi1, hv1⟩
    dsimp only at hi1 hv1 ⊢
    unfold per_epoch_processing.list_writes.push_items_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i1.val < items.length := by scalar_tac
      have hiv : i1.val < items.val.length := hil
      rw [slice_get_some items i1 hiv, bind_tc_ok]
      dsimp only
      have hlt' : (view w1).length < N := by
        rw [hv1]
        simp only [List.length_append, List.length_map, List.length_take]
        have : items.length = items.val.length := rfl
        omega
      obtain ⟨w2, hpush, hv2⟩ := hc.push w1 items.val[i1.val]
        (hok _ (List.getElem_mem hiv)) hlt'
      rw [hpush]
      simp only [bind_tc_ok, uncurry_apply_pair]
      have hmax : i1.val < Usize.max := by scalar_tac
      obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i1 hmax
      rw [hadd]
      simp only [bind_tc_ok, spec_ok]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv2, hv1, hi', List.take_succ_eq_append_getElem hiv, List.map_append,
        List.append_assoc]
      rfl
    · rename_i hge
      have hiv : i1.val = items.length := by scalar_tac
      simp only [spec_ok]
      refine ⟨w1, rfl, ?_⟩
      rw [hv1, hiv]
      simp
  · exact ⟨hi, hv⟩

/-- `shift_window` drops the first `shift` entries, appends the items and writes the window back,
and returns `Ok`, when the window has its full length, the items replace exactly the dropped
entries and each item fits an entry. -/
theorem shift_window_spec {W T E α : Type} (inst : LhWindowWrites W T E)
    (view committed : W → List α) (absItem : T → α) (itemOk : T → Prop) (N : Nat)
    (hc : WindowContract inst view committed absItem itemOk N) (w : W) (shift : Usize)
    (items : Slice T) (hlen : (view w).length = N) (hshift : shift.val ≤ N)
    (hitems : items.length = shift.val) (hok : ∀ t ∈ items.val, itemOk t) :
    per_epoch_processing.list_writes.shift_window inst w shift items ⦃ res =>
      ∃ w', res = (.Ok (), w') ∧
        committed w' = (view w).drop shift.val ++ items.val.map absItem ⦄ := by
  unfold per_epoch_processing.list_writes.shift_window
  obtain ⟨w1, hpop, hv1⟩ := hc.pop_front w shift (by omega)
  rw [hpop]
  simp only [bind_tc_ok, uncurry_apply_pair]
  unfold per_epoch_processing.list_writes.push_items
  apply spec_bind (push_items_loop_spec inst view committed absItem itemOk N hc items
    ((view w).drop shift.val) w1 0#usize (by simp) (by simp [hv1]) hok
    (by simp only [List.length_drop]; omega))
  rintro ⟨r, w2⟩ ⟨w2x, hx, hv2⟩
  simp only [Prod.mk.injEq] at hx
  obtain ⟨hr, hs⟩ := hx
  subst hs
  cases r with
  | Err e => cases hr
  | Ok u =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    have hl2 : (view w2).length = N := by
      rw [hv2]
      simp only [List.length_append, List.length_drop, List.length_map]
      have : items.length = items.val.length := rfl
      omega
    obtain ⟨w3, hcom, hc3⟩ := hc.commit w2 hl2
    rw [hcom]
    simp only [bind_tc_ok, uncurry_apply_pair, spec_ok]
    exact ⟨w3, rfl, by rw [hc3, hv2]⟩

/-- The PTC window writes after `ptc_for_epoch`: when the spec `process_ptc_window` succeeds and
`ptc_for_epoch` returned its PTCs (`ptc_for_epoch_spec`), the window write succeeds and writes the
spec window. Each PTC has `PTC_SIZE` entries (`compute_ptc_length`), so each one fits. -/
theorem ptc_window_writes_spec {W E : Type} (p : Spec.Preset) (o : Spec.Oracle)
    (inst : LhWindowWrites W (alloc.vec.Vec Usize) E) (view committed : W → List (List Nat))
    (N : Nat)
    (hc : WindowContract inst view committed natsOf (fun t => (natsOf t).length = p.PTC_SIZE) N)
    (state state' : Spec.BeaconState) (hspec : Spec.process_ptc_window p o state = .ok state')
    (v : alloc.vec.Vec (alloc.vec.Vec Usize))
    (hv : state'.ptc_window = state.ptc_window.drop p.SLOTS_PER_EPOCH ++ ptcsOf v) (w : W)
    (hw : view w = state.ptc_window) (hN : state.ptc_window.length = N) (shift : Usize)
    (hshift : shift.val = p.SLOTS_PER_EPOCH) :
    per_epoch_processing.list_writes.shift_window inst w shift (alloc.vec.Vec.deref v) ⦃ res =>
      ∃ w', res = (.Ok (), w') ∧ committed w' = state'.ptc_window ⦄ := by
  obtain ⟨epoch, start, ptcs, -, -, -, hle, hw', hplen, hk⟩ :=
    spec_ptc_window_get p o state state' hspec
  have hpt : ptcsOf v = ptcs := by
    rw [hw'] at hv
    exact (List.append_cancel_left hv).symm
  have hvlen : v.val.length = p.SLOTS_PER_EPOCH := by
    have := congrArg List.length hpt
    simp only [ptcsOf, List.length_map] at this
    omega
  apply spec_mono (shift_window_spec inst view committed natsOf
    (fun t => (natsOf t).length = p.PTC_SIZE) N hc w shift (alloc.vec.Vec.deref v)
    (by rw [hw, hN]) (by omega) (by simp [alloc.vec.Vec.deref, Slice.length, hvlen, hshift])
    ?_)
  · rintro ⟨r, w3⟩ ⟨w4, hx, hc'⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨_, rfl, ?_⟩
    rw [hc', hw, hv, hshift]
    rfl
  · intro t ht
    simp only [alloc.vec.Vec.deref] at ht
    obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem ht
    have hkp : k < p.SLOTS_PER_EPOCH := by omega
    obtain ⟨hk2, hcp⟩ := hk k hkp
    have := Spec.compute_ptc_length p o state _ _ hcp
    have hk3 : (ptcsOf v)[k]'(by simp [ptcsOf]; omega) = ptcs[k] := by simp only [hpt]
    simp only [ptcsOf, List.getElem_map] at hk3
    show (natsOf v.val[k]).length = p.PTC_SIZE
    rw [hk3, this]

end EpochProofs
