import EpochProofs.Trusted.EpochTail
import EpochProofs.Spec.PresetCfg
import EpochProofs.Equiv.SinglePassLoop
import EpochProofs.Equiv.Justification

/-!
# The deposit writes after the single pass

`apply_deposit_writes` in `deposit_writes.rs` writes the deposit queue, applies the new validator
deposits and runs the effective balance update of each new validator. `apply_deposit_writes_spec`
shows that, under the trusted `DepositWritesContract`, it returns `Ok` exactly when
`depositWritesSpec` returns `ok`, with the same state. `depositWritesSpec` is the part of the
Lighthouse model from the deposit queue write to the effective balance updates of the new
validators (`lhNewValidators` after `lhQueueWrite`, `LighthouseOrder.lean`).

The proof covers each error site of the Rust: a failed read or write of the state, a balance
overflow and an index overflow. Each one returns `Err` only when the spec fails too.
-/

namespace EpochProofs

namespace Spec

/-- The model from the deposit queue write to the effective balance updates of the new
validators. -/
def depositWritesSpec [PresetCfg] (o : Oracle) (t : BeaconState) (next : Nat) (dbtc : Gwei)
    (post news : List PendingDeposit) (eb : Bool) : SpecM BeaconState := do
  let t2 := { t with
    pending_deposits := t.pending_deposits.drop next ++ post
    deposit_balance_to_consume := dbtc }
  let t3 ← news.foldlM (apply_pending_deposit P o) t2
  if eb then
    (List.range' t2.validators.length (t3.validators.length - t2.validators.length)).foldlM
      ebUpdateAt t3
  else pure t3

theorem depositWritesSpec_eq (o : Oracle) (s t : BeaconState) (plan : LhDepositPlan)
    (h : t.pending_deposits = s.pending_deposits) :
    depositWritesSpec o t plan.next_deposit_index plan.deposit_balance_to_consume plan.postponed
        plan.new_validator_deposits true =
      lhNewValidators o plan (lhQueueWrite s plan t) := by
  simp only [depositWritesSpec, lhNewValidators, lhApplyPendingDeposit_mainnet, lhQueueWrite, h,
    if_true]

theorem add_validator_to_registry_len (p : Preset) (t t' : BeaconState) (pubkey : BLSPubkey)
    (wc : Bytes32) (amount : Gwei)
    (h : add_validator_to_registry p t pubkey wc amount = .ok t') :
    t'.validators.length = t.validators.length + 1 := by
  unfold add_validator_to_registry get_index_for_new_validator at h
  cases hv : get_validator_from_deposit p pubkey wc amount with
  | error e => simp [hv, bind, Except.bind] at h
  | ok v =>
    simp only [hv, set_or_append_list_len, bind, Except.bind, pure, Except.pure] at h
    revert h
    repeat' split
    all_goals intro h
    all_goals first
      | (simp only [reduceCtorEq] at h)
      | (cases h; simp)

theorem apply_pending_deposit_known [PresetCfg] (o : Oracle) (t : BeaconState) (d : PendingDeposit)
    (hm : d.pubkey ∈ t.validators.map (·.pubkey)) :
    apply_pending_deposit P o t d = (do
      let b ← listGet t.balances ((t.validators.map (·.pubkey)).idxOf d.pubkey)
      let c ← uint64Add b d.amount
      let bs ← listSet t.balances ((t.validators.map (·.pubkey)).idxOf d.pubkey) c
      pure { t with balances := bs }) := by
  simp only [apply_pending_deposit, hm, not_true_eq_false, if_false, increase_balance,
    bind_assoc]

theorem apply_pending_deposit_new [PresetCfg] (o : Oracle) (t : BeaconState) (d : PendingDeposit)
    (hm : d.pubkey ∉ t.validators.map (·.pubkey)) :
    apply_pending_deposit P o t d =
      if is_valid_deposit_signature P o d.pubkey d.withdrawal_credentials d.amount
          d.signature then
        add_validator_to_registry P t d.pubkey d.withdrawal_credentials d.amount
      else pure t := by
  simp only [apply_pending_deposit, hm, not_false_eq_true, if_true]

theorem foldlM_take_succ' {α β : Type} (f : β → α → SpecM β) (b x : β) (l : List α) (i : Nat)
    (hi : i < l.length) (hp : (l.take i).foldlM f b = .ok x) :
    (l.take (i + 1)).foldlM f b = f x l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldlM_append, hp]
  show List.foldlM f x [l[i]] = _
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases f x l[i] <;> rfl

theorem depositLoop_next_le [PresetCfg] (fs avail : Nat) :
    ∀ (vs : List DepositSpecView) (ls : DepositLoopState) (r : DepositLoopResult),
      depositLoop P fs avail ls vs = .ok r →
      r.state.next_deposit_index ≤ ls.next_deposit_index + vs.length
  | [], ls, r, h => by
    simp only [depositLoop, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | v :: vs, ls, r, h => by
    simp only [depositLoop] at h
    obtain ⟨r1, h1, h⟩ := specM_bind_ok h
    rcases depositStep_cases fs avail ls v r1 h1 with ⟨hs, hst⟩ | ⟨hs, -, hn1, -⟩
    · simp only [hs, if_true, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [hst]
      simp
    · simp only [hs, Bool.false_eq_true, if_false] at h
      have := depositLoop_next_le fs avail vs r1.state r h
      simp only [List.length_cons]
      omega

/-- The deposit plan never skips past the end of the queue, so the queue write after the single
pass succeeds. -/
theorem lhDepositPlan_next_le (s : BeaconState) (tab : Gwei) (current_epoch : Epoch)
    (plan : LhDepositPlan) (h : lhDepositPlan s tab current_epoch = .ok plan) :
    plan.next_deposit_index ≤ s.pending_deposits.length := by
  unfold lhDepositPlan at h
  obtain ⟨fslot, -, h⟩ := specM_bind_ok h
  obtain ⟨churn, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨next, dbtc, postponed⟩, hd, h⟩ := specM_bind_ok h
  obtain ⟨⟨topups, post, news⟩, -, h⟩ := specM_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  show next ≤ _
  unfold depositDecisions at hd
  obtain ⟨avail, -, hd⟩ := specM_bind_ok hd
  obtain ⟨r, hr, hd⟩ := specM_bind_ok hd
  have hn : next = r.state.next_deposit_index := by
    dsimp only at hd
    split at hd
    · obtain ⟨y, -, hd⟩ := specM_bind_ok hd
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
      exact hd.1.symm
    · simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hd
      exact hd.1.symm
  rw [hn]
  have := depositLoop_next_le _ _ _ _ r hr
  simp only [List.length_map, List.length_take] at this
  omega

end Spec

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev LhDWError (E : Type) := per_epoch_processing.deposit_writes.DepositWritesError E


theorem slice_get_some {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.val.length) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice α) s i = ok (some s.val[i.val]) := by
  show ok s.val[i.val]? = _
  rw [List.getElem?_eq_getElem h]

/-- What a deposit write returns, in spec terms. -/
def TailPost {S E A : Type} (view : S → Spec.BeaconState) (spec : Spec.SpecM Spec.BeaconState) :
    core.result.Result A (LhDWError E) × S → Prop
  | (.Ok _, s') => spec = .ok (view s')
  | (.Err _, _) => ∃ e, spec = .error e

theorem foldlM_take_succ {α β : Type} (f : β → α → Spec.SpecM β) (b : β) (l : List α) (i : Nat)
    (hi : i < l.length) :
    (l.take (i + 1)).foldlM f b = (l.take i).foldlM f b >>= fun x => f x l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases (l.take i).foldlM f b with
  | error e => rfl
  | ok x =>
    show f x l[i] >>= pure = f x l[i]
    cases f x l[i] <;> rfl

theorem foldlM_error_of_take {α β : Type} (f : β → α → Spec.SpecM β) (b x : β) (l : List α)
    (i : Nat) (hi : i < l.length) (hp : (l.take i).foldlM f b = .ok x) (e : Spec.SpecError)
    (he : f x l[i] = .error e) : l.foldlM f b = .error e := by
  have hsplit : l = l.take i ++ (l[i] :: l.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [hsplit, List.foldlM_append, hp]
  show (List.foldlM f x (l[i] :: l.drop (i + 1))) = _
  rw [List.foldlM_cons, he]
  rfl

theorem update_effective_balances_loop_spec {S D E : Type} (inst : LhDepositWrites S D E)
    (o : Spec.Oracle) (view : S → Spec.BeaconState) (absDep : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) (hc : DepositWritesContract inst o view absDep postOf)
    (idx : Slice Usize) (t0 : Spec.BeaconState) (s : S) (j : Usize) (hj : j.val ≤ idx.length)
    (hp : ((idx.val.map (·.val)).take j.val).foldlM Spec.ebUpdateAt t0 = .ok (view s)) :
    per_epoch_processing.deposit_writes.update_effective_balances_loop inst s idx j
      ⦃ res => TailPost view ((idx.val.map (·.val)).foldlM Spec.ebUpdateAt t0) res ⦄ := by
  unfold per_epoch_processing.deposit_writes.update_effective_balances_loop
  apply loop.spec_decr_nat
    (measure := fun (x : S × Usize) => idx.length - x.2.val)
    (inv := fun (x : S × Usize) => x.2.val ≤ idx.length ∧
      ((idx.val.map (·.val)).take x.2.val).foldlM Spec.ebUpdateAt t0 = .ok (view x.1))
  · rintro ⟨s1, j1⟩ ⟨hj1, hp1⟩
    dsimp only at hj1 hp1 ⊢
    unfold per_epoch_processing.deposit_writes.update_effective_balances_loop.body
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

/-- What `apply_new_validator_deposits` returns, in spec terms: the fold of
`apply_pending_deposit`, and the indices of the new validators, which are the indices from `L0`
on. -/
def NewPost {S E : Type} (view : S → Spec.BeaconState) (L0 : Nat)
    (spec : Spec.SpecM Spec.BeaconState) :
    core.result.Result (alloc.vec.Vec Usize) (LhDWError E) × S → Prop
  | (.Ok added, s') => spec = .ok (view s') ∧ L0 ≤ (view s').validators.length ∧
      added.val.map (·.val) = List.range' L0 ((view s').validators.length - L0)
  | (.Err _, _) => ∃ e, spec = .error e

theorem range'_snoc (L0 n : Nat) (h : L0 ≤ n) :
    List.range' L0 (n + 1 - L0) = List.range' L0 (n - L0) ++ [n] := by
  rw [show n + 1 - L0 = (n - L0) + 1 by omega, List.range'_concat]
  congr 2
  omega

theorem apply_new_validator_deposits_loop_spec [EpochProofs.Spec.PresetCfg] {S D E : Type} (inst : LhDepositWrites S D E)
    (o : Spec.Oracle) (view : S → Spec.BeaconState) (absDep : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) (hc : DepositWritesContract inst o view absDep postOf)
    (deps : Slice D) (t0 : Spec.BeaconState) (L0 : Nat) (s : S) (added : alloc.vec.Vec Usize)
    (i : Usize) (hi : i.val ≤ deps.length)
    (hp : ((deps.val.map absDep).take i.val).foldlM (Spec.apply_pending_deposit
      Spec.P o) t0 = .ok (view s))
    (hL : L0 ≤ (view s).validators.length)
    (ha : added.val.map (·.val) = List.range' L0 ((view s).validators.length - L0))
    (hal : added.length ≤ i.val) :
    per_epoch_processing.deposit_writes.apply_new_validator_deposits_loop inst s deps added i
      ⦃ res => NewPost view L0 ((deps.val.map absDep).foldlM (Spec.apply_pending_deposit
        Spec.P o) t0) res ⦄ := by
  unfold per_epoch_processing.deposit_writes.apply_new_validator_deposits_loop
  apply loop.spec_decr_nat
    (measure := fun (x : S × alloc.vec.Vec Usize × Usize) => deps.length - x.2.2.val)
    (inv := fun (x : S × alloc.vec.Vec Usize × Usize) => x.2.2.val ≤ deps.length ∧
      ((deps.val.map absDep).take x.2.2.val).foldlM (Spec.apply_pending_deposit
        Spec.P o) t0 = .ok (view x.1) ∧
      L0 ≤ (view x.1).validators.length ∧
      x.2.1.val.map (·.val) = List.range' L0 ((view x.1).validators.length - L0) ∧
      x.2.1.length ≤ x.2.2.val)
  · rintro ⟨s1, added1, i1⟩ ⟨hi1, hp1, hL1, ha1, hal1⟩
    dsimp only at hi1 hp1 hL1 ha1 hal1 ⊢
    unfold per_epoch_processing.deposit_writes.apply_new_validator_deposits_loop.body
    dsimp only
    split
    · rename_i hlt
      have hil : i1.val < deps.length := by scalar_tac
      have hiv : i1.val < deps.val.length := hil
      have hml : i1.val < (deps.val.map absDep).length := by simpa using hiv
      have hmax : i1.val < Usize.max := by scalar_tac
      rw [slice_get_some deps i1 hiv, bind_tc_ok]
      dsimp only
      set x := deps.val[i1.val] with hxv
      have hget : (deps.val.map absDep)[i1.val] = absDep x := by simp [hxv]
      have hstep := Spec.foldlM_take_succ' (Spec.apply_pending_deposit Spec.P o)
        t0 (view s1) _ _ hml hp1
      rw [hget] at hstep
      obtain ⟨r, s2, hvi, hv2, hr⟩ := hc.validator_index s1 x
      rw [hvi]
      simp only [bind_tc_ok, uncurry_apply_pair]
      by_cases hm : (absDep x).pubkey ∈ (view s1).validators.map (·.pubkey)
      · rw [if_pos hm] at hr
        obtain ⟨index, rfl, hidx⟩ : ∃ index : Usize, r = some index ∧
            index.val = ((view s1).validators.map (·.pubkey)).idxOf (absDep x).pubkey := by
          cases r with
          | none => simp at hr
          | some index => exact ⟨index, rfl, by simpa using hr⟩
        have hsp := Spec.apply_pending_deposit_known o (view s1) (absDep x) hm
        dsimp only
        rcases hc.balance s2 index with ⟨b, hb, hbv⟩ | ⟨hnone, e, hb⟩
        · rw [hb]
          simp only [bind_tc_ok]
          obtain ⟨a, ham, hav⟩ := hc.amount s2 x
          rw [ham, bind_tc_ok]
          rw [hv2] at hbv
          have hlg : Spec.listGet (view s1).balances
              (((view s1).validators.map (·.pubkey)).idxOf (absDep x).pubkey) = .ok b.val := by
            rw [← hidx]; simp [Spec.listGet, hbv, pure, Except.pure]
          rcases safe_add_cases b a with ⟨c, hcadd, huc⟩ | ⟨hcadd, huc⟩
          · rw [hcadd]
            simp only [bind_tc_ok]
            have hlt' : index.val < (view s2).balances.length := by
              rw [hv2]; exact (List.getElem?_eq_some_iff.mp hbv).1
            obtain ⟨s3, hsb, hv3⟩ := hc.set_balance s2 index c hlt'
            rw [hsb]
            simp only [bind_tc_ok, uncurry_apply_pair]
            obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i1 hmax
            rw [hadd]
            simp only [bind_tc_ok, spec_ok]
            have hset : Spec.listSet (view s1).balances
                (((view s1).validators.map (·.pubkey)).idxOf (absDep x).pubkey) c.val =
                .ok ((view s1).balances.set index.val c.val) := by
              rw [← hidx]
              have : index.val < (view s1).balances.length := by rw [← hv2]; exact hlt'
              simp [Spec.listSet, this, pure, Except.pure]
            have hv3' : view s3 = { view s1 with
                balances := (view s1).balances.set index.val c.val } := by rw [hv3, hv2]
            have hstep' : (List.take (i1.val + 1) (deps.val.map absDep)).foldlM
                (Spec.apply_pending_deposit Spec.P o) t0 = .ok (view s3) := by
              rw [hstep, hsp, hlg]
              simp only [except_ok_bind]
              rw [hav] at huc
              rw [huc, except_ok_bind, hset, except_ok_bind, hv3']
              rfl
            refine ⟨⟨by omega, by rw [hi']; exact hstep', ?_, ?_, by omega⟩, by omega⟩
            · rw [hv3']; exact hL1
            · rw [hv3']; exact ha1
          · rw [hcadd]
            simp only [bind_tc_ok, spec_ok]
            refine ⟨.overflow, ?_⟩
            apply foldlM_error_of_take _ _ _ _ _ hml hp1
            rw [hget, hsp, hlg]
            simp only [except_ok_bind]
            rw [hav] at huc
            rw [huc]
            rfl
        · rw [hb]
          simp only [bind_tc_ok, spec_ok]
          refine ⟨.indexOutOfRange, ?_⟩
          apply foldlM_error_of_take _ _ _ _ _ hml hp1
          rw [hget, hsp]
          rw [hv2] at hnone
          have hlg : Spec.listGet (view s1).balances
              (((view s1).validators.map (·.pubkey)).idxOf (absDep x).pubkey) =
              .error .indexOutOfRange := by
            rw [← hidx]; simp [Spec.listGet, hnone, throw, throwThe, MonadExceptOf.throw]
          rw [hlg]
          rfl
      · rw [if_neg hm] at hr
        obtain rfl : r = none := by cases r <;> simp_all
        have hsp := Spec.apply_pending_deposit_new o (view s1) (absDep x) hm
        dsimp only
        rw [hc.is_valid_signature, bind_tc_ok]
        by_cases hsig : Spec.is_valid_deposit_signature Spec.P o (absDep x).pubkey
            (absDep x).withdrawal_credentials (absDep x).amount (absDep x).signature = true
        · rw [if_pos hsig] at hsp
          simp only [hsig, if_true]
          cases hreg : Spec.add_validator_to_registry Spec.P (view s1)
              (absDep x).pubkey (absDep x).withdrawal_credentials (absDep x).amount with
          | ok t' =>
            rw [← hv2] at hreg
            obtain ⟨index, s3, hav, hv3, hidx⟩ := (hc.add_validator s2 x).1 t' hreg
            rw [hav]
            simp only [bind_tc_ok, uncurry_apply_pair]
            have hpush : added1.val.length < Usize.max := by
              have : added1.length ≤ i1.val := hal1
              scalar_tac
            obtain ⟨added2, hpu, hav2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec added1 index hpush)
            rw [hpu, bind_tc_ok]
            obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i1 hmax
            rw [hadd]
            simp only [bind_tc_ok, spec_ok]
            rw [hv2] at hreg hidx
            have hlen := Spec.add_validator_to_registry_len _ _ _ _ _ _ hreg
            refine ⟨⟨by omega, ?_, ?_, ?_, ?_⟩, by omega⟩
            · rw [hi', hstep, hsp, hreg, hv3]
            · rw [hv3, hlen]; omega
            · rw [hav2, hv3, hlen, List.map_append, ha1, range'_snoc _ _ hL1]
              simp [hidx]
            · have : added2.length = added1.length + 1 := by
                simp [alloc.vec.Vec.length, hav2]
              omega
          | error e =>
            rw [← hv2] at hreg
            obtain ⟨e', s3, hav⟩ := (hc.add_validator s2 x).2 e hreg
            rw [hav]
            simp only [bind_tc_ok, uncurry_apply_pair, spec_ok]
            refine ⟨e, ?_⟩
            apply foldlM_error_of_take _ _ _ _ _ hml hp1
            rw [hget, hsp, ← hv2, hreg]
        · rw [if_neg hsig] at hsp
          simp only [hsig, Bool.false_eq_true, if_false]
          obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i1 hmax
          rw [hadd]
          simp only [bind_tc_ok, spec_ok]
          refine ⟨⟨by omega, ?_, by rw [hv2]; exact hL1, by rw [hv2]; exact ha1, by omega⟩,
            by omega⟩
          rw [hi', hstep, hsp, hv2]
          rfl
    · rename_i hge
      have hiv : i1.val = deps.length := by scalar_tac
      simp only [spec_ok]
      have h1 : (deps.val.map absDep).take i1.val = deps.val.map absDep := by
        rw [hiv]; simp
      exact ⟨by rw [← h1, hp1], hL1, ha1⟩
  · exact ⟨hi, hp, hL, ha, hal⟩

/-- The deposit writes after the single pass equal the model under the trusted
`DepositWritesContract`: `Ok` exactly when `depositWritesSpec` is `ok`, with the same state. The
queue write needs the next deposit index to be at most the queue length, which
`lhDepositPlan_next_le` gives for the plan. -/
theorem apply_deposit_writes_spec {S D E : Type} (inst : LhDepositWrites S D E) (o : Spec.Oracle)
    (view : S → Spec.BeaconState) (absDep : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) (hc : DepositWritesContract inst o view absDep postOf)
    (s : S) (next : Usize) (dbtc : U64) (deps : Slice D) (eb : Bool)
    (hnext : next.val ≤ (view s).pending_deposits.length) :
    per_epoch_processing.deposit_writes.apply_deposit_writes inst s next dbtc deps eb
      ⦃ res => TailPost view (Spec.depositWritesSpec o (view s) next.val dbtc.val (postOf s)
        (deps.val.map absDep) eb) res ⦄ := by
  unfold per_epoch_processing.deposit_writes.apply_deposit_writes
  obtain ⟨s1, hw, hv1⟩ := hc.write_queue s next dbtc hnext
  rw [hw]
  simp only [bind_tc_ok, uncurry_apply_pair]
  unfold per_epoch_processing.deposit_writes.apply_new_validator_deposits
  apply spec_bind (apply_new_validator_deposits_loop_spec inst o view absDep postOf hc deps
    (view s1) (view s1).validators.length s1 (alloc.vec.Vec.new Usize) 0#usize (by simp)
    (by simp [pure, Except.pure]) le_rfl (by simp) (by simp))
  rintro ⟨r1, s2⟩ hpost
  cases r1 with
  | Ok added =>
    obtain ⟨hf, hL, ha⟩ := hpost
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    have hspec : Spec.depositWritesSpec o (view s) next.val dbtc.val (postOf s)
        (deps.val.map absDep) eb = (if eb then
          (List.range' (view s1).validators.length
            ((view s2).validators.length - (view s1).validators.length)).foldlM
            Spec.ebUpdateAt (view s2) else pure (view s2)) := by
      unfold Spec.depositWritesSpec
      rw [← hv1]
      dsimp only
      rw [hf, except_ok_bind]
    cases eb with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      show _ = _
      rw [hspec]
      rfl
    | true =>
      simp only [if_true]
      unfold per_epoch_processing.deposit_writes.update_effective_balances
      apply spec_bind (update_effective_balances_loop_spec inst o view absDep postOf hc
        (alloc.vec.Vec.deref added) (view s2) s2 0#usize (by simp)
        (by simp [pure, Except.pure]))
      rintro ⟨r2, s3⟩ hpost2
      have hidx : ((alloc.vec.Vec.deref added).val.map (·.val)) = List.range'
          (view s1).validators.length ((view s2).validators.length -
            (view s1).validators.length) := by
        simpa [alloc.vec.Vec.deref] using ha
      rw [hidx] at hpost2
      rw [hspec, if_pos rfl]
      cases r2 with
      | Ok _ =>
        simp only [uncurry_apply_pair, bind_tc_ok, spec_ok]
        exact hpost2
      | Err e =>
        simp only [uncurry_apply_pair, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, spec_ok]
        exact hpost2
  | Err e =>
    obtain ⟨e', he'⟩ := hpost
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]
    refine ⟨e', ?_⟩
    unfold Spec.depositWritesSpec
    rw [← hv1]
    dsimp only
    rw [he']
    rfl

/-- `apply_deposit_writes` is the model step from the queue write to the effective balance updates
of the new validators (`lhNewValidators` after `lhQueueWrite`), for the plan of the epoch input
`s`, on any state `view st` that still holds the queue of `s`. -/
theorem apply_deposit_writes_model {S D E : Type} (inst : LhDepositWrites S D E)
    (o : Spec.Oracle) (view : S → Spec.BeaconState) (absDep : D → Spec.PendingDeposit)
    (postOf : S → List Spec.PendingDeposit) (hc : DepositWritesContract inst o view absDep postOf)
    (s : Spec.BeaconState) (tab : Spec.Gwei) (current_epoch : Spec.Epoch) (plan : Spec.LhDepositPlan)
    (hplan : Spec.lhDepositPlan s tab current_epoch = .ok plan) (st : S)
    (hq : (view st).pending_deposits = s.pending_deposits) (next : Usize) (dbtc : U64)
    (deps : Slice D) (hnext : next.val = plan.next_deposit_index)
    (hdbtc : dbtc.val = plan.deposit_balance_to_consume) (hpost : postOf st = plan.postponed)
    (hdeps : deps.val.map absDep = plan.new_validator_deposits) :
    per_epoch_processing.deposit_writes.apply_deposit_writes inst st next dbtc deps true
      ⦃ res => TailPost view (Spec.lhNewValidators o plan (Spec.lhQueueWrite s plan (view st)))
        res ⦄ := by
  have hle : next.val ≤ (view st).pending_deposits.length := by
    rw [hq, hnext]; exact Spec.lhDepositPlan_next_le s tab current_epoch plan hplan
  have h := apply_deposit_writes_spec inst o view absDep postOf hc st next dbtc deps true hle
  rwa [hnext, hdbtc, hpost, hdeps, Spec.depositWritesSpec_eq o s (view st) plan hq] at h

end EpochProofs
