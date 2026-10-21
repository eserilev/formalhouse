import EpochProofs.Spec.Fulu
import EpochProofs.Sanity.SelectionPass

/-!
# The Fulu functions as Gloas functions

- `get_activation_churn_limit_fuluView`, `process_pending_deposits_fulu_eq`: the Fulu activation
  churn is the Gloas activation churn with the two Fulu config values. So Fulu
  `process_pending_deposits` is Gloas `process_pending_deposits` on `p.fuluView f`.
- `next_sync_committee_indices_loop_iff`, `get_next_sync_committee_indices_fulu_iff`: the Electra
  sync committee loop returns what `compute_balance_weighted_selection` returns.
- `compute_proposer_index_loop_selection`, `compute_proposer_indices_fulu_ok`: an Electra
  proposer is the first item of a selection of size 1, if the Electra loop ends before its last
  pass.
-/

namespace EpochProofs.Spec

/-- `p` with the Gloas activation churn values replaced by the Fulu values. -/
def Preset.fuluView (p : Preset) (f : FuluConfig) : Preset :=
  { p with
    CHURN_LIMIT_QUOTIENT_GLOAS := f.CHURN_LIMIT_QUOTIENT
    MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS := f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT }

theorem get_activation_churn_limit_fuluView (p : Preset) (f : FuluConfig) (tab : Gwei) :
    get_activation_churn_limit (p.fuluView f) tab = get_activation_exit_churn_limit p f tab := by
  simp only [get_activation_churn_limit, get_activation_exit_churn_limit, get_balance_churn_limit,
    Preset.fuluView]
  cases uint64Div tab f.CHURN_LIMIT_QUOTIENT <;> simp only [bind, Except.bind]
  rename_i q
  cases uint64Mod (max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q) p.EFFECTIVE_BALANCE_INCREMENT <;>
    simp only

theorem process_pending_deposits_fulu_eq (p : Preset) (f : FuluConfig) (tab : Gwei)
    (apply_pending_deposit : BeaconState → PendingDeposit → SpecM BeaconState)
    (state : BeaconState) :
    process_pending_deposits_fulu p f tab apply_pending_deposit state =
      process_pending_deposits (p.fuluView f) tab apply_pending_deposit state := by
  unfold process_pending_deposits_fulu process_pending_deposits
  rw [get_activation_churn_limit_fuluView]
  rfl

private theorem bind_ok {α β : Type} (x : SpecM α) (k : α → SpecM β) (v : β) :
    (x >>= k) = .ok v ↔ ∃ a, x = .ok a ∧ k a = .ok v := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

private theorem pure_ok {α : Type} (a v : α) : (pure a : SpecM α) = .ok v ↔ a = v := by
  simp [pure, Except.pure]

private theorem throw_ok {α : Type} (e : SpecError) (v : α) :
    (throw e : SpecM α) = .ok v ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

private theorem listGet_ok {α : Type} (l : List α) (k : Nat) (a : α) :
    listGet l k = .ok a ↔ l[k]? = some a := by
  unfold listGet
  cases h : l[k]? <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

private theorem mod16 (i : Nat) : uint64Mod i 16 = .ok (i % 16) := by
  simp [uint64Mod, pure, Except.pure]

private theorem off16 (i : Nat) : uint64Mul (i % 16) 2 = .ok (i % 16 * 2) := by
  have : i % 16 * 2 < UINT64_SIZE := by unfold UINT64_SIZE; omega
  simp [uint64Mul, this, pure, Except.pure]

private theorem modTotal (i total : Nat) (h : 0 < total) : uint64Mod i total = .ok (i % total) := by
  simp [uint64Mod, Nat.pos_iff_ne_zero.mp h, pure, Except.pure]

/-- The random bytes of pass `i`. -/
def fuluRandomBytes (o : Oracle) (seed : Bytes32) (i : Nat) : Bytes32 :=
  o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))

/-- One pass of the Electra loops: the accepted candidate of pass `i`, if any. -/
def electraPass (p : Preset) (o : Oracle) (validators : List Validator) (indices : List ValidatorIndex)
    (seed : Bytes32) (total : Uint64) (i : Uint64) : SpecM (Option ValidatorIndex) := do
  let MAX_RANDOM_VALUE := 2 ^ 16 - 1
  let shuffled_index ← compute_shuffled_index p o (← uint64Mod i total) total seed
  let candidate_index ← listGet indices shuffled_index
  let random_bytes := o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))
  let offset ← uint64Mul (← uint64Mod i 16) 2
  let random_value ← bytes_to_uint64 ((random_bytes.toList.drop offset).take 2)
  let effective_balance := (← listGet validators candidate_index).effective_balance
  if (← uint64Mul effective_balance MAX_RANDOM_VALUE) ≥
      (← uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA random_value) then
    pure (some candidate_index)
  else pure none

theorem next_sync_committee_indices_loop_succ (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (total : Uint64) (fuel : Nat)
    (sel : List ValidatorIndex) (i : Uint64) :
    next_sync_committee_indices_loop p o state.validators indices seed total (fuel + 1) sel i =
      if sel.length < p.SYNC_COMMITTEE_SIZE then do
        let c ← electraPass p o state.validators indices seed total i
        let i ← uint64Add i 1
        next_sync_committee_indices_loop p o state.validators indices seed total fuel (sel ++ c.toList) i
      else pure sel := by
  simp only [next_sync_committee_indices_loop, electraPass]
  split
  · simp only [Bind.bind, Except.bind, pure, Except.pure]
    (repeat' split) <;> simp_all
  · rfl

/-- The canonical result of pass `i`, which both loops compute. -/
def passResult (p : Preset) (o : Oracle) (validators : List Validator) (indices : List ValidatorIndex)
    (seed : Bytes32) (total i : Nat) (c : Option ValidatorIndex) : Prop :=
  ∃ nx, compute_shuffled_index p o (i % total) total seed = .ok nx ∧ ∃ cand, indices[nx]? = some cand ∧
    ∃ v, validators[cand]? = some v ∧
    ∃ rv, bytes_to_uint64 (((fuluRandomBytes o seed i).toList.drop (i % 16 * 2)).take 2) = .ok rv ∧
    ∃ w, uint64Mul v.effective_balance (2 ^ 16 - 1) = .ok w ∧
    ∃ t, uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA rv = .ok t ∧
    c = if w ≥ t then some cand else none

theorem electraPass_ok (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (i : Nat) (htotal : 0 < indices.length)
    (c : Option ValidatorIndex) :
    electraPass p o state.validators indices seed indices.length i = .ok c ↔
      passResult p o state.validators indices seed indices.length i c := by
  unfold electraPass passResult fuluRandomBytes
  simp only [bind_ok, modTotal i _ htotal, mod16, listGet_ok, Except.ok.injEq, exists_eq_left']
  simp only [off16, Except.ok.injEq, exists_eq_left']
  constructor
  · rintro ⟨nx, hnx, cand, hc, rv, hrv, v, hv, w, hw, t, ht, hfin⟩
    refine ⟨nx, hnx, cand, hc, v, hv, rv, hrv, w, hw, t, ht, ?_⟩
    split at hfin <;> rename_i h <;>
      simp only [pure, Except.pure, Except.ok.injEq] at hfin <;> subst hfin
    · rw [if_pos h]
    · rw [if_neg h]
  · rintro ⟨nx, hnx, cand, hc, v, hv, rv, hrv, w, hw, t, ht, rfl⟩
    refine ⟨nx, hnx, cand, hc, rv, hrv, v, hv, w, hw, t, ht, ?_⟩
    split <;> rfl

/-- `ebs[k]` is the effective balance of validator `indices[k]`. -/
def EBsOf (state : BeaconState) (indices : List ValidatorIndex) (ebs : List Gwei) : Prop :=
  ∀ k : Nat, ebs[k]? = indices[k]?.bind fun x => state.validators[x]?.map fun v : Validator =>
    v.effective_balance

theorem selectionPass_ok (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (ebs : List Gwei)
    (hebs : EBsOf state indices ebs) (i : Nat) (rb : Bytes32)
    (hrb : i % 16 ≠ 0 → rb = fuluRandomBytes o seed i) (htotal : 0 < indices.length)
    (c : Option ValidatorIndex) (rb' : Bytes32) :
    selectionPass p o indices seed true indices.length ebs i rb = .ok (c, rb') ↔
      passResult p o state.validators indices seed indices.length i c ∧ rb' = fuluRandomBytes o seed i := by
  unfold EBsOf at hebs
  have hrbx : (if (i % 16 * 2 == 0) = true then o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))
      else rb) = o.hash (seed.toList ++ uint_to_bytes 8 (i / 16)) := by
    split
    · rfl
    · rename_i h
      exact hrb (fun h0 => h (by simp [h0]))
  unfold selectionPass passResult fuluRandomBytes
  simp only [bind_ok, modTotal i _ htotal, mod16, Except.ok.injEq, exists_eq_left']
  simp only [off16, Except.ok.injEq, exists_eq_left', if_true, hrbx, pure_bind, bind_ok,
    listGet_ok]
  constructor
  · rintro ⟨nx, hnx, eb, heb, w, hw, rv, hrv, t, ht, hfin⟩
    have hk := hebs nx
    rw [heb] at hk
    cases hc : indices[nx]? with
    | none => rw [hc] at hk; simp at hk
    | some cand =>
      rw [hc, Option.bind_some] at hk
      cases hv : state.validators[cand]? with
      | none => rw [hv] at hk; simp at hk
      | some v =>
        rw [hv, Option.map_some, Option.some.injEq] at hk
        subst hk
        split at hfin
        · rename_i h
          simp only [bind_ok, listGet_ok, hc, Option.some.injEq, exists_eq_left', pure,
            Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
          exact ⟨⟨nx, hnx, cand, hc, v, hv, rv, hrv, w, hw, t, ht, by rw [if_pos h, hfin.1]⟩,
            hfin.2.symm⟩
        · rename_i h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
          exact ⟨⟨nx, hnx, cand, hc, v, hv, rv, hrv, w, hw, t, ht, by rw [if_neg h, hfin.1]⟩,
            hfin.2.symm⟩
  · rintro ⟨⟨nx, hnx, cand, hc, v, hv, rv, hrv, w, hw, t, ht, rfl⟩, rfl⟩
    have hk := hebs nx
    rw [hc] at hk
    simp only [Option.bind_some, hv, Option.map_some] at hk
    refine ⟨nx, hnx, v.effective_balance, hk, w, hw, rv, hrv, t, ht, ?_⟩
    split
    · rename_i h
      simp [bind_ok, listGet_ok, hc, pure, Except.pure]
    · rename_i h
      simp [pure, Except.pure]

private theorem add1_ok (i i' : Nat) (h : uint64Add i 1 = .ok i') : i' = i + 1 := by
  unfold uint64Add at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem rb_next (o : Oracle) (seed : Bytes32) (i : Nat) :
    (i + 1) % 16 ≠ 0 → fuluRandomBytes o seed i = fuluRandomBytes o seed (i + 1) := by
  intro h
  unfold fuluRandomBytes
  rw [show (i + 1) / 16 = i / 16 by omega]

/-- The Electra sync committee loop returns what the selection loop returns. -/
theorem next_sync_committee_indices_loop_iff (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (ebs : List Gwei)
    (hebs : EBsOf state indices ebs) (htotal : 0 < indices.length) (fuel : Nat)
    (sel : List ValidatorIndex) (i : Nat) (rb : Bytes32)
    (hrb : i % 16 ≠ 0 → rb = fuluRandomBytes o seed i) (v : List ValidatorIndex) :
    next_sync_committee_indices_loop p o state.validators indices seed indices.length fuel sel i = .ok v ↔
      compute_balance_weighted_selection_loop p o indices seed p.SYNC_COMMITTEE_SIZE true
        indices.length ebs fuel sel i rb = .ok v := by
  induction fuel generalizing sel i rb with
  | zero =>
    simp [next_sync_committee_indices_loop, compute_balance_weighted_selection_loop, throw,
      throwThe, MonadExceptOf.throw]
  | succ n ih =>
    rw [next_sync_committee_indices_loop_succ, selection_loop_succ]
    split
    · simp only [bind_ok]
      constructor
      · rintro ⟨c, hc, i', hi', hl⟩
        have hp := (electraPass_ok p o state indices seed i htotal c).mp hc
        refine ⟨(c, fuluRandomBytes o seed i),
          (selectionPass_ok p o state indices seed ebs hebs i rb hrb htotal c _).mpr ⟨hp, rfl⟩,
          i', hi', ?_⟩
        have := add1_ok i i' hi'
        subst this
        exact (ih _ _ _ (rb_next o seed i)).mp hl
      · rintro ⟨⟨c, rb'⟩, hc, i', hi', hl⟩
        obtain ⟨hp, hrb'⟩ :=
          (selectionPass_ok p o state indices seed ebs hebs i rb hrb htotal c rb').mp hc
        subst hrb'
        refine ⟨c, (electraPass_ok p o state indices seed i htotal c).mpr hp, i', hi', ?_⟩
        have := add1_ok i i' hi'
        subst this
        exact (ih _ _ _ (rb_next o seed i)).mpr hl
    · rfl

theorem active_validator_index_lt (state : BeaconState) (epoch : Epoch) (x : ValidatorIndex)
    (hx : x ∈ get_active_validator_indices state epoch) : x < state.validators.length := by
  unfold get_active_validator_indices at hx
  simp only [List.mem_map, List.mem_filter] at hx
  obtain ⟨⟨v, j⟩, ⟨hmem, _⟩, rfl⟩ := hx
  simpa using (List.mem_zipIdx hmem).2.1

/-- The effective balances that `compute_balance_weighted_selection` reads. -/
theorem effective_balances_ok (state : BeaconState) (indices : List ValidatorIndex)
    (hvalid : ∀ x ∈ indices, x < state.validators.length) :
    ∃ ebs, (indices.mapM fun index => do
        pure (← listGet state.validators index).effective_balance) = .ok ebs ∧
      EBsOf state indices ebs := by
  induction indices with
  | nil => exact ⟨[], rfl, fun k => by simp⟩
  | cons x xs ih =>
    obtain ⟨ebs, hebs, hof⟩ := ih (fun y hy => hvalid y (List.mem_cons_of_mem x hy))
    have hx := hvalid x List.mem_cons_self
    refine ⟨state.validators[x].effective_balance :: ebs, ?_, ?_⟩
    · rw [List.mapM_cons, hebs]
      simp [listGet, List.getElem?_eq_getElem hx, bind, Except.bind, pure, Except.pure]
    · intro k
      cases k with
      | zero => simp [List.getElem?_eq_getElem hx]
      | succ k => simpa using hof k

private theorem sync_loop_empty (p : Preset) (o : Oracle) (state : BeaconState) (seed : Bytes32)
    (hsize : 0 < p.SYNC_COMMITTEE_SIZE) (v : List ValidatorIndex) :
    next_sync_committee_indices_loop p o state.validators [] seed 0 UINT64_SIZE [] 0 ≠ .ok v := by
  rw [show UINT64_SIZE = (UINT64_SIZE - 1) + 1 by unfold UINT64_SIZE; omega,
    next_sync_committee_indices_loop_succ]
  simp [hsize, electraPass, uint64Mod, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The Electra `get_next_sync_committee_indices` returns what the Gloas one returns. -/
theorem get_next_sync_committee_indices_fulu_iff (p : Preset) (o : Oracle) (state : BeaconState)
    (hsize : 0 < p.SYNC_COMMITTEE_SIZE) (v : List ValidatorIndex) :
    get_next_sync_committee_indices_fulu p o state = .ok v ↔
      get_next_sync_committee_indices p o state = .ok v := by
  unfold get_next_sync_committee_indices_fulu get_next_sync_committee_indices
  simp only [bind_ok]
  apply exists_congr; intro ce; apply and_congr_right; intro _
  apply exists_congr; intro e; apply and_congr_right; intro _
  apply exists_congr; intro sd; apply and_congr_right; intro _
  unfold compute_balance_weighted_selection
  generalize hA : get_active_validator_indices state e = A
  have hvalid : ∀ x ∈ A, x < state.validators.length := by
    intro x hx; rw [← hA] at hx; exact active_validator_index_lt state e x hx
  by_cases hpos : 0 < A.length
  · obtain ⟨ebs, hebs, hof⟩ := effective_balances_ok state A hvalid
    simp only [hpos, not_true_eq_false, if_false, pure_bind, hebs, bind_ok, Except.ok.injEq,
      exists_eq_left']
    exact next_sync_committee_indices_loop_iff p o state A sd ebs hof hpos UINT64_SIZE [] 0
      Bytes32.zero (by simp) v
  · have hA0 : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hA0
    have hr : ((throw SpecError.assertionFailed : SpecM PUnit) >>= fun _ =>
        (do
          let effective_balances ← List.mapM (fun index => do
            let __do_lift ← listGet state.validators index
            pure __do_lift.effective_balance) ([] : List ValidatorIndex)
          compute_balance_weighted_selection_loop p o [] sd p.SYNC_COMMITTEE_SIZE true 0
            effective_balances UINT64_SIZE [] 0 Bytes32.zero)) ≠ .ok v := by
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    simp only [List.length_nil, Nat.lt_irrefl, not_false_eq_true, if_true]
    exact iff_of_false (sync_loop_empty p o state sd hsize v) hr

theorem compute_proposer_index_loop_succ (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (total : Uint64) (fuel : Nat) (i : Uint64) :
    compute_proposer_index_loop p o state.validators indices seed total (fuel + 1) i =
      (electraPass p o state.validators indices seed total i >>= fun c =>
        match c with
        | some cand => pure cand
        | none => uint64Add i 1 >>= fun i =>
          compute_proposer_index_loop p o state.validators indices seed total fuel i) := by
  simp only [compute_proposer_index_loop, electraPass]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  (repeat' split) <;> simp_all

private theorem selection_loop_one_done (p : Preset) (o : Oracle) (indices : List ValidatorIndex)
    (seed : Bytes32) (total : Nat) (ebs : List Gwei) (fuel : Nat) (c : ValidatorIndex) (i : Nat)
    (rb : Bytes32) :
    compute_balance_weighted_selection_loop p o indices seed 1 true total ebs (fuel + 1) [c] i rb =
      .ok [c] := by
  rw [selection_loop_succ]
  simp [pure, Except.pure]

theorem compute_proposer_index_loop_mono (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (total : Nat) (n k : Nat) (i : Nat)
    (c : ValidatorIndex)
    (h : compute_proposer_index_loop p o state.validators indices seed total n i = .ok c) :
    compute_proposer_index_loop p o state.validators indices seed total (n + k) i = .ok c := by
  induction n generalizing i with
  | zero => simp [compute_proposer_index_loop, throw, throwThe, MonadExceptOf.throw] at h
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega, compute_proposer_index_loop_succ]
    rw [compute_proposer_index_loop_succ] at h
    simp only [bind_ok] at h ⊢
    obtain ⟨r, hr, hk⟩ := h
    refine ⟨r, hr, ?_⟩
    cases r with
    | some cand => exact hk
    | none =>
      simp only [bind_ok] at hk ⊢
      obtain ⟨i', hi', hl⟩ := hk
      exact ⟨i', hi', ih i' hl⟩

/-- An Electra proposer loop that ends with fuel `n` is a selection loop of size 1 with fuel
`n + 1`, if `i + n` fits in a `Uint64`. -/
theorem compute_proposer_index_loop_selection (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (ebs : List Gwei)
    (hebs : EBsOf state indices ebs) (htotal : 0 < indices.length) (n : Nat) (i : Nat)
    (rb : Bytes32) (hrb : i % 16 ≠ 0 → rb = fuluRandomBytes o seed i)
    (hfit : i + n < UINT64_SIZE) (c : ValidatorIndex)
    (h : compute_proposer_index_loop p o state.validators indices seed indices.length n i = .ok c) :
    compute_balance_weighted_selection_loop p o indices seed 1 true indices.length ebs (n + 1) [] i
      rb = .ok [c] := by
  induction n generalizing i rb with
  | zero => simp [compute_proposer_index_loop, throw, throwThe, MonadExceptOf.throw] at h
  | succ m ih =>
    rw [compute_proposer_index_loop_succ] at h
    simp only [bind_ok] at h
    obtain ⟨r, hr, hk⟩ := h
    have hp := (electraPass_ok p o state indices seed i htotal r).mp hr
    have hsel := (selectionPass_ok p o state indices seed ebs hebs i rb hrb htotal r _).mpr ⟨hp, rfl⟩
    have hadd : uint64Add i 1 = .ok (i + 1) := by
      simp only [uint64Add, show i + 1 < UINT64_SIZE by omega, if_true, pure, Except.pure]
    rw [selection_loop_succ]
    simp only [List.length_nil, Nat.zero_lt_one, if_true, bind_ok]
    refine ⟨_, hsel, i + 1, hadd, ?_⟩
    cases r with
    | some cand =>
      simp only [pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      exact selection_loop_one_done p o indices seed _ ebs m cand (i + 1) _
    | none =>
      simp only [bind_ok, hadd, Except.ok.injEq, exists_eq_left'] at hk
      exact ih (i + 1) _ (rb_next o seed i) (by omega) hk

/-- A selection loop of size 1 returns the proposer of the Electra loop. -/
theorem selection_compute_proposer_index_loop (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (ebs : List Gwei)
    (hebs : EBsOf state indices ebs) (htotal : 0 < indices.length) (n : Nat) (i : Nat)
    (rb : Bytes32) (hrb : i % 16 ≠ 0 → rb = fuluRandomBytes o seed i) (v : List ValidatorIndex)
    (h : compute_balance_weighted_selection_loop p o indices seed 1 true indices.length ebs n [] i
      rb = .ok v) :
    ∃ c, v = [c] ∧
      compute_proposer_index_loop p o state.validators indices seed indices.length n i = .ok c := by
  induction n generalizing i rb with
  | zero => simp [compute_balance_weighted_selection_loop, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ m ih =>
    rw [selection_loop_succ] at h
    simp only [List.length_nil, Nat.zero_lt_one, if_true, bind_ok] at h
    obtain ⟨⟨r, rb'⟩, hsel, i', hi', hl⟩ := h
    obtain ⟨hp, rfl⟩ := (selectionPass_ok p o state indices seed ebs hebs i rb hrb htotal r rb').mp hsel
    have hr := (electraPass_ok p o state indices seed i htotal r).mpr hp
    have := add1_ok i i' hi'
    subst this
    rw [compute_proposer_index_loop_succ]
    simp only [bind_ok]
    cases r with
    | some cand =>
      cases m with
      | zero => simp [compute_balance_weighted_selection_loop, throw, throwThe,
          MonadExceptOf.throw] at hl
      | succ m' =>
        simp only [Option.toList, List.nil_append] at hl
        rw [selection_loop_one_done] at hl
        simp only [Except.ok.injEq] at hl
        exact ⟨cand, hl.symm, _, hr, rfl⟩
    | none =>
      simp only [Option.toList, List.nil_append] at hl
      obtain ⟨c, hv, hc⟩ := ih (i + 1) _ (rb_next o seed i) hl
      exact ⟨c, hv, _, hr, by simp only [bind_ok]; exact ⟨i + 1, hi', hc⟩⟩

/-- The Electra proposer loop for `seed`, if it returns, returns before its last pass. Like the
selection end facts of Gloas, this is a fact about the hash values: the last pass needs
`2**64 - 1` rejected candidates before it. -/
def ProposerFin (p : Preset) (o : Oracle) (state : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) : Prop :=
  ∀ c, compute_proposer_index_loop p o state.validators indices seed indices.length UINT64_SIZE 0 = .ok c →
    compute_proposer_index_loop p o state.validators indices seed indices.length (UINT64_SIZE - 1) 0 = .ok c

theorem compute_proposer_index_selection (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32)
    (hvalid : ∀ x ∈ indices, x < state.validators.length)
    (hfin : ProposerFin p o state indices seed) (c : ValidatorIndex)
    (h : compute_proposer_index p o state indices seed = .ok c) :
    (compute_balance_weighted_selection p o state indices seed 1 true >>= fun s => listGet s 0) =
      .ok c := by
  unfold compute_proposer_index at h
  by_cases hpos : 0 < indices.length
  · simp only [hpos, not_true_eq_false, if_false, pure_bind] at h
    obtain ⟨ebs, hebs, hof⟩ := effective_balances_ok state indices hvalid
    have hl := compute_proposer_index_loop_selection p o state indices seed ebs hof hpos
      (UINT64_SIZE - 1) 0 Bytes32.zero (by simp) (by unfold UINT64_SIZE; omega) c (hfin c h)
    rw [show UINT64_SIZE - 1 + 1 = UINT64_SIZE by unfold UINT64_SIZE; omega] at hl
    unfold compute_balance_weighted_selection
    simp only [hpos, not_true_eq_false, if_false, pure_bind, hebs, bind_ok, Except.ok.injEq,
      exists_eq_left', hl]
    simp [listGet, pure, Except.pure]
  · simp [hpos, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem selection_compute_proposer_index (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32)
    (hvalid : ∀ x ∈ indices, x < state.validators.length) (c : ValidatorIndex)
    (h : (compute_balance_weighted_selection p o state indices seed 1 true >>= fun s =>
      listGet s 0) = .ok c) :
    compute_proposer_index p o state indices seed = .ok c := by
  unfold compute_balance_weighted_selection at h
  unfold compute_proposer_index
  by_cases hpos : 0 < indices.length
  · obtain ⟨ebs, hebs, hof⟩ := effective_balances_ok state indices hvalid
    simp only [hpos, not_true_eq_false, if_false, pure_bind, hebs, bind_ok, Except.ok.injEq,
      exists_eq_left'] at h ⊢
    obtain ⟨v, hv, hc⟩ := h
    obtain ⟨c', rfl, hc'⟩ := selection_compute_proposer_index_loop p o state indices seed ebs hof
      hpos UINT64_SIZE 0 Bytes32.zero (by simp) v hv
    simp [listGet, pure, Except.pure] at hc
    rw [← hc]; exact hc'
  · simp [hpos, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

private theorem mapM_ok_of {α β : Type} (f g : α → SpecM β) (l : List α)
    (hfg : ∀ a ∈ l, ∀ b, f a = .ok b → g a = .ok b) (r : List β) (h : l.mapM f = .ok r) :
    l.mapM g = .ok r := by
  induction l generalizing r with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.mapM_cons, bind_ok, pure_ok] at h ⊢
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact ⟨b, hfg a List.mem_cons_self b hb, bs,
      ih (fun x hx => hfg x (List.mem_cons_of_mem a hx)) bs hbs, rfl⟩

/-- Fulu `compute_proposer_indices` returns what Gloas `compute_proposer_indices` returns, on the
same candidates. -/
theorem compute_proposer_indices_fulu_ok (p : Preset) (o : Oracle) (state : BeaconState)
    (epoch : Epoch) (seed : Bytes32) (indices : List ValidatorIndex)
    (hvalid : ∀ x ∈ indices, x < state.validators.length)
    (hfin : ∀ s, ProposerFin p o state indices s) (props : List ValidatorIndex)
    (h : compute_proposer_indices_fulu p o state epoch seed indices = .ok props) :
    compute_proposer_indices p o state epoch seed indices = .ok props := by
  unfold compute_proposer_indices_fulu at h
  unfold compute_proposer_indices
  simp only [bind_ok] at h ⊢
  obtain ⟨ss, hss, sd, hsd, hm⟩ := h
  exact ⟨ss, hss, sd, hsd, mapM_ok_of _ _ sd (fun s _ c hc =>
    compute_proposer_index_selection p o state indices s hvalid (hfin s) c hc) props hm⟩

theorem compute_proposer_indices_ok_fulu (p : Preset) (o : Oracle) (state : BeaconState)
    (epoch : Epoch) (seed : Bytes32) (indices : List ValidatorIndex)
    (hvalid : ∀ x ∈ indices, x < state.validators.length) (props : List ValidatorIndex)
    (h : compute_proposer_indices p o state epoch seed indices = .ok props) :
    compute_proposer_indices_fulu p o state epoch seed indices = .ok props := by
  unfold compute_proposer_indices at h
  unfold compute_proposer_indices_fulu
  simp only [bind_ok] at h ⊢
  obtain ⟨ss, hss, sd, hsd, hm⟩ := h
  exact ⟨ss, hss, sd, hsd, mapM_ok_of _ _ sd (fun s _ c hc =>
    selection_compute_proposer_index p o state indices s hvalid c hc) props hm⟩

end EpochProofs.Spec
