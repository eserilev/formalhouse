import CacheProofs
import EpochProofs.Sanity.RowsInactivity
import EpochProofs.Spec.TotalActiveBalance
import EpochProofs.Spec.JustificationLighthouse

/-!
# Bridge: the progressive balances cache and the epoch spec

`CacheProofs.PB` proves that a coherent `ProgressiveBalancesCache` returns, for each flag, the
spec total `get_total_balance(state, get_unslashed_participating_indices(state, flag, epoch))`.
That spec is the model of `consensus/types/proofs`. This file proves that the same total in the
epoch spec (`EpochProofs.Spec`) is equal, on the state that `pbState` maps.

So the value that Lighthouse reads from the cache is the value that the epoch model computes.
The only fact left about the cache is that it is coherent with the state (`Coherent`), which
`CacheProofs.PB.build_coherent` and the update theorems give.
-/

namespace EpochProofs.CacheBridge

open CacheProofs.PB (flagSum activeAt slashedAt ebAt specPred sum_filter_eq_flagSum)

/-- The validator fields that the progressive balances model reads. -/
def pbValidator (v : EpochProofs.Spec.Validator) : CacheProofs.Spec.Validator :=
  ⟨v.effective_balance, v.slashed, v.activation_epoch, v.exit_epoch⟩

/-- The state of the progressive balances model, at the current epoch `current_epoch`. -/
def pbState (s : EpochProofs.Spec.BeaconState) (current_epoch : Nat) :
    CacheProofs.Spec.BeaconState :=
  ⟨current_epoch, s.validators.map pbValidator,
    s.previous_epoch_participation.map (·.toNat), s.current_epoch_participation.map (·.toNat)⟩

set_option maxRecDepth 100000 in
theorem has_flag_nat : ∀ n < 256, ∀ k < 3,
    (UInt8.ofNat n &&& UInt8.ofNat (2 ^ k) == UInt8.ofNat (2 ^ k)) = (n &&& 2 ^ k == 2 ^ k) := by
  decide

/-- `has_flag` on a `uint8` is `has_flag` on its value. -/
theorem has_flag_bridge (x : UInt8) (f : Nat) (hf : f < 3) :
    EpochProofs.Spec.has_flag x f = .ok (CacheProofs.Spec.has_flag x.toNat f) := by
  have h := has_flag_nat x.toNat x.toNat_lt f hf
  rw [UInt8.ofNat_toNat] at h
  have hf' : 2 ^ f < 256 := by
    rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl <;> decide
  simp only [EpochProofs.Spec.has_flag, hf', if_true, pure, Except.pure, h,
    CacheProofs.Spec.has_flag]

theorem activeAt_map (vs : List EpochProofs.Spec.Validator) (e i : Nat) :
    activeAt (vs.map pbValidator) e i =
      match vs[i]? with
      | some v => EpochProofs.Spec.is_active_validator v e
      | none => false := by
  simp only [activeAt, List.getElem?_map]
  cases vs[i]? <;> rfl

theorem active_zipIdx (vs : List EpochProofs.Spec.Validator) (e k : Nat) :
    ((vs.zipIdx k).filter fun x => EpochProofs.Spec.is_active_validator x.1 e).map (·.2) =
      ((List.range vs.length).filter (activeAt (vs.map pbValidator) e)).map (· + k) := by
  induction vs generalizing k with
  | nil => simp
  | cons v vs ih =>
    rw [List.zipIdx_cons, List.length_cons, List.range_succ_eq_map, List.filter_cons,
      List.map_cons]
    simp only [List.filter_cons, List.filter_map]
    have hf : (activeAt (pbValidator v :: vs.map pbValidator) e ∘ Nat.succ) =
        activeAt (vs.map pbValidator) e := by
      funext i; simp [activeAt]
    have hg : ∀ L : List Nat, (L.map Nat.succ).map (· + k) = L.map (· + (k + 1)) := by
      intro L; simp only [List.map_map]; congr 1; funext i; simp; omega
    rw [hf]
    have h0 : activeAt (pbValidator v :: vs.map pbValidator) e 0 =
        EpochProofs.Spec.is_active_validator v e := by
      simp [activeAt, pbValidator, EpochProofs.Spec.is_active_validator,
        CacheProofs.Spec.is_active_validator]
    rw [h0]
    by_cases ha : EpochProofs.Spec.is_active_validator v e
    · simp only [ha, if_true, List.map_cons, hg, ih]; simp
    · simp only [ha, Bool.false_eq_true, if_false, hg, ih]

/-- `get_active_validator_indices` in the closed form of the cache model. -/
theorem get_active_validator_indices_bridge (s : EpochProofs.Spec.BeaconState) (e : Nat) :
    EpochProofs.Spec.get_active_validator_indices s e =
      (List.range s.validators.length).filter (activeAt (s.validators.map pbValidator) e) := by
  have h := active_zipIdx s.validators e 0
  simp only [Nat.add_zero, List.map_id_fun', id_eq] at h
  exact h

theorem mapM_eb (vs : List EpochProofs.Spec.Validator) (L : List Nat)
    (hL : ∀ i ∈ L, i < vs.length) :
    L.mapM (fun index => do
        pure (← EpochProofs.Spec.listGet vs index).effective_balance :
          Nat → EpochProofs.Spec.SpecM Nat) =
      .ok (L.map (ebAt (vs.map pbValidator))) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have hi : i < vs.length := hL i (by simp)
    rw [List.mapM_cons, ih (fun j hj => hL j (by simp [hj]))]
    simp only [EpochProofs.Spec.listGet, List.getElem?_eq_getElem hi]
    simp [ebAt, hi, pbValidator, bind, Except.bind, pure, Except.pure]

/-- `get_total_balance(state, get_unslashed_participating_indices(state, f, e))` in the epoch
spec is the closed form of the cache model, `max EFFECTIVE_BALANCE_INCREMENT flagSum`, on the
mapped state. -/
theorem participating_total_bridge (p : EpochProofs.Spec.Preset)
    (s : EpochProofs.Spec.BeaconState) (f : Nat) (hf : f < 3) (cur prev e : Nat)
    (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (hprev : EpochProofs.Spec.get_previous_epoch p s = .ok prev)
    (he : e = prev ∨ e = cur)
    (hlen : (if e = cur then s.current_epoch_participation
      else s.previous_epoch_participation).length = s.validators.length)
    (hfit : max p.EFFECTIVE_BALANCE_INCREMENT (flagSum (s.validators.map pbValidator)
      ((if e = cur then s.current_epoch_participation
        else s.previous_epoch_participation).map (·.toNat)) e f) < 2 ^ 64) :
    (EpochProofs.Spec.get_unslashed_participating_indices p s f e >>=
        EpochProofs.Spec.get_total_balance p s) =
      .ok (max p.EFFECTIVE_BALANCE_INCREMENT (flagSum (s.validators.map pbValidator)
        ((if e = cur then s.current_epoch_participation
          else s.previous_epoch_participation).map (·.toNat)) e f)) := by
  generalize hP : (if e = cur then s.current_epoch_participation
    else s.previous_epoch_participation) = P at hlen hfit ⊢
  have hP' : (if (e == cur) = true then s.current_epoch_participation
      else s.previous_epoch_participation) = P := by
    rw [← hP]; by_cases h : e = cur <;> simp [h]
  have hcond : (!(e == prev || e == cur)) = false := by
    rcases he with h | h <;> simp [h]
  unfold EpochProofs.Spec.get_unslashed_participating_indices
  simp only [bind, Except.bind, hprev, hcur, hcond, Bool.false_eq_true, if_false, hP',
    get_active_validator_indices_bridge]
  set vs := s.validators.map pbValidator with hvs
  set L0 := (List.range s.validators.length).filter (activeAt vs e) with hL0
  have hL0mem : ∀ i ∈ L0, i < s.validators.length := fun i hi => by
    simp only [hL0, List.mem_filter, List.mem_range] at hi; exact hi.1
  rw [EpochProofs.Spec.forIn_yield_eq_foldlM (step := EpochProofs.Spec.filterStep (fun i => do
      EpochProofs.Spec.has_flag (← EpochProofs.Spec.listGet P i) f) id)]
  rotate_left
  · intro i acc
    simp only [EpochProofs.Spec.filterStep, bind, Except.bind, pure, Except.pure]
    cases EpochProofs.Spec.listGet P i with
    | error e => rfl
    | ok x =>
      dsimp only
      rw [has_flag_bridge x f hf]
      cases CacheProofs.Spec.has_flag x.toNat f <;> rfl
  rw [EpochProofs.Spec.foldlM_filterStep_ok _
    (fun i => CacheProofs.Spec.has_flag ((P.map (·.toNat)).getD i 0) f)]
  rotate_left
  · intro i hi
    have hi' : i < P.length := by rw [hlen]; exact hL0mem i hi
    simp [EpochProofs.Spec.listGet, hi', bind, Except.bind, has_flag_bridge _ f hf, pure,
      Except.pure]
  simp only [List.nil_append, List.map_id]
  set L1 := L0.filter (fun i => CacheProofs.Spec.has_flag ((P.map (·.toNat)).getD i 0) f)
    with hL1
  have hL1mem : ∀ i ∈ L1, i < s.validators.length := fun i hi =>
    hL0mem i (List.mem_filter.mp hi).1
  rw [EpochProofs.Spec.forIn_yield_eq_foldlM (step := EpochProofs.Spec.filterStep (fun i => do
      pure !(← EpochProofs.Spec.listGet s.validators i).slashed) id)]
  rotate_left
  · intro i acc
    simp only [EpochProofs.Spec.filterStep, bind, Except.bind, pure, Except.pure]
    cases EpochProofs.Spec.listGet s.validators i with
    | error e => rfl
    | ok v => dsimp only; cases v.slashed <;> rfl
  rw [EpochProofs.Spec.foldlM_filterStep_ok _ (fun i => !slashedAt vs i)]
  rotate_left
  · intro i hi
    have hi' := hL1mem i hi
    simp [EpochProofs.Spec.listGet, hi', bind, Except.bind, pure, Except.pure, slashedAt, hvs,
      pbValidator]
  simp only [List.nil_append, List.map_id]
  have hL2mem : ∀ i ∈ L1.filter (fun i => !slashedAt vs i), i < s.validators.length :=
    fun i hi => hL1mem i (List.mem_filter.mp hi).1
  have hfilt : L1.filter (fun i => !slashedAt vs i) =
      (List.range vs.length).filter (specPred vs (P.map (·.toNat)) e f) := by
    simp only [hL1, hL0, List.filter_filter, hvs, List.length_map]; rfl
  unfold EpochProofs.Spec.get_total_balance
  have hm := mapM_eb s.validators _ hL2mem
  simp only [bind, Except.bind, pure, Except.pure] at hm ⊢
  rw [hm, ← hvs]
  simp only [hfilt]
  have hlen' : (P.map (·.toNat)).length = vs.length := by simp [hvs, hlen]
  unfold EpochProofs.Spec.uint64Sum
  rw [sum_filter_eq_flagSum vs (P.map (·.toNat)) e f hlen']
  have hsum : flagSum vs (P.map (·.toNat)) e f < EpochProofs.Spec.UINT64_SIZE := by
    simp only [EpochProofs.Spec.UINT64_SIZE]
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hfit
  simp [hsum, pure, Except.pure]

theorem previous_epoch_bridge (p : EpochProofs.Spec.Preset) (s : EpochProofs.Spec.BeaconState)
    (cur prev : Nat) (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (hprev : EpochProofs.Spec.get_previous_epoch p s = .ok prev) :
    CacheProofs.Spec.get_previous_epoch (pbState s cur) = prev := by
  simp only [EpochProofs.Spec.get_previous_epoch, bind, Except.bind, hcur, pure,
    Except.pure, Except.ok.injEq] at hprev
  subst hprev
  simp only [CacheProofs.Spec.get_previous_epoch, CacheProofs.Spec.get_current_epoch, pbState,
    CacheProofs.Spec.GENESIS_EPOCH, EpochProofs.Spec.saturating_sub]
  by_cases h : cur = 0
  · simp [h]
  · simp only [h, if_false]
    by_cases h1 : cur > 1
    · rw [if_pos h1]
    · rw [if_neg h1]
      have hc1 : cur = 1 := by
        have h1' : ¬ 1 < cur := h1
        omega
      subst hc1; rfl

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache PreviousCoherent CurrentCoherent total_flag_balance_ok
  lhPreviousEpochFlagAttestingBalance lhCurrentEpochFlagAttestingBalance) in
/-- The previous epoch total that Lighthouse reads from a coherent progressive balances cache
equals the epoch spec total `get_total_balance(state, get_unslashed_participating_indices(state,
f, get_previous_epoch(state)))`, after the genesis epoch. -/
theorem lh_previous_flag_balance_eq (p : EpochProofs.Spec.Preset)
    (s : EpochProofs.Spec.BeaconState) (f : Usize) (hf : f.val < 3) (cur prev : Nat)
    (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (hprev : EpochProofs.Spec.get_previous_epoch p s = .ok prev) (hne : prev ≠ cur)
    (hlen : s.previous_epoch_participation.length = s.validators.length)
    (hfit : max p.EFFECTIVE_BALANCE_INCREMENT (flagSum (s.validators.map pbValidator)
      (s.previous_epoch_participation.map (·.toNat)) prev f.val) < 2 ^ 64)
    (c : LhCache) (hc : PreviousCoherent p.EFFECTIVE_BALANCE_INCREMENT (pbState s cur) c) :
    ∃ x : U64, lhPreviousEpochFlagAttestingBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices p s f.val prev >>=
        EpochProofs.Spec.get_total_balance p s) = .ok x.val := by
  unfold PreviousCoherent at hc
  rw [previous_epoch_bridge p s cur prev hcur hprev] at hc
  obtain ⟨x, hx, hv⟩ := total_flag_balance_ok _ f _ _ hc hf
  refine ⟨x, hx, ?_⟩
  have h := participating_total_bridge p s f.val hf cur prev prev hcur hprev (Or.inl rfl)
    (by simp [hne, hlen]) (by simpa [hne] using hfit)
  simp only [hne, if_false] at h
  rw [h, hv, Nat.max_comm]
  rfl

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache PreviousCoherent CurrentCoherent total_flag_balance_ok
  lhPreviousEpochFlagAttestingBalance lhCurrentEpochFlagAttestingBalance) in
/-- The current epoch total that Lighthouse reads from a coherent progressive balances cache
equals the epoch spec total for `get_current_epoch(state)`. -/
theorem lh_current_flag_balance_eq (p : EpochProofs.Spec.Preset)
    (s : EpochProofs.Spec.BeaconState) (f : Usize) (hf : f.val < 3) (cur prev : Nat)
    (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (hprev : EpochProofs.Spec.get_previous_epoch p s = .ok prev)
    (hlen : s.current_epoch_participation.length = s.validators.length)
    (hfit : max p.EFFECTIVE_BALANCE_INCREMENT (flagSum (s.validators.map pbValidator)
      (s.current_epoch_participation.map (·.toNat)) cur f.val) < 2 ^ 64)
    (c : LhCache) (hc : CurrentCoherent p.EFFECTIVE_BALANCE_INCREMENT (pbState s cur) c) :
    ∃ x : U64, lhCurrentEpochFlagAttestingBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices p s f.val cur >>=
        EpochProofs.Spec.get_total_balance p s) = .ok x.val := by
  obtain ⟨-, hc⟩ := hc
  obtain ⟨x, hx, hv⟩ := total_flag_balance_ok _ f _ _ hc hf
  refine ⟨x, hx, ?_⟩
  have h := participating_total_bridge p s f.val hf cur prev cur hcur hprev (Or.inr rfl)
    (by simp [hlen]) (by simpa using hfit)
  simp only [if_true] at h
  rw [h, hv, Nat.max_comm]
  rfl

end EpochProofs.CacheBridge
