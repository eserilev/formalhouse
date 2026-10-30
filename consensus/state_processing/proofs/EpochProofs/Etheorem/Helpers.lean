import EpochProofs.Assumptions.Etheorem
import EpochProofs.Spec.Epoch
import EpochProofs.Sanity.RewardsBound
import EpochProofs.Sanity.Invariants.BalanceFloor
import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Fulu.EpochProcessing
import EpochProofs.Sanity.FuluRegistry

/-!
# Shared helpers: the reference equals Etheorem

Many epoch steps call the same helpers. This file proves each helper equal to its Etheorem
copy, so a step proof uses one lemma per call.

Etheorem's `UInt64` arithmetic wraps. The reference raises on overflow, as pyspec does. So a
lemma about arithmetic has the form "if the reference returns `n`, then Etheorem's value reads
as `n`". A wrap in Etheorem happens only where the reference raises.

`PresetAgrees p` says that the Etheorem preset and config hold the values of `p`. Fulu's churn
limits are the Electra ones, and `FuluChurnAgrees p f` says that Etheorem's Fulu config holds
them.

Each proof here holds for Gloas and for Fulu. `forkproof EpochEtheorem` (see `Forks.lean`)
elaborates the shared text once per fork, and `forkonly` holds the parts that differ.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs

/-! ## `UInt64` arithmetic -/

theorem uint64Add_ok {a b : UInt64} {n : Nat} (h : Spec.uint64Add a.toNat b.toNat = .ok n) :
    (a + b).toNat = n := by
  unfold Spec.uint64Add at h
  split at h
  · cases h; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [Spec.UINT64_SIZE] using ‹_›)]
  · cases h

theorem uint64Sub_ok {a b : UInt64} {n : Nat} (h : Spec.uint64Sub a.toNat b.toNat = .ok n) :
    (a - b).toNat = n := by
  unfold Spec.uint64Sub at h
  split at h
  · cases h; rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr ‹_›)]
  · cases h

theorem uint64Mul_ok {a b : UInt64} {n : Nat} (h : Spec.uint64Mul a.toNat b.toNat = .ok n) :
    (a * b).toNat = n := by
  unfold Spec.uint64Mul at h
  split at h
  · cases h; rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [Spec.UINT64_SIZE] using ‹_›)]
  · cases h

theorem uint64Div_ok {a b : UInt64} {n : Nat} (h : Spec.uint64Div a.toNat b.toNat = .ok n) :
    (a / b).toNat = n := by
  unfold Spec.uint64Div at h
  split at h
  · cases h
  · cases h; rw [UInt64.toNat_div]

theorem uint64Mod_ok {a b : UInt64} {n : Nat} (h : Spec.uint64Mod a.toNat b.toNat = .ok n) :
    (a % b).toNat = n := by
  unfold Spec.uint64Mod at h
  split at h
  · cases h
  · cases h; rw [UInt64.toNat_mod]

/-- Division of `UInt64` values never wraps, so the reference succeeds when the divisor is not
zero. -/
theorem uint64Div_toNat (a b : UInt64) (hb : b.toNat ≠ 0) :
    Spec.uint64Div a.toNat b.toNat = .ok (a / b).toNat := by
  simp [Spec.uint64Div, hb, UInt64.toNat_div]; rfl

theorem uint64Mod_toNat (a b : UInt64) (hb : b.toNat ≠ 0) :
    Spec.uint64Mod a.toNat b.toNat = .ok (a % b).toNat := by
  simp [Spec.uint64Mod, hb, UInt64.toNat_mod]; rfl

theorem umax_toNat (a b : UInt64) : (umax a b).toNat = max a.toNat b.toNat := by
  unfold umax
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega

theorem umin_toNat (a b : UInt64) : (umin a b).toNat = min a.toNat b.toNat := by
  unfold umin
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega

/-! ## Lists -/

/-- `indicesWhere` keeps the indices where the predicate holds, in order. -/
theorem indicesWhere_toList {α : Type} [Inhabited α] (xs : Array α) (q : α → Nat → Bool) :
    (indicesWhere xs q).toList =
      ((List.range xs.size).filter fun i => q xs[i]! i).map UInt64.ofNat := by
  have key : ∀ (l : List Nat) (acc : Array UInt64),
      (l.foldl (fun r i => if q xs[i]! i = true then r.push (UInt64.ofNat i) else r) acc).toList =
        acc.toList ++ ((l.filter fun i => q xs[i]! i).map UInt64.ofNat) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i l ih =>
      intro acc
      by_cases hq : q xs[i]! i = true
      · simp [hq, ih]
      · simp [hq, ih]
  have hbody : (fun (i : Nat) (r : Array UInt64) =>
      if q xs[i]! i = true then (pure (ForInStep.yield (r.push (UInt64.ofNat i))) : Id _)
      else pure (ForInStep.yield r)) =
      fun i r => pure (ForInStep.yield
        (if q xs[i]! i = true then r.push (UInt64.ofNat i) else r)) := by
    funext i r; split <;> rfl
  unfold indicesWhere
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', pure_bind, bind_pure]
  rw [hbody, List.forIn_pure_yield_eq_foldl]
  simp only [Std.Legacy.Range.size, List.range_eq_range', Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  have h := key (List.range' 0 xs.size) #[]
  rw [Array.toList_empty, List.nil_append] at h
  exact h

theorem zipIdx_map_eq {α β : Type} [Inhabited α] (xs : Array α) (f : α → β) :
    (xs.toList.map f).zipIdx = (List.range xs.size).map fun i => (f xs[i]!, i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_zipIdx, List.length_map, Array.length_toList] at h1
    simp [List.getElem_zipIdx, getElem!_pos xs i h1]

theorem foldl_add_toNat {β : Type} (g : β → UInt64) : ∀ (l : List β) (a : UInt64),
    a.toNat + (l.map fun i => (g i).toNat).sum < 2 ^ 64 →
    (l.foldl (fun acc i => acc + g i) a).toNat = a.toNat + (l.map fun i => (g i).toNat).sum := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons i l ih =>
    intro a h
    simp only [List.map_cons, List.sum_cons, List.foldl_cons] at h ⊢
    have hstep : (a + g i).toNat = a.toNat + (g i).toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    rw [ih _ (by rw [hstep]; omega), hstep]
    omega

/-! ## Integer square root

Etheorem's `isqrt` runs at most 200 Newton steps. From `n` the distance to the floor square
root halves each step, so 65 steps are enough for `n < 2 ^ 64`. -/

theorem isqrtAux_eq (n s : Nat) (hs : s * s ≤ n) (hs1 : n < (s + 1) * (s + 1)) (hn : 0 < n) :
    ∀ f x, s ≤ x → x - s < 2 ^ f → isqrtAux n (f + 1) x = s := by
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hs1; omega
    · exact h
  -- One Newton step from `x ≥ s` stays at or above `s`.
  have hge : ∀ x, s ≤ x → s ≤ (x + n / x) / 2 := by
    intro x hx
    have := Spec.sqrt_step n x (by omega)
    by_cases hlt : (x + n / x) / 2 < s
    · have := Nat.mul_self_le_mul_self (show (x + n / x) / 2 + 1 ≤ s by omega)
      omega
    · omega
  -- Above `s`, `n / x ≤ s`, so the step at least halves the distance.
  have hdiv : ∀ x, s + 1 ≤ x → n / x ≤ s := by
    intro x hx
    have : n < (s + 1) * x := Nat.lt_of_lt_of_le hs1 (Nat.mul_le_mul_left _ hx)
    have h2 : n / x < s + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr this
    omega
  intro f
  induction f with
  | zero =>
    intro x hx hd
    have hxs : x = s := by simp at hd; omega
    subst hxs
    have := hge x (Nat.le_refl x)
    simp only [isqrtAux]
    rw [if_neg (by omega)]
  | succ f ih =>
    intro x hx hd
    rw [isqrtAux]
    have hy := hge x hx
    by_cases hlt : (x + n / x) / 2 < x
    · rw [if_pos hlt]
      have hxs : s + 1 ≤ x := by omega
      have := hdiv x hxs
      apply ih _ hy
      rw [Nat.pow_succ] at hd
      omega
    · rw [if_neg hlt]
      by_cases hxs : s + 1 ≤ x
      · have := hdiv x hxs; omega
      · omega

theorem isqrt_eq_integer_squareroot (n : Nat) (hn : n < 2 ^ 64) :
    isqrt n = Spec.integer_squareroot n := by
  have hs := Spec.integer_squareroot_mul_self_le n
  have hs1 := Spec.integer_squareroot_spec n
  unfold isqrt
  split
  · rename_i h0
    subst h0
    have : Spec.integer_squareroot 0 = 0 := by
      unfold Spec.integer_squareroot
      rw [if_neg (by simp [Spec.UINT64_MAX]), Spec.integer_squareroot.loop.eq_1]
      simp
    rw [this]
  · rename_i h0
    have hle : Spec.integer_squareroot n ≤ n := by
      rcases Nat.eq_zero_or_pos (Spec.integer_squareroot n) with h | h
      · rw [h]; exact Nat.zero_le _
      · exact Nat.le_trans (Nat.le_mul_of_pos_left _ h) hs
    exact isqrtAux_eq n _ hs hs1 (by omega) 199 n hle
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans hn (Nat.pow_lt_pow_right (by omega)
        (by omega))))

theorem listGet_map_ok {α β : Type} [Inhabited α] (xs : Array α) (f : α → β) (i : Nat) {v : β}
    (h : Spec.listGet (xs.toList.map f) i = .ok v) : i < xs.size ∧ v = f xs[i]! := by
  unfold Spec.listGet at h
  by_cases hi : i < xs.size
  · have hget : (xs.toList.map f)[i]? = some (f xs[i]!) := by simp [hi]
    rw [hget] at h
    exact ⟨hi, (Except.ok.inj h).symm⟩
  · have hnone : (xs.toList.map f)[i]? = none := by simp; omega
    rw [hnone] at h
    cases h

/-! ## Checked `uint64` arithmetic in Etheorem

Etheorem's `checkedAdd` and `checkedMul` raise `.arithmetic` on overflow, as the spec's `uint64`
does. Below `2^64` they return the plain sum and product. -/

theorem checkedAdd_of_lt {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [EthCLLib.Spec.ErrorConv EthCLLib.Spec.StateTransitionError E] (a b : UInt64) (d : String)
    (h : a.toNat + b.toNat < 2 ^ 64) :
    (EthCLLib.Spec.checkedAdd a b d : m UInt64) = pure (a + b) := by
  unfold EthCLLib.Spec.checkedAdd
  rw [if_neg]
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa [UInt64.size] using h)]
  omega

theorem checkedMul_of_lt {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [EthCLLib.Spec.ErrorConv EthCLLib.Spec.StateTransitionError E] (a b : UInt64) (d : String)
    (h : a.toNat * b.toNat < 2 ^ 64) :
    (EthCLLib.Spec.checkedMul a b d : m UInt64) = pure (a * b) := by
  unfold EthCLLib.Spec.checkedMul
  rw [if_neg]
  intro hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨ha, hne⟩ := hc
  apply hne
  have ha' : a.toNat ≠ 0 := fun h0 => ha (UInt64.toNat_inj.mp (by simpa using h0))
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [UInt64.size] using h),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha')]

/-- A spec `uint64Add` that returns has no overflow. -/
theorem uint64Add_lt {a b s : Nat} (h : Spec.uint64Add a b = .ok s) : a + b < 2 ^ 64 := by
  unfold Spec.uint64Add at h
  split at h
  · assumption
  · cases h

/-- A spec `uint64Mul` that returns has no overflow. -/
theorem uint64Mul_lt {a b s : Nat} (h : Spec.uint64Mul a b = .ok s) : a * b < 2 ^ 64 := by
  unfold Spec.uint64Mul at h
  split at h
  · assumption
  · cases h

/-- The value of a spec `uint64Add` that returns. -/
theorem uint64Add_val {a b s : Nat} (h : Spec.uint64Add a b = .ok s) : s = a + b := by
  unfold Spec.uint64Add at h
  split at h
  · cases h; rfl
  · cases h

/-- Every step of a successful `mapM` succeeds. -/
theorem mapM_ok_each {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) {vs : List β}, l.mapM f = .ok vs → ∀ a ∈ l, ∃ b, f a = .ok b := by
  intro l
  induction l with
  | nil => intro _ _ a ha; simp at ha
  | cons x l ih =>
    intro vs h a ha
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hx : f x with
    | error err => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      simp only at h
      cases hl : l.mapM f with
      | error err => rw [hl] at h; cases h
      | ok bs =>
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨b, hx⟩
        · exact ih hl a ha

section WithPreset

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]

/-! ## Epochs and slots

The preset structures (`PresetAgrees` and the others) are in `Assumptions/Etheorem.lean`. -/

section Epochs

variable {p : Spec.Preset} (hp : PresetAgrees p)
include hp

theorem compute_epoch_at_slot_eq (slot : UInt64) :
    Spec.compute_epoch_at_slot p slot.toNat =
      .ok (EthCLSpecs.Gloas.computeEpochAtSlot slot).toNat := by
  have hlt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  have hpos := EthCLSpecs.Gloas.Const.slotsPerEpochPos
  have hne : (UInt64.ofNat EthCLSpecs.Gloas.Const.slotsPerEpoch).toNat ≠ 0 := by
    rw [UInt64.toNat_ofNat_of_lt' hlt]; omega
  have h := uint64Div_toNat slot _ hne
  rw [UInt64.toNat_ofNat_of_lt' hlt] at h
  unfold EthCLSpecs.Gloas.computeEpochAtSlot Spec.compute_epoch_at_slot
  rw [← hp.slotsPerEpoch]
  exact h

variable [HasherTag]

theorem get_current_epoch_eq (e : EtheoremState) :
    Spec.get_current_epoch p (toSpecState e) =
      .ok (EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat :=
  compute_epoch_at_slot_eq hp e.slot

theorem get_previous_epoch_eq (e : EtheoremState) :
    Spec.get_previous_epoch p (toSpecState e) =
      .ok (EthCLSpecs.Gloas.previousEpochOf (pureState e)).toNat := by
  unfold Spec.get_previous_epoch EthCLSpecs.Gloas.previousEpochOf
  rw [get_current_epoch_eq hp]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Spec.saturating_sub]
  generalize EthCLSpecs.Gloas.currentEpochOf (pureState e) = c
  have hg : EthCLSpecs.Gloas.Const.genesisEpoch = 0 := rfl
  rw [hg]
  by_cases h0 : c = 0
  · subst h0; simp
  · have hc : 0 < c.toNat := by
      rcases Nat.eq_zero_or_pos c.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) h0
      · exact h
    simp only [beq_iff_eq, h0, if_false]
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp only [UInt64.toNat_one]
    rcases Nat.lt_or_ge 1 c.toNat with h1 | h1
    · rw [if_pos h1]
    · have h2 : c.toNat = 1 := by omega
      rw [if_neg (Nat.not_lt.mpr h1), h2]

omit [HasherTag] in
theorem compute_start_slot_at_epoch_ok (epoch : UInt64) {n : Nat}
    (h : Spec.compute_start_slot_at_epoch p epoch.toNat = .ok n) :
    (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch).toNat = n := by
  have hlt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  unfold EthCLSpecs.Gloas.computeStartSlotAtEpoch
  unfold Spec.compute_start_slot_at_epoch at h
  rw [← hp.slotsPerEpoch, ← UInt64.toNat_ofNat_of_lt' hlt] at h
  exact uint64Mul_ok h

omit [HasherTag] in
theorem compute_activation_exit_epoch_ok (epoch : UInt64) {n : Nat}
    (h : Spec.compute_activation_exit_epoch p epoch.toNat = .ok n) :
    (EthCLSpecs.Gloas.computeActivationExitEpoch epoch).toNat = n := by
  unfold EthCLSpecs.Gloas.computeActivationExitEpoch
  unfold Spec.compute_activation_exit_epoch at h
  rw [← hp.maxSeedLookahead] at h
  cases h1 : Spec.uint64Add epoch.toNat 1 with
  | error err => rw [h1] at h; cases h
  | ok m =>
    rw [h1] at h
    have hm := uint64Add_ok (a := epoch) (b := 1) (by simpa using h1)
    rw [← hm] at h
    exact uint64Add_ok h

end Epochs

/-! ## Active validators -/

omit [EthCLSpecs.Gloas.Config] in
theorem is_active_validator_eq (v : EthCLSpecs.Gloas.Validator) (epoch : UInt64) :
    Spec.is_active_validator (absValidator v) epoch.toNat =
      EthCLSpecs.Gloas.isActiveValidator v epoch := by
  simp only [Spec.is_active_validator, EthCLSpecs.Gloas.isActiveValidator, absValidator]
  exact Bool.eq_iff_iff.mpr (by simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt])

section Active

variable {p : Spec.Preset} (hp : PresetAgrees p) [HasherTag]
include hp

theorem get_active_validator_indices_eq (e : EtheoremState) (epoch : UInt64) :
    Spec.get_active_validator_indices (toSpecState e) epoch.toNat =
      (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).toList.map
        UInt64.toNat := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  unfold Spec.get_active_validator_indices EthCLSpecs.Gloas.getActiveValidatorIndices
  simp only [view_uncachedBox, toSpecState_validators, SSZList.toList, SSZList.toArray]
  rw [indicesWhere_toList, zipIdx_map_eq, List.filter_map, List.map_map, List.map_map]
  simp only [Function.comp_def]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_filter, List.mem_range] at hi
  simp [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi.1 hsize)]

end Active

omit [EthCLSpecs.Gloas.Config] in
/-- The effective balances that `get_total_balance` reads. The read raises past the end. -/
theorem mapM_effective_balance_ok (xs : Array EthCLSpecs.Gloas.Validator) :
    ∀ (l : List Nat) (bs : List Nat),
      l.mapM (fun index => do
          pure (← Spec.listGet (xs.toList.map absValidator) index).effective_balance) = .ok bs →
        (∀ i ∈ l, i < xs.size) ∧ bs = l.map fun i => xs[i]!.effectiveBalance.toNat := by
  intro l
  induction l with
  | nil => intro bs h; simp [List.mapM_nil, pure, Except.pure] at h; simp [h]
  | cons i l ih =>
    intro bs h
    rw [List.mapM_cons] at h
    unfold Spec.listGet at h
    by_cases hi : i < xs.size
    · have hget : (xs.toList.map absValidator)[i]? = some (absValidator xs[i]!) := by
        simp [hi]
      rw [hget] at h
      cases hm : l.mapM (fun index => do
          pure (← Spec.listGet (xs.toList.map absValidator) index).effective_balance) with
      | error err =>
        unfold Spec.listGet at hm
        rw [hm] at h; cases h
      | ok bs' =>
        unfold Spec.listGet at hm
        rw [hm] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨hl, hbs⟩ := ih bs' (by unfold Spec.listGet; exact hm)
        refine ⟨?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hi
          · exact hl j hj
        · rw [← h, hbs]; simp [absValidator]
    · have hnone : (xs.toList.map absValidator)[i]? = none := by simp; omega
      rw [hnone] at h
      cases h

section Balances

variable {p : Spec.Preset} (hp : PresetAgrees p) [HasherTag]
include hp

theorem get_total_balance_ok (e : EtheoremState) (indices : Array UInt64) {n : Nat}
    (h : Spec.get_total_balance p (toSpecState e) (indices.toList.map UInt64.toNat) = .ok n) :
    (EthCLSpecs.Gloas.getTotalBalance (pureState e) indices).toNat = n := by
  unfold Spec.get_total_balance at h
  simp only [toSpecState_validators, SSZList.toList] at h
  cases hm : (indices.toList.map UInt64.toNat).mapM (fun index => do
      pure (← Spec.listGet (e.validators.val.toList.map absValidator) index).effective_balance) with
  | error err => rw [hm] at h; cases h
  | ok bs =>
    rw [hm] at h
    obtain ⟨-, hbs⟩ := mapM_effective_balance_ok e.validators.val _ bs hm
    unfold Spec.uint64Sum at h
    rw [show ∀ {β : Type} (f : List Nat → Spec.SpecM β), (Except.ok bs : Spec.SpecM _) >>= f = f bs
      from fun _ => rfl] at h
    by_cases hsum : bs.sum < Spec.UINT64_SIZE
    · have hn : n = max p.EFFECTIVE_BALANCE_INCREMENT bs.sum := by
        simp only [hsum, if_true] at h
        exact (Except.ok.inj h).symm
      subst hn
      unfold EthCLSpecs.Gloas.getTotalBalance
      simp only [view_uncachedBox]
      rw [umax_toNat, hp.effectiveBalanceIncrementG, ← Array.foldl_toList]
      have hsum' : (indices.toList.map fun i => (e.validators[i.toNat]!.effectiveBalance).toNat).sum
          = bs.sum := by
        rw [hbs, List.map_map]
        simp [Function.comp_def, sszList_getElem!_val]
      rw [foldl_add_toNat _ _ _ (by simp only [hsum', UInt64.toNat_zero, Nat.zero_add]; exact hsum),
        hsum']
      simp [Nat.max_comm]
    · simp only [hsum, if_false] at h
      cases h

end Balances

/-! ## Total active balance, base reward and churn -/

section Rewards

variable {p : Spec.Preset} (hp : PresetAgrees p) [HasherTag]
include hp

/-- `get_total_active_balance` in Etheorem, as a `Nat`. -/
abbrev etheoremTotalActiveBalance (e : EtheoremState) : Nat :=
  (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat

theorem get_total_active_balance_ok (e : EtheoremState) {n : Nat}
    (h : Spec.get_total_active_balance p (toSpecState e) = .ok n) :
    etheoremTotalActiveBalance e = n := by
  unfold Spec.get_total_active_balance at h
  rw [get_current_epoch_eq hp] at h
  change Spec.get_total_balance p (toSpecState e)
    (Spec.get_active_validator_indices (toSpecState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat) = .ok n at h
  rw [get_active_validator_indices_eq hp] at h
  exact get_total_balance_ok hp e _ h

omit hp in
theorem get_base_reward_per_increment_ok (e : EtheoremState) {n : Nat}
    (h : Spec.get_base_reward_per_increment p (etheoremTotalActiveBalance e) = .ok n)
    (hp : PresetAgrees p) :
    EthCLSpecs.Gloas.getBaseRewardPerIncrement (pureState e) = n := by
  unfold Spec.get_base_reward_per_increment at h
  unfold EthCLSpecs.Gloas.getBaseRewardPerIncrement
  rw [isqrt_eq_integer_squareroot _ (UInt64.toNat_lt _), hp.effectiveBalanceIncrement,
    hp.baseRewardFactor]
  cases hm : Spec.uint64Mul p.EFFECTIVE_BALANCE_INCREMENT p.BASE_REWARD_FACTOR with
  | error err => rw [hm] at h; cases h
  | ok m =>
    rw [hm] at h
    have hm' : m = p.EFFECTIVE_BALANCE_INCREMENT * p.BASE_REWARD_FACTOR := by
      unfold Spec.uint64Mul at hm
      split at hm
      · exact (Except.ok.inj hm).symm
      · cases hm
    change Spec.uint64Div m _ = _ at h
    unfold Spec.uint64Div at h
    split at h
    · cases h
    · rw [← hm']; exact (Except.ok.inj h)

forkonly Gloas
theorem get_exit_churn_limit_ok (e : EtheoremState) {n : Nat}
    (h : Spec.get_exit_churn_limit p (etheoremTotalActiveBalance e) = .ok n) :
    (EthCLSpecs.Gloas.getExitChurnLimit (pureState e)).toNat = n := by
  unfold Spec.get_exit_churn_limit at h
  unfold EthCLSpecs.Gloas.getExitChurnLimit
  rw [← hp.churnLimitQuotientGloas] at h
  cases hd : Spec.uint64Div (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat
      EthCLSpecs.Gloas.Const.churnLimitQuotientGloas.toNat with
  | error err => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    have hd' := uint64Div_ok hd
    simp only [bind, Except.bind] at h
    rw [← hp.minPerEpochChurnLimitElectra, ← hd', ← umax_toNat, ← hp.effectiveBalanceIncrementG] at h
    cases hm : Spec.uint64Mod (umax EthCLSpecs.Gloas.Const.minPerEpochChurnLimitElectra
        (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e) /
          EthCLSpecs.Gloas.Const.churnLimitQuotientGloas)).toNat
        EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG.toNat with
    | error err => rw [hm] at h; cases h
    | ok m =>
      rw [hm] at h
      rw [← uint64Mod_ok hm] at h
      exact uint64Sub_ok h

theorem get_activation_churn_limit_ok (e : EtheoremState) {n : Nat}
    (h : Spec.get_activation_churn_limit p (etheoremTotalActiveBalance e) = .ok n) :
    (EthCLSpecs.Gloas.getActivationChurnLimit (pureState e)).toNat = n := by
  unfold Spec.get_activation_churn_limit at h
  unfold EthCLSpecs.Gloas.getActivationChurnLimit
  rw [← hp.churnLimitQuotientGloas] at h
  cases hd : Spec.uint64Div (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat
      EthCLSpecs.Gloas.Const.churnLimitQuotientGloas.toNat with
  | error err => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    have hd' := uint64Div_ok hd
    simp only [bind, Except.bind] at h
    rw [← hp.minPerEpochChurnLimitElectra, ← hd', ← umax_toNat, ← hp.effectiveBalanceIncrementG] at h
    cases hm : Spec.uint64Mod (umax EthCLSpecs.Gloas.Const.minPerEpochChurnLimitElectra
        (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e) /
          EthCLSpecs.Gloas.Const.churnLimitQuotientGloas)).toNat
        EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG.toNat with
    | error err => rw [hm] at h; cases h
    | ok m =>
      rw [hm] at h
      rw [← uint64Mod_ok hm] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i c hs
        have hc := uint64Sub_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [umin_toNat, hc, hp.maxPerEpochActivationChurnLimitGloas, h]
end forkonly

forkonly Fulu
theorem get_activation_exit_churn_limit_ok {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f)
    (e : EtheoremState) {n : Nat}
    (h : Spec.get_activation_exit_churn_limit p f (etheoremTotalActiveBalance e) = .ok n) :
    (EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e)).toNat = n := by
  unfold Spec.get_activation_exit_churn_limit Spec.get_balance_churn_limit at h
  unfold EthCLSpecs.Fulu.getActivationExitChurnLimit EthCLSpecs.Fulu.getBalanceChurnLimit
  rw [← hf.churnLimitQuotient] at h
  cases hd : Spec.uint64Div (EthCLSpecs.Fulu.getTotalActiveBalance (pureState e)).toNat
      EthCLSpecs.Fulu.Const.churnLimitQuotient.toNat with
  | error err => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    have hd' := uint64Div_ok hd
    simp only [bind, Except.bind] at h
    rw [← hp.minPerEpochChurnLimitElectra, ← hd', ← umax_toNat, ← hp.effectiveBalanceIncrementG] at h
    cases hm : Spec.uint64Mod (umax EthCLSpecs.Fulu.Const.minPerEpochChurnLimitElectra
        (EthCLSpecs.Fulu.getTotalActiveBalance (pureState e) /
          EthCLSpecs.Fulu.Const.churnLimitQuotient)).toNat
        EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG.toNat with
    | error err => rw [hm] at h; cases h
    | ok m =>
      rw [hm] at h
      rw [← uint64Mod_ok hm] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i c hs
        have hc := uint64Sub_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [umin_toNat, hc, hf.maxPerEpochActivationExitChurnLimit, h]

/-- The Gloas exit churn at `fuluTab` reads as Etheorem's Fulu churn. -/
theorem get_exit_churn_limit_ok {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f) (e : EtheoremState)
    {n : Nat}
    (h : Spec.get_exit_churn_limit p (Spec.fuluTab p f (etheoremTotalActiveBalance e)) = .ok n) :
    (EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e)).toNat = n := by
  rw [← Spec.fulu_exit_churn_eq p f hf.compat] at h
  exact get_activation_exit_churn_limit_ok hp hf e h

/-- The Gloas activation churn at `fuluTab` reads as Etheorem's Fulu churn. -/
theorem get_activation_churn_limit_ok {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f)
    (e : EtheoremState) {n : Nat}
    (h : Spec.get_activation_churn_limit p (Spec.fuluTab p f (etheoremTotalActiveBalance e)) =
      .ok n) :
    (EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e)).toNat = n := by
  rw [← Spec.fulu_activation_churn_eq p f hf.compat] at h
  exact get_activation_exit_churn_limit_ok hp hf e h
end forkonly

end Rewards

/-! ## Balance writes -/

section BalanceWrites

variable [HasherTag]

open EthCLSpecs.Proofs.Gloas (GloasRun)

omit [EthCLSpecs.Gloas.Config] in
/-- `increase_balance` equals Etheorem's `increaseBalance`. Etheorem returns the written state
as its value and leaves the threaded state alone. -/
theorem increase_balance_etheorem (state preState : EtheoremState) (i : EthCLSpecs.Gloas.ValidatorIndex)
    (delta : EthCLSpecs.Gloas.Gwei) {bs : List Nat}
    (h : Spec.increase_balance (state.balances.toList.map UInt64.toNat) i.toNat delta.toNat =
      .ok bs) :
    (EthCLSpecs.Gloas.increaseBalance (StateTransition := GloasRun) (pureState state) i
        delta).run (pureState preState) =
      .ok (pureState { state with
          balances := state.balances.set! i.toNat (state.balances.val[i.toNat]! + delta) },
        pureState preState) ∧
    bs = (state.balances.set! i.toNat (state.balances.val[i.toNat]! + delta)).toList.map
      UInt64.toNat := by
  unfold Spec.increase_balance at h
  cases hg : Spec.listGet (state.balances.toList.map UInt64.toNat) i.toNat with
  | error err => rw [hg] at h; cases h
  | ok b =>
    rw [hg] at h
    obtain ⟨hi, hb⟩ := listGet_map_ok state.balances.val UInt64.toNat i.toNat hg
    change (do Spec.listSet _ _ (← Spec.uint64Add b delta.toNat)) = _ at h
    rw [hb] at h
    cases ha : Spec.uint64Add (state.balances.val[i.toNat]!).toNat delta.toNat with
    | error err => rw [ha] at h; cases h
    | ok c =>
      rw [ha] at h
      have hc := uint64Add_ok ha
      have hsum : (state.balances.val[i.toNat]!).toNat + delta.toNat < 2 ^ 64 := by
        unfold Spec.uint64Add at ha
        split at ha
        · simpa [Spec.UINT64_SIZE] using ‹_›
        · cases ha
      have hcarry : ¬ (state.balances.val[i.toNat]! + delta < state.balances.val[i.toNat]!) := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
        omega
      refine ⟨?_, ?_⟩
      · unfold EthCLSpecs.Gloas.increaseBalance sszGetIdx checkedAdd
        simp only [view_uncachedBox]
        have hsome : state.balances.val[i.toNat]? = some state.balances.val[i.toNat]! := by
          simp [hi]
        rw [hsome]
        simp [hcarry, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
        rfl
      · change Spec.listSet _ _ c = _ at h
        unfold Spec.listSet at h
        rw [if_pos (by simpa using hi)] at h
        cases h
        rw [map_toList_set!, hc]

omit [EthCLSpecs.Gloas.Config] in
/-- `decrease_balance` equals Etheorem's `decreaseBalance`. -/
theorem decrease_balance_etheorem (state preState : EtheoremState) (i : EthCLSpecs.Gloas.ValidatorIndex)
    (delta : EthCLSpecs.Gloas.Gwei) {bs : List Nat}
    (h : Spec.decrease_balance (state.balances.toList.map UInt64.toNat) i.toNat delta.toNat =
      .ok bs) :
    (EthCLSpecs.Gloas.decreaseBalance (StateTransition := GloasRun) (pureState state) i
        delta).run (pureState preState) =
      .ok (pureState { state with
          balances := state.balances.set! i.toNat
            (if delta > state.balances.val[i.toNat]! then 0
             else state.balances.val[i.toNat]! - delta) },
        pureState preState) ∧
    bs = (state.balances.set! i.toNat
      (if delta > state.balances.val[i.toNat]! then 0
       else state.balances.val[i.toNat]! - delta)).toList.map UInt64.toNat := by
  unfold Spec.decrease_balance at h
  cases hg : Spec.listGet (state.balances.toList.map UInt64.toNat) i.toNat with
  | error err => rw [hg] at h; cases h
  | ok b =>
    rw [hg] at h
    obtain ⟨hi, hb⟩ := listGet_map_ok state.balances.val UInt64.toNat i.toNat hg
    refine ⟨?_, ?_⟩
    · unfold EthCLSpecs.Gloas.decreaseBalance sszGetIdx
      simp only [view_uncachedBox]
      have hsome : state.balances.val[i.toNat]? = some state.balances.val[i.toNat]! := by
        simp [hi]
      rw [hsome]
      simp [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl
    · change Spec.listSet _ _ (Spec.saturating_sub b delta.toNat) = _ at h
      unfold Spec.listSet at h
      rw [if_pos (by simpa using hi)] at h
      cases h
      rw [map_toList_set!, hb]
      congr 1
      unfold Spec.saturating_sub
      generalize hbal : state.balances.val[i.toNat]! = bal
      split
      · rename_i hgt
        have hgt' : delta.toNat < bal.toNat := hgt
        rw [if_neg (by rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; omega),
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
      · rename_i hle
        have hle' : bal.toNat ≤ delta.toNat := Nat.not_lt.mp hle
        by_cases hd : delta > bal
        · rw [if_pos hd]; simp
        · rw [if_neg hd]
          have hd' : delta.toNat ≤ bal.toNat := by
            rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at hd; omega
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
          rw [Nat.sub_self, Nat.sub_eq_zero_of_le hle']

end BalanceWrites

/-! ## Exits -/

section Exits

variable {p : Spec.Preset} (hp : PresetAgrees p) [HasherTag]
include hp

open EthCLSpecs.Proofs.Gloas (GloasRun)

forkonly Gloas
omit hp in
/-- Etheorem's `computeExitEpochAndUpdateChurn` on a plain state, as one value. -/
theorem computeExitEpochAndUpdateChurn_run (e : EtheoremState) (b : UInt64) :
    (EthCLSpecs.Gloas.computeExitEpochAndUpdateChurn (StateTransition := GloasRun) b).run
        (pureState e) =
      (let earliest := umax e.earliestExitEpoch
          (EthCLSpecs.Gloas.computeActivationExitEpoch (EthCLSpecs.Gloas.computeEpochAtSlot e.slot))
       let per := EthCLSpecs.Gloas.getExitChurnLimit (pureState e)
       let consume := if e.earliestExitEpoch < earliest then per else e.exitBalanceToConsume
       let r := EthCLSpecs.Gloas.reserveChurn b consume per earliest
       .ok (r.1, pureState { e with exitBalanceToConsume := r.2 - b, earliestExitEpoch := r.1 })) :=
  rfl

/-- `compute_exit_epoch_and_update_churn` equals Etheorem's. Both write the same two churn
fields and return the same exit epoch. -/
theorem compute_exit_epoch_and_update_churn_etheorem (e : EtheoremState) (b : UInt64) {ep : Nat}
    {s' : Spec.BeaconState}
    (h : Spec.compute_exit_epoch_and_update_churn p (etheoremTotalActiveBalance e) (toSpecState e)
      b.toNat = .ok (ep, s')) :
    ∃ ee ebtc : UInt64,
      (EthCLSpecs.Gloas.computeExitEpochAndUpdateChurn (StateTransition := GloasRun) b).run
          (pureState e) =
        .ok (ee, pureState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee }) ∧
      ep = ee.toNat ∧
      s' = toSpecState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee } := by
  rw [computeExitEpochAndUpdateChurn_run]
  unfold Spec.compute_exit_epoch_and_update_churn at h
  rw [get_current_epoch_eq hp] at h
  simp only [bind, Except.bind, toSpecState_earliest_exit_epoch,
    toSpecState_exit_balance_to_consume] at h
  generalize hc : EthCLSpecs.Gloas.currentEpochOf (pureState e) = c at h
  have hc' : EthCLSpecs.Gloas.computeEpochAtSlot e.slot = c := hc
  rw [hc']
  split at h
  · cases h
  next cae hcae =>
  have hcae' := compute_activation_exit_epoch_ok hp c hcae
  split at h
  · cases h
  next per hper =>
  have hper' := get_exit_churn_limit_ok hp e hper
  generalize hE : umax e.earliestExitEpoch (EthCLSpecs.Gloas.computeActivationExitEpoch c) = E
  have hEn : E.toNat = max e.earliestExitEpoch.toNat cae := by rw [← hE, umax_toNat, hcae']
  generalize hP : EthCLSpecs.Gloas.getExitChurnLimit (pureState e) = P at hper'
  generalize hC : (if e.earliestExitEpoch < E then P else e.exitBalanceToConsume) = C
  have hCn : C.toNat = (if e.earliestExitEpoch.toNat < max e.earliestExitEpoch.toNat cae then per
      else e.exitBalanceToConsume.toNat) := by
    rw [← hC, ← hEn]
    split
    · rename_i hlt; rw [if_pos (UInt64.lt_iff_toNat_lt.mp hlt), hper']
    · rename_i hlt; rw [if_neg (fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h'))]
  rw [← hCn, ← hEn] at h
  unfold EthCLSpecs.Gloas.reserveChurn
  dsimp only
  rw [hC]
  split at h
  · rename_i hgt
    have hgt' : b > C := UInt64.lt_iff_toNat_lt.mpr hgt
    rw [if_pos hgt']
    split at h
    · cases h
    next btp hbtp =>
    split at h
    · cases h
    next x hx =>
    split at h
    · cases h
    next d hd =>
    split at h
    · cases h
    next add hadd =>
    split at h
    · cases h
    next E' hE' =>
    split at h
    · cases h
    next m hm =>
    split at h
    · cases h
    next C' hC' =>
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next f hf =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hbtp' := uint64Sub_ok hbtp
    rw [← hbtp'] at hx
    have hx' := uint64Sub_ok (b := 1) (by simpa using hx)
    rw [← hx', ← hper'] at hd
    have hd' := uint64Div_ok hd
    rw [← hd'] at hadd
    have hadd' := uint64Add_ok (a := (b - C - 1) / P) (b := 1)
      (by rw [UInt64.toNat_one]; exact hadd)
    rw [← hadd'] at hE'
    have hE'' := uint64Add_ok hE'
    rw [← hadd', ← hper'] at hm
    have hm' := uint64Mul_ok hm
    rw [← hm'] at hC'
    have hC'' := uint64Add_ok hC'
    rw [← hC''] at hf
    have hf' := uint64Sub_ok hf
    refine ⟨_, _, rfl, hE''.symm, ?_⟩
    simp only [toSpecState]
    rw [hf', hE'']
  · rename_i hle
    have hle' : ¬ b > C := fun h' => hle (UInt64.lt_iff_toNat_lt.mp h')
    rw [if_neg hle']
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next f hf =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hf' := uint64Sub_ok hf
    refine ⟨_, _, rfl, by simp only [hEn], ?_⟩
    simp only [toSpecState]
    rw [hf', hEn]
end forkonly

forkonly Fulu
omit hp in
/-- Etheorem's `computeExitEpochAndUpdateChurn` on a plain state, as one value. -/
theorem computeExitEpochAndUpdateChurn_run (e : EtheoremState) (b : UInt64) :
    (EthCLSpecs.Fulu.computeExitEpochAndUpdateChurn (StateTransition := FuluRun) b).run
        (pureState e) =
      (let earliest := umax e.earliestExitEpoch
          (EthCLSpecs.Fulu.computeActivationExitEpoch (EthCLSpecs.Fulu.computeEpochAtSlot e.slot))
       let per := EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e)
       let consume := if e.earliestExitEpoch < earliest then per else e.exitBalanceToConsume
       let r := EthCLSpecs.Fulu.reserveChurn b consume per earliest
       .ok (r.1, pureState { e with exitBalanceToConsume := r.2 - b, earliestExitEpoch := r.1 })) :=
  rfl

/-- `compute_exit_epoch_and_update_churn` equals Etheorem's. Both write the same two churn
fields and return the same exit epoch. -/
theorem compute_exit_epoch_and_update_churn_etheorem {f : Spec.FuluConfig}
    (hf : FuluChurnAgrees p f) (e : EtheoremState) (b : UInt64) {ep : Nat} {s' : Spec.BeaconState}
    (h : Spec.compute_exit_epoch_and_update_churn p (Spec.fuluTab p f (etheoremTotalActiveBalance e))
      (toSpecState e) b.toNat = .ok (ep, s')) :
    ∃ ee ebtc : UInt64,
      (EthCLSpecs.Fulu.computeExitEpochAndUpdateChurn (StateTransition := FuluRun) b).run
          (pureState e) =
        .ok (ee, pureState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee }) ∧
      ep = ee.toNat ∧
      s' = toSpecState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee } := by
  rw [computeExitEpochAndUpdateChurn_run]
  unfold Spec.compute_exit_epoch_and_update_churn at h
  rw [get_current_epoch_eq hp] at h
  simp only [bind, Except.bind, toSpecState_earliest_exit_epoch,
    toSpecState_exit_balance_to_consume] at h
  generalize hc : EthCLSpecs.Fulu.currentEpochOf (pureState e) = c at h
  have hc' : EthCLSpecs.Fulu.computeEpochAtSlot e.slot = c := hc
  rw [hc']
  split at h
  · cases h
  next cae hcae =>
  have hcae' := compute_activation_exit_epoch_ok hp c hcae
  split at h
  · cases h
  next per hper =>
  have hper' := get_exit_churn_limit_ok hp hf e hper
  generalize hE : umax e.earliestExitEpoch (EthCLSpecs.Fulu.computeActivationExitEpoch c) = E
  have hEn : E.toNat = max e.earliestExitEpoch.toNat cae := by rw [← hE, umax_toNat, hcae']
  generalize hP : EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e) = P at hper'
  generalize hC : (if e.earliestExitEpoch < E then P else e.exitBalanceToConsume) = C
  have hCn : C.toNat = (if e.earliestExitEpoch.toNat < max e.earliestExitEpoch.toNat cae then per
      else e.exitBalanceToConsume.toNat) := by
    rw [← hC, ← hEn]
    split
    · rename_i hlt; rw [if_pos (UInt64.lt_iff_toNat_lt.mp hlt), hper']
    · rename_i hlt; rw [if_neg (fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h'))]
  rw [← hCn, ← hEn] at h
  unfold EthCLSpecs.Fulu.reserveChurn
  dsimp only
  rw [hC]
  split at h
  · rename_i hgt
    have hgt' : b > C := UInt64.lt_iff_toNat_lt.mpr hgt
    rw [if_pos hgt']
    split at h
    · cases h
    next btp hbtp =>
    split at h
    · cases h
    next x hx =>
    split at h
    · cases h
    next d hd =>
    split at h
    · cases h
    next add hadd =>
    split at h
    · cases h
    next E' hE' =>
    split at h
    · cases h
    next m hm =>
    split at h
    · cases h
    next C' hC' =>
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next f hf =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hbtp' := uint64Sub_ok hbtp
    rw [← hbtp'] at hx
    have hx' := uint64Sub_ok (b := 1) (by simpa using hx)
    rw [← hx', ← hper'] at hd
    have hd' := uint64Div_ok hd
    rw [← hd'] at hadd
    have hadd' := uint64Add_ok (a := (b - C - 1) / P) (b := 1)
      (by rw [UInt64.toNat_one]; exact hadd)
    rw [← hadd'] at hE'
    have hE'' := uint64Add_ok hE'
    rw [← hadd', ← hper'] at hm
    have hm' := uint64Mul_ok hm
    rw [← hm'] at hC'
    have hC'' := uint64Add_ok hC'
    rw [← hC''] at hf
    have hf' := uint64Sub_ok hf
    refine ⟨_, _, rfl, hE''.symm, ?_⟩
    simp only [toSpecState]
    rw [hf', hE'']
  · rename_i hle
    have hle' : ¬ b > C := fun h' => hle (UInt64.lt_iff_toNat_lt.mp h')
    rw [if_neg hle']
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next f hf =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hf' := uint64Sub_ok hf
    refine ⟨_, _, rfl, by simp only [hEn], ?_⟩
    simp only [toSpecState]
    rw [hf', hEn]
end forkonly

omit [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] hp in
theorem checkedAdd_run_ok {σ : Type} (a b : UInt64) (d : String) (st : σ)
    (h : a.toNat + b.toNat < 2 ^ 64) :
    (checkedAdd (m := StateT σ (Except StateTransitionError)) a b d).run st = .ok (a + b, st) := by
  have hcarry : ¬ (a + b < a) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt h]; omega
  simp only [checkedAdd, hcarry, if_false]
  rfl

forkonly Gloas
/-- `initiate_validator_exit` equals Etheorem's `initiateValidatorExit`. -/
theorem initiate_validator_exit_etheorem (e : EtheoremState) (i : UInt64) {s' : Spec.BeaconState}
    (h : Spec.initiate_validator_exit p (etheoremTotalActiveBalance e) (toSpecState e) i.toNat =
      .ok s') :
    ∃ e' : EtheoremState,
      (EthCLSpecs.Gloas.initiateValidatorExit (StateTransition := GloasRun) i).run (pureState e) =
        .ok ((), pureState e') ∧ s' = toSpecState e' := by
  unfold Spec.initiate_validator_exit at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  next v hv =>
  rw [toSpecState_validators] at hv
  obtain ⟨hi, rfl⟩ := listGet_map_ok e.validators.val absValidator i.toNat hv
  have hsome : e.validators.val[i.toNat]? = some e.validators.val[i.toNat]! := by simp [hi]
  unfold EthCLSpecs.Gloas.initiateValidatorExit
  simp only [run_bind]
  rw [show (get : GloasRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  simp only [view_uncachedBox]
  rw [run_sszGetIdx_some _ _ _ hsome, except_bind_ok]
  dsimp only
  have hfar : (EthCLSpecs.Gloas.Const.farFutureEpoch).toNat = Spec.FAR_FUTURE_EPOCH := rfl
  by_cases hx : (absValidator e.validators.val[i.toNat]!).exit_epoch != Spec.FAR_FUTURE_EPOCH
  · rw [if_pos hx] at h
    cases h
    have hx' : (!EthCLSpecs.Gloas.hasNotInitiatedExit e.validators.val[i.toNat]!) = true := by
      simp only [EthCLSpecs.Gloas.hasNotInitiatedExit, Bool.not_eq_true']
      simp only [absValidator, bne_iff_ne, ne_eq] at hx
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; apply hx; rw [heq, hfar]
    rw [if_pos hx']
    exact ⟨e, rfl, rfl⟩
  · rw [if_neg hx] at h
    have hx' : ¬ (!EthCLSpecs.Gloas.hasNotInitiatedExit e.validators.val[i.toNat]!) = true := by
      simp only [EthCLSpecs.Gloas.hasNotInitiatedExit, Bool.not_eq_true', Bool.not_eq_false,
        beq_iff_eq]
      simp only [absValidator, bne_iff_ne, ne_eq, Decidable.not_not] at hx
      apply UInt64.toNat_inj.mp
      rw [hx, hfar]
    rw [if_neg hx']
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next r hr =>
    obtain ⟨ep, s1⟩ := r
    obtain ⟨ee, ebtc, hrun, hep, hs1⟩ :=
      compute_exit_epoch_and_update_churn_etheorem hp e (e.validators.val[i.toNat]!).effectiveBalance hr
    simp only [run_bind]
    rw [hrun, except_bind_ok]
    split at h
    · cases h
    next w hw =>
    rw [← hp.minValidatorWithdrawabilityDelay, hep] at hw
    have hsum : ee.toNat + EthCLSpecs.Gloas.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64 := by
      unfold Spec.uint64Add at hw
      split at hw
      · simpa [Spec.UINT64_SIZE] using ‹_›
      · cases hw
    have hw' := uint64Add_ok hw
    rw [checkedAdd_run_ok _ _ _ _ hsum, except_bind_ok]
    split at h
    · cases h
    next vs hvs =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨{ e with
        exitBalanceToConsume := ebtc
        earliestExitEpoch := ee
        validators := e.validators.set! i.toNat
          { e.validators[i.toNat]! with
            exitEpoch := ee
            withdrawableEpoch := ee + EthCLSpecs.Gloas.Const.minValidatorWithdrawabilityDelay } },
      rfl, ?_⟩
    subst hs1
    unfold Spec.listSet at hvs
    have hlen : i.toNat <
        (toSpecState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee }).validators.length := by
      simpa using hi
    rw [if_pos hlen] at hvs
    cases hvs
    simp only [toSpecState, map_toList_set!, sszList_getElem!_val, absValidator, hep, ← hw']
end forkonly

forkonly Fulu
/-- `initiate_validator_exit` equals Etheorem's `initiateValidatorExit`. -/
theorem initiate_validator_exit_etheorem {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f)
    (e : EtheoremState) (i : UInt64) {s' : Spec.BeaconState}
    (h : Spec.initiate_validator_exit p (Spec.fuluTab p f (etheoremTotalActiveBalance e))
      (toSpecState e) i.toNat = .ok s') :
    ∃ e' : EtheoremState,
      (EthCLSpecs.Fulu.initiateValidatorExit (StateTransition := FuluRun) i).run (pureState e) =
        .ok ((), pureState e') ∧ s' = toSpecState e' := by
  unfold Spec.initiate_validator_exit at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  next v hv =>
  rw [toSpecState_validators] at hv
  obtain ⟨hi, rfl⟩ := listGet_map_ok e.validators.val absValidator i.toNat hv
  have hsome : e.validators.val[i.toNat]? = some e.validators.val[i.toNat]! := by simp [hi]
  unfold EthCLSpecs.Fulu.initiateValidatorExit
  simp only [run_bind]
  rw [show (get : FuluRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  simp only [view_uncachedBox]
  rw [run_sszGetIdx_some _ _ _ hsome, except_bind_ok]
  dsimp only
  have hfar : (EthCLSpecs.Fulu.Const.farFutureEpoch).toNat = Spec.FAR_FUTURE_EPOCH := rfl
  by_cases hx : (absValidator e.validators.val[i.toNat]!).exit_epoch != Spec.FAR_FUTURE_EPOCH
  · rw [if_pos hx] at h
    cases h
    have hx' : (!EthCLSpecs.Fulu.hasNotInitiatedExit e.validators.val[i.toNat]!) = true := by
      simp only [EthCLSpecs.Fulu.hasNotInitiatedExit, Bool.not_eq_true']
      simp only [absValidator, bne_iff_ne, ne_eq] at hx
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; apply hx; rw [heq, hfar]
    rw [if_pos hx']
    exact ⟨e, rfl, rfl⟩
  · rw [if_neg hx] at h
    have hx' : ¬ (!EthCLSpecs.Fulu.hasNotInitiatedExit e.validators.val[i.toNat]!) = true := by
      simp only [EthCLSpecs.Fulu.hasNotInitiatedExit, Bool.not_eq_true', Bool.not_eq_false,
        beq_iff_eq]
      simp only [absValidator, bne_iff_ne, ne_eq, Decidable.not_not] at hx
      apply UInt64.toNat_inj.mp
      rw [hx, hfar]
    rw [if_neg hx']
    split at h
    · cases h
    next _ _ =>
    split at h
    · cases h
    next r hr =>
    obtain ⟨ep, s1⟩ := r
    obtain ⟨ee, ebtc, hrun, hep, hs1⟩ :=
      compute_exit_epoch_and_update_churn_etheorem hp hf e (e.validators.val[i.toNat]!).effectiveBalance hr
    simp only [run_bind]
    rw [hrun, except_bind_ok]
    split at h
    · cases h
    next w hw =>
    rw [← hp.minValidatorWithdrawabilityDelay, hep] at hw
    have hsum : ee.toNat + EthCLSpecs.Fulu.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64 := by
      unfold Spec.uint64Add at hw
      split at hw
      · simpa [Spec.UINT64_SIZE] using ‹_›
      · cases hw
    have hw' := uint64Add_ok hw
    rw [checkedAdd_run_ok _ _ _ _ hsum, except_bind_ok]
    split at h
    · cases h
    next vs hvs =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨{ e with
        exitBalanceToConsume := ebtc
        earliestExitEpoch := ee
        validators := e.validators.set! i.toNat
          { e.validators[i.toNat]! with
            exitEpoch := ee
            withdrawableEpoch := ee + EthCLSpecs.Fulu.Const.minValidatorWithdrawabilityDelay } },
      rfl, ?_⟩
    subst hs1
    unfold Spec.listSet at hvs
    have hlen : i.toNat <
        (toSpecState { e with exitBalanceToConsume := ebtc, earliestExitEpoch := ee }).validators.length := by
      simpa using hi
    rw [if_pos hlen] at hvs
    cases hvs
    simp only [toSpecState, map_toList_set!, sszList_getElem!_val, absValidator, hep, ← hw']
end forkonly

end Exits

end WithPreset

/-! ## The two presets -/

forkonly Gloas
section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
theorem presetAgrees_mainnet : PresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
end

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
theorem presetAgrees_minimal : PresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
end
end forkonly

forkonly Fulu
section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
theorem presetAgrees_mainnet : PresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
theorem fuluChurnAgrees_mainnet : FuluChurnAgrees Spec.Preset.mainnet Spec.FuluConfig.mainnet :=
  ⟨Spec.fuluCompat_mainnet, rfl, rfl⟩
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
theorem presetAgrees_minimal : PresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
theorem fuluChurnAgrees_minimal : FuluChurnAgrees Spec.Preset.minimal Spec.FuluConfig.minimal :=
  ⟨Spec.fuluCompat_minimal, rfl, rfl⟩
end
end forkonly

end forkproof

