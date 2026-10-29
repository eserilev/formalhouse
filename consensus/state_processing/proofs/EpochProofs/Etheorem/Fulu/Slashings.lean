import EpochProofs.Etheorem.Fulu.Participation

/-!
# `process_slashings`: the reference equals Etheorem

The main theorem is `slashings_etheorem`. `slashingsE` is Etheorem's step on a plain state, and
`processSlashings_run` proves that Etheorem's run gives it.

The reference computes `epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2` only for a slashed validator.
`slashings_target_lt` shows that this sum always fits in a `uint64`, because the epoch is at most
half of the slot. Etheorem raises on an overflow of the slashings sum and of the penalty
products, at the same operations as the reference. `slashingsPreamble_bounds` and
`slashing_fold` read the bounds off a reference run that returns.
-/

namespace EpochProofs.Etheorem.Fulu
open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Fulu

variable [EthCLSpecs.Fulu.Preset] [HasherTag]

/-- The test of Etheorem's slashings loop for one validator. -/
def slashCondE (epoch : UInt64) (v : EthCLSpecs.Fulu.Validator) : Bool :=
  v.slashed && epoch + UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSlashingsVector / 2 ==
    v.withdrawableEpoch

/-- The penalty that Etheorem's `decreaseBalance` writes. -/
def decreasedE (b d : UInt64) : UInt64 := if d > b then 0 else b - d

/-- One iteration of Etheorem's slashings loop on a plain state. -/
def slashStepE (epoch ppi : UInt64) (w : EState) (i : Nat) : EState :=
  if slashCondE epoch w.validators[i]! then
    { w with balances := w.balances.set! (UInt64.ofNat i).toNat (decreasedE
        w.balances.val[(UInt64.ofNat i).toNat]!
        (ppi * (w.validators[i]!.effectiveBalance / EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG))) }
  else w

variable [EthCLSpecs.Fulu.Config]

/-- The penalty per increment in Etheorem's `process_slashings`. -/
def slashPpiE (e : EState) : UInt64 :=
  umin (e.slashings.toArray.foldl (· + ·) 0 *
      UInt64.ofNat EthCLSpecs.Fulu.Const.proportionalSlashingMultiplierBellatrix)
    (EthCLSpecs.Fulu.getTotalActiveBalance (pureState e)) /
  (EthCLSpecs.Fulu.getTotalActiveBalance (pureState e) / EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG)

/-- The state after Etheorem's `process_slashings`. -/
def slashingsE (e : EState) : EState :=
  (List.range' 0 e.validators.val.size).foldl
    (slashStepE (EthCLSpecs.Fulu.currentEpochOf (pureState e)) (slashPpiE e)) e

omit [EthCLSpecs.Fulu.Config] in
/-- Etheorem's checked sum of a list runs as the plain sum while the total stays below `2^64`. -/
theorem foldlM_checkedAdd_run (d : String) (s : EthCLSpecs.Fulu.State) :
    ∀ (l : List UInt64) (acc : UInt64), acc.toNat + (l.map UInt64.toNat).sum < 2 ^ 64 →
      (l.foldlM (fun a x => checkedAdd a x d) acc : FuluRun UInt64).run s =
        .ok (l.foldl (· + ·) acc, s) := by
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons x l ih =>
    intro acc h
    simp only [List.map_cons, List.sum_cons] at h
    rw [List.foldlM_cons, run_bind, checkedAdd_of_lt _ _ _ (by omega), run_pure, except_bind_ok,
      List.foldl_cons]
    apply ih
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by first | omega | (simp only [UInt64.size]; omega))]
    omega

omit [EthCLSpecs.Fulu.Config] in
theorem processSlashings_run (e : EState)
    (hsum : (e.slashings.toList.map UInt64.toNat).sum < 2 ^ 64)
    (hmul : (e.slashings.toArray.foldl (· + ·) 0).toNat *
      (UInt64.ofNat EthCLSpecs.Fulu.Const.proportionalSlashingMultiplierBellatrix).toNat < 2 ^ 64)
    (hidx : ∀ i < e.validators.val.size,
      slashCondE (EthCLSpecs.Fulu.currentEpochOf (pureState e)) e.validators[i]! →
        (UInt64.ofNat i).toNat < e.balances.val.size ∧
          (slashPpiE e).toNat * (e.validators[i]!.effectiveBalance /
            EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG).toNat < 2 ^ 64) :
    (EthCLSpecs.Fulu.processSlashings (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState (slashingsE e)) := by
  unfold EthCLSpecs.Fulu.processSlashings
  rw [run_bind, show (get : FuluRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  simp only [view_uncachedBox]
  rw [run_bind, ← Array.foldlM_toList, foldlM_checkedAdd_run _ _ _ _ (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hsum),
    except_bind_ok]
  dsimp only
  rw [Array.foldl_toList] 
  rw [run_bind, checkedMul_of_lt _ _ _ hmul, run_pure, except_bind_ok]
  dsimp only
  rw [run_bind, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_run_pureState (pureState e)
    (fun i w => slashStepE (EthCLSpecs.Fulu.currentEpochOf (pureState e)) (slashPpiE e) w i)
    (fun w => w.validators = e.validators ∧ w.balances.val.size = e.balances.val.size)]
  · rfl
  · intro i hi w hw
    unfold slashStepE
    split
    · exact ⟨hw.1, by simp [hw.2]⟩
    · exact hw
  · intro i hi w hw
    obtain ⟨hv, hb⟩ := hw
    have hi' : i < e.validators.val.size := by simpa using hi
    simp only [view_uncachedBox, slashStepE]
    by_cases hc : slashCondE (EthCLSpecs.Fulu.currentEpochOf (pureState e)) w.validators[i]! = true
    · rw [if_pos hc]
      have hc' := hc
      unfold slashCondE at hc'
      rw [if_pos hc']
      rw [hv] at hc
      obtain ⟨hlt, hmulI⟩ := hidx i hi' hc
      rw [← hb] at hlt
      rw [← hv] at hmulI
      have hsome : w.balances.val[(UInt64.ofNat i).toNat]? =
          some w.balances.val[(UInt64.ofNat i).toNat]! := by
        rw [getElem!_pos w.balances.val _ hlt]; exact Array.getElem?_eq_getElem hlt
      rw [run_bind]
      erw [checkedMul_of_lt _ _ _ hmulI]
      rw [run_pure, except_bind_ok]
      rw [run_bind]
      unfold EthCLSpecs.Fulu.decreaseBalance
      rw [run_bind, view_uncachedBox, run_sszGetIdx_some _ _ _ hsome, except_bind_ok]
      rfl
    · rw [if_neg hc]
      have hc' := hc
      unfold slashCondE at hc'
      rw [if_neg hc']
      rfl
  · exact ⟨rfl, rfl⟩

omit [EthCLSpecs.Fulu.Config] [HasherTag] in
theorem foldl_slashStepE_validators (epoch ppi : UInt64) : ∀ (l : List Nat) (w : EState),
    (l.foldl (slashStepE epoch ppi) w) =
      { w with balances := (l.foldl (slashStepE epoch ppi) w).balances } := by
  intro l
  induction l with
  | nil => intro w; rfl
  | cons i l ih =>
    intro w
    rw [List.foldl_cons, ih]
    unfold slashStepE
    split <;> rfl

section Slashings

variable {p : Spec.Preset} (hpp : PassesPresetAgrees p)
include hpp

theorem slashing_fold (e : EState) (epoch ppi : UInt64) {target per : Nat}
    (htarget : (epoch + UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSlashingsVector / 2).toNat = target)
    (hper : ppi.toNat = per) :
    ∀ (l : List Nat) (w : EState) {R : List Nat}, w.validators = e.validators →
      (∀ i ∈ l, i < e.validators.val.size) →
      (l.map fun i => (absValidator e.validators.val[i]!, i)).foldlM
        (Spec.slashingLoopStep p target per) (w.balances.toList.map UInt64.toNat) = .ok R →
      R = (l.foldl (slashStepE epoch ppi) w).balances.toList.map UInt64.toNat ∧
        ∀ i ∈ l, slashCondE epoch e.validators[i]! → (UInt64.ofNat i).toNat < w.balances.val.size ∧
          ppi.toNat * (e.validators[i]!.effectiveBalance /
            EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG).toNat < 2 ^ 64 := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hpp.validatorRegistryLimit
  intro l
  induction l with
  | nil => intro w R _ _ h; simp only [List.map_nil, List.foldlM_nil, pure, Except.pure] at h; cases h
           exact ⟨rfl, by simp⟩
  | cons i l ih =>
    intro w R hv hl h
    have hi : i < e.validators.val.size := hl i (by simp)
    have hiN : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi hsize)
    simp only [List.map_cons, List.foldlM_cons, bind, Except.bind] at h
    cases hstep : Spec.slashingLoopStep p target per (w.balances.toList.map UInt64.toNat)
        (absValidator e.validators.val[i]!, i) with
    | error err => rw [hstep] at h; cases h
    | ok B =>
    rw [hstep] at h
    have hcond : (slashCondE epoch e.validators[i]!) =
        ((absValidator e.validators.val[i]!).slashed &&
          target == (absValidator e.validators.val[i]!).withdrawable_epoch) := by
      unfold slashCondE
      rw [sszList_getElem!_val]
      simp only [absValidator, ← htarget]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      exact ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp h⟩
    have hcondw : slashCondE epoch w.validators[i]! = slashCondE epoch e.validators[i]! := by rw [hv]
    -- One step.
    have key : B = (slashStepE epoch ppi w i).balances.toList.map UInt64.toNat ∧
        (slashCondE epoch e.validators[i]! → (UInt64.ofNat i).toNat < w.balances.val.size ∧
          ppi.toNat * (e.validators[i]!.effectiveBalance /
            EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG).toNat < 2 ^ 64) := by
      unfold Spec.slashingLoopStep at hstep
      unfold slashStepE
      rw [hcondw]
      split at hstep
      · rename_i hc
        rw [← hcond] at hc
        rw [if_pos hc]
        simp only [bind, Except.bind] at hstep
        cases hd : Spec.uint64Div (absValidator e.validators.val[i]!).effective_balance
            p.EFFECTIVE_BALANCE_INCREMENT with
        | error err => rw [hd] at hstep; cases hstep
        | ok incs =>
        rw [hd] at hstep
        dsimp only at hstep
        have hincs : (e.validators.val[i]!.effectiveBalance /
            EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG).toNat = incs := by
          rw [← hpp.effectiveBalanceIncrementG] at hd
          exact uint64Div_ok hd
        cases hm : Spec.uint64Mul per incs with
        | error err => rw [hm] at hstep; cases hstep
        | ok pen =>
        rw [hm] at hstep
        rw [← hper, ← hincs] at hm
        have hpen := uint64Mul_ok hm
        dsimp only at hstep
        have hstep' : Spec.decrease_balance (w.balances.toList.map UInt64.toNat) (UInt64.ofNat i).toNat
            (ppi * (e.validators.val[i]!.effectiveBalance /
              EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG)).toNat = .ok B := by
          rw [hiN, hpen]; exact hstep
        obtain ⟨-, hB⟩ := decrease_balance_etheorem w w (UInt64.ofNat i) _ hstep'
        refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
        · rw [hB, sszList_getElem!_val, hv]; rfl
        · unfold Spec.decrease_balance at hstep'
          cases hg : Spec.listGet (w.balances.toList.map UInt64.toNat) (UInt64.ofNat i).toNat with
          | error err => rw [hg] at hstep'; cases hstep'
          | ok b => exact (listGet_map_ok _ _ _ hg).1
        · rw [sszList_getElem!_val]; exact uint64Mul_lt hm
      · rename_i hc
        rw [← hcond] at hc
        rw [if_neg hc]
        simp only [pure, Except.pure] at hstep
        cases hstep
        exact ⟨rfl, fun h' => absurd h' hc⟩
    obtain ⟨hB, hidx⟩ := key
    rw [hB] at h
    have hv' : (slashStepE epoch ppi w i).validators = e.validators := by
      unfold slashStepE; split <;> exact hv
    obtain ⟨hR, hidx'⟩ := ih (slashStepE epoch ppi w i) hv' (fun j hj => hl j (by simp [hj])) h
    refine ⟨by rw [hR]; rfl, ?_⟩
    intro j hj hc
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hidx hc
    · obtain ⟨h1, h2⟩ := hidx' j hj hc
      refine ⟨?_, h2⟩
      unfold slashStepE at h1
      split at h1
      · simpa using h1
      · exact h1

omit [HasherTag] in
theorem slashings_target_lt (slot : UInt64) :
    (EthCLSpecs.Fulu.computeEpochAtSlot slot).toNat + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 <
      Spec.UINT64_SIZE := by
  have hlt := EthCLSpecs.Fulu.Const.slotsPerEpochLt
  have h2 : 2 ≤ (p.SLOTS_PER_EPOCH : Nat) := hpp.slotsPerEpochTwo
  have hv : @LT.lt Nat _ p.EPOCHS_PER_SLASHINGS_VECTOR (2 ^ 63) := hpp.epochsPerSlashingsVectorLt
  have hs := UInt64.toNat_lt slot
  unfold EthCLSpecs.Fulu.computeEpochAtSlot
  rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' hlt, hpp.slotsPerEpoch]
  have : slot.toNat / p.SLOTS_PER_EPOCH ≤ slot.toNat / 2 := Nat.div_le_div_left h2 (by omega)
  simp only [Spec.UINT64_SIZE]
  omega

omit [HasherTag] in
theorem slashings_target_toNat (epoch : UInt64)
    (h : epoch.toNat + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE) :
    (epoch + UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSlashingsVector / 2).toNat =
      epoch.toNat + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 := by
  have hv : @LT.lt Nat _ p.EPOCHS_PER_SLASHINGS_VECTOR (2 ^ 63) := hpp.epochsPerSlashingsVectorLt
  have h' : epoch.toNat + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 < 2 ^ 64 := by
    simpa [Spec.UINT64_SIZE] using h
  have hv' : EthCLSpecs.Fulu.Const.epochsPerSlashingsVector < 2 ^ 64 := by
    rw [hpp.epochsPerSlashingsVector]; omega
  have hd : (UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSlashingsVector / 2).toNat =
      p.EPOCHS_PER_SLASHINGS_VECTOR / 2 := by
    rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' hv', hpp.epochsPerSlashingsVector]; rfl
  rw [UInt64.toNat_add, hd, Nat.mod_eq_of_lt h']

theorem slashPpiE_toNat (e : EState) {adj per : Nat}
    (h : Spec.slashingsPreamble p (etheoremTotalActiveBalance e) (absEState e).slashings =
      .ok (adj, per)) :
    (slashPpiE e).toNat = per := by
  have hp := hpp.toPresetAgrees
  unfold Spec.slashingsPreamble at h
  simp only [bind, Except.bind] at h
  cases hs : Spec.uint64Sum (absEState e).slashings with
  | error err => rw [hs] at h; cases h
  | ok total =>
  rw [hs] at h
  dsimp only at h
  have hsum : total = (e.slashings.toList.map UInt64.toNat).sum ∧
      (e.slashings.toList.map UInt64.toNat).sum < 2 ^ 64 := by
    unfold Spec.uint64Sum at hs
    simp only [absEState_slashings] at hs
    split at hs
    · cases hs; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
    · cases hs
  obtain ⟨rfl, hlt⟩ := hsum
  have hm : @LT.lt Nat _ p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (2 ^ 64) :=
    hpp.proportionalSlashingMultiplierLt
  have hmul : EthCLSpecs.Fulu.Const.proportionalSlashingMultiplierBellatrix < 2 ^ 64 := by
    rw [hpp.proportionalSlashingMultiplierBellatrix]; exact hm
  have hsumE : (e.slashings.toArray.foldl (· + ·) 0).toNat =
      (e.slashings.toList.map UInt64.toNat).sum := by
    have hf : e.slashings.toArray.foldl (· + ·) (0 : UInt64) =
        e.slashings.toList.foldl (fun acc i => acc + (fun x : UInt64 => x) i) 0 := by
      rw [Vector.toList, Array.foldl_toList]
    rw [hf, foldl_add_toNat (fun x : UInt64 => x) _ 0 (by simpa using hlt)]
    simp
  cases hmu : Spec.uint64Mul (e.slashings.toList.map UInt64.toNat).sum
      p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX with
  | error err => rw [hmu] at h; cases h
  | ok m =>
  rw [hmu] at h
  rw [← hsumE, ← hpp.proportionalSlashingMultiplierBellatrix,
    ← UInt64.toNat_ofNat_of_lt' hmul] at hmu
  have hm' := uint64Mul_ok hmu
  dsimp only at h
  cases hd1 : Spec.uint64Div (etheoremTotalActiveBalance e) p.EFFECTIVE_BALANCE_INCREMENT with
  | error err => rw [hd1] at h; cases h
  | ok d =>
  rw [hd1] at h
  rw [← hp.effectiveBalanceIncrementG] at hd1
  have hd1' := uint64Div_ok hd1
  dsimp only at h
  cases hd2 : Spec.uint64Div (min m (etheoremTotalActiveBalance e)) d with
  | error err => rw [hd2] at h; cases h
  | ok q =>
  rw [hd2] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rw [← hd1', ← hm', ← umin_toNat] at hd2
  exact uint64Div_ok hd2

/-- A preamble that returns has no overflow in the slashings sum or in its product with
`PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX`. Etheorem checks the same two operations. -/
theorem slashingsPreamble_bounds (e : EState) {adj per : Nat}
    (h : Spec.slashingsPreamble p (etheoremTotalActiveBalance e) (absEState e).slashings =
      .ok (adj, per)) :
    (e.slashings.toList.map UInt64.toNat).sum < 2 ^ 64 ∧
      (e.slashings.toArray.foldl (· + ·) 0).toNat *
        (UInt64.ofNat EthCLSpecs.Fulu.Const.proportionalSlashingMultiplierBellatrix).toNat <
          2 ^ 64 := by
  unfold Spec.slashingsPreamble at h
  simp only [bind, Except.bind] at h
  cases hs : Spec.uint64Sum (absEState e).slashings with
  | error err => rw [hs] at h; cases h
  | ok total =>
  rw [hs] at h
  dsimp only at h
  have hsum : total = (e.slashings.toList.map UInt64.toNat).sum ∧
      (e.slashings.toList.map UInt64.toNat).sum < 2 ^ 64 := by
    unfold Spec.uint64Sum at hs
    simp only [absEState_slashings] at hs
    split at hs
    · cases hs; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
    · cases hs
  obtain ⟨rfl, hlt⟩ := hsum
  refine ⟨hlt, ?_⟩
  have hm : @LT.lt Nat _ p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (2 ^ 64) :=
    hpp.proportionalSlashingMultiplierLt
  have hmul : EthCLSpecs.Fulu.Const.proportionalSlashingMultiplierBellatrix < 2 ^ 64 := by
    rw [hpp.proportionalSlashingMultiplierBellatrix]; exact hm
  have hsumE : (e.slashings.toArray.foldl (· + ·) 0).toNat =
      (e.slashings.toList.map UInt64.toNat).sum := by
    have hf : e.slashings.toArray.foldl (· + ·) (0 : UInt64) =
        e.slashings.toList.foldl (fun acc i => acc + (fun x : UInt64 => x) i) 0 := by
      rw [Vector.toList, Array.foldl_toList]
    rw [hf, foldl_add_toNat (fun x : UInt64 => x) _ 0 (by simpa using hlt)]
    simp
  cases hmu : Spec.uint64Mul (e.slashings.toList.map UInt64.toNat).sum
      p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX with
  | error err => rw [hmu] at h; cases h
  | ok m =>
  rw [hsumE, UInt64.toNat_ofNat_of_lt' hmul, hpp.proportionalSlashingMultiplierBellatrix]
  exact uint64Mul_lt hmu

/-- `process_slashings` equals Etheorem's. -/
theorem slashings_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_slashings p (etheoremTotalActiveBalance e) (absEState e) = .ok s') :
    (EthCLSpecs.Fulu.processSlashings (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState (slashingsE e)) ∧
      s' = absEState (slashingsE e) := by
  have hp := hpp.toPresetAgrees
  have hepoch := get_current_epoch_eq hp e
  have htgt := slashings_target_lt hpp e.slot
  rw [Spec.process_slashings_eq p _ _ _ hepoch htgt] at h
  simp only [bind, Except.bind] at h
  cases hpre : Spec.slashingsPreamble p (etheoremTotalActiveBalance e) (absEState e).slashings with
  | error err => rw [hpre] at h; cases h
  | ok ap =>
  obtain ⟨adj, per⟩ := ap
  rw [hpre] at h
  dsimp only at h
  have hppi := slashPpiE_toNat hpp e hpre
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  cases hf : (absEState e).validators.zipIdx.foldlM
      (Spec.slashingLoopStep p ((EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat +
        p.EPOCHS_PER_SLASHINGS_VECTOR / 2) per) (absEState e).balances with
  | error err => rw [hf] at h; cases h
  | ok R =>
  rw [hf] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [absEState_validators, absEState_balances, SSZList.toList, zipIdx_map_eq,
    List.range_eq_range'] at hf
  obtain ⟨hR, hidx⟩ := slashing_fold hpp e (EthCLSpecs.Fulu.currentEpochOf (pureState e)) (slashPpiE e)
    (slashings_target_toNat hpp _ htgt) hppi (List.range' 0 e.validators.val.size) e rfl
    (fun i hi => by simpa using hi) hf
  obtain ⟨hsum, hmul⟩ := slashingsPreamble_bounds hpp e hpre
  refine ⟨processSlashings_run e hsum hmul (fun i hi hc => hidx i (by simpa using hi) hc), ?_⟩
  have hE : slashingsE e = { e with balances := (slashingsE e).balances } :=
    foldl_slashStepE_validators _ _ _ _
  rw [hE, absEState_set_balances, hR]
  rfl

end Slashings

end EpochProofs.Etheorem.Fulu
