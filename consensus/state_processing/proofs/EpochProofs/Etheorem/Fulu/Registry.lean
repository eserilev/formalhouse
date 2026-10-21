import EpochProofs.Etheorem.Fulu.Helpers
import EpochProofs.Sanity.Invariants.LighthouseEpoch
import EpochProofs.Sanity.Block.ExecutionRequests

/-!
# The reference `process_registry_updates` equals Etheorem's

The main theorem is `process_registry_updates_etheorem`.

pyspec runs the three registry checks as `if`/`elif`/`elif`. Etheorem runs them as three
separate `if`s on the validator at the start of the step. The checks exclude each other when
`EJECTION_BALANCE < MIN_ACTIVATION_BALANCE` and the finalized epoch is below
`FAR_FUTURE_EPOCH`. If the finalized epoch is `FAR_FUTURE_EPOCH`, a validator with
`activation_eligibility_epoch = FAR_FUTURE_EPOCH` passes the first and the third check, and
the two specs differ. No reachable state has this finalized epoch.

The reference reads `get_total_active_balance` once, before the loop. Etheorem reads it again
at each exit. The loop keeps the effective balance and the activity at the current epoch of
each validator (`Spec.activeKey`), so the two values agree.
-/

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Fulu (FuluRun)

section Body

variable [EthCLSpecs.Fulu.Preset] [HasherTag]

/-- A `for` loop over indices that runs on the reference and on Etheorem. If each step agrees,
the loops agree. -/
theorem forIn_list_etheorem (Inv : EState → Prop)
    (specBody : Nat → Spec.BeaconState → Spec.SpecM (ForInStep Spec.BeaconState))
    (body : Nat → PUnit → FuluRun (ForInStep PUnit))
    (hstep : ∀ i e r, Inv e → specBody i (absEState e) = .ok r →
      ∃ e', (body i PUnit.unit).run (pureState e) = .ok (.yield PUnit.unit, pureState e') ∧
        r = .yield (absEState e') ∧ Inv e') :
    ∀ (l : List Nat) (e : EState) {s' : Spec.BeaconState}, Inv e →
      forIn l (absEState e) specBody = .ok s' →
      ∃ e', (forIn l PUnit.unit body).run (pureState e) = .ok (PUnit.unit, pureState e') ∧
        s' = absEState e' ∧ Inv e' := by
  intro l
  induction l with
  | nil =>
    intro e s' hinv h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨e, rfl, h.symm, hinv⟩
  | cons i rest ih =>
    intro e s' hinv h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := Spec.specM_bind_ok h
    obtain ⟨e1, hrun1, rfl, hinv1⟩ := hstep i e r hinv hr
    obtain ⟨e', hrun, hs', hinv'⟩ := ih e1 hinv1 h
    refine ⟨e', ?_, hs', hinv'⟩
    rw [List.forIn_cons, run_bind, hrun1, except_bind_ok]
    exact hrun

omit [EthCLSpecs.Fulu.Preset] [HasherTag] in
theorem run_get_gloas [EthCLSpecs.Fulu.Preset] [HasherTag] (s : EthCLSpecs.Fulu.State) :
    (get : FuluRun EthCLSpecs.Fulu.State).run s = .ok (s, s) := rfl

theorem modValidator_run (e : EState) (i : UInt64)
    (f : EthCLSpecs.Fulu.Validator → EthCLSpecs.Fulu.Validator) :
    (EthCLSpecs.Fulu.modifyState (fun st => EthCLSpecs.Fulu.modValidator st i f) :
        FuluRun Unit).run (pureState e) =
      .ok ((), pureState { e with validators := e.validators.set! i.toNat (f e.validators[i.toNat]!) }) :=
  rfl

section WithConfig

variable [EthCLSpecs.Fulu.Config]

open EthCLSpecs.Fulu in
/-- The Etheorem preset holds the registry and deposit values of `p`. They are not in
`PresetAgrees`. -/
structure QueuesPresetAgrees (p : Spec.Preset) : Prop where
  minActivationBalance : Const.minActivationBalance.toNat = p.MIN_ACTIVATION_BALANCE
  ejectionBalance : Const.ejectionBalanceG.toNat = p.EJECTION_BALANCE
  ejection_lt : p.EJECTION_BALANCE < p.MIN_ACTIVATION_BALANCE
  maxEffectiveBalanceElectra :
    Const.maxEffectiveBalanceElectraG.toNat = p.MAX_EFFECTIVE_BALANCE_ELECTRA
  maxPendingDepositsPerEpoch : Const.maxPendingDepositsPerEpoch = p.MAX_PENDING_DEPOSITS_PER_EPOCH

omit [EthCLSpecs.Fulu.Preset] [HasherTag] [EthCLSpecs.Fulu.Config] in
theorem far_toNat : (EthCLSpecs.Fulu.Const.farFutureEpoch).toNat = Spec.FAR_FUTURE_EPOCH := rfl

omit [HasherTag] in
theorem is_eligible_for_activation_queue_eq {p : Spec.Preset} (hq : QueuesPresetAgrees p)
    (v : EthCLSpecs.Fulu.Validator) :
    Spec.is_eligible_for_activation_queue p (absValidator v) =
      EthCLSpecs.Fulu.isEligibleForActivationQueue v := by
  simp only [Spec.is_eligible_for_activation_queue, EthCLSpecs.Fulu.isEligibleForActivationQueue,
    absValidator, ← hq.minActivationBalance, ← far_toNat]
  apply Bool.eq_iff_iff.mpr
  simp [UInt64.le_iff_toNat_le, UInt64.toNat_inj]

omit [EthCLSpecs.Fulu.Config] in
theorem is_eligible_for_activation_eq (e : EState) (v : EthCLSpecs.Fulu.Validator) :
    Spec.is_eligible_for_activation (absEState e) (absValidator v) =
      EthCLSpecs.Fulu.isEligibleForActivation (pureState e) v := by
  simp only [Spec.is_eligible_for_activation, EthCLSpecs.Fulu.isEligibleForActivation,
    absValidator, absEState_finalized_checkpoint, absCheckpoint, view_uncachedBox, ← far_toNat]
  apply Bool.eq_iff_iff.mpr
  simp [UInt64.le_iff_toNat_le, UInt64.toNat_inj]

omit [EthCLSpecs.Fulu.Config] in
theorem range_forIn_eq {β : Type} (n : Nat) (b : β) (f : Nat → β → FuluRun (ForInStep β)) :
    forIn [0:n] b f = forIn (List.range n) b f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']

/-- The loop body of Etheorem's `processRegistryUpdates`. -/
def regBody (cur act : UInt64) (idx : Nat) (_ : PUnit) : FuluRun (ForInStep PUnit) := do
  let state ← get
  let validator := state.view.validators[idx]!
  if EthCLSpecs.Fulu.isEligibleForActivationQueue validator then
    EthCLSpecs.Fulu.modifyState fun state => EthCLSpecs.Fulu.modValidator state (UInt64.ofNat idx)
      fun validator => { validator with activationEligibilityEpoch := cur + 1 }
  if EthCLSpecs.Fulu.isActiveValidator validator cur &&
      validator.effectiveBalance ≤ EthCLSpecs.Fulu.Const.ejectionBalanceG then
    EthCLSpecs.Fulu.initiateValidatorExit (UInt64.ofNat idx)
  if EthCLSpecs.Fulu.isEligibleForActivation state validator then
    EthCLSpecs.Fulu.modifyState fun state => EthCLSpecs.Fulu.modValidator state (UInt64.ofNat idx)
      fun validator => { validator with activationEpoch := act }
  pure (.yield PUnit.unit)

theorem processRegistryUpdates_run (e : EState) :
    (EthCLSpecs.Fulu.processRegistryUpdates (StateTransition := FuluRun)).run (pureState e) =
      ((forIn (List.range e.validators.val.size) PUnit.unit
        (regBody (EthCLSpecs.Fulu.currentEpochOf (pureState e))
          (EthCLSpecs.Fulu.computeActivationExitEpoch
            (EthCLSpecs.Fulu.currentEpochOf (pureState e))))).run (pureState e) >>=
        fun p => .ok ((), p.2)) := by
  unfold EthCLSpecs.Fulu.processRegistryUpdates
  simp only [run_bind, run_get_gloas, except_bind_ok]
  rw [range_forIn_eq]
  rfl


omit [EthCLSpecs.Fulu.Preset] [HasherTag] [EthCLSpecs.Fulu.Config] in
/-- A write that keeps the key of the item keeps the list of keys. -/
theorem map_set_of_key {α κ : Type} (f : α → κ) (l : List α) (i : Nat) (a : α)
    (hi : i < l.length) (ha : f a = f l[i]) : (l.set i a).map f = l.map f := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_set]
  split
  · subst_vars; exact ha
  · rfl

section RegistryStep

variable {p : Spec.Preset} (hp : PresetAgrees p) (hq : QueuesPresetAgrees p)
  {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f)
include hp hq hf

theorem regBody_step (e : EState) (C : UInt64) (act tab idx : Nat)
    (hcur : Spec.get_current_epoch p (absEState e) = .ok C.toNat)
    (hact : Spec.compute_activation_exit_epoch p C.toNat = .ok act)
    (hCfar : C.toNat < Spec.FAR_FUTURE_EPOCH)
    (htab : Spec.fuluTab p f (etheoremTotalActiveBalance e) = tab)
    (hfin : (absEState e).finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH)
    {r : ForInStep Spec.BeaconState}
    (h : Spec.registrySpecBody p tab C.toNat act idx (absEState e) = .ok r) :
    ∃ e', (regBody C (EthCLSpecs.Fulu.computeActivationExitEpoch C) idx PUnit.unit).run
        (pureState e) = .ok (.yield PUnit.unit, pureState e') ∧ r = .yield (absEState e') ∧
      (absEState e').slot = (absEState e).slot ∧
      (absEState e').finalized_checkpoint = (absEState e).finalized_checkpoint ∧
      (absEState e').validators.map (Spec.activeKey C.toNat) =
        (absEState e).validators.map (Spec.activeKey C.toNat) := by
  unfold Spec.registrySpecBody at h
  obtain ⟨v', hv', h⟩ := Spec.specM_bind_ok h
  rw [absEState_validators] at hv'
  obtain ⟨hi, rfl⟩ := listGet_map_ok e.validators.val absValidator idx hv'
  have hidx64 : idx < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hi (Nat.le_trans e.validators.property (Nat.le_of_lt hp.validatorRegistryLimit))
  have hofNat : (UInt64.ofNat idx).toNat = idx := UInt64.toNat_ofNat_of_lt' hidx64
  have hactC := compute_activation_exit_epoch_ok hp C hact
  have hact' := Spec.compute_activation_exit_epoch_ok p _ _ hact
  generalize hv : e.validators.val[idx]! = v at h
  have hv2 : e.validators.val[idx] = v := by rw [← hv, getElem!_pos e.validators.val idx hi]
  have hvget : e.validators[idx]! = v := by rw [sszList_getElem!_val, hv]
  unfold regBody
  simp only [run_bind, run_get_gloas, except_bind_ok, view_uncachedBox, hvget]
  rw [is_eligible_for_activation_queue_eq hq, is_active_validator_eq,
    is_eligible_for_activation_eq] at h
  have hej : decide ((absValidator v).effective_balance ≤ p.EJECTION_BALANCE) =
      decide (v.effectiveBalance ≤ EthCLSpecs.Fulu.Const.ejectionBalanceG) := by
    simp [absValidator, ← hq.ejectionBalance, UInt64.le_iff_toNat_le]
  rw [hej] at h
  have hfin' : (pureState e).view.finalizedCheckpoint.epoch.toNat < Spec.FAR_FUTURE_EPOCH := hfin
  -- The three Etheorem conditions are exclusive.
  have hAB : EthCLSpecs.Fulu.isEligibleForActivationQueue v = true →
      (EthCLSpecs.Fulu.isActiveValidator v C &&
        decide (v.effectiveBalance ≤ EthCLSpecs.Fulu.Const.ejectionBalanceG)) = false := by
    intro hA
    have hlt : (p.EJECTION_BALANCE : Nat) < p.MIN_ACTIVATION_BALANCE := hq.ejection_lt
    simp only [EthCLSpecs.Fulu.isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hA
    have h1 : (p.MIN_ACTIVATION_BALANCE : Nat) ≤ v.effectiveBalance.toNat := by
      rw [← hq.minActivationBalance]; exact UInt64.le_iff_toNat_le.mp hA.2
    rw [Bool.eq_false_iff]
    intro hB
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    have h3 : v.effectiveBalance.toNat ≤ (p.EJECTION_BALANCE : Nat) := by
      rw [← hq.ejectionBalance]; exact UInt64.le_iff_toNat_le.mp hB.2
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.le_trans h1 h3))
  have hAC : EthCLSpecs.Fulu.isEligibleForActivationQueue v = true →
      EthCLSpecs.Fulu.isEligibleForActivation (pureState e) v = false := by
    intro hA
    simp only [EthCLSpecs.Fulu.isEligibleForActivationQueue, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hA
    rw [Bool.eq_false_iff]
    intro hC
    simp only [EthCLSpecs.Fulu.isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hC
    have h3 := UInt64.le_iff_toNat_le.mp hC.1
    rw [hA.1, far_toNat] at h3
    have : (Spec.FAR_FUTURE_EPOCH : Nat) ≤ (pureState e).view.finalizedCheckpoint.epoch.toNat := h3
    omega
  have hBC : EthCLSpecs.Fulu.isActiveValidator v C = true →
      EthCLSpecs.Fulu.isEligibleForActivation (pureState e) v = false := by
    intro hB
    simp only [EthCLSpecs.Fulu.isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at hB
    rw [Bool.eq_false_iff]
    intro hC
    simp only [EthCLSpecs.Fulu.isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hC
    have h3 := UInt64.le_iff_toNat_le.mp hB.1
    rw [hC.2, far_toNat] at h3
    have : (Spec.FAR_FUTURE_EPOCH : Nat) ≤ C.toNat := h3
    omega
  by_cases hA : EthCLSpecs.Fulu.isEligibleForActivationQueue v = true
  · simp only [hA, if_true, hAB hA, hAC hA, Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨n, hn, h⟩ := Spec.specM_bind_ok h
    obtain ⟨l, hl, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    subst h
    have hn' := uint64Add_ok (a := C) (b := 1) (by simpa using hn)
    unfold Spec.listSet at hl
    rw [if_pos (by simpa using hi)] at hl
    simp only [pure, Except.pure, Except.ok.injEq] at hl
    subst hl
    let v1 : EthCLSpecs.Fulu.Validator := { v with activationEligibilityEpoch := C + 1 }
    refine ⟨{ e with validators := e.validators.set! idx v1 }, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [run_bind, modValidator_run, except_bind_ok, hofNat, hvget]
      rfl
    · rw [← hn']
      simp only [absEState, map_toList_set!]
      rfl
    · rw [absEState_set_validators, map_toList_set!, absEState_validators]
      apply map_set_of_key _ _ _ _ (by simpa using hi)
      simp [Spec.activeKey, absValidator, hv2, Spec.is_active_validator, v1]
  have hA' : EthCLSpecs.Fulu.isEligibleForActivationQueue v = false := by simpa using hA
  simp only [hA', Bool.false_eq_true, if_false] at h ⊢
  by_cases hB : (EthCLSpecs.Fulu.isActiveValidator v C &&
      decide (v.effectiveBalance ≤ EthCLSpecs.Fulu.Const.ejectionBalanceG)) = true
  · have hBa : EthCLSpecs.Fulu.isActiveValidator v C = true := by
      simp only [Bool.and_eq_true] at hB; exact hB.1
    simp only [hB, if_true, hBC hBa, Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨s1, hs1, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    subst h
    have hs1' : Spec.initiate_validator_exit p (Spec.fuluTab p f (etheoremTotalActiveBalance e))
        (absEState e)
        (UInt64.ofNat idx).toNat = .ok s1 := by rw [htab, hofNat]; exact hs1
    obtain ⟨e1, hrun1, rfl⟩ := initiate_validator_exit_etheorem hp hf e _ hs1'
    obtain ⟨-, hcs, hcases⟩ := Spec.initiate_validator_exit_cases p tab _ _ idx hs1
    refine ⟨e1, ?_, rfl, hcs.1, hcs.2.1, ?_⟩
    · simp only [run_bind, run_pure, except_bind_ok, hrun1]
    · rcases hcases with hval | ⟨w, c, ee, hw, hwfar, hc, hle, hset⟩
      · exact congrArg _ hval
      · rw [hset]
        rw [hcur] at hc
        cases hc
        have hwv : w = absValidator v := by
          rw [absEState_validators] at hw
          simp [hi, hv2] at hw
          exact hw.symm
        subst hwv
        apply map_set_of_key _ _ _ _ (by simpa using hi)
        simp only [Spec.activeKey, absEState_validators, List.getElem_map, Prod.mk.injEq]
        have hv3 : (e.validators.toList)[idx]'(by simpa using hi) = v := by
          simp [SSZList.toList, hv2]
        rw [hv3]
        simp only [Spec.is_active_validator, hwfar]
        have h1 : C.toNat < ee := by omega
        simp only [h1, decide_true, Bool.and_true]
        have h2 : decide (C.toNat < Spec.FAR_FUTURE_EPOCH) = true := decide_eq_true hCfar
        rw [h2, Bool.and_true]
        exact ⟨trivial, rfl⟩
  · have hB' : (EthCLSpecs.Fulu.isActiveValidator v C &&
        decide (v.effectiveBalance ≤ EthCLSpecs.Fulu.Const.ejectionBalanceG)) = false := by
      simpa using hB
    simp only [hB', Bool.false_eq_true, if_false] at h ⊢
    by_cases hC : EthCLSpecs.Fulu.isEligibleForActivation (pureState e) v = true
    · simp only [hC, if_true] at h ⊢
      obtain ⟨l, hl, h⟩ := Spec.specM_bind_ok h
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      subst h
      unfold Spec.listSet at hl
      rw [if_pos (by simpa using hi)] at hl
      simp only [pure, Except.pure, Except.ok.injEq] at hl
      subst hl
      let v1 : EthCLSpecs.Fulu.Validator :=
        { v with activationEpoch := EthCLSpecs.Fulu.computeActivationExitEpoch C }
      refine ⟨{ e with validators := e.validators.set! idx v1 }, ?_, ?_, rfl, rfl, ?_⟩
      · simp only [run_bind, run_pure, modValidator_run, except_bind_ok, hofNat, hvget]
        rfl
      · simp only [absEState, map_toList_set!]
        rw [← hactC]
        rfl
      · rw [absEState_set_validators, map_toList_set!, absEState_validators]
        apply map_set_of_key _ _ _ _ (by simpa using hi)
        simp only [EthCLSpecs.Fulu.isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq, view_uncachedBox] at hC
        have hfar : v.activationEpoch.toNat = Spec.FAR_FUTURE_EPOCH := by rw [hC.2]; rfl
        have h1 : ¬ act ≤ C.toNat := by omega
        have h2 : ¬ Spec.FAR_FUTURE_EPOCH ≤ C.toNat := Nat.not_le.mpr hCfar
        simp [Spec.activeKey, absValidator, hv2, Spec.is_active_validator, v1, hactC, hfar, h1, h2]
    · have hC' : EthCLSpecs.Fulu.isEligibleForActivation (pureState e) v = false := by
        simpa using hC
      simp only [hC', Bool.false_eq_true, if_false, pure, Except.pure, bind, Except.bind,
        Except.ok.injEq] at h
      subst h
      refine ⟨e, ?_, rfl, rfl, rfl, rfl⟩
      simp only [hC', Bool.false_eq_true, if_false, run_bind, run_pure, except_bind_ok]

/-- The reference `process_registry_updates` equals Etheorem's. -/
theorem process_registry_updates_etheorem (e : EState) {tab : Nat} {s' : Spec.BeaconState}
    (htab : Spec.get_total_active_balance p (absEState e) = .ok tab)
    (hfin : (absEState e).finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH)
    (h : Spec.process_registry_updates p (Spec.fuluTab p f tab) (absEState e) = .ok s') :
    ∃ e' : EState,
      (EthCLSpecs.Fulu.processRegistryUpdates (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ s' = absEState e' := by
  have hcur := get_current_epoch_eq hp e
  generalize hC : EthCLSpecs.Fulu.currentEpochOf (pureState e) = C at hcur
  have hact0 := h
  unfold Spec.process_registry_updates at hact0
  rw [hcur] at hact0
  simp only [bind, Except.bind] at hact0
  split at hact0
  · cases hact0
  next act hact =>
  rw [Spec.process_registry_updates_forIn p (Spec.fuluTab p f tab) _ C.toNat act hcur hact] at h
  have hactC := compute_activation_exit_epoch_ok hp C hact
  have hact' := Spec.compute_activation_exit_epoch_ok p _ _ hact
  have hCfar : C.toNat < Spec.FAR_FUTURE_EPOCH := by
    have := UInt64.toNat_lt (EthCLSpecs.Fulu.computeActivationExitEpoch C)
    rw [hactC] at this
    simp only [Spec.FAR_FUTURE_EPOCH]
    omega
  have hlen : (absEState e).validators.length = e.validators.val.size := by simp
  rw [hlen] at h
  let Inv : EState → Prop := fun e1 =>
    (absEState e1).slot = (absEState e).slot ∧
      (absEState e1).finalized_checkpoint = (absEState e).finalized_checkpoint ∧
      (absEState e1).validators.map (Spec.activeKey C.toNat) =
        (absEState e).validators.map (Spec.activeKey C.toNat)
  have hstep : ∀ i e1 r, Inv e1 →
      Spec.registrySpecBody p (Spec.fuluTab p f tab) C.toNat act i (absEState e1) = .ok r →
      ∃ e', (regBody C (EthCLSpecs.Fulu.computeActivationExitEpoch C) i PUnit.unit).run
          (pureState e1) = .ok (.yield PUnit.unit, pureState e') ∧
        r = .yield (absEState e') ∧ Inv e' := by
    intro i e1 r ⟨hs, hf', hk⟩ hr
    have hcur1 : Spec.get_current_epoch p (absEState e1) = .ok C.toNat := by
      rw [← hcur]; simp only [Spec.get_current_epoch, hs]
    have htab1 : Spec.fuluTab p f (etheoremTotalActiveBalance e1) = Spec.fuluTab p f tab := by
      congr 1
      apply get_total_active_balance_ok hp e1
      rw [Spec.get_total_active_balance_congr_key p (absEState e) (absEState e1) C.toNat hcur hs hk]
      exact htab
    obtain ⟨e', hrun, hr', hs', hf'', hk'⟩ :=
      regBody_step hp hq hf e1 C act (Spec.fuluTab p f tab) i hcur1 hact hCfar htab1 (hf' ▸ hfin) hr
    exact ⟨e', hrun, hr', hs'.trans hs, hf''.trans hf', hk'.trans hk⟩
  obtain ⟨e', hrun, hs', -⟩ :=
    forIn_list_etheorem Inv _ _ hstep (List.range e.validators.val.size) e ⟨rfl, rfl, rfl⟩ h
  refine ⟨e', ?_, hs'⟩
  rw [processRegistryUpdates_run, hC, hrun]
  rfl

end RegistryStep

end WithConfig

end Body

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
theorem queuesPresetAgrees_mainnet : QueuesPresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
theorem queuesPresetAgrees_minimal : QueuesPresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
end

end EpochProofs.Etheorem.Fulu
