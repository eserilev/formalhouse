import EthLib.Consensus.Transition.EpochUpdates
import EpochProofs.EthLib.Churn
import EpochProofs.EthLib.Consolidations
import EpochProofs.EthLib.Loops

/-!
# `process_registry_updates`: the reference and EthLib agree

Gloas and Fulu read different churn limits. `specRegistryUpdates` is the reference step with the
churn limit as a parameter, and the reference steps of both forks are equal to it.

The reference takes the total active balance once. EthLib reads it again for each exit. No write of
this step changes it: a validator that the step activates or exits keeps its status in the current
epoch.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- `initiate_validator_exit` of the reference, on the churn limit of the fork. -/
def specInitiateExit (p : Spec.Preset) (churnLimit : Spec.SpecM Nat) (state : Spec.BeaconState)
    (index : Nat) : Spec.SpecM Spec.BeaconState := do
  let validator ← Spec.listGet state.validators index
  if validator.exit_epoch != Spec.FAR_FUTURE_EPOCH then
    return state

  let (exit_queue_epoch, state) ←
    specExitQueue p churnLimit state validator.effective_balance

  let validator := { validator with exit_epoch := exit_queue_epoch }
  let validator := { validator with
    withdrawable_epoch :=
      ← Spec.uint64Add validator.exit_epoch p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY }
  pure { state with validators := ← Spec.listSet state.validators index validator }

/-- `process_registry_updates` of the reference, on the churn limit of the fork. -/
def specRegistryUpdates (p : Spec.Preset) (churnLimit : Spec.SpecM Nat)
    (state : Spec.BeaconState) : Spec.SpecM Spec.BeaconState := do
  let current_epoch ← Spec.get_current_epoch p state
  let activation_epoch ← Spec.compute_activation_exit_epoch p current_epoch

  let mut state := state
  for index in List.range state.validators.length do
    let validator ← Spec.listGet state.validators index
    if Spec.is_eligible_for_activation_queue p validator then
      let validator := { validator with
        activation_eligibility_epoch := ← Spec.uint64Add current_epoch 1 }
      state := { state with validators := ← Spec.listSet state.validators index validator }
    else if Spec.is_active_validator validator current_epoch
        && validator.effective_balance ≤ p.EJECTION_BALANCE then
      state ← specInitiateExit p churnLimit state index
    else if Spec.is_eligible_for_activation state validator then
      let validator := { validator with activation_epoch }
      state := { state with validators := ← Spec.listSet state.validators index validator }
  pure state

theorem specRegistryUpdates_gloas (p : Spec.Preset) (total : Nat) :
    Spec.process_registry_updates p total =
      specRegistryUpdates p (Spec.get_exit_churn_limit p total) := rfl

theorem specRegistryUpdates_fulu (p : Spec.Preset) (f : Spec.FuluConfig) (total : Nat) :
    Spec.process_registry_updates_fulu p f total =
      specRegistryUpdates p (Spec.get_activation_exit_churn_limit p f total) := rfl

/-- What each write of the registry step keeps. -/
structure RegistryKept (s st : BeaconState preset fork) : Prop where
  slot : st.slot = s.slot
  size : st.validators.data.size = s.validators.data.size
  total : getTotalActiveBalance st = getTotalActiveBalance s
  pendingDeposits : st.pendingDeposits = s.pendingDeposits
  historicalSummaries : st.historicalSummaries = s.historicalSummaries

theorem RegistryKept.epoch {s st : BeaconState preset fork} (h : RegistryKept s st) :
    getCurrentEpoch st = getCurrentEpoch s := by
  rw [getCurrentEpoch, getCurrentEpoch, h.slot]

theorem toSpecValidator_set (data : Array Validator) (i : Nat) (h : i < data.size)
    (v : Validator) :
    (readList toSpecValidator data).set i (toSpecValidator v) =
      readList toSpecValidator (data.set i v h) := by
  simp [readList, List.map_set]

/-- A write of one validator that keeps its effective balance and its status. -/
theorem write_validator {s st : BeaconState preset fork} (h : RegistryKept s st) {i : Nat}
    {v w : Validator} (hv : st.validators.data[i]? = some v)
    (hactive : isActiveValidator w (getCurrentEpoch s) = isActiveValidator v (getCurrentEpoch s))
    (hbalance : w.effectiveBalance = v.effectiveBalance) :
    ∃ (st' : BeaconState preset fork) (hi : i < st.validators.data.size),
      st' = { st with validators := st.validators.set i w hi } ∧
      st.setValidatorAt i w = .ok st' ∧ RegistryKept s st' ∧
      Spec.listSet (toSpecState st).validators i (toSpecValidator w) =
        .ok (toSpecState st').validators ∧
      { toSpecState st with validators := (toSpecState st').validators } = toSpecState st' := by
  have hi : i < st.validators.data.size := (Array.getElem?_eq_some_iff.mp hv).1
  refine ⟨_, hi, rfl, ?_, ?_, ?_, rfl⟩
  · rw [BeaconState.setValidatorAt, dite_eq_left hi]
    rfl
  · refine ⟨h.slot, ?_, ?_, h.pendingDeposits, h.historicalSummaries⟩
    · simpa [RootedForkList.set] using h.size
    · rw [← h.total]
      refine total_active_balance_congr rfl ?_
      rw [h.epoch]
      simp only [RootedForkList.set, Array.toList_set]
      exact SameActive.set (by simpa using hv) hactive hbalance
  · have hi' : i < (toSpecState st).validators.length := by simpa [toSpecState, readList] using hi
    rw [Spec.listSet, ite_eq_left hi']
    refine congrArg Except.ok ?_
    simp only [toSpecState, RootedForkList.set]
    exact toSpecValidator_set _ _ hi _

theorem initiate_exit_same (hdiv : DivisorsNonzero preset config) (electra : .pectra ≤ fork)
    {s st : BeaconState preset fork} (h : RegistryKept s st)
    {churnLimit : Spec.SpecM Nat} {churn : UInt64}
    (hchurn : ∀ st : BeaconState preset fork, getTotalActiveBalance st = getTotalActiveBalance s →
      exitChurnLimit config st = .ok churn)
    (hspec : churnLimit = .ok churn.toNat) {index : UInt64} {v : Validator}
    (hv : st.validators.data[index.toNat]? = some v)
    (hactive : isActiveValidator v (getCurrentEpoch s) = true) :
    SameOutcome (fun st' acc => acc = toSpecState st' ∧ RegistryKept s st')
      (initiateValidatorExit config st index)
      (specInitiateExit (toSpecPreset preset config) churnLimit (toSpecState st) index.toNat) := by
  unfold initiateValidatorExit specInitiateExit exitQueue
  have hget : getValidator st index = .ok v := by rw [getValidator, hv]
  have hspecGet : Spec.listGet (toSpecState st).validators index.toNat =
      .ok (toSpecValidator v) := by
    simp [Spec.listGet, toSpecState, readList, hv, pure, Except.pure]
  rw [hget, hspecGet]
  simp only [bind_ok, electra, dite_true]
  refine .ite (by
    simp only [bne_iff_ne, ne_eq, ← UInt64.toNat_inj]
    rfl) (fun _ => .returned ⟨rfl, h⟩) (fun hfar => ?_)
  refine .bind (exit_queue_same hdiv electra st (hchurn st h.total) hspec v.effectiveBalance) ?_
  rintro ⟨st₁, exitEpoch⟩ _ ⟨rfl, hepoch, left, hst₁⟩ -
  simp only at hst₁ hepoch ⊢
  refine .bind (addChecked_same exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY).liftArith ?_
  rintro withdrawable _ rfl -
  have hkept : RegistryKept s st₁ := by
    subst hst₁
    exact ⟨h.slot, h.size, (total_active_balance_congr rfl rfl).trans h.total, h.pendingDeposits,
      h.historicalSummaries⟩
  have hv₁ : st₁.validators.data[index.toNat]? = some v := by
    subst hst₁
    exact hv
  rw [h.epoch] at hepoch
  have hstill : isActiveValidator
      { v with exitEpoch := exitEpoch, withdrawableEpoch := withdrawable } (getCurrentEpoch s) =
      isActiveValidator v (getCurrentEpoch s) := by
    rw [hactive]
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at hactive ⊢
    exact ⟨hactive.1, hepoch⟩
  obtain ⟨st', hi, rfl, -, hkept', hlist, heq⟩ := write_validator hkept hv₁ hstill rfl
  have hlist' := hlist
  simp only [toSpecValidator] at hlist' ⊢
  rw [hlist']
  simp only [bind_ok]
  rw [BeaconState.setValidator, dite_eq_left hi]
  exact .returned ⟨heq, hkept'⟩

theorem registry_updates_same (hdiv : DivisorsNonzero preset config) (electra : .pectra ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit)
    {churnLimit : Spec.SpecM Nat} {churn : UInt64}
    (hchurn : ∀ st : BeaconState preset fork, getTotalActiveBalance st = getTotalActiveBalance s →
      exitChurnLimit config st = .ok churn)
    (hspec : churnLimit = .ok churn.toNat) :
    SameOutcome (fun st acc => acc = toSpecState st ∧ RegistryKept s st)
      (processRegistryUpdates config s)
      (specRegistryUpdates (toSpecPreset preset config) churnLimit (toSpecState s)) := by
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  unfold processRegistryUpdates specRegistryUpdates
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok, electra, ite_true, hlength]
  refine .bind (activation_exit_epoch_same _).liftArith.liftAccessor ?_
  rintro activation _ rfl hactivation
  have hactivation' : getCurrentEpoch s < activation := by
    apply lt_of_activationExitEpoch (preset := preset)
    cases h : computeActivationExitEpoch preset (getCurrentEpoch s) with
    | error e => rw [h] at hactivation; cases hactivation
    | ok a => rw [h] at hactivation; cases hactivation; rfl
  rw [bind_pure]
  refine SameOutcome.forIn_range (R := fun _ st acc => acc = toSpecState st ∧ RegistryKept s st) _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  rintro i st _ hi ⟨rfl, h⟩
  have hi' : i < st.validators.data.size := by rw [h.size]; exact hi
  obtain ⟨v, hv⟩ : ∃ v, st.validators.data[i]? = some v := ⟨_, Array.getElem?_eq_getElem hi'⟩
  have hget : getValidatorAt st i = .ok v := by rw [getValidatorAt, hv]
  have hspecGet : Spec.listGet (toSpecState st).validators i = .ok (toSpecValidator v) := by
    simp [Spec.listGet, toSpecState, readList, hv, pure, Except.pure]
  unfold updateRegistryEntryElectra
  rw [hget, hspecGet, h.epoch]
  simp only [bind_ok, liftAccessor, Except.mapError]
  have hqueue : (Spec.is_eligible_for_activation_queue (toSpecPreset preset config)
      (toSpecValidator v)) = isEligibleForActivationQueue preset fork v := by
    simp only [Spec.is_eligible_for_activation_queue, isEligibleForActivationQueue, electra,
      ite_true, toSpecValidator, spec_preset, UInt64.le_iff_toNat_le, ge_iff_le]
    congr 1
  have heligible : Spec.is_eligible_for_activation (toSpecState st) (toSpecValidator v) =
      isEligibleForActivation st v := by
    simp only [Spec.is_eligible_for_activation, isEligibleForActivation, toSpecValidator,
      UInt64.le_iff_toNat_le]
    congr 1
  have heject : decide ((toSpecValidator v).effective_balance ≤
      (toSpecPreset preset config).EJECTION_BALANCE) =
      decide (v.effectiveBalance ≤ config.EJECTION_BALANCE) := by
    simp only [UInt64.le_iff_toNat_le]
    rfl
  rw [hqueue, heligible, heject, is_active_validator_eq]
  by_cases h₁ : isEligibleForActivationQueue preset fork v = true
  · rw [ite_eq_left h₁, ite_eq_left h₁]
    refine .bind (addChecked_same (getCurrentEpoch s) 1).liftArith.liftAccessor ?_
    rintro next _ rfl -
    obtain ⟨st', hi₂, -, hset, hkept, hlist, heq⟩ := write_validator h hv
      (w := { v with activationEligibilityEpoch := next }) rfl rfl
    simp only [toSpecValidator] at hlist ⊢
    rw [hset, hlist]
    exact .returned ⟨_, rfl, heq, hkept⟩
  rw [ite_eq_right h₁, ite_eq_right h₁]
  by_cases h₂ : (isActiveValidator v (getCurrentEpoch s) &&
      decide (v.effectiveBalance ≤ config.EJECTION_BALANCE)) = true
  · rw [ite_eq_left h₂, ite_eq_left h₂]
    obtain ⟨index, hindex, rfl⟩ := ofNatChecked_ok (Nat.lt_trans hi (registry_lt hregistry))
    rw [hindex]
    show SameOutcome _ (liftAccessor (initiateValidatorExit config st index)) _
    rw [← bind_pure (liftAccessor (initiateValidatorExit config st index))]
    simp only [Bool.and_eq_true] at h₂
    refine .bind (initiate_exit_same hdiv electra h hchurn hspec hv h₂.1).liftAccessor ?_
    rintro st' _ h' -
    exact .returned ⟨_, rfl, h'⟩
  rw [ite_eq_right h₂, ite_eq_right h₂]
  by_cases h₃ : isEligibleForActivation st v = true
  · rw [ite_eq_left h₃, ite_eq_left h₃]
    have hfar : v.activationEpoch = FAR_FUTURE_EPOCH := by
      simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at h₃
      exact h₃.2
    have hinactive : isActiveValidator v (getCurrentEpoch s) = false := by
      rw [Bool.eq_false_iff]
      intro hactive
      simp only [isActiveValidator, hfar, Bool.and_eq_true, decide_eq_true_eq,
        UInt64.le_iff_toNat_le] at hactive
      have hle : 2 ^ 64 - 1 ≤ (getCurrentEpoch s).toNat := hactive.1
      have hlt := UInt64.lt_iff_toNat_lt.mp hactivation'
      have := activation.toNat_lt
      omega
    have hstill : isActiveValidator { v with activationEpoch := activation } (getCurrentEpoch s) =
        isActiveValidator v (getCurrentEpoch s) := by
      rw [hinactive]
      simp [isActiveValidator, UInt64.not_le.mpr hactivation']
    obtain ⟨st', hi₂, -, hset, hkept, hlist, heq⟩ := write_validator h hv hstill rfl
    simp only [toSpecValidator] at hlist ⊢
    rw [hset, hlist]
    exact .returned ⟨_, rfl, heq, hkept⟩
  · rw [ite_eq_right h₃, ite_eq_right h₃]
    exact .returned ⟨_, rfl, rfl, h⟩

end EpochProofs.EthLib
