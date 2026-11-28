import EthLib.Consensus.Transition.EpochParticipation
import EthLib.Consensus.Transition.EpochRewards
import EpochProofs.EthLib.Accessors
import EpochProofs.EthLib.Balances
import EpochProofs.EthLib.Loops

/-!
# `process_inactivity_updates`: the reference and EthLib agree

This file also compares `get_eligible_validator_indices` and `is_in_inactivity_leak`.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem is_in_inactivity_leak_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset fork) :
    SameOutcome (fun a b => b = a) (isInInactivityLeak s)
      (Spec.is_in_inactivity_leak (toSpecPreset preset config) (toSpecState s)) := by
  unfold isInInactivityLeak getFinalityDelay Spec.is_in_inactivity_leak Spec.get_finality_delay
  rw [get_previous_epoch_eq hslots]
  simp only [bind_ok]
  refine .bind (subChecked_same (getPreviousEpoch s)
    s.finalizedCheckpoint.epoch).liftArith.liftAccessor ?_
  rintro delay _ rfl -
  exact .returned (by simp [spec_preset, UInt64.lt_iff_toNat_lt])

theorem isEligibleValidator_same (previous : UInt64) (v : Validator) :
    SameOutcome (fun a b => b = a) (isEligibleValidator previous v)
      (if Spec.is_active_validator (toSpecValidator v) previous.toNat then .ok true
      else if (toSpecValidator v).slashed then do
        let next ← Spec.uint64Add previous.toNat 1
        .ok (decide (next < (toSpecValidator v).withdrawable_epoch))
      else .ok false) := by
  unfold isEligibleValidator
  rw [is_active_validator_eq]
  refine .ite Iff.rfl (fun _ => .returned rfl) (fun _ => ?_)
  refine .ite Iff.rfl (fun _ => ?_) (fun _ => .returned rfl)
  refine .bind (addChecked_same previous 1).liftArith.liftAccessor ?_
  rintro next _ rfl -
  refine .returned ?_
  simp only [UInt64.lt_iff_toNat_lt]
  rfl

theorem eligible_loop_same (previous : UInt64) :
    ∀ (l : List (Validator × Nat)) (acc : List Nat),
      (∀ p ∈ l, p.2 < 2 ^ 64) →
      SameOutcome (fun indices acc' => acc' = acc ++ indices.map UInt64.toNat ∧
          (indices.map UInt64.toNat).Sublist (l.map (·.2)))
        (l.filterMapM fun (validator, position) => do
          if ← isEligibleValidator previous validator then
            return some (← liftAccessor (liftArith (ofNatChecked position)))
          else return none)
        (forIn (l.map fun p => (toSpecValidator p.1, p.2)) acc fun x acc =>
          if Spec.is_active_validator x.1 previous.toNat then
            Pure.pure (.yield (acc ++ [x.2]))
          else if x.1.slashed then do
            let next ← Spec.uint64Add previous.toNat 1
            if next < x.1.withdrawable_epoch then Pure.pure (.yield (acc ++ [x.2]))
            else Pure.pure (.yield acc)
          else Pure.pure (.yield acc))
  | [], acc, _ => .returned ⟨by simp, by simp⟩
  | (v, position) :: l, acc, hlt => by
    have hbody :
        (if Spec.is_active_validator (toSpecValidator v) previous.toNat then
          Pure.pure (ForInStep.yield (acc ++ [position]))
        else if (toSpecValidator v).slashed then do
          let next ← Spec.uint64Add previous.toNat 1
          if next < (toSpecValidator v).withdrawable_epoch then
            Pure.pure (.yield (acc ++ [position]))
          else Pure.pure (.yield acc)
        else Pure.pure (.yield acc) : Spec.SpecM (ForInStep (List Nat))) =
        (if Spec.is_active_validator (toSpecValidator v) previous.toNat then .ok true
        else if (toSpecValidator v).slashed then do
          let next ← Spec.uint64Add previous.toNat 1
          .ok (decide (next < (toSpecValidator v).withdrawable_epoch))
        else .ok false) >>= fun eligible =>
          .ok (.yield (if eligible then acc ++ [position] else acc)) := by
      split
      · rfl
      · split
        · cases Spec.uint64Add previous.toNat 1 with
          | error e => rfl
          | ok next =>
            simp only [bind_ok]
            by_cases h : next < (toSpecValidator v).withdrawable_epoch
            · simp [h, Pure.pure, Except.pure]
            · simp [h, Pure.pure, Except.pure]
        · rfl
    simp only [List.map_cons, List.forIn_cons, List.filterMapM_cons, hbody, bind_assoc, bind_ok]
    refine .bind (isEligibleValidator_same previous v) ?_
    rintro _ eligible rfl -
    have hrest := fun acc => eligible_loop_same previous l acc fun p hp =>
      hlt p (List.mem_cons_of_mem _ hp)
    cases eligible
    · simp only [Bool.false_eq_true, ite_false, pure_eq_ok, bind_ok]
      exact (hrest acc).mono fun _ _ h => ⟨h.1, h.2.cons _⟩
    · obtain ⟨index, hindex, hnat⟩ := ofNatChecked_ok (hlt _ List.mem_cons_self)
      simp only at hnat
      subst hnat
      simp only [ite_true, hindex, _root_.EthLib.Consensus.liftArith, liftAccessor, Except.mapError,
        pure_eq_ok, bind_ok]
      refine .bind_pure (hrest (acc ++ [index.toNat])) fun indices acc' h => ?_
      exact ⟨by simp [h.1], h.2.cons_cons _⟩

theorem get_eligible_validator_indices_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome (SameIndices s) (getEligibleValidatorIndices s)
      (Spec.get_eligible_validator_indices (toSpecPreset preset config) (toSpecState s)) := by
  unfold getEligibleValidatorIndices Spec.get_eligible_validator_indices
  rw [get_previous_epoch_eq hslots]
  simp only [bind_ok]
  have hzip : (toSpecState s).validators.zipIdx =
      s.validators.data.toList.zipIdx.map fun p => (toSpecValidator p.1, p.2) := by
    simp [toSpecState, readList, List.zipIdx_map]
  rw [hzip]
  have hlt : ∀ p ∈ s.validators.data.toList.zipIdx, p.2 < s.validators.data.size := by
    rintro ⟨v, i⟩ hmem
    simpa using (List.mem_zipIdx' hmem).1
  have hloop := eligible_loop_same (getPreviousEpoch s) s.validators.data.toList.zipIdx []
    fun p hp => Nat.lt_trans (hlt p hp) (registry_lt hregistry)
  rw [bind_pure]
  refine hloop.mono fun indices acc h => ?_
  refine ⟨by simpa using h.1, ?_, ?_⟩
  · refine List.Nodup.of_map UInt64.toNat (h.2.nodup ?_)
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  · intro index hmem
    have hmem' := h.2.subset (List.mem_map_of_mem hmem)
    obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hmem'
    rw [← hpi]
    exact hlt p hp

theorem markIndices_getD {size : Nat} {indices : List UInt64} {index : UInt64}
    (hindex : index.toNat < size) :
    (markIndices size indices).getD index.toNat false =
      decide (index.toNat ∈ indices.map UInt64.toNat) := by
  rw [Array.getD_eq_getD_getElem?, getElem?_markIndices, ite_eq_left hindex, Option.getD_some]
  rw [Bool.eq_iff_iff]
  simp

/-- The second write of one inactivity score, after the first write of `score`. -/
theorem inactivity_recovery_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (s : BeaconState preset fork)
    (scores : InactivityScores preset fork) (index : Nat) (hindex : index < scores.data.size)
    (score : UInt64) :
    SameOutcome (fun (scores' : InactivityScores preset fork) r =>
        ∃ acc, r = ForInStep.yield acc ∧ acc = readList UInt64.toNat scores'.data)
      (do
        let leaking ← isInInactivityLeak s
        return ⟨scores.data.set index (if leaking then score
          else saturatingSub score config.INACTIVITY_SCORE_RECOVERY_RATE) hindex,
          fun before => by simpa using scores.bound before⟩)
      (do
        let acc ← Spec.listSet (readList UInt64.toNat scores.data) index score.toNat
        let leaking ← Spec.is_in_inactivity_leak (toSpecPreset preset config) (toSpecState s)
        if (!leaking) = true then do
          let score ← Spec.listGet acc index
          let acc ← Spec.listSet acc index
            (Spec.saturating_sub score config.INACTIVITY_SCORE_RECOVERY_RATE.toNat)
          pure (ForInStep.yield acc)
        else pure (ForInStep.yield acc)) := by
  rw [listSet_readList hindex, bind_ok]
  refine .bind (is_in_inactivity_leak_same hslots s) ?_
  rintro _ leaking rfl -
  cases leaking
  · have hindex' : index < (scores.data.set index score hindex).size := by simpa using hindex
    simp only [Bool.not_false, ite_true, listGet_readList hindex', bind_ok, Array.getElem_set_self,
      ← saturatingSub_eq, listSet_readList hindex', Bool.false_eq_true, ite_false]
    exact .returned ⟨_, rfl, by simp⟩
  · exact .returned ⟨_, rfl, rfl⟩

theorem inactivity_updates_same (hdiv : DivisorsNonzero preset config) (altair : .altair ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processInactivityUpdates config s altair)
      (Spec.process_inactivity_updates (toSpecPreset preset config) (toSpecState s)) := by
  unfold processInactivityUpdates Spec.process_inactivity_updates
  rw [get_current_epoch_eq hdiv.slots, get_previous_epoch_eq hdiv.slots]
  simp only [bind_ok, spec_preset]
  refine .ite (by
    rw [beq_iff_eq, ← UInt64.toNat_inj]
    rfl) (fun _ => .returned rfl) (fun _ => ?_)
  refine .bind (get_eligible_validator_indices_same hdiv.slots hregistry) ?_
  rintro eligible _ ⟨rfl, -, hinside⟩ -
  rw [toSpecState_inactivity_scores s altair]
  refine .bind (SameOutcome.forIn_indices (R := fun (scores : InactivityScores preset fork) acc =>
    acc = readList UInt64.toNat scores.data) eligible rfl ?_) ?_
  · rintro index scores _ hmem rfl
    unfold updateInactivityScore nextInactivityScore
    have hparticipating : SameOutcome (SameIndices s) _
        (Spec.get_unslashed_participating_indices _ _ Spec.TIMELY_TARGET_FLAG_INDEX _) :=
      get_unslashed_participating_indices_same (config := config) hdiv.slots altair hregistry
        TIMELY_TARGET_FLAG_INDEX (by decide) (getPreviousEpoch s)
    generalize Spec.get_unslashed_participating_indices (toSpecPreset preset config)
      (toSpecState s) Spec.TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch s).toNat = spec
      at hparticipating ⊢
    generalize getUnslashedParticipatingIndices s altair TIMELY_TARGET_FLAG_INDEX
      (getPreviousEpoch s) = read
      at hparticipating ⊢
    cases hparticipating with
    | failed => exact .failed
    | @returned participating _ hsame =>
    obtain ⟨rfl, -, -⟩ := hsame
    simp only [Except.map, liftAccessor, Except.mapError, bind_ok,
      markIndices_getD (hinside index hmem)]
    by_cases hlt : index.toNat < scores.data.size
    · simp only [hlt, dite_true, listGet_readList hlt, bind_ok]
      by_cases hhit : index.toNat ∈ participating.map UInt64.toNat
      · simp only [hhit, decide_true, ite_true]
        have hone : Spec.saturating_sub scores.data[index.toNat].toNat 1 =
            (saturatingSub scores.data[index.toNat] 1).toNat := (saturatingSub_eq _ 1).symm
        rw [hone]
        simp only [pure_eq_ok, bind_ok, bind_assoc]
        exact inactivity_recovery_same hdiv.slots s scores _ hlt _
      · simp only [hhit, decide_false, Bool.false_eq_true, ite_false]
        simp only [bind_assoc]
        refine .bind (addChecked_same scores.data[index.toNat]
          config.INACTIVITY_SCORE_BIAS).liftArith.liftAccessor ?_
        rintro score _ rfl -
        simp only [pure_eq_ok, bind_ok]
        exact inactivity_recovery_same hdiv.slots s scores _ hlt score
    · simp only [hlt, dite_false, listGet_readList_error hlt]
      split <;> exact .failed
  · rintro scores _ rfl -
    refine .returned ?_
    rw [SameState, toSpecState_with_inactivity_scores s altair]

end EpochProofs.EthLib
