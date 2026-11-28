import EthLib.Consensus.Churn
import EpochProofs.EthLib.Balances
import EpochProofs.EthLib.EffectiveBalances
import EpochProofs.Spec.Fulu
import EpochProofs.Spec.RegistryUpdates

/-!
# Churn limits and the exit queue: the reference and EthLib agree

The reference takes `get_total_active_balance(state)` as a parameter. EthLib reads it from the
state each time. `total_active_balance_congr` says when two states have the same value.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- The validators of two states have the same effective balances and are active in the same way
in `epoch`. -/
def SameActive (epoch : UInt64) (l l' : List Validator) : Prop :=
  l.map (fun v => (isActiveValidator v epoch, v.effectiveBalance)) =
    l'.map (fun v => (isActiveValidator v epoch, v.effectiveBalance))

theorem SameActive.set {epoch : UInt64} {l : List Validator} {i : Nat} {v w : Validator}
    (hv : l[i]? = some v) (hactive : isActiveValidator w epoch = isActiveValidator v epoch)
    (hbalance : w.effectiveBalance = v.effectiveBalance) : SameActive epoch (l.set i w) l := by
  unfold SameActive
  rw [List.map_set, hactive, hbalance]
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · rename_i h
    subst h
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    simp [hlt]
  · rfl

theorem filterMap_active_eq (epoch : UInt64) (l : List Validator) :
    (l.zipIdx.filterMap fun (v, position) =>
        if isActiveValidator v epoch then some position else none) =
      ((l.map fun v => (isActiveValidator v epoch, v.effectiveBalance)).zipIdx.filterMap
        fun x => if x.1.1 then some x.2 else none) := by
  rw [List.zipIdx_map, List.filterMap_map]
  rfl

theorem sumMarked_toList (validators : Array Validator) (marked : Array Bool) (epoch : UInt64) :
    sumMarked validators marked =
      ((validators.toList.map fun v => (isActiveValidator v epoch, v.effectiveBalance)).zip
        marked.toList).foldl
          (fun sum x => if x.2 then sum + x.1.2.toNat else sum) 0 := by
  unfold sumMarked
  rw [← Array.foldl_toList, Array.toList_zip, List.zip_map_left, List.foldl_map]
  rfl

theorem total_active_balance_congr {s s' : BeaconState preset fork} (hslot : s'.slot = s.slot)
    (hsame : SameActive (getCurrentEpoch s) s'.validators.data.toList s.validators.data.toList) :
    getTotalActiveBalance s' = getTotalActiveBalance s := by
  have hepoch : getCurrentEpoch s' = getCurrentEpoch s := by
    rw [getCurrentEpoch, getCurrentEpoch, hslot]
  have hsize : s'.validators.data.size = s.validators.data.size := by
    simpa using congrArg List.length hsame
  unfold getTotalActiveBalance getActiveValidatorIndicesChecked getTotalBalance
  simp only [filterMap_active_eq, sumMarked_toList _ _ (getCurrentEpoch s), hepoch, hsize]
  rw [show _ = _ from hsame]

theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  rw [UInt64.max_def]
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem roundToIncrement_eq (hdiv : DivisorsNonzero preset config) (amount : UInt64) :
    (do
      let remainder ← Spec.uint64Mod amount.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      Spec.uint64Sub amount.toNat remainder) = .ok (roundToIncrement preset amount).toNat :=
  round_to_increment_eq hdiv.increment amount

theorem exit_churn_limit_eq (hdiv : DivisorsNonzero preset config) {s : BeaconState preset fork}
    {total : UInt64} (htotal : getTotalActiveBalance s = .ok total) :
    ∃ churn, getExitChurnLimit config s = .ok churn ∧
      Spec.get_exit_churn_limit (toSpecPreset preset config) total.toNat = .ok churn.toNat := by
  refine ⟨_, by rw [getExitChurnLimit, htotal]; rfl, ?_⟩
  unfold Spec.get_exit_churn_limit
  simp only [spec_preset, uint64Div_eq hdiv.churnLimitQuotientGloas, bind_ok, ← toNat_max,
    roundToIncrement_eq hdiv]

theorem activation_exit_churn_limit_eq (hdiv : DivisorsNonzero preset config)
    {s : BeaconState preset fork} {total : UInt64}
    (htotal : getTotalActiveBalance s = .ok total) :
    ∃ churn, getActivationExitChurnLimit config s = .ok churn ∧
      Spec.get_activation_exit_churn_limit (toSpecPreset preset config) (toSpecFuluConfig config)
        total.toNat = .ok churn.toNat := by
  refine ⟨_, by rw [getActivationExitChurnLimit, getBalanceChurnLimit, htotal]; rfl, ?_⟩
  unfold Spec.get_activation_exit_churn_limit Spec.get_balance_churn_limit
  simp only [spec_preset, toSpecFuluConfig, uint64Div_eq hdiv.churnLimitQuotient, bind_ok,
    ← toNat_max, roundToIncrement_eq hdiv, ← toNat_min]
  rfl

theorem activation_churn_limit_eq (hdiv : DivisorsNonzero preset config)
    {s : BeaconState preset fork} {total : UInt64}
    (htotal : getTotalActiveBalance s = .ok total) :
    ∃ churn, getActivationChurnLimit config s = .ok churn ∧
      Spec.get_activation_churn_limit (toSpecPreset preset config) total.toNat =
        .ok churn.toNat := by
  refine ⟨_, by rw [getActivationChurnLimit, getExitChurnLimit, htotal]; rfl, ?_⟩
  unfold Spec.get_activation_churn_limit
  simp only [spec_preset, uint64Div_eq hdiv.churnLimitQuotientGloas, bind_ok, ← toNat_max]
  rw [← bind_assoc, roundToIncrement_eq hdiv, bind_ok, ← toNat_min]
  rfl

theorem activation_exit_epoch_same (epoch : UInt64) :
    SameOutcome SameNumber (computeActivationExitEpoch preset epoch)
      (Spec.compute_activation_exit_epoch (toSpecPreset preset config) epoch.toNat) := by
  unfold computeActivationExitEpoch Spec.compute_activation_exit_epoch
  refine .bind (addChecked_same epoch 1) ?_
  rintro next _ rfl -
  exact addChecked_same next preset.MAX_SEED_LOOKAHEAD

theorem lt_of_activationExitEpoch {epoch first : UInt64}
    (h : computeActivationExitEpoch preset epoch = .ok first) : epoch < first := by
  unfold computeActivationExitEpoch addChecked at h
  split at h
  · rename_i h₁
    rw [bind_ok] at h
    split at h
    · rename_i h₂
      cases h
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt h₂, UInt64.toNat_add,
        Nat.mod_eq_of_lt h₁, UInt64.toNat_one]
      omega
    · cases h
  · cases h

/-- The exit queue of the reference, on the churn limit of the fork. -/
def specExitQueue (p : Spec.Preset) (churnLimit : Spec.SpecM Nat) (state : Spec.BeaconState)
    (exit_balance : Nat) : Spec.SpecM (Nat × Spec.BeaconState) := do
  let mut earliest_exit_epoch := max state.earliest_exit_epoch
    (← Spec.compute_activation_exit_epoch p (← Spec.get_current_epoch p state))
  let per_epoch_churn ← churnLimit
  let mut exit_balance_to_consume :=
    if state.earliest_exit_epoch < earliest_exit_epoch then per_epoch_churn
    else state.exit_balance_to_consume

  if exit_balance > exit_balance_to_consume then
    let balance_to_process ← Spec.uint64Sub exit_balance exit_balance_to_consume
    let additional_epochs ←
      Spec.uint64Add (← Spec.uint64Div (← Spec.uint64Sub balance_to_process 1) per_epoch_churn) 1
    earliest_exit_epoch ← Spec.uint64Add earliest_exit_epoch additional_epochs
    exit_balance_to_consume ←
      Spec.uint64Add exit_balance_to_consume (← Spec.uint64Mul additional_epochs per_epoch_churn)

  let state := { state with
    exit_balance_to_consume := ← Spec.uint64Sub exit_balance_to_consume exit_balance
    earliest_exit_epoch }
  pure (state.earliest_exit_epoch, state)

theorem specExitQueue_gloas (p : Spec.Preset) (total : Nat) :
    Spec.compute_exit_epoch_and_update_churn p total =
      specExitQueue p (Spec.get_exit_churn_limit p total) := rfl

theorem specExitQueue_fulu (p : Spec.Preset) (f : Spec.FuluConfig) (total : Nat) :
    Spec.compute_exit_epoch_and_update_churn_fulu p f total =
      specExitQueue p (Spec.get_activation_exit_churn_limit p f total) := rfl

theorem exit_queue_same (hdiv : DivisorsNonzero preset config) (electra : .pectra ≤ fork)
    (s : BeaconState preset fork) {churnLimit : Spec.SpecM Nat} {churn : UInt64}
    (hchurn : exitChurnLimit config s = .ok churn) (hspec : churnLimit = .ok churn.toNat)
    (amount : UInt64) :
    SameOutcome (fun r specR => specR = (r.2.toNat, toSpecState r.1) ∧
        getCurrentEpoch s < r.2 ∧ ∃ left,
          r.1 = { s with
            exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => r.2 })
      (computeExitEpochAndUpdateChurn config s electra amount)
      (specExitQueue (toSpecPreset preset config) churnLimit (toSpecState s) amount.toNat) := by
  unfold computeExitEpochAndUpdateChurn specExitQueue
  rw [get_current_epoch_eq hdiv.slots, hchurn, hspec]
  simp only [bind_ok]
  refine .bind (activation_exit_epoch_same _).liftArith ?_
  rintro first _ rfl hfirst
  have hfirst' : getCurrentEpoch s < first := by
    apply lt_of_activationExitEpoch (preset := preset)
    cases h : computeActivationExitEpoch preset (getCurrentEpoch s) with
    | error e => rw [h] at hfirst; cases hfirst
    | ok a => rw [h] at hfirst; cases hfirst; rfl
  rw [toSpecState_earliest_exit_epoch s electra, toSpecState_exit_balance_to_consume s electra]
  unfold churnQueue
  have hepoch : max (s.earliestExitEpoch electra).toNat first.toNat =
      (max (s.earliestExitEpoch electra) first).toNat := (toNat_max _ _).symm
  simp only [hepoch]
  have hfirstEpoch : getCurrentEpoch s < max (s.earliestExitEpoch electra) first := by
    rw [UInt64.lt_iff_toNat_lt, toNat_max]
    rw [UInt64.lt_iff_toNat_lt] at hfirst'
    omega
  generalize max (s.earliestExitEpoch electra) first = epoch at hfirstEpoch ⊢
  have havailable : (if (s.earliestExitEpoch electra).toNat < epoch.toNat then churn.toNat
      else (s.exitBalanceToConsume electra).toNat) =
      (if s.earliestExitEpoch electra < epoch then churn
        else s.exitBalanceToConsume electra).toNat := by
    by_cases h : s.earliestExitEpoch electra < epoch
    · rw [ite_eq_left h, ite_eq_left (UInt64.lt_iff_toNat_lt.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (UInt64.lt_iff_toNat_lt.mpr h'))]
  simp only [havailable]
  generalize (if s.earliestExitEpoch electra < epoch then churn
    else s.exitBalanceToConsume electra) = available
  have hwrite (epoch left : UInt64) :
      { toSpecState s with
        exit_balance_to_consume := left.toNat, earliest_exit_epoch := epoch.toNat } =
      toSpecState { s with
        exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch } := by
    simp [toSpecState, fieldOr, electra]
  by_cases hle : amount ≤ available
  · have hle' := UInt64.le_iff_toNat_le.mp hle
    rw [ite_eq_left hle, ite_eq_right (Nat.not_lt.mpr hle'), Spec.uint64Sub, ite_eq_left hle']
    refine .returned ⟨?_, hfirstEpoch, _, rfl⟩
    rw [← UInt64.toNat_sub_of_le _ _ hle, hwrite]
  · have hlt : available < amount := UInt64.not_le.mp hle
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    rw [ite_eq_right hle, ite_eq_left hlt']
    have hrest : (amount - available).toNat = amount.toNat - available.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
    have hone : (1 : UInt64) ≤ amount - available := by
      rw [UInt64.le_iff_toNat_le, hrest, UInt64.toNat_one]
      omega
    have hrestOne : (amount - available - 1).toNat = amount.toNat - available.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ hone, hrest, UInt64.toNat_one]
    have hsub : Spec.uint64Sub amount.toNat available.toNat =
        .ok (amount.toNat - available.toNat) := by
      rw [Spec.uint64Sub, ite_eq_left (Nat.le_of_lt hlt')]
      rfl
    have hsubOne : Spec.uint64Sub (amount.toNat - available.toNat) 1 =
        .ok (amount - available - 1).toNat := by
      rw [Spec.uint64Sub, hrestOne]
      exact ite_eq_left (Nat.sub_pos_of_lt hlt')
    simp only [hsub, hsubOne, bind_ok]
    by_cases hzero : churn = 0
    · subst hzero
      exact .failed
    rw [divChecked, ite_eq_right hzero, uint64Div_eq hzero]
    simp only [bind_ok]
    have hchurnPos : 0 < churn.toNat := by
      refine Nat.pos_of_ne_zero fun h => hzero (UInt64.toNat_inj.mp h)
    have hquotient : ((amount - available - 1) / churn).toNat + 1 < 2 ^ 64 := by
      rw [UInt64.toNat_div, hrestOne]
      have := Nat.div_le_self (amount.toNat - available.toNat - 1) churn.toNat
      have := amount.toNat_lt
      omega
    have hadditional : ((amount - available - 1) / churn + 1).toNat =
        ((amount - available - 1) / churn).toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hquotient]
    have hadd : Spec.uint64Add ((amount - available - 1) / churn).toNat 1 =
        .ok ((amount - available - 1) / churn + 1).toNat := by
      rw [Spec.uint64Add, Spec.UINT64_SIZE, ite_eq_left hquotient, hadditional]
      rfl
    have hcover : amount.toNat - available.toNat ≤
        ((amount - available - 1) / churn + 1).toNat * churn.toNat := by
      rw [hadditional, UInt64.toNat_div, hrestOne]
      have := Nat.lt_div_mul_add hchurnPos (a := amount.toNat - available.toNat - 1)
      rw [Nat.add_mul]
      omega
    rw [hadd]
    simp only [bind_ok]
    generalize (amount - available - 1) / churn + 1 = additional at hcover ⊢
    simp only [liftArith_bind, bind_assoc]
    refine .bind (addChecked_same epoch additional).liftArith ?_
    rintro newEpoch _ rfl hnewEpoch
    have hnew : epoch ≤ newEpoch := by
      unfold addChecked at hnewEpoch
      split at hnewEpoch
      · rename_i h
        cases hnewEpoch
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h]
        omega
      · cases hnewEpoch
    refine .bind (mulChecked_same additional churn).liftArith ?_
    rintro product _ rfl hproduct
    have hproductNat : product.toNat = additional.toNat * churn.toNat := by
      unfold mulChecked at hproduct
      split at hproduct
      · rename_i h
        cases hproduct
        rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]
      · cases hproduct
    refine .bind (addChecked_same available product).liftArith ?_
    rintro newAvailable _ rfl hnewAvailable
    have hcovers : amount ≤ newAvailable := by
      unfold addChecked at hnewAvailable
      split at hnewAvailable
      · rename_i h
        cases hnewAvailable
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h, hproductNat]
        omega
      · cases hnewAvailable
    rw [Spec.uint64Sub, ite_eq_left (UInt64.le_iff_toNat_le.mp hcovers)]
    refine .returned ⟨?_, UInt64.lt_of_lt_of_le hfirstEpoch hnew, _, rfl⟩
    rw [← UInt64.toNat_sub_of_le _ _ hcovers, hwrite]

end EpochProofs.EthLib
