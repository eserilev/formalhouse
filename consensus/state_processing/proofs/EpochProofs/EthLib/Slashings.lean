import EthLib.Consensus.Transition.EpochUpdates
import EpochProofs.EthLib.Balances
import EpochProofs.EthLib.Loops

/-!
# `process_slashings`: the reference and EthLib agree

The reference takes `get_total_active_balance(state)` as a parameter. The theorem reads it first,
as `process_epoch` does.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- A sum with a check at each addition, and a sum with one check at the end. -/
theorem checkedSum_same (values : List UInt64) (start : UInt64) :
    SameOutcome SameNumber (values.foldlM addChecked start)
      (if start.toNat + (values.map UInt64.toNat).sum < 2 ^ 64 then
        .ok (start.toNat + (values.map UInt64.toNat).sum)
      else .error .overflow) := by
  induction values generalizing start with
  | nil =>
    have h := start.toNat_lt
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, h, ite_true]
    exact .returned rfl
  | cons value values ih =>
    rw [List.foldlM_cons, List.map_cons, List.sum_cons]
    by_cases h : start.toNat + value.toNat < 2 ^ 64
    · have hadd : (start + value).toNat = start.toNat + value.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
      rw [addChecked, ite_eq_left h, bind_ok, ← Nat.add_assoc, ← hadd]
      exact ih _
    · rw [addChecked, ite_eq_right h, ite_eq_right (by omega)]
      exact .failed

theorem slashings_sum_same (s : BeaconState preset fork) :
    SameOutcome SameNumber (slashingsSum s) (Spec.uint64Sum (toSpecState s).slashings) := by
  have h := checkedSum_same s.slashings.elements.toList 0
  rw [UInt64.toNat_zero, Nat.zero_add] at h
  exact h.liftArith.liftAccessor

theorem slashings_same (hdiv : DivisorsNonzero preset config) (electra : .pectra ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processSlashings s)
      (do
        let total ← Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s)
        Spec.process_slashings (toSpecPreset preset config) total (toSpecState s)) := by
  have bellatrix : fork ≥ .bellatrix := Nat.le_trans (by decide) electra
  unfold processSlashings Spec.process_slashings
  refine .bind (get_total_active_balance_same hdiv.slots hregistry).liftAccessor ?_
  rintro total _ rfl -
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok, electra, ite_true, parameters, bellatrix, spec_preset]
  refine .bind (slashings_sum_same s) ?_
  rintro sum _ rfl -
  refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
  rintro slashed _ rfl -
  have hincrement : divChecked total preset.EFFECTIVE_BALANCE_INCREMENT =
      .ok (total / preset.EFFECTIVE_BALANCE_INCREMENT) := by
    rw [divChecked, ite_eq_right hdiv.increment]
  rw [hincrement]
  simp only [uint64Div_eq hdiv.increment, bind_ok, ← toNat_min]
  refine .bind (divChecked_same _ _).liftArith.liftAccessor ?_
  rintro perIncrement _ rfl -
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  have htwo : Spec.uint64Div preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat 2 =
      .ok (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat :=
    uint64Div_eq (b := 2) (by decide)
  rw [← hlength, ← bind_pure ((List.range _).foldlM _ _)]
  refine .bind (SameOutcome.forIn_zipIdx (R := fun _ => OnlyBalancesChanged s) _
    (OnlyBalancesChanged.refl s) ?_) fun st balances h _ => .pure h.toSpecState_eq
  intro i st balances v hv h
  obtain ⟨w, hw, rfl⟩ : ∃ w, s.validators.data[i]? = some w ∧ toSpecValidator w = v := by
    simpa [toSpecState, readList] using hv
  have hget : getValidatorAt st i = .ok w := by
    obtain ⟨l, rfl, -, -⟩ := h
    rw [getValidatorAt]
    simp only [hw]
  have hepoch : getCurrentEpoch st = getCurrentEpoch s := by
    obtain ⟨l, rfl, -, -⟩ := h
    rfl
  unfold applySlashingPenaltyElectra
  rw [hget, hepoch]
  show SameOutcome _ (if w.slashed then _ else _) (if w.slashed then _ else _)
  refine .ite Iff.rfl (fun _ => ?_) (fun _ => .returned ⟨_, rfl, h⟩)
  simp only [htwo, bind_ok]
  refine .bind (addChecked_same _ _).liftArith.liftAccessor ?_
  rintro due _ rfl -
  refine .ite (by
    rw [beq_iff_eq]
    exact UInt64.toNat_inj.symm) (fun _ => ?_) (fun _ => .returned ⟨_, rfl, h⟩)
  have hincrements : Spec.uint64Div (toSpecValidator w).effective_balance
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = _ := uint64Div_eq hdiv.increment
  rw [hincrements, bind_ok]
  refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
  rintro penalty _ rfl -
  have hi : i < 2 ^ 64 :=
    Nat.lt_trans (Array.getElem?_eq_some_iff.mp hw).1 (registry_lt hregistry)
  obtain ⟨index, hindex, rfl⟩ := ofNatChecked_ok hi
  rw [hindex]
  show SameOutcome _ (liftAccessor (decreaseBalance st index penalty)) _
  rw [← bind_pure (liftAccessor (decreaseBalance st index penalty))]
  exact .bind (decrease_balance_same h index penalty).liftAccessor fun _ balances h _ =>
    .returned ⟨balances, rfl, h⟩

end EpochProofs.EthLib
