import EthLib.Consensus.Transition.BuilderPayments
import EpochProofs.EthLib.Accessors
import EpochProofs.Spec.BuilderPendingPayments

/-!
# `process_builder_pending_payments`: the reference and EthLib agree

The reference takes `get_total_active_balance(state)` as a parameter. The theorem reads it first,
as `process_epoch` does.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem builder_payment_quorum_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameNumber (getBuilderPaymentQuorumThreshold s)
      (do
        let total ← Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s)
        Spec.get_builder_payment_quorum_threshold (toSpecPreset preset config) total) := by
  unfold getBuilderPaymentQuorumThreshold Spec.get_builder_payment_quorum_threshold
  refine .bind (get_total_active_balance_same hslots hregistry) ?_
  rintro total _ rfl -
  simp only [toSpecPreset, uint64Div_eq hslots, bind_ok]
  refine .bind (mulChecked_same (total / preset.SLOTS_PER_EPOCH)
    BUILDER_PAYMENT_THRESHOLD_NUMERATOR).liftArith ?_
  rintro quorum _ rfl -
  have hdiv := uint64Div_eq (a := quorum) (b := BUILDER_PAYMENT_THRESHOLD_DENOMINATOR) (by decide)
  have hdiv' : Spec.uint64Div quorum.toNat Spec.BUILDER_PAYMENT_THRESHOLD_DENOMINATOR = _ := hdiv
  rw [hdiv']
  exact .returned rfl

theorem forIn_released {payments : List BuilderPendingPayment} {quorum : UInt64} :
    ∀ {acc : List Spec.BuilderPendingWithdrawal},
      (forIn (payments.map toSpecBuilderPendingPayment) acc fun payment acc =>
        if payment.weight ≥ quorum.toNat then
          Pure.pure (ForInStep.yield (acc ++ [payment.withdrawal]))
        else Pure.pure (ForInStep.yield acc) : Spec.SpecM _) =
      .ok (acc ++ ((payments.filter (quorum ≤ ·.weight)).map (·.withdrawal)).map
        toSpecBuilderPendingWithdrawal) := by
  induction payments with
  | nil => intro acc; simp [Pure.pure, Except.pure]
  | cons payment payments ih =>
    intro acc
    rw [List.map_cons, List.forIn_cons]
    by_cases h : quorum ≤ payment.weight
    · have h' : (toSpecBuilderPendingPayment payment).weight ≥ quorum.toNat :=
        UInt64.le_iff_toNat_le.mp h
      rw [ite_eq_left h', pure_eq_ok, bind_ok]
      simp only
      rw [ih]
      simp [h, toSpecBuilderPendingPayment]
    · have h' : ¬(toSpecBuilderPendingPayment payment).weight ≥ quorum.toNat := fun h' =>
        h (UInt64.le_iff_toNat_le.mpr h')
      rw [ite_eq_right h', pure_eq_ok, bind_ok]
      simp only
      rw [ih]
      simp [h]

theorem shiftPayments_toList (payments : BuilderPendingPayments preset) :
    (shiftPayments payments).elements.toList =
      payments.elements.toList.drop preset.SLOTS_PER_EPOCH.toNat ++
        List.replicate preset.SLOTS_PER_EPOCH.toNat BuilderPendingPayment.empty := by
  apply List.ext_getElem?
  intro i
  simp only [shiftPayments, RootedVector.ofVector]
  by_cases hi : i < 2 * preset.SLOTS_PER_EPOCH.toNat
  · rw [Vector.getElem?_toList, Vector.getElem?_eq_getElem hi, Vector.getElem_ofFn]
    by_cases h : i < preset.SLOTS_PER_EPOCH.toNat
    · rw [List.getElem?_append_left (by simp; omega)]
      have hlt : preset.SLOTS_PER_EPOCH.toNat + i < 2 * preset.SLOTS_PER_EPOCH.toNat := by omega
      rw [List.getElem?_drop, Vector.getElem?_toList, Vector.getElem?_eq_getElem hlt,
        dite_eq_left h]
      simp only [Nat.add_comm]
      rfl
    · rw [List.getElem?_append_right (by simp; omega)]
      rw [dite_eq_right h, List.getElem?_replicate, ite_eq_left (by simp; omega)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem builder_pending_payments_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (gloas : .glamsterdam ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (liftAccessor (processBuilderPendingPayments s gloas))
      (do
        let total ← Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s)
        Spec.process_builder_pending_payments (toSpecPreset preset config) total
          (toSpecState s)) := by
  unfold processBuilderPendingPayments Spec.process_builder_pending_payments
  refine .liftAccessor ?_
  rw [← bind_assoc]
  refine .bind (builder_payment_quorum_same hslots hregistry) ?_
  rintro quorum _ rfl -
  rw [toSpecState_builder_pending_payments s gloas]
  have htake (n : Nat) (l : List BuilderPendingPayment) :
      (l.map toSpecBuilderPendingPayment).take n = (l.take n).map toSpecBuilderPendingPayment :=
    List.map_take.symm
  simp only [htake, forIn_released, bind_ok]
  refine .returned ?_
  rw [SameState]
  have hempty : toSpecBuilderPendingPayment BuilderPendingPayment.empty =
      Spec.BuilderPendingPayment.empty := rfl
  simp only [toSpecState, fieldOr, gloas, dite_true, readList, releasedPayments,
    shiftPayments_toList, toSpecPreset, List.map_append, List.map_replicate, hempty, List.map_drop,
    Array.toList_append]
  rw [List.take_left' (by simp; omega)]

end EpochProofs.EthLib
