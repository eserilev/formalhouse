import EthLib.Consensus.Transition.EpochUpdates
import EpochProofs.EthLib.Accessors
import EpochProofs.EthLib.Loops
import EpochProofs.Spec.EffectiveBalanceUpdates

/-!
# `process_effective_balance_updates`: the reference and EthLib agree
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem is_compounding_eq (credentials : Bytes32) :
    Spec.is_compounding_withdrawal_credential credentials =
      isCompoundingWithdrawalCredential credentials := by
  have h : credentials.toList.take 1 = [credentials[0]] := by
    rw [List.take_one, List.head?_eq_getElem?, Vector.getElem?_toList]
    simp
  rw [Spec.is_compounding_withdrawal_credential, h, isCompoundingWithdrawalCredential]
  simp [Spec.COMPOUNDING_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]

theorem get_max_effective_balance_eq (electra : .pectra ≤ fork) (v : Validator) :
    Spec.get_max_effective_balance (toSpecPreset preset config) (toSpecValidator v) =
      (withdrawalMaxEffectiveBalance preset fork v).toNat := by
  simp only [Spec.get_max_effective_balance, Spec.has_compounding_withdrawal_credential,
    toSpecValidator, is_compounding_eq, withdrawalMaxEffectiveBalance, electra, ite_true,
    getMaxEffectiveBalance, hasCompoundingWithdrawalCredential, toSpecPreset]
  split <;> simp_all

/-- A balance, rounded down to a whole number of increments. -/
theorem round_to_increment_eq {increment : UInt64} (h : increment ≠ 0) (balance : UInt64) :
    (do
      let remainder ← Spec.uint64Mod balance.toNat increment.toNat
      Spec.uint64Sub balance.toNat remainder) = .ok (balance - balance % increment).toNat := by
  have hle : balance % increment ≤ balance := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  rw [uint64Mod_eq h, bind_ok, Spec.uint64Sub, ite_eq_left (UInt64.le_iff_toNat_le.mp hle),
    UInt64.toNat_sub_of_le _ _ hle]
  rfl

/-- The two states of the effective balance loop after `i` validators. -/
def EffectiveBalancesWritten (s : BeaconState preset fork) (i : Nat) (st : BeaconState preset fork)
    (acc : List Spec.Validator) : Prop :=
  ∃ l : Validators preset fork, st = { s with validators := l } ∧
    l.data.size = s.validators.data.size ∧ acc = (readList toSpecValidator l.data).take i ∧
    ∀ j, i ≤ j → l.data[j]? = s.validators.data[j]?

theorem write_effective_balance {s : BeaconState preset fork} {i : Nat} {l : Validators preset fork}
    {w : Validator} (hsize : l.data.size = s.validators.data.size)
    (hrest : ∀ j, i ≤ j → l.data[j]? = s.validators.data[j]?)
    (hw : s.validators.data[i]? = some w) (effective : UInt64) {acc : List Spec.Validator}
    (hacc : acc = (readList toSpecValidator l.data).take i ++
      [toSpecValidator { w with effectiveBalance := effective }]) :
    SameOutcome (fun st r => ∃ acc', r = ForInStep.yield acc' ∧
        EffectiveBalancesWritten s (i + 1) st acc')
      (liftAccessor (BeaconState.setValidatorAt { s with validators := l } i
        { w with effectiveBalance := effective }))
      (pure (.yield acc)) := by
  have hi : i < l.data.size := by
    rw [hsize]
    exact (Array.getElem?_eq_some_iff.mp hw).1
  refine .liftAccessor ?_
  rw [BeaconState.setValidatorAt, dite_eq_left hi]
  refine .returned ⟨_, rfl, l.set i _ hi, rfl, ?_, ?_, ?_⟩
  · simpa [RootedForkList.set] using hsize
  · rw [hacc]
    simp [RootedForkList.set, readList, List.take_add_one, List.map_set, hi, List.take_set_of_le]
  · intro j hj
    simp only [RootedForkList.set]
    rw [Array.getElem?_set_ne _ (by omega)]
    exact hrest j (by omega)

theorem effective_balance_updates_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork) :
    SameOutcome SameState (processEffectiveBalanceUpdates s)
      (Spec.process_effective_balance_updates (toSpecPreset preset config) (toSpecState s)) := by
  unfold processEffectiveBalanceUpdates Spec.process_effective_balance_updates
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  rw [← hlength]
  rw [← bind_pure ((List.range _).foldlM _ _)]
  refine .bind (SameOutcome.forIn_zipIdx (R := EffectiveBalancesWritten s) _ ?_ ?_) ?_
  · exact ⟨s.validators, rfl, rfl, by simp, fun _ _ => rfl⟩
  · rintro i _ _ v hv ⟨l, rfl, hsize, rfl, hrest⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w, s.validators.data[i]? = some w ∧ toSpecValidator w = v := by
      simpa [toSpecState, readList] using hv
    have hget : getValidatorAt { s with validators := l } i = .ok w := by
      rw [getValidatorAt]
      simp only
      rw [hrest i (Nat.le_refl i), hw]
    unfold updateEffectiveBalance
    rw [hget]
    have hbalance : (toSpecState s).balances[i]? = s.balances.data[i]?.map UInt64.toNat := by
      simp [toSpecState, readList]
    simp only [hbalance]
    cases hb : s.balances.data[i]? with
    | none =>
      have herror : ∃ e, getBalanceAt { s with validators := l } i = .error e := by
        rw [getBalanceAt]
        simp only [hb]
        cases ofNatChecked i <;> exact ⟨_, rfl⟩
      obtain ⟨e, he⟩ := herror
      rw [he]
      exact .failed
    | some balance =>
      have hok : getBalanceAt { s with validators := l } i = .ok balance := by
        rw [getBalanceAt]
        simp only [hb]
      rw [hok]
      simp only [Option.map_some, spec_preset, uint64Div_eq hdiv.hysteresisQuotient, pure_eq_ok,
        bind_ok]
      show SameOutcome _ (updatedEffectiveBalance preset _ balance w.effectiveBalance >>= _) _
      unfold updatedEffectiveBalance leavesBand
      simp only [bind_assoc]
      refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
      rintro downward _ rfl -
      refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
      rintro upward _ rfl -
      refine .bind (addChecked_same balance downward).liftArith.liftAccessor ?_
      rintro below _ rfl -
      by_cases hbelow : below < w.effectiveBalance
      · have hbelow' : below.toNat < (toSpecValidator w).effective_balance :=
          UInt64.lt_iff_toNat_lt.mp hbelow
        simp only [hbelow, hbelow', ite_true, pure_eq_ok, bind_ok]
        rw [← bind_assoc, round_to_increment_eq hdiv.increment]
        exact write_effective_balance hsize hrest hw _ (by
          rw [get_max_effective_balance_eq electra, ← toNat_min]
          rfl)
      · have hbelow' : ¬below.toNat < (toSpecValidator w).effective_balance := fun h =>
          hbelow (UInt64.lt_iff_toNat_lt.mpr h)
        simp only [hbelow, hbelow', ite_false, bind_assoc]
        refine .bind (addChecked_same w.effectiveBalance upward).liftArith.liftAccessor ?_
        rintro above _ rfl -
        simp only [pure_eq_ok, bind_ok]
        by_cases habove : above < balance
        · have habove' := UInt64.lt_iff_toNat_lt.mp habove
          simp only [habove, habove', decide_true, ite_true]
          rw [← bind_assoc, round_to_increment_eq hdiv.increment]
          exact write_effective_balance hsize hrest hw _ (by
            rw [get_max_effective_balance_eq electra, ← toNat_min]
            rfl)
        · have habove' : ¬above.toNat < balance.toNat := fun h =>
            habove (UInt64.lt_iff_toNat_lt.mpr h)
          simp only [habove, habove', decide_false, Bool.false_eq_true, ite_false]
          exact write_effective_balance hsize hrest hw _ rfl
  · rintro _ _ ⟨l, rfl, hsize, rfl, -⟩ -
    refine .pure ?_
    rw [SameState, List.take_of_length_le (by simp [readList, hlength, hsize])]
    rfl

end EpochProofs.EthLib
