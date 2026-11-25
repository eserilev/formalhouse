import EthLib.Consensus.Transition.Requests
import EpochProofs.EthLib.Balances
import EpochProofs.Spec.PendingConsolidations

/-!
# `process_pending_consolidations`: the reference and EthLib agree
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem getValidator_same (s : BeaconState preset fork) (index : UInt64) :
    SameOutcome (fun v w => w = toSpecValidator v) (getValidator s index)
      (Spec.listGet (toSpecState s).validators index.toNat) := by
  unfold getValidator Spec.listGet
  simp only [toSpecState, readList, List.getElem?_map, Array.getElem?_toList]
  cases s.validators.data[index.toNat]? with
  | none => exact .failed
  | some v => exact .returned rfl

theorem getBalance_same (s : BeaconState preset fork) (index : UInt64) :
    SameOutcome SameNumber (getBalance s index)
      (Spec.listGet (toSpecState s).balances index.toNat) := by
  unfold getBalance Spec.listGet
  simp only [toSpecState, readList, List.getElem?_map, Array.getElem?_toList]
  cases s.balances.data[index.toNat]? with
  | none => exact .failed
  | some v => exact .returned rfl

/-- One consolidation of the reference loop, on the number of consolidations read and the state. -/
def consolidationStep (next : Nat) (consolidation : Spec.PendingConsolidation)
    (acc : Nat × Spec.BeaconState) : Spec.SpecM (ForInStep (Nat × Spec.BeaconState)) := do
  let source ← Spec.listGet acc.2.validators consolidation.source_index
  if source.slashed then pure (.yield (acc.1 + 1, acc.2))
  else if source.withdrawable_epoch > next then pure (.done (acc.1, acc.2))
  else do
    let balance ← Spec.listGet acc.2.balances consolidation.source_index
    let balances ← Spec.decrease_balance acc.2.balances consolidation.source_index
      (min balance source.effective_balance)
    let balances ← Spec.increase_balance balances consolidation.target_index
      (min balance source.effective_balance)
    pure (.yield (acc.1 + 1, { acc.2 with balances := balances }))

theorem passPendingConsolidations_same (next : UInt64) :
    ∀ (l : List PendingConsolidation) (s : BeaconState preset fork) (k : Nat),
      SameOutcome (fun r acc => acc = (k + r.2, toSpecState r.1) ∧
          ∃ b : Balances preset fork, r.1 = { s with balances := b })
        (passPendingConsolidations next s l)
        (forIn (l.map toSpecPendingConsolidation) (k, toSpecState s)
          (consolidationStep next.toNat))
  | [], s, k => .returned ⟨rfl, s.balances, rfl⟩
  | consolidation :: rest, s, k => by
    rw [List.map_cons, List.forIn_cons, passPendingConsolidations]
    unfold consolidationStep
    simp only [bind_assoc]
    refine .bind (getValidator_same s consolidation.sourceIndex).liftAccessor ?_
    rintro source _ rfl -
    by_cases hslashed : source.slashed = true
    · have hslashed' : (toSpecValidator source).slashed = true := hslashed
      simp only [hslashed, hslashed', ite_true, pure_eq_ok, bind_ok]
      refine .bind_pure (passPendingConsolidations_same next rest s (k + 1)) ?_
      rintro ⟨s', read⟩ _ ⟨rfl, hb⟩
      exact ⟨by simp; omega, hb⟩
    · have hslashed' : ¬(toSpecValidator source).slashed = true := hslashed
      simp only [hslashed, hslashed', ite_false, Bool.false_eq_true]
      by_cases hwait : next < source.withdrawableEpoch
      · have hwait' : (toSpecValidator source).withdrawable_epoch > next.toNat :=
          UInt64.lt_iff_toNat_lt.mp hwait
        simp only [hwait, hwait', ite_true, pure_eq_ok, bind_ok]
        exact .returned ⟨rfl, s.balances, rfl⟩
      · have hwait' : ¬(toSpecValidator source).withdrawable_epoch > next.toNat := fun h =>
          hwait (UInt64.lt_iff_toNat_lt.mpr h)
        simp only [hwait, hwait', ite_false, bind_assoc]
        refine .bind (getBalance_same s consolidation.sourceIndex).liftAccessor ?_
        rintro balance _ rfl -
        have hmin : min balance.toNat (toSpecValidator source).effective_balance =
            (min balance source.effectiveBalance).toNat := (toNat_min _ _).symm
        rw [hmin]
        refine .bind (decrease_balance_same (OnlyBalancesChanged.refl s) _ _).liftAccessor ?_
        rintro s₁ balances₁ h₁ -
        refine .bind (increase_balance_same h₁ _ _).liftAccessor ?_
        rintro s₂ balances₂ h₂ -
        simp only [pure_eq_ok, bind_ok]
        rw [h₂.toSpecState_eq]
        refine .bind_pure (passPendingConsolidations_same next rest s₂ (k + 1)) ?_
        rintro ⟨s', read⟩ _ ⟨rfl, b, hb⟩
        obtain ⟨l, rfl, -, -⟩ := h₂
        exact ⟨by simp; omega, b, hb⟩

theorem pending_consolidations_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork) :
    SameOutcome SameState (processPendingConsolidations s electra)
      (Spec.process_pending_consolidations (toSpecPreset preset config) (toSpecState s)) := by
  unfold processPendingConsolidations Spec.process_pending_consolidations
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  rw [toSpecState_pending_consolidations s electra]
  refine .bind (passPendingConsolidations_same next (s.pendingConsolidations electra).data.toList
    s 0) ?_
  rintro ⟨s', read⟩ _ ⟨rfl, b, hb⟩ -
  refine .returned ?_
  simp only at hb
  subst hb
  rw [SameState, toSpecState_with_pending_consolidations _ electra]
  simp only [toSpecState_pending_consolidations _ electra]
  simp [readList, List.map_drop]

end EpochProofs.EthLib
