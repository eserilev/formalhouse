import EthLib.Consensus.Transition.EpochRewards
import EpochProofs.EthLib.Consolidations
import EpochProofs.EthLib.Inactivity
import EpochProofs.Sanity.Invariants.BalanceFloor
import EpochProofs.Sanity.RewardsBound
import Mathlib.Data.Nat.Sqrt

/-!
# `process_rewards_and_penalties`: the reference and EthLib agree

The reference takes `get_total_active_balance(state)` as a parameter. EthLib reads it in the step,
but not in the genesis epoch. So the theorem takes the value that EthLib reads.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem integer_squareroot_eq (n : UInt64) :
    Spec.integer_squareroot n.toNat = (integerSquareroot n).toNat := by
  have hsqrt : Nat.sqrt n.toNat = Spec.integer_squareroot n.toNat := by
    have hle := Spec.integer_squareroot_mul_self_le n.toNat
    have hlt := Spec.integer_squareroot_spec n.toNat
    exact Nat.eq_sqrt.mpr ⟨hle, hlt⟩ |>.symm
  rw [integerSquareroot, hsqrt, UInt64.toNat_ofNat_of_lt']
  rw [← hsqrt]
  exact Nat.lt_of_le_of_lt (Nat.sqrt_le_self _) n.toNat_lt

theorem base_reward_same (hdiv : DivisorsNonzero preset config) (altair : .altair ≤ fork)
    (s : BeaconState preset fork) (total index : UInt64) :
    SameOutcome SameNumber (getBaseReward s total index)
      (Spec.get_base_reward (toSpecPreset preset config) total.toNat (toSpecState s)
        index.toNat) := by
  unfold getBaseReward getBaseRewardPerIncrement Spec.get_base_reward
    Spec.get_base_reward_per_increment
  simp only [altair, ite_true, spec_preset]
  refine .bind (getValidator_same s index) ?_
  rintro v _ rfl -
  have hincrements : Spec.uint64Div (toSpecValidator v).effective_balance
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = _ := uint64Div_eq hdiv.increment
  rw [hincrements, bind_ok, integer_squareroot_eq]
  refine .bind (M := SameNumber) (.liftArith (.bind (mulChecked_same _ _) ?_)) ?_
  · rintro product _ rfl -
    exact divChecked_same _ _
  · rintro perIncrement _ rfl -
    exact (mulChecked_same _ _).liftArith

/-- The rewards and penalties of EthLib are those of the reference, one for each validator. -/
def SameDeltas (n : Nat) (deltas : Array Gwei × Array Gwei) (specDeltas : List Nat × List Nat) :
    Prop :=
  specDeltas = (readList UInt64.toNat deltas.1, readList UInt64.toNat deltas.2) ∧
    deltas.1.size = n ∧ deltas.2.size = n

theorem zeroDeltas (n : Nat) :
    SameDeltas n (Array.replicate n 0, Array.replicate n 0)
      (List.replicate n 0, List.replicate n 0) := by
  refine ⟨?_, by simp, by simp⟩
  simp [readList]

theorem addDelta_same {deltas : Array Gwei} {index amount : UInt64}
    (hindex : index.toNat < deltas.size) :
    SameOutcome (fun (a : Array Gwei) b => b = readList UInt64.toNat a ∧ a.size = deltas.size)
      (addDelta deltas index amount)
      (do
        let sum ← Spec.uint64Add deltas[index.toNat].toNat amount.toNat
        Spec.listSet (readList UInt64.toNat deltas) index.toNat sum) := by
  rw [addDelta, dite_eq_left hindex]
  refine .bind (addChecked_same _ _).liftArith.liftAccessor ?_
  rintro sum _ rfl -
  rw [listSet_readList hindex]
  exact .returned ⟨rfl, by simp⟩

theorem flag_index_deltas_same (hdiv : DivisorsNonzero preset config) (altair : .altair ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) {total : UInt64}
    (htotal : getTotalActiveBalance s = .ok total)
    (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    SameOutcome (SameDeltas s.validators.data.size) (getFlagIndexDeltas s altair flag)
      (Spec.get_flag_index_deltas (toSpecPreset preset config) total.toNat (toSpecState s)
        flag.val) := by
  have hflag : flag.val.toUInt64.toNat = flag.val := by
    have := flag.isLt
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans this (by decide))
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  unfold getFlagIndexDeltas Spec.get_flag_index_deltas
  rw [get_previous_epoch_eq hdiv.slots, hlength]
  simp only [bind_ok, spec_preset]
  have hparticipating := get_unslashed_participating_indices_same (config := config) hdiv.slots
    altair hregistry flag.val.toUInt64 (by rw [hflag]; exact flag.isLt) (getPreviousEpoch s)
  rw [hflag] at hparticipating
  refine .bind hparticipating.liftAccessor ?_
  intro participating specParticipating hsame _
  have hweight : Spec.listGet Spec.PARTICIPATION_FLAG_WEIGHTS flag.val =
      .ok PARTICIPATION_FLAG_WEIGHTS[flag].toNat := by
    match flag with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  rw [hweight, bind_ok]
  refine .bind (get_total_balance_same hsame).liftAccessor ?_
  rintro balance _ rfl -
  rw [htotal]
  simp only [uint64Div_eq hdiv.increment, bind_ok, liftAccessor, Except.mapError]
  refine .bind (get_eligible_validator_indices_same hdiv.slots hregistry) ?_
  rintro eligible _ ⟨rfl, -, hinside⟩ -
  obtain ⟨rfl, -, -⟩ := hsame
  rw [← bind_pure (List.foldlM _ _ _)]
  refine .bind (SameOutcome.forIn_indices (R := SameDeltas s.validators.data.size) eligible
    (zeroDeltas _) ?_) (fun _ _ h _ => .returned h)
  rintro index ⟨rewards, penalties⟩ _ hmem ⟨rfl, hrewards, hpenalties⟩
  simp only at hrewards hpenalties ⊢
  have hindex := hinside index hmem
  have hindexRewards : index.toNat < rewards.size := by rw [hrewards]; exact hindex
  have hindexPenalties : index.toNat < penalties.size := by rw [hpenalties]; exact hindex
  unfold addFlagDelta
  refine .bind (base_reward_same hdiv altair s total index).liftAccessor ?_
  rintro base _ rfl -
  rw [markIndices_getD hindex]
  by_cases hhit : index.toNat ∈ participating.map UInt64.toNat
  · simp only [hhit, decide_true, ite_true]
    refine .bind (is_in_inactivity_leak_same hdiv.slots s) ?_
    rintro _ leak rfl -
    cases leak
    · simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false,
        listGet_readList hindexRewards, bind_ok]
      rw [← bind_assoc (Spec.uint64Mul _ _)]
      refine .bind (M := SameNumber) (SameOutcome.liftAccessor (.liftArith
        (.bind (mulChecked_same _ _) ?_))) ?_
      · rintro product _ rfl -
        exact mulChecked_same _ _
      rintro numerator _ rfl -
      refine .bind (mulChecked_same _ WEIGHT_DENOMINATOR).liftArith.liftAccessor ?_
      rintro denominator _ rfl -
      refine .bind (divChecked_same _ _).liftArith.liftAccessor ?_
      rintro reward _ rfl -
      rw [← bind_assoc (Spec.uint64Add _ _)]
      refine .bind (addDelta_same hindexRewards) ?_
      rintro rewards' _ ⟨rfl, hsize⟩ -
      exact .returned ⟨_, rfl, rfl, hsize.trans hrewards, hpenalties⟩
    · exact .returned ⟨_, rfl, rfl, hrewards, hpenalties⟩
  · simp only [hhit, decide_false, Bool.false_eq_true, ite_false]
    have hhead : (flag.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX) ↔
        flag.val = Spec.TIMELY_HEAD_FLAG_INDEX := by
      rw [← UInt64.toNat_inj, hflag]
      rfl
    by_cases hflagHead : flag.val = Spec.TIMELY_HEAD_FLAG_INDEX
    · rw [ite_eq_left (hhead.mpr hflagHead), ite_eq_right (by simp [hflagHead])]
      exact .returned ⟨_, rfl, rfl, hrewards, hpenalties⟩
    · rw [ite_eq_right (fun h => hflagHead (hhead.mp h)), ite_eq_left (by simpa using hflagHead)]
      simp only [listGet_readList hindexPenalties, bind_ok]
      refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
      rintro scaled _ rfl -
      have hden : Spec.uint64Div scaled.toNat Spec.WEIGHT_DENOMINATOR =
          .ok (scaled / WEIGHT_DENOMINATOR).toNat :=
        uint64Div_eq (b := WEIGHT_DENOMINATOR) (by decide)
      rw [hden, bind_ok, ← bind_assoc]
      refine .bind (addDelta_same hindexPenalties) ?_
      rintro penalties' _ ⟨rfl, hsize⟩ -
      exact .returned ⟨_, rfl, rfl, hrewards, hsize.trans hpenalties⟩

theorem inactivity_penalty_deltas_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) :
    SameOutcome (SameDeltas s.validators.data.size) (getInactivityPenaltyDeltas config s)
      (Spec.get_inactivity_penalty_deltas (toSpecPreset preset config) (toSpecState s)) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : fork ≥ .bellatrix := Nat.le_trans (by decide) electra
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  unfold getInactivityPenaltyDeltas Spec.get_inactivity_penalty_deltas
  rw [get_previous_epoch_eq hdiv.slots, hlength]
  simp only [bind_ok, spec_preset, altair, dite_true]
  refine .bind (get_unslashed_participating_indices_same hdiv.slots altair hregistry
    TIMELY_TARGET_FLAG_INDEX (by decide) (getPreviousEpoch s)).liftAccessor ?_
  rintro matching _ ⟨rfl, -, -⟩ -
  refine .bind (get_eligible_validator_indices_same hdiv.slots hregistry) ?_
  rintro eligible _ ⟨rfl, -, hinside⟩ -
  refine .bind (SameOutcome.forIn_indices (R := fun (penalties : Array Gwei) acc =>
    acc = readList UInt64.toNat penalties ∧ penalties.size = s.validators.data.size) eligible
    ⟨by simp [readList], by simp⟩ ?_) ?_
  · rintro index penalties _ hmem ⟨rfl, hpenalties⟩
    have hindex := hinside index hmem
    have hindexPenalties : index.toNat < penalties.size := by rw [hpenalties]; exact hindex
    unfold addInactivityScorePenalty
    rw [markIndices_getD hindex]
    by_cases hhit : index.toNat ∈ matching.map UInt64.toNat
    · simp only [hhit, decide_true, ite_true, not_true_eq_false, ite_false]
      exact .returned ⟨_, rfl, rfl, hpenalties⟩
    · simp only [hhit, decide_false, Bool.false_eq_true, ite_false, not_false_eq_true, ite_true,
        listGet_readList hindexPenalties, bind_ok]
      refine .bind (getValidator_same s index).liftAccessor ?_
      rintro v _ rfl -
      rw [toSpecState_inactivity_scores s altair]
      cases hscore : (s.inactivityScores altair).data[index.toNat]? with
      | none =>
        have : ¬index.toNat < (s.inactivityScores altair).data.size := by simpa using hscore
        rw [listGet_readList_error this]
        exact .failed
      | some score =>
        obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hscore
        rw [listGet_readList hlt, bind_ok]
        simp only [parameters, bellatrix, ite_true]
        refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
        rintro numerator _ rfl -
        refine .bind (mulChecked_same _ _).liftArith.liftAccessor ?_
        rintro denominator _ rfl -
        rw [← bind_pure (Bind.bind (liftAccessor _) _)]
        simp only [bind_assoc]
        refine .bind (divChecked_same _ _).liftArith.liftAccessor ?_
        rintro penalty _ rfl -
        rw [← bind_assoc (Spec.uint64Add _ _)]
        refine .bind (addDelta_same hindexPenalties) ?_
        rintro penalties' _ ⟨rfl, hsize⟩ -
        exact .returned ⟨_, rfl, rfl, hsize.trans hpenalties⟩
  · rintro penalties _ ⟨rfl, hpenalties⟩ -
    exact .returned ⟨by simp [readList], by simp, hpenalties⟩

theorem apply_deltas_same {s st : BeaconState preset fork} (hregistry : s.RegistryWithinLimit)
    {balances : List Nat} {deltas : Array Gwei × Array Gwei} {specDeltas : List Nat × List Nat}
    (hdeltas : SameDeltas s.validators.data.size deltas specDeltas)
    (h : OnlyBalancesChanged s st balances) :
    SameOutcome (OnlyBalancesChanged s) (applyAllDeltas st deltas)
      (forIn (List.range s.validators.data.size) balances fun index balances => do
        let reward ← Spec.listGet specDeltas.1 index
        let balances ← Spec.increase_balance balances index reward
        let penalty ← Spec.listGet specDeltas.2 index
        let balances ← Spec.decrease_balance balances index penalty
        pure (.yield balances)) := by
  obtain ⟨rfl, hrewards, hpenalties⟩ := hdeltas
  have hvalidators : st.validators = s.validators := by
    obtain ⟨l, rfl, -, -⟩ := h
    rfl
  unfold applyAllDeltas
  rw [hvalidators]
  refine SameOutcome.forIn_range (R := fun _ => OnlyBalancesChanged s) _ h ?_
  intro i st balances hi h
  unfold applyDeltas
  obtain ⟨index, hindex, rfl⟩ := ofNatChecked_ok (Nat.lt_trans hi (registry_lt hregistry))
  have hi₁ : index.toNat < deltas.1.size := by rw [hrewards]; exact hi
  have hi₂ : index.toNat < deltas.2.size := by rw [hpenalties]; exact hi
  rw [hindex]
  simp only [listGet_readList hi₁, listGet_readList hi₂, bind_ok]
  refine .liftAccessor ?_
  have hget₁ : deltas.1.getD index.toNat 0 = deltas.1[index.toNat] := by simp [Array.getD, hi₁]
  have hget₂ : deltas.2.getD index.toNat 0 = deltas.2[index.toNat] := by simp [Array.getD, hi₂]
  rw [hget₁, hget₂]
  refine .bind (x := increaseBalance st index _) (increase_balance_same h index _) ?_
  rintro st₁ balances₁ h₁ -
  rw [← bind_pure (decreaseBalance st₁ index _)]
  exact .bind (decrease_balance_same h₁ index _) fun _ balances₂ h₂ _ =>
    .returned ⟨balances₂, rfl, h₂⟩

theorem rewards_and_penalties_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit)
    {total : UInt64} (htotal : getTotalActiveBalance s = .ok total) :
    SameOutcome SameState (processRewardsAndPenalties config s)
      (Spec.process_rewards_and_penalties (toSpecPreset preset config) total.toNat
        (toSpecState s)) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  unfold processRewardsAndPenalties Spec.process_rewards_and_penalties
  rw [get_current_epoch_eq hdiv.slots, hlength]
  simp only [bind_ok, altair, dite_true]
  refine .ite (by
    rw [beq_iff_eq, ← UInt64.toNat_inj]
    rfl) (fun _ => .returned rfl) (fun _ => ?_)
  have hflag := flag_index_deltas_same hdiv altair hregistry htotal
  have hfin : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
  have hrange : List.range Spec.PARTICIPATION_FLAG_WEIGHTS.length = [0, 1, 2] := by decide
  rw [hfin, hrange]
  simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind]
  refine .bind (hflag ⟨0, by decide⟩) fun deltas₀ _ h₀ _ => ?_
  refine .bind (hflag ⟨1, by decide⟩) fun deltas₁ _ h₁ _ => ?_
  refine .bind (hflag ⟨2, by decide⟩) fun deltas₂ _ h₂ _ => ?_
  refine .bind (inactivity_penalty_deltas_same hdiv electra hregistry) fun deltas₃ _ h₃ _ => ?_
  simp only [List.cons_append, List.nil_append, List.foldlM_cons, List.foldlM_nil,
    List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  refine .bind (apply_deltas_same hregistry h₀ (.refl s)) fun s₀ _ hs₀ _ => ?_
  refine .bind (apply_deltas_same hregistry h₁ hs₀) fun s₁ _ hs₁ _ => ?_
  refine .bind (apply_deltas_same hregistry h₂ hs₁) fun s₂ _ hs₂ _ => ?_
  refine .bind (apply_deltas_same hregistry h₃ hs₂) fun s₃ _ hs₃ _ => ?_
  exact .returned hs₃.toSpecState_eq

end EpochProofs.EthLib
