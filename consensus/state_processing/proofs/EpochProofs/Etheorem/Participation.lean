import EpochProofs.Etheorem.Helpers
import EpochProofs.Sanity.RowsInactivity

/-!
# Participation: the reference equals Etheorem

The passes read the same index sets: the participating indices of one flag, the eligible
indices and the leak flag. This file proves each one equal to its Etheorem copy.

`PassesPresetAgrees p` adds the preset values that the passes read to `PresetAgrees p`.
-/

namespace EpochProofs.Etheorem
open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Gloas

set_option maxRecDepth 20000 in
/-- The two flag tests agree on every byte, for the three flag indices. -/
theorem hasFlag_eq_spec : ∀ n < 256, ∀ k < 3,
    (UInt8.ofNat n &&& UInt8.ofNat (2 ^ k) == UInt8.ofNat (2 ^ k)) = hasFlag (UInt8.ofNat n) k := by
  decide

theorem has_flag_eq (f : UInt8) (k : Nat) (hk : k < 3) : Spec.has_flag f k = .ok (hasFlag f k) := by
  have h := hasFlag_eq_spec f.toNat f.toNat_lt k hk
  rw [UInt8.ofNat_toNat] at h
  have hk' : 2 ^ k < 256 := by
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  simp only [Spec.has_flag, hk', if_true, pure, Except.pure, h]

/-- The value of a test that does not fail, and `false` otherwise. -/
def okValue (b : Spec.SpecM Bool) : Bool :=
  match b with
  | .ok v => v
  | .error _ => false

/-- If a filtering fold succeeds, every test succeeds and the fold is `List.filter`. -/
theorem foldlM_filterStep_inv {α β : Type} (P : α → Spec.SpecM Bool) (out : α → β) :
    ∀ (l : List α) (acc r : List β), l.foldlM (Spec.filterStep P out) acc = .ok r →
      (∀ x ∈ l, P x = .ok (okValue (P x))) ∧ r = acc ++ (l.filter (okValue ∘ P)).map out := by
  intro l
  induction l with
  | nil => intro acc r h; exact ⟨by simp, by simpa [pure, Except.pure] using h.symm⟩
  | cons x xs ih =>
    intro acc r h
    rw [List.foldlM_cons] at h
    cases hp : P x with
    | error e => simp [Spec.filterStep, hp, bind, Except.bind] at h
    | ok b =>
      simp only [Spec.filterStep, hp, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨hQ, hr⟩ := ih _ _ h
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp [hp, okValue]
        · exact hQ y hy
      · rw [hr]
        cases b <;> simp [hp, okValue]

theorem foldl_push_filter {α : Type} (c : α → Bool) : ∀ (l : List α) (acc : Array α),
    (l.foldl (fun r i => if c i then r.push i else r) acc).toList = acc.toList ++ l.filter c := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i l ih => intro acc; by_cases hc : c i <;> simp [hc, ih]

/-- A loop in `Except` whose every step yields `step b a` runs as the fold of `step`. -/
theorem forIn_except_yield {ε α β : Type} (step : β → α → β) :
    ∀ (l : List α) (body : α → β → Except ε (ForInStep β)) (init : β),
      (∀ a ∈ l, ∀ b, body a b = .ok (.yield (step b a))) →
      forIn l init body = .ok (l.foldl step init) := by
  intro l
  induction l with
  | nil => intro body init _; rfl
  | cons a l ih =>
    intro body init hb
    rw [List.forIn_cons, hb a (by simp) init]
    exact ih body _ (fun a' ha' b => hb a' (by simp [ha']) b)

/-! ## `Except` binds -/

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind {ε α β : Type} (x : ε) (f : α → Except ε β) :
    (Except.error x >>= f) = Except.error x := rfl

theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error err => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem uint64Mul_ok_val {a b n : Nat} (h : Spec.uint64Mul a b = .ok n) : n = a * b := by
  unfold Spec.uint64Mul at h; split at h
  · cases h; rfl
  · cases h

theorem mem_map_toNat_iff (mt : Array UInt64) (vi : UInt64) :
    vi.toNat ∈ mt.toList.map UInt64.toNat ↔ mt.contains vi = true := by
  rw [Array.contains_iff_mem, ← Array.mem_toList_iff]
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := List.mem_map.mp h
    rwa [UInt64.toNat_inj.mp hwv] at hw
  · intro h; exact List.mem_map_of_mem h

section WithPreset

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

open EthCLSpecs.Gloas in
/-- The preset values that the passes read, beyond `PresetAgrees`. -/
structure PassesPresetAgrees [EthCLSpecs.Gloas.Config] (p : Spec.Preset) : Prop
    extends PresetAgrees p where
  minEpochsToInactivityPenalty :
    Const.minEpochsToInactivityPenalty.toNat = p.MIN_EPOCHS_TO_INACTIVITY_PENALTY
  inactivityScoreBias : Const.inactivityScoreBias.toNat = p.INACTIVITY_SCORE_BIAS
  inactivityScoreRecoveryRate :
    Const.inactivityScoreRecoveryRate.toNat = p.INACTIVITY_SCORE_RECOVERY_RATE
  inactivityPenaltyQuotientBellatrix :
    Const.inactivityPenaltyQuotientBellatrix = p.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
  epochsPerSlashingsVector : Const.epochsPerSlashingsVector = p.EPOCHS_PER_SLASHINGS_VECTOR
  proportionalSlashingMultiplierBellatrix :
    Const.proportionalSlashingMultiplierBellatrix = p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX
  slotsPerHistoricalRoot : Const.slotsPerHistoricalRoot = p.SLOTS_PER_HISTORICAL_ROOT
  slotsPerEpochTwo : 2 ≤ p.SLOTS_PER_EPOCH
  epochsPerSlashingsVectorLt : p.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 63
  proportionalSlashingMultiplierLt : p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX < 2 ^ 64
  /-- The increment and the base reward factor of mainnet and minimal. With them the base reward is
  at most `1 / 256` of the effective balance (`rewardsBaseReward_bound`), so Etheorem's product
  `base_reward * weight` fits in `uint64`. -/
  effectiveBalanceIncrementEq : p.EFFECTIVE_BALANCE_INCREMENT = 1000000000
  baseRewardFactorEq : p.BASE_REWARD_FACTOR = 64

/-- A loop that writes a plain state on each step runs as a fold over plain states. -/
theorem forIn_pureState {α : Type} (G : α → EState → EState)
    (body : α → EthCLSpecs.Gloas.State → Id (ForInStep EthCLSpecs.Gloas.State))
    (hb : ∀ a w, body a (pureState w) = pure (ForInStep.yield (pureState (G a w)))) :
    ∀ (l : List α) (v : EState), forIn l (pureState v) body = pure (pureState (l.foldl (fun w a => G a w) v)) := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons a l ih => intro v; rw [List.forIn_cons, hb]; exact ih _

/-- A monadic loop over plain states runs as a fold, while each step succeeds. `I` holds on every
state the fold reaches. -/
theorem forIn_run_pureState {α : Type} (s0 : EthCLSpecs.Gloas.State) (G : α → EState → EState)
    (I : EState → Prop) (body : α → EthCLSpecs.Gloas.State → GloasRun (ForInStep EthCLSpecs.Gloas.State))
    (l : List α) (hI : ∀ a ∈ l, ∀ w, I w → I (G a w))
    (hb : ∀ a ∈ l, ∀ w, I w →
      (body a (pureState w)).run s0 = .ok (ForInStep.yield (pureState (G a w)), s0))
    (v : EState) (hv : I v) :
    (forIn l (pureState v) body).run s0 = .ok (pureState (l.foldl (fun w a => G a w) v), s0) := by
  induction l generalizing v with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, run_bind, hb a (by simp) v hv, except_bind_ok]
    exact ih (fun b hb' w hw => hI b (by simp [hb']) w hw)
      (fun b hb' w hw => hb b (by simp [hb']) w hw) _ (hI a (by simp) v hv)

/-- The pure box is the uncached constructor, so a `match` on it reduces. -/
theorem pureState_eq (w : EState) :
    pureState w = SizzLean.Cache.SSZ.Box.uncached ⟨w⟩ := rfl

/-- The participation list that Etheorem reads for `epoch`. -/
def eParticipation (e : EState) (epoch : UInt64) :
    SSZList EthCLSpecs.Gloas.ParticipationFlags EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
  if epoch == EthCLSpecs.Gloas.computeEpochAtSlot e.slot then e.currentEpochParticipation
  else e.previousEpochParticipation

/-- The participating indices of `flag` that Etheorem returns, when every participation read is
in bounds. -/
def eUnslashed (e : EState) (flag : Nat) (epoch : UInt64) : Array UInt64 :=
  (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).filter
    (fun i => hasFlag (eParticipation e epoch)[i.toNat]! flag && !(e.validators[i.toNat]!).slashed)

/-- Etheorem's `getUnslashedParticipatingIndices` returns `eUnslashed` when the participation
list covers every active index. Etheorem reads `epoch_participation[i]` with `sszGetIdx`, which
rejects past the end, as the spec's `IndexError` does. -/
theorem getUnslashedParticipatingIndices_ok (e : EState) (flag : Nat) (epoch : UInt64)
    (hlt : ∀ i ∈ (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).toList,
      i.toNat < (eParticipation e epoch).val.size) :
    EthCLSpecs.Gloas.getUnslashedParticipatingIndices (pureState e) flag epoch =
      .ok (eUnslashed e flag epoch) := by
  unfold EthCLSpecs.Gloas.getUnslashedParticipatingIndices
  simp only [view_uncachedBox]
  rw [← Array.forIn_toList]
  have hpart : (if (epoch == EthCLSpecs.Gloas.computeEpochAtSlot e.slot) = true then
      e.currentEpochParticipation else e.previousEpochParticipation) = eParticipation e epoch := rfl
  rw [hpart, forIn_except_yield (fun r i => if (hasFlag (eParticipation e epoch)[i.toNat]! flag &&
      !(e.validators[i.toNat]!).slashed) = true then r.push i else r)]
  · show Except.ok _ = _
    congr 1
    apply Array.toList_inj.mp
    rw [foldl_push_filter, eUnslashed, Array.toList_filter]
    simp
  · intro i hi r
    have hget : (sszGetIdx (eParticipation e epoch) i.toNat :
        Except StateTransitionError EthCLSpecs.Gloas.ParticipationFlags) =
        .ok (eParticipation e epoch)[i.toNat]! := by
      have hl := hlt i hi
      simp [sszGetIdx, liftErr, MonadExcept.ofExcept, Except.mapError, hl]
      rfl
    rw [hget, ok_bind]
    split <;> rfl

/-- Every validator active in the previous epoch is eligible. -/
theorem active_prev_mem_eligible (e : EState) (i : UInt64)
    (hi : i ∈ (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e)
      (EthCLSpecs.Gloas.previousEpochOf (pureState e))).toList) :
    i ∈ (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList := by
  unfold EthCLSpecs.Gloas.getActiveValidatorIndices at hi
  unfold EthCLSpecs.Gloas.getEligibleValidatorIndices
  rw [indicesWhere_toList] at hi ⊢
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  refine List.mem_map.mpr ⟨j, ?_, rfl⟩
  rw [List.mem_filter] at hj ⊢
  exact ⟨hj.1, by simp only [Bool.or_eq_true]; exact Or.inl hj.2⟩

variable [EthCLSpecs.Gloas.Config] {p : Spec.Preset} (hp : PresetAgrees p)
include hp

theorem active_lt (e : EState) (epoch : UInt64) :
    ∀ i ∈ (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).toList,
      i.toNat < e.validators.val.size := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  intro i hi
  unfold EthCLSpecs.Gloas.getActiveValidatorIndices at hi
  rw [indicesWhere_toList] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have hj' := (List.mem_range.mp (List.mem_filter.mp hj).1)
  simp only [view_uncachedBox, SSZList.toArray] at hj'
  rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hj' hsize)]
  exact hj'

/-- `get_unslashed_participating_indices` equals Etheorem's. The reference also raises when the
epoch is not the previous or the current one. Etheorem has no such assert. -/
theorem get_unslashed_participating_indices_ok (e : EState) (flag : Nat) (hflag : flag < 3)
    (epoch : UInt64) {l : List Nat}
    (h : Spec.get_unslashed_participating_indices p (absEState e) flag epoch.toNat = .ok l) :
    EthCLSpecs.Gloas.getUnslashedParticipatingIndices (pureState e) flag epoch =
      .ok (eUnslashed e flag epoch) ∧
    l = (eUnslashed e flag epoch).toList.map UInt64.toNat := by
  unfold Spec.get_unslashed_participating_indices at h
  rw [get_previous_epoch_eq hp, get_current_epoch_eq hp] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rw [get_active_validator_indices_eq hp] at h
  simp only [pure, Except.pure] at h
  generalize hpart : (if (epoch.toNat == UInt64.toNat (EthCLSpecs.Gloas.currentEpochOf (pureState e))) = true then
      (absEState e).current_epoch_participation else (absEState e).previous_epoch_participation) = part at h
  rw [Spec.forIn_yield_eq_foldlM (step := Spec.filterStep
      (fun i => do Spec.has_flag (← Spec.listGet part i) flag) id)] at h
  rotate_left
  · intro i acc
    simp only [Spec.filterStep, bind, Except.bind, pure, Except.pure]
    cases Spec.listGet part i with
    | error err => rfl
    | ok f =>
      dsimp only
      cases Spec.has_flag f flag with
      | error err => rfl
      | ok b => cases b <;> rfl
  cases h1 : (List.map UInt64.toNat (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).toList).foldlM
      (Spec.filterStep (fun i => do Spec.has_flag (← Spec.listGet part i) flag) id) [] with
  | error err => rw [h1] at h; cases h
  | ok l1 =>
  rw [h1] at h
  dsimp only at h
  rw [Spec.forIn_yield_eq_foldlM (step := Spec.filterStep
      (fun i => do pure !(← Spec.listGet (absEState e).validators i).slashed) id)] at h
  rotate_left
  · intro i acc
    simp only [Spec.filterStep, bind, Except.bind, pure, Except.pure]
    cases Spec.listGet (absEState e).validators i with
    | error err => rfl
    | ok v => dsimp only; cases v.slashed <;> rfl
  cases h2 : l1.foldlM
      (Spec.filterStep (fun i => do pure !(← Spec.listGet (absEState e).validators i).slashed) id) [] with
  | error err => rw [h2] at h; cases h
  | ok l2 =>
  rw [h2] at h
  cases h
  have hpart' : part = (eParticipation e epoch).val.toList := by
    rw [← hpart]
    unfold eParticipation
    have hc : EthCLSpecs.Gloas.currentEpochOf (pureState e) =
        EthCLSpecs.Gloas.computeEpochAtSlot e.slot := rfl
    rw [hc]
    by_cases heq : epoch = EthCLSpecs.Gloas.computeEpochAtSlot e.slot
    · simp [heq]
    · have : (epoch.toNat == (EthCLSpecs.Gloas.computeEpochAtSlot e.slot).toNat) = false := by
        simpa [UInt64.toNat_inj] using heq
      simp [this, heq]
  subst hpart'
  obtain ⟨hQ1, rfl⟩ := foldlM_filterStep_inv _ _ _ _ _ h1
  obtain ⟨-, rfl⟩ := foldlM_filterStep_inv _ _ _ _ _ h2
  refine ⟨getUnslashedParticipatingIndices_ok e flag epoch ?_, ?_⟩
  · -- Each participation read of the reference succeeds, so it is in bounds.
    intro i hi
    have hP1 := hQ1 i.toNat (List.mem_map_of_mem hi)
    simp only [bind, Except.bind] at hP1
    cases hg : Spec.listGet (eParticipation e epoch).val.toList i.toNat with
    | error err => rw [hg] at hP1; cases hP1
    | ok f => exact (listGet_map_ok _ id _ (by simpa using hg)).1
  rw [eUnslashed, Array.toList_filter]
  simp only [List.nil_append, List.map_id, List.filter_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  have hlt := active_lt hp e epoch i hi
  have hP2 : okValue (do pure !(← Spec.listGet (absEState e).validators i.toNat).slashed) =
      !(e.validators[i.toNat]!).slashed := by
    have hg : Spec.listGet (absEState e).validators i.toNat =
        .ok (absValidator e.validators.val[i.toNat]!) := by
      simp [Spec.listGet, hlt, pure, Except.pure]
    simp only [hg, okValue, bind, Except.bind, absValidator, pure, Except.pure, sszList_getElem!_val]
    done
  have hP1 := hQ1 i.toNat (List.mem_map_of_mem hi)
  generalize hb : okValue (do Spec.has_flag (← Spec.listGet (eParticipation e epoch).val.toList i.toNat) flag) = b at hP1
  have hval : b = hasFlag (eParticipation e epoch)[i.toNat]! flag := by
    simp only [bind, Except.bind] at hP1
    cases hg : Spec.listGet (eParticipation e epoch).val.toList i.toNat with
    | error err => rw [hg] at hP1; cases hP1
    | ok f =>
      rw [hg] at hP1
      obtain ⟨-, rfl⟩ := listGet_map_ok _ id _ (by simpa using hg)
      simp only [id] at hP1
      rw [has_flag_eq _ _ hflag] at hP1
      cases hP1
      simp [sszList_getElem!_val]
  simp only [Function.comp_apply, hP2, hb, hval, Bool.and_comm]

omit [HasherTag] [EthCLSpecs.Gloas.Config] hp in
theorem validatorEligible_eq (v : EthCLSpecs.Gloas.Validator) (E : UInt64) {b : Bool}
    (h : Spec.validatorEligible E.toNat (absValidator v) = .ok b) :
    b = (EthCLSpecs.Gloas.isActiveValidator v E ||
      v.slashed && decide (E + 1 < v.withdrawableEpoch)) := by
  unfold Spec.validatorEligible at h
  rw [is_active_validator_eq] at h
  by_cases ha : EthCLSpecs.Gloas.isActiveValidator v E = true
  · rw [if_pos ha] at h; cases h; simp [ha]
  · rw [if_neg ha] at h
    simp only [absValidator] at h
    by_cases hs : v.slashed = true
    · rw [if_pos hs] at h
      simp only [bind, Except.bind] at h
      cases hadd : Spec.uint64Add E.toNat 1 with
      | error err => rw [hadd] at h; cases h
      | ok n =>
        rw [hadd] at h
        have hn := uint64Add_ok (a := E) (b := 1) (by simpa using hadd)
        cases h
        simp [ha, hs, UInt64.lt_iff_toNat_lt, hn]
    · rw [if_neg hs] at h; cases h; simp [ha, hs]

/-- `get_eligible_validator_indices` equals Etheorem's. -/
theorem get_eligible_validator_indices_ok (e : EState) {l : List Nat}
    (h : Spec.get_eligible_validator_indices p (absEState e) = .ok l) :
    l = (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList.map UInt64.toNat := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  rw [Spec.get_eligible_validator_indices_eq p _ _ (get_previous_epoch_eq hp e)] at h
  obtain ⟨hQ, rfl⟩ := foldlM_filterStep_inv _ _ _ _ _ h
  unfold EthCLSpecs.Gloas.getEligibleValidatorIndices
  simp only [view_uncachedBox, SSZList.toArray]
  rw [indicesWhere_toList, List.map_map]
  simp only [List.nil_append, absEState_validators, SSZList.toList] at hQ ⊢
  rw [zipIdx_map_eq, List.filter_map, List.map_map]
  rw [zipIdx_map_eq] at hQ
  have hfilter : ∀ i ∈ List.range e.validators.val.size,
      ((okValue ∘ fun x => Spec.validatorEligible
        (UInt64.toNat (EthCLSpecs.Gloas.previousEpochOf (pureState e))) x.fst) ∘
          fun i => (absValidator e.validators.val[i]!, i)) i =
      (EthCLSpecs.Gloas.isActiveValidator e.validators.val[i]!
          (EthCLSpecs.Gloas.previousEpochOf (pureState e)) ||
        e.validators.val[i]!.slashed &&
          decide (EthCLSpecs.Gloas.previousEpochOf (pureState e) + 1 <
            e.validators.val[i]!.withdrawableEpoch)) := by
    intro i hi
    exact validatorEligible_eq _ _ (hQ _ (List.mem_map_of_mem hi))
  rw [List.filter_congr hfilter]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
  simp [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi' hsize)]

omit hp in
/-- `is_in_inactivity_leak` equals Etheorem's. Etheorem's subtraction wraps only where the
reference raises. -/
theorem is_in_inactivity_leak_ok (hpp : PassesPresetAgrees p) (e : EState) {b : Bool}
    (h : Spec.is_in_inactivity_leak p (absEState e) = .ok b) :
    b = EthCLSpecs.Gloas.isInInactivityLeak (pureState e) := by
  unfold Spec.is_in_inactivity_leak Spec.get_finality_delay at h
  rw [get_previous_epoch_eq hpp.toPresetAgrees] at h
  simp only [bind, Except.bind] at h
  cases hd : Spec.uint64Sub (EthCLSpecs.Gloas.previousEpochOf (pureState e)).toNat
      (absEState e).finalized_checkpoint.epoch with
  | error err => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    cases h
    have hd' := uint64Sub_ok (a := EthCLSpecs.Gloas.previousEpochOf (pureState e))
      (b := e.finalizedCheckpoint.epoch) hd
    unfold EthCLSpecs.Gloas.isInInactivityLeak EthCLSpecs.Gloas.getFinalityDelay
    simp only [view_uncachedBox]
    rw [← hpp.minEpochsToInactivityPenalty, ← hd']
    simp [UInt64.lt_iff_toNat_lt]

end WithPreset

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
theorem passesPresetAgrees_mainnet : PassesPresetAgrees Spec.Preset.mainnet where
  toPresetAgrees := presetAgrees_mainnet
  minEpochsToInactivityPenalty := rfl
  inactivityScoreBias := rfl
  inactivityScoreRecoveryRate := rfl
  inactivityPenaltyQuotientBellatrix := rfl
  epochsPerSlashingsVector := rfl
  proportionalSlashingMultiplierBellatrix := rfl
  slotsPerHistoricalRoot := rfl
  slotsPerEpochTwo := by decide
  epochsPerSlashingsVectorLt := by decide
  proportionalSlashingMultiplierLt := by decide
  effectiveBalanceIncrementEq := rfl
  baseRewardFactorEq := rfl
end

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
theorem passesPresetAgrees_minimal : PassesPresetAgrees Spec.Preset.minimal where
  toPresetAgrees := presetAgrees_minimal
  minEpochsToInactivityPenalty := rfl
  inactivityScoreBias := rfl
  inactivityScoreRecoveryRate := rfl
  inactivityPenaltyQuotientBellatrix := rfl
  epochsPerSlashingsVector := rfl
  proportionalSlashingMultiplierBellatrix := rfl
  slotsPerHistoricalRoot := rfl
  slotsPerEpochTwo := by decide
  epochsPerSlashingsVectorLt := by decide
  proportionalSlashingMultiplierLt := by decide
  effectiveBalanceIncrementEq := rfl
  baseRewardFactorEq := rfl
end

end EpochProofs.Etheorem
