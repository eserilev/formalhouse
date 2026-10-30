import EpochProofs.Etheorem.Slashings

/-!
# `process_rewards_and_penalties`: the reference equals Etheorem

The main theorem is `rewards_etheorem`. `flagDeltasE` and `inactPenE` are Etheorem's deltas on a
plain state. `flag_deltas_etheorem` and `inact_deltas_etheorem` prove them equal to the reference
deltas. `applyDeltas_run` runs one round of Etheorem's `applyDeltas` against the reference loop.

Etheorem computes rewards and penalties in `Nat` and writes `UInt64.ofNat` of the result. It sets
each entry, where the reference adds to a zero entry. The two agree because each eligible index
occurs once. Etheorem raises on an overflow of the products in the deltas, F5 (the
`effective_balance * inactivity_score` product) among them, and the reference raises on the same
products. Etheorem also computes `base_reward * weight` for an index where the reference does not.
`get_base_reward_small` shows that this product fits in `uint64` with the mainnet and minimal
increment and base reward factor.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Gloas

/-- A reference loop that succeeds simulates a fold. `Rel` sees the indices still to run. -/
theorem forIn_sim_spec {α β γ : Type} (body : α → β → Spec.SpecM (ForInStep β)) (g : α → γ → γ)
    (Rel : List α → β → γ → Prop)
    (hstep : ∀ a rest b c s, Rel (a :: rest) b c → body a b = .ok s →
      ∃ b', s = .yield b' ∧ Rel rest b' (g a c)) :
    ∀ (l : List α) (b : β) (c : γ) (r : β), Rel l b c → forIn l b body = .ok r →
      Rel [] r (l.foldl (fun c a => g a c) c) := by
  intro l
  induction l with
  | nil => intro b c r hr h; cases h; exact hr
  | cons a rest ih =>
    intro b c r hr h
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := bind_ok_inv h
    obtain ⟨b', rfl, hr'⟩ := hstep a rest b c s hr hs
    exact ih b' (g a c) r hr' h

/-- An Etheorem loop in `Except` whose steps all succeed is a fold. -/
theorem forIn_except_ok {ε α β : Type} (body : α → β → Except ε (ForInStep β)) (g : α → β → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, body a b = .ok (.yield (g a b))) →
      ∀ b, forIn l b body = .ok (l.foldl (fun b a => g a b) b) := by
  intro l
  induction l with
  | nil => intro _ b; rfl
  | cons a rest ih =>
    intro hb b
    rw [List.forIn_cons, hb a (by simp) b]
    exact ih (fun a' ha' b' => hb a' (by simp [ha']) b') _

theorem toList_set!_map (c : Array UInt64) (i : Nat) (v : UInt64) :
    (c.set! i v).toList.map UInt64.toNat = (c.toList.map UInt64.toNat).set i v.toNat := by
  simp [List.map_set]

theorem getElem!_set!_ne (c : Array UInt64) (i j : Nat) (v : UInt64) (h : j ≠ i) :
    (c.set! i v)[j]! = c[j]! := by
  simp [getElem!_def, Ne.symm h]

theorem replicate_getElem! (n k : Nat) : (Array.replicate n (0 : UInt64))[k]! = 0 := by
  rw [getElem!_def, Array.getElem?_replicate]; by_cases h : k < n <;> simp [h] <;> rfl

theorem size_set! (c : Array UInt64) (i : Nat) (v : UInt64) : (c.set! i v).size = c.size := by
  simp

theorem weight_eq (f : Nat) (hf : f < 3) {w : Nat}
    (h : Spec.listGet Spec.PARTICIPATION_FLAG_WEIGHTS f = .ok w) :
    w = EthCLSpecs.Gloas.Const.participationFlagWeights[f]! := by
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl <;>
    simp [Spec.listGet, Spec.PARTICIPATION_FLAG_WEIGHTS, Spec.TIMELY_SOURCE_WEIGHT,
      Spec.TIMELY_TARGET_WEIGHT, Spec.TIMELY_HEAD_WEIGHT, pure, Except.pure] at h <;>
    subst h <;> rfl

theorem uint64Add_ok_val {a b n : Nat} (h : Spec.uint64Add a b = .ok n) : n = a + b ∧ a + b < 2 ^ 64 := by
  unfold Spec.uint64Add at h; split at h
  · cases h; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
  · cases h

theorem uint64Mul_ok_lt {a b n : Nat} (h : Spec.uint64Mul a b = .ok n) : n = a * b ∧ a * b < 2 ^ 64 := by
  unfold Spec.uint64Mul at h; split at h
  · cases h; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
  · cases h

theorem uint64Div_ok_val {a b n : Nat} (h : Spec.uint64Div a b = .ok n) : n = a / b := by
  unfold Spec.uint64Div at h; split at h
  · cases h
  · cases h; rfl

variable [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config]

/-- Etheorem's `get_base_reward` for an index in range. -/
def baseRewardE (e : EtheoremState) (vi : UInt64) : Nat :=
  e.validators.val[vi.toNat]!.effectiveBalance.toNat / EthCLSpecs.Gloas.Const.effectiveBalanceIncrement *
    EthCLSpecs.Gloas.getBaseRewardPerIncrement (pureState e)

/-- One iteration of Etheorem's `get_flag_index_deltas` loop. The pair is
`(penalties, rewards)`, the order Etheorem keeps. -/
def flagStepE (e : EtheoremState) (f : Nat) (acc : MProd (Array UInt64) (Array UInt64)) (vi : UInt64) :
    MProd (Array UInt64) (Array UInt64) :=
  let unslashed := eUnslashed e f (EthCLSpecs.Gloas.previousEpochOf (pureState e))
  let weight := EthCLSpecs.Gloas.Const.participationFlagWeights[f]!
  let usi := (EthCLSpecs.Gloas.getTotalBalance (pureState e) unslashed).toNat /
    EthCLSpecs.Gloas.Const.effectiveBalanceIncrement
  let ai := (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat /
    EthCLSpecs.Gloas.Const.effectiveBalanceIncrement
  let br := baseRewardE e vi
  if unslashed.contains vi then
    if !EthCLSpecs.Gloas.isInInactivityLeak (pureState e) then
      ⟨acc.1, acc.2.set! vi.toNat
        (UInt64.ofNat (br * weight * usi / (ai * EthCLSpecs.Gloas.Const.weightDenominator)))⟩
    else acc
  else if f != EthCLSpecs.Gloas.Const.timelyHeadFlagIndex then
    ⟨acc.1.set! vi.toNat (UInt64.ofNat (br * weight / EthCLSpecs.Gloas.Const.weightDenominator)), acc.2⟩
  else acc

/-- Etheorem's `get_flag_index_deltas` as `(rewards, penalties)`. -/
def flagDeltasE (e : EtheoremState) (f : Nat) : Array UInt64 × Array UInt64 :=
  let r := (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList.foldl (flagStepE e f)
    ⟨Array.replicate e.validators.val.size 0, Array.replicate e.validators.val.size 0⟩
  (r.2, r.1)

variable {p : Spec.Preset} (hpp : PassesPresetAgrees p)
include hpp

theorem eligible_lt (e : EtheoremState) :
    ∀ i ∈ (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList,
      i.toNat < e.validators.val.size := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hpp.validatorRegistryLimit
  intro i hi
  unfold EthCLSpecs.Gloas.getEligibleValidatorIndices at hi
  rw [indicesWhere_toList] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have hj' := (List.mem_range.mp (List.mem_filter.mp hj).1)
  simp only [view_uncachedBox, SSZList.toArray] at hj'
  rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hj' hsize)]
  exact hj'

theorem get_base_reward_eq (e : EtheoremState) (a : Nat) (ha : a < e.validators.val.size) {br : Nat}
    (h : Spec.get_base_reward p (etheoremTotalActiveBalance e) (toSpecState e) a = .ok br) :
    br = baseRewardE e (UInt64.ofNat a) := by
  have hp := hpp.toPresetAgrees
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hsize)
  unfold Spec.get_base_reward at h
  obtain ⟨v, hv, h⟩ := bind_ok_inv h
  rw [toSpecState_validators] at hv
  obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator a hv
  obtain ⟨incs, hincs, h⟩ := bind_ok_inv h
  obtain ⟨brpi, hbrpi, h⟩ := bind_ok_inv h
  have hb := get_base_reward_per_increment_ok e hbrpi hp
  rw [uint64Div_ok_val hincs] at h
  obtain ⟨rfl, -⟩ := uint64Mul_ok_lt h
  unfold baseRewardE
  rw [haN, hb, hp.effectiveBalanceIncrement]
  rfl

omit hpp in
/-- Etheorem's unslashed participating indices of flag `f` at the previous epoch. -/
abbrev Eus (f : Nat) (e : EtheoremState) : Array UInt64 :=
  eUnslashed e f (EthCLSpecs.Gloas.previousEpochOf (pureState e))

theorem eligible_nodup (e : EtheoremState) :
    ((EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList.map UInt64.toNat).Nodup := by
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hpp.validatorRegistryLimit
  unfold EthCLSpecs.Gloas.getEligibleValidatorIndices
  rw [indicesWhere_toList, List.map_map]
  rw [List.map_congr_left (g := id) (fun i hi => by
    have := List.mem_range.mp (List.mem_filter.mp hi).1
    simp only [view_uncachedBox, SSZList.toArray] at this
    simp [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans this hsize)])]
  rw [List.map_id]
  exact List.Pairwise.filter _ List.nodup_range

omit hpp in
/-- Etheorem's `unslashed_participating_increments` for flag `f`. -/
abbrev usiE (f : Nat) (e : EtheoremState) : Nat :=
  (EthCLSpecs.Gloas.getTotalBalance (pureState e) (Eus f e)).toNat /
    EthCLSpecs.Gloas.Const.effectiveBalanceIncrement

/-- Etheorem's `get_flag_index_deltas` returns `flagDeltasE` when its products fit in `uint64`.
Etheorem computes `base_reward * weight` for every eligible index, and
`base_reward * weight * unslashed_participating_increments` where the reference does. -/
theorem getFlagIndexDeltas_eq (e : EtheoremState) (f : Nat)
    (hus : EthCLSpecs.Gloas.getUnslashedParticipatingIndices (pureState e) f
      (EthCLSpecs.Gloas.previousEpochOf (pureState e)) = .ok (Eus f e))
    (hw : EthCLSpecs.Gloas.Const.participationFlagWeights[f]! < 2 ^ 64)
    (hb : ∀ vi ∈ (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList,
      baseRewardE e vi < 2 ^ 64 ∧
      baseRewardE e vi * EthCLSpecs.Gloas.Const.participationFlagWeights[f]! < 2 ^ 64 ∧
      ((Eus f e).contains vi = true → (!EthCLSpecs.Gloas.isInInactivityLeak (pureState e)) = true →
        baseRewardE e vi * EthCLSpecs.Gloas.Const.participationFlagWeights[f]! * usiE f e <
          2 ^ 64)) :
    EthCLSpecs.Gloas.getFlagIndexDeltas (pureState e) f = .ok (flagDeltasE e f) := by
  unfold EthCLSpecs.Gloas.getFlagIndexDeltas
  simp only [view_uncachedBox]
  rw [hus, ok_bind, ← Array.forIn_toList, forIn_except_ok _ (fun vi acc => flagStepE e f acc vi)]
  · rfl
  · intro vi hvi acc
    have hlt := eligible_lt hpp e vi hvi
    obtain ⟨hbr, hbw, hbwu⟩ := hb vi hvi
    have hsome : e.validators.val[vi.toNat]? = some e.validators.val[vi.toNat]! := by
      rw [getElem!_pos e.validators.val _ hlt]; exact Array.getElem?_eq_getElem hlt
    have hgb : (liftErr (EthCLSpecs.Gloas.getBaseReward (pureState e) vi) :
        Except StateTransitionError Nat) = .ok (baseRewardE e vi) := by
      unfold EthCLSpecs.Gloas.getBaseReward
      simp only [view_uncachedBox, sszGetIdx, hsome, liftErr, MonadExcept.ofExcept,
        Except.mapError]
      rfl
    have hwN := UInt64.toNat_ofNat_of_lt' hw
    have hbrN := UInt64.toNat_ofNat_of_lt' hbr
    have hweighted : (UInt64.ofNat (baseRewardE e vi) *
        UInt64.ofNat EthCLSpecs.Gloas.Const.participationFlagWeights[f]!).toNat =
        baseRewardE e vi * EthCLSpecs.Gloas.Const.participationFlagWeights[f]! := by
      rw [UInt64.toNat_mul, hwN, hbrN, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hbw)]
    rw [hgb, ok_bind, checkedMul_of_lt _ _ _ (by rw [hbrN, hwN]; exact hbw)]
    simp only [pure, Except.pure, ok_bind]
    unfold flagStepE
    split
    · rename_i hin
      split
      · rename_i hl
        have husi : usiE f e < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt _)
        have hprod := hbwu hin hl
        rw [checkedMul_of_lt _ _ _ (by
          rw [hweighted, UInt64.toNat_ofNat_of_lt' husi]; exact hprod)]
        simp only [pure, Except.pure, ok_bind, hin, if_true]
        have hnum : (UInt64.ofNat (baseRewardE e vi) *
            UInt64.ofNat EthCLSpecs.Gloas.Const.participationFlagWeights[f]! *
            UInt64.ofNat (usiE f e)).toNat =
            baseRewardE e vi * EthCLSpecs.Gloas.Const.participationFlagWeights[f]! * usiE f e := by
          rw [UInt64.toNat_mul, hweighted, UInt64.toNat_ofNat_of_lt' husi,
            Nat.mod_eq_of_lt (by simpa [UInt64.size] using hprod)]
        rw [hnum]
      · simp only [hin, if_true]
    · rename_i hin
      split
      · simp only [hin, Bool.false_eq_true, if_false]
        rw [hweighted]
      · rename_i hh
        simp only [hin, Bool.false_eq_true, if_false]

/-- Etheorem's total active balance is at least one increment. -/
theorem inc_le_etheoremTotalActiveBalance (e : EtheoremState) :
    p.EFFECTIVE_BALANCE_INCREMENT ≤ etheoremTotalActiveBalance e := by
  have hp := hpp.toPresetAgrees
  unfold etheoremTotalActiveBalance EthCLSpecs.Gloas.getTotalActiveBalance
    EthCLSpecs.Gloas.getTotalBalance
  simp only [view_uncachedBox]
  rw [umax_toNat, hp.effectiveBalanceIncrementG]
  exact Nat.le_max_right _ _

/-- A reference base reward is at most `1 / 256` of the effective balance, so it fits in `uint64`
even after a multiplication by a flag weight. -/
theorem get_base_reward_small (e : EtheoremState) (a : Nat) {br : Nat}
    (h : Spec.get_base_reward p (etheoremTotalActiveBalance e) (toSpecState e) a = .ok br) :
    br * 26 < 2 ^ 64 := by
  unfold Spec.get_base_reward at h
  obtain ⟨v, hv, h⟩ := bind_ok_inv h
  rw [toSpecState_validators] at hv
  obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator a hv
  have h256 := Spec.rewardsBaseReward_bound p _ _ br hpp.effectiveBalanceIncrementEq
    hpp.baseRewardFactorEq (inc_le_etheoremTotalActiveBalance hpp e) h
  change 256 * br ≤ (e.validators.val[a]!).effectiveBalance.toNat at h256
  have heb := UInt64.toNat_lt (e.validators.val[a]!).effectiveBalance
  omega

omit hpp [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem participationFlagWeights_le (f : Nat) (hf : f < 3) :
    EthCLSpecs.Gloas.Const.participationFlagWeights[f]! ≤ 26 := by
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl <;> decide

/-- `get_flag_index_deltas` equals Etheorem's. -/
theorem flag_deltas_etheorem (e : EtheoremState) (f : Nat) (hf : f < 3) {R P : List Nat}
    (h : Spec.get_flag_index_deltas p (etheoremTotalActiveBalance e) (toSpecState e) f = .ok (R, P)) :
    EthCLSpecs.Gloas.getFlagIndexDeltas (pureState e) f = .ok (flagDeltasE e f) ∧
    R = (flagDeltasE e f).1.toList.map UInt64.toNat ∧
      P = (flagDeltasE e f).2.toList.map UInt64.toNat := by
  have hp := hpp.toPresetAgrees
  unfold Spec.get_flag_index_deltas at h
  rw [get_previous_epoch_eq hp] at h
  simp only [ok_bind] at h
  obtain ⟨usp, husp, h⟩ := bind_ok_inv h
  obtain ⟨w, hw, h⟩ := bind_ok_inv h
  obtain ⟨usb, husb, h⟩ := bind_ok_inv h
  obtain ⟨usi, husi, h⟩ := bind_ok_inv h
  obtain ⟨ai, hai, h⟩ := bind_ok_inv h
  obtain ⟨el, hel, h⟩ := bind_ok_inv h
  obtain ⟨r, hr, h⟩ := bind_ok_inv h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  -- The values the loop reads.
  have hel' := get_eligible_validator_indices_ok hp e hel
  obtain ⟨huspE, husp'⟩ := get_unslashed_participating_indices_ok hp e f hf _ husp
  rw [husp'] at husb
  have husb' := get_total_balance_ok hp e _ husb
  have hw' := weight_eq f hf hw
  have husi' := uint64Div_ok_val husi
  have hai' := uint64Div_ok_val hai
  -- The loop.
  let Rel : List Nat → MProd (List Nat) (List Nat) → MProd (Array UInt64) (Array UInt64) → Prop :=
    fun rest b c => b.fst = c.fst.toList.map UInt64.toNat ∧ b.snd = c.snd.toList.map UInt64.toNat ∧
      (∀ j ∈ rest, c.fst[j]! = 0 ∧ c.snd[j]! = 0 ∧ j < e.validators.val.size) ∧ rest.Nodup
  -- The products that Etheorem checks, read off the reference step of index `a`.
  let Good : Nat → Prop := fun a =>
    baseRewardE e (UInt64.ofNat a) * 26 < 2 ^ 64 ∧
    ((Eus f e).contains (UInt64.ofNat a) = true →
      (!EthCLSpecs.Gloas.isInInactivityLeak (pureState e)) = true →
      baseRewardE e (UInt64.ofNat a) * EthCLSpecs.Gloas.Const.participationFlagWeights[f]! *
        usiE f e < 2 ^ 64)
  let Rel' : List Nat → MProd (List Nat) (List Nat) → MProd (Array UInt64) (Array UInt64) →
      Prop := fun rest b c => Rel rest b c ∧ ∀ j ∈ el, j ∉ rest → Good j
  have hsim := forIn_sim_spec _ (fun (i : Nat) c => flagStepE e f c (UInt64.ofNat i)) Rel' ?_ el _
    ⟨Array.replicate e.validators.val.size 0, Array.replicate e.validators.val.size 0⟩ r ?_ hr
  · obtain ⟨⟨h1, h2, -, -⟩, hgood⟩ := hsim
    rw [hel', List.foldl_map] at h1 h2
    simp only [UInt64.ofNat_toNat] at h1 h2
    refine ⟨?_, h2, h1⟩
    have hw64 : EthCLSpecs.Gloas.Const.participationFlagWeights[f]! < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (participationFlagWeights_le f hf) (by decide)
    refine getFlagIndexDeltas_eq hpp e f huspE hw64 (fun vi hvi => ?_)
    have hG := hgood vi.toNat (by rw [hel']; exact List.mem_map_of_mem hvi) (by simp)
    simp only [Good, UInt64.ofNat_toNat] at hG
    obtain ⟨h26, hG2⟩ := hG
    have hwle := participationFlagWeights_le f hf
    refine ⟨by omega, Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hwle) h26, hG2⟩
  · intro a rest b c st hrel' hbody
    obtain ⟨hrel, hga⟩ := hrel'
    have hG : Good a := by
      obtain ⟨br, hbr, hbody⟩ := bind_ok_inv hbody
      have ha := (hrel.2.2.1 a (by simp)).2.2
      have hbr' := get_base_reward_eq hpp e a ha hbr
      have hsmall := get_base_reward_small hpp e a hbr
      rw [hbr'] at hsmall
      refine ⟨hsmall, fun hin hl => ?_⟩
      have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt'
        (Nat.lt_trans ha (Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit))
      have hin' : a ∈ usp := by
        rw [husp']
        have := (mem_map_toNat_iff _ _).mpr hin
        rwa [haN] at this
      rw [if_pos hin'] at hbody
      obtain ⟨lk, hlk, hbody⟩ := bind_ok_inv hbody
      have hlk' := is_in_inactivity_leak_ok hpp e hlk
      rw [if_pos (by rw [hlk']; exact hl)] at hbody
      obtain ⟨m1, hm1, hbody⟩ := bind_ok_inv hbody
      obtain ⟨rn, hrn, -⟩ := bind_ok_inv hbody
      obtain ⟨hm1v, -⟩ := uint64Mul_ok_lt hm1
      obtain ⟨-, hrnlt⟩ := uint64Mul_ok_lt hrn
      rw [hm1v, husi', hbr', hw', ← husb'] at hrnlt
      simpa [usiE, hp.effectiveBalanceIncrement] using hrnlt
    suffices H : ∃ b', st = .yield b' ∧ Rel rest b' (flagStepE e f c (UInt64.ofNat a)) by
      obtain ⟨b', h1, h2⟩ := H
      refine ⟨b', h1, h2, fun j hj hjr => ?_⟩
      by_cases hja : j = a
      · subst hja; exact hG
      · exact hga j hj (by simp [hja, hjr])
    obtain ⟨hb1, hb2, hz, hnd⟩ := hrel
    obtain ⟨hza1, hza2, ha⟩ := hz a (by simp)
    have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hsize)
    have hrest : ∀ j ∈ rest, j ≠ a := by
      intro j hj hja; subst hja; exact (List.nodup_cons.mp hnd).1 hj
    have hnd' := (List.nodup_cons.mp hnd).2
    have hmem : (a ∈ usp) = ((Eus f e).contains (UInt64.ofNat a) = true) := by
      rw [husp', ← mem_map_toNat_iff, haN]
    obtain ⟨br, hbr, hbody⟩ := bind_ok_inv hbody
    have hbr' := get_base_reward_eq hpp e a ha hbr
    unfold flagStepE
    by_cases hin : a ∈ usp
    · rw [if_pos hin] at hbody
      have hin' : (Eus f e).contains (UInt64.ofNat a) = true := hmem ▸ hin
      obtain ⟨lk, hlk, hbody⟩ := bind_ok_inv hbody
      have hlk' := is_in_inactivity_leak_ok hpp e hlk
      by_cases hl : (!lk) = true
      · rw [if_pos hl] at hbody
        obtain ⟨m1, hm1, hbody⟩ := bind_ok_inv hbody
        obtain ⟨rn, hrn, hbody⟩ := bind_ok_inv hbody
        obtain ⟨cur, hcur, hbody⟩ := bind_ok_inv hbody
        obtain ⟨m2, hm2, hbody⟩ := bind_ok_inv hbody
        obtain ⟨rw', hrw, hbody⟩ := bind_ok_inv hbody
        obtain ⟨sm, hsm, hbody⟩ := bind_ok_inv hbody
        obtain ⟨r1, hr1, hbody⟩ := bind_ok_inv hbody
        simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
        subst hbody
        refine ⟨_, rfl, ?_⟩
        rw [hb2] at hcur hr1
        obtain ⟨hlta, hcurv⟩ := listGet_map_ok c.snd UInt64.toNat a hcur
        rw [hza2] at hcurv
        obtain ⟨hm1v, -⟩ := uint64Mul_ok_lt hm1
        obtain ⟨hrnv, hrnlt⟩ := uint64Mul_ok_lt hrn
        obtain ⟨hm2v, -⟩ := uint64Mul_ok_lt hm2
        have hrwv := uint64Div_ok_val hrw
        obtain ⟨hsmv, -⟩ := uint64Add_ok_val hsm
        have hX : rw' = baseRewardE e (UInt64.ofNat a) *
            EthCLSpecs.Gloas.Const.participationFlagWeights[f]! *
            ((EthCLSpecs.Gloas.getTotalBalance (pureState e) (Eus f e)).toNat /
              EthCLSpecs.Gloas.Const.effectiveBalanceIncrement) /
            ((EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat /
              EthCLSpecs.Gloas.Const.effectiveBalanceIncrement *
              EthCLSpecs.Gloas.Const.weightDenominator) := by
          rw [hrwv, hrnv, hm1v, hm2v, husi', hai', hbr', hw', ← husb', hp.effectiveBalanceIncrement]
          rfl
        have hXlt : rw' < 2 ^ 64 := by rw [hrwv]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hrnv]; exact hrnlt)
        have hsm' : sm = rw' := by rw [hsmv, hcurv]; simp
        simp only [hin', hlk'.symm ▸ hl, if_true]
        refine ⟨hb1, ?_, ?_, hnd'⟩
        · unfold Spec.listSet at hr1
          rw [if_pos (by simpa using hlta)] at hr1
          cases hr1
          simp only
          rw [toList_set!_map, haN, ← hX, UInt64.toNat_ofNat_of_lt' hXlt, hsm']
        · intro j hj
          obtain ⟨z1, z2, hj'⟩ := hz j (by simp [hj])
          refine ⟨z1, ?_, hj'⟩
          rw [haN, getElem!_set!_ne _ _ _ _ (hrest j hj)]; exact z2
      · rw [if_neg hl] at hbody
        simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
        subst hbody
        refine ⟨_, rfl, ?_⟩
        simp only [hin', show (!EthCLSpecs.Gloas.isInInactivityLeak (pureState e)) = false by
          rw [← hlk']; simpa using hl, if_true, Bool.false_eq_true, if_false]
        exact ⟨hb1, hb2, fun j hj => hz j (by simp [hj]), hnd'⟩
    · rw [if_neg hin] at hbody
      have hin' : (Eus f e).contains (UInt64.ofNat a) = false := by
        have : ¬ ((Eus f e).contains (UInt64.ofNat a) = true) := hmem ▸ hin
        simpa using this
      have hhead : (f != Spec.TIMELY_HEAD_FLAG_INDEX) = (f != EthCLSpecs.Gloas.Const.timelyHeadFlagIndex) := rfl
      by_cases hh : (f != Spec.TIMELY_HEAD_FLAG_INDEX) = true
      · rw [if_pos hh] at hbody
        obtain ⟨cur, hcur, hbody⟩ := bind_ok_inv hbody
        obtain ⟨m1, hm1, hbody⟩ := bind_ok_inv hbody
        obtain ⟨pen, hpen, hbody⟩ := bind_ok_inv hbody
        obtain ⟨sm, hsm, hbody⟩ := bind_ok_inv hbody
        obtain ⟨r1, hr1, hbody⟩ := bind_ok_inv hbody
        simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
        subst hbody
        refine ⟨_, rfl, ?_⟩
        rw [hb1] at hcur hr1
        obtain ⟨hlta, hcurv⟩ := listGet_map_ok c.fst UInt64.toNat a hcur
        rw [hza1] at hcurv
        obtain ⟨hm1v, hm1lt⟩ := uint64Mul_ok_lt hm1
        have hpenv := uint64Div_ok_val hpen
        obtain ⟨hsmv, -⟩ := uint64Add_ok_val hsm
        have hX : pen = baseRewardE e (UInt64.ofNat a) *
            EthCLSpecs.Gloas.Const.participationFlagWeights[f]! /
            EthCLSpecs.Gloas.Const.weightDenominator := by
          rw [hpenv, hm1v, hbr', hw']; rfl
        have hXlt : pen < 2 ^ 64 := by rw [hpenv]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hm1v]; exact hm1lt)
        have hsm' : sm = pen := by rw [hsmv, hcurv]; simp
        simp only [hin', Bool.false_eq_true, if_false, ← hhead, hh, if_true]
        refine ⟨?_, hb2, ?_, hnd'⟩
        · unfold Spec.listSet at hr1
          rw [if_pos (by simpa using hlta)] at hr1
          cases hr1
          simp only
          rw [toList_set!_map, haN, ← hX, UInt64.toNat_ofNat_of_lt' hXlt, hsm']
        · intro j hj
          obtain ⟨z1, z2, hj'⟩ := hz j (by simp [hj])
          refine ⟨?_, z2, hj'⟩
          rw [haN, getElem!_set!_ne _ _ _ _ (hrest j hj)]; exact z1
      · rw [if_neg hh] at hbody
        simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
        subst hbody
        refine ⟨_, rfl, ?_⟩
        simp only [hin', Bool.false_eq_true, if_false, ← hhead, hh]
        exact ⟨hb1, hb2, fun j hj => hz j (by simp [hj]), hnd'⟩
  · refine ⟨⟨by simp [toSpecState_validators], by simp [toSpecState_validators], ?_, ?_⟩,
      fun j hj hjr => absurd hj hjr⟩
    · intro j hj
      rw [hel'] at hj
      obtain ⟨vi, hvi, rfl⟩ := List.mem_map.mp hj
      exact ⟨replicate_getElem! _ _, replicate_getElem! _ _, eligible_lt hpp e vi hvi⟩
    · rw [hel']
      exact eligible_nodup hpp e

omit hpp in
/-- One iteration of Etheorem's `get_inactivity_penalty_deltas` loop. -/
def inactPenStepE (e : EtheoremState) (acc : Array UInt64) (vi : UInt64) : Array UInt64 :=
  if !(Eus EthCLSpecs.Gloas.Const.timelyTargetFlagIndex e).contains vi then
    acc.set! vi.toNat (UInt64.ofNat (e.validators[vi.toNat]!.effectiveBalance.toNat *
      e.inactivityScores[vi.toNat]!.toNat /
      (EthCLSpecs.Gloas.Const.inactivityScoreBias.toNat *
        EthCLSpecs.Gloas.Const.inactivityPenaltyQuotientBellatrix)))
  else acc

omit hpp in
/-- Etheorem's `get_inactivity_penalty_deltas`. -/
def inactPenE (e : EtheoremState) : Array UInt64 :=
  (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList.foldl (inactPenStepE e)
    (Array.replicate e.validators.val.size 0)

omit hpp in
/-- Etheorem's `get_inactivity_penalty_deltas` returns `inactPenE` when each score it reads is in
bounds and each product `effective_balance * inactivity_scores[index]` fits in `uint64`. -/
theorem getInactivityPenaltyDeltas_eq (e : EtheoremState)
    (hmt : EthCLSpecs.Gloas.getUnslashedParticipatingIndices (pureState e)
      EthCLSpecs.Gloas.Const.timelyTargetFlagIndex (EthCLSpecs.Gloas.previousEpochOf (pureState e)) =
        .ok (Eus EthCLSpecs.Gloas.Const.timelyTargetFlagIndex e))
    (hb : ∀ vi ∈ (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList,
      (Eus EthCLSpecs.Gloas.Const.timelyTargetFlagIndex e).contains vi = false →
        vi.toNat < e.inactivityScores.val.size ∧
          e.validators[vi.toNat]!.effectiveBalance.toNat * e.inactivityScores[vi.toNat]!.toNat <
            2 ^ 64) :
    EthCLSpecs.Gloas.getInactivityPenaltyDeltas (pureState e) = .ok (inactPenE e) := by
  unfold EthCLSpecs.Gloas.getInactivityPenaltyDeltas inactPenE
  simp only [view_uncachedBox]
  rw [hmt, ok_bind, ← Array.forIn_toList, forIn_except_ok _ (fun vi acc => inactPenStepE e acc vi)]
  · rfl
  · intro vi hvi acc
    unfold inactPenStepE
    by_cases hin : (Eus EthCLSpecs.Gloas.Const.timelyTargetFlagIndex e).contains vi = true
    · simp only [hin, Bool.not_true, Bool.false_eq_true, if_false]
      rfl
    · have hin' : (Eus EthCLSpecs.Gloas.Const.timelyTargetFlagIndex e).contains vi = false := by
        simpa using hin
      obtain ⟨hlt, hmul⟩ := hb vi hvi hin'
      have hq : e.inactivityScores.val[vi.toNat]? = some e.inactivityScores[vi.toNat]! := by
        rw [sszList_getElem!_val, getElem!_pos e.inactivityScores.val _ hlt]
        exact Array.getElem?_eq_getElem hlt
      simp only [hin', Bool.not_false, if_true]
      simp only [sszGetIdx, hq, liftErr, MonadExcept.ofExcept, Except.mapError]
      simp only [pure, Except.pure, ok_bind]
      rw [checkedMul_of_lt _ _ _ hmul]
      simp only [pure, Except.pure, ok_bind]
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by simpa [UInt64.size] using hmul)]

/-- `get_inactivity_penalty_deltas` equals Etheorem's. -/
theorem inact_deltas_etheorem (e : EtheoremState) {R P : List Nat}
    (h : Spec.get_inactivity_penalty_deltas p (toSpecState e) = .ok (R, P)) :
    EthCLSpecs.Gloas.getInactivityPenaltyDeltas (pureState e) = .ok (inactPenE e) ∧
    R = List.replicate e.validators.val.size 0 ∧ P = (inactPenE e).toList.map UInt64.toNat := by
  have hp := hpp.toPresetAgrees
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  unfold Spec.get_inactivity_penalty_deltas at h
  rw [get_previous_epoch_eq hp] at h
  simp only [ok_bind] at h
  obtain ⟨mt, hmt, h⟩ := bind_ok_inv h
  obtain ⟨el, hel, h⟩ := bind_ok_inv h
  obtain ⟨r, hr, h⟩ := bind_ok_inv h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hel' := get_eligible_validator_indices_ok hp e hel
  obtain ⟨hmtE, hmt'⟩ := get_unslashed_participating_indices_ok hp e 1 (by decide) _ hmt
  let Rel : List Nat → List Nat → Array UInt64 → Prop :=
    fun rest b c => b = c.toList.map UInt64.toNat ∧
      (∀ j ∈ rest, c[j]! = 0 ∧ j < e.validators.val.size) ∧ rest.Nodup
  -- The score read and the product that Etheorem checks, read off the reference step of `a`.
  let Good : Nat → Prop := fun a =>
    (Eus 1 e).contains (UInt64.ofNat a) = false →
      (UInt64.ofNat a).toNat < e.inactivityScores.val.size ∧
        e.validators[(UInt64.ofNat a).toNat]!.effectiveBalance.toNat *
          e.inactivityScores[(UInt64.ofNat a).toNat]!.toNat < 2 ^ 64
  let Rel' : List Nat → List Nat → Array UInt64 → Prop :=
    fun rest b c => Rel rest b c ∧ ∀ j ∈ el, j ∉ rest → Good j
  have hsim := forIn_sim_spec _ (fun (i : Nat) c => inactPenStepE e c (UInt64.ofNat i)) Rel' ?_ el _
    (Array.replicate e.validators.val.size 0) r ?_ hr
  · obtain ⟨⟨h1, -, -⟩, hgood⟩ := hsim
    rw [hel', List.foldl_map] at h1
    simp only [UInt64.ofNat_toNat] at h1
    refine ⟨getInactivityPenaltyDeltas_eq e hmtE (fun vi hvi hin => ?_), by simp [toSpecState_validators], h1⟩
    have hG := hgood vi.toNat (by rw [hel']; exact List.mem_map_of_mem hvi) (by simp)
    simp only [Good, UInt64.ofNat_toNat] at hG
    exact hG hin
  · intro a rest b c st hrel' hbody
    obtain ⟨hrel, hga⟩ := hrel'
    have hG : Good a := by
      intro hin
      have ha := (hrel.2.1 a (by simp)).2
      have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hsize)
      rw [haN]
      have hin' : a ∉ mt := by
        rw [hmt']
        intro hm
        have := (mem_map_toNat_iff _ _).mp (by rwa [← haN] at hm)
        rw [this] at hin
        cases hin
      rw [if_pos hin'] at hbody
      obtain ⟨v, hv, hbody⟩ := bind_ok_inv hbody
      rw [toSpecState_validators] at hv
      obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator a hv
      obtain ⟨sc, hsc, hbody⟩ := bind_ok_inv hbody
      rw [toSpecState_inactivity_scores] at hsc
      obtain ⟨hlt, rfl⟩ := listGet_map_ok e.inactivityScores.val UInt64.toNat a hsc
      obtain ⟨num, hnum, -⟩ := bind_ok_inv hbody
      obtain ⟨-, hnumlt⟩ := uint64Mul_ok_lt hnum
      refine ⟨hlt, ?_⟩
      rw [sszList_getElem!_val, sszList_getElem!_val]
      exact hnumlt
    suffices H : ∃ b', st = .yield b' ∧ Rel rest b' (inactPenStepE e c (UInt64.ofNat a)) by
      obtain ⟨b', h1, h2⟩ := H
      refine ⟨b', h1, h2, fun j hj hjr => ?_⟩
      by_cases hja : j = a
      · subst hja; exact hG
      · exact hga j hj (by simp [hja, hjr])
    obtain ⟨hb, hz, hnd⟩ := hrel
    obtain ⟨hza, ha⟩ := hz a (by simp)
    have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hsize)
    have hrest : ∀ j ∈ rest, j ≠ a := by
      intro j hj hja; subst hja; exact (List.nodup_cons.mp hnd).1 hj
    have hnd' := (List.nodup_cons.mp hnd).2
    have hmem : (a ∈ mt) = ((Eus 1 e).contains (UInt64.ofNat a) = true) := by
      rw [hmt', ← mem_map_toNat_iff, haN]
    unfold inactPenStepE
    by_cases hin : a ∈ mt
    · have hin' : (Eus 1 e).contains (UInt64.ofNat a) = true := hmem ▸ hin
      rw [if_neg (fun h' => h' hin)] at hbody
      simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
      subst hbody
      refine ⟨_, rfl, ?_⟩
      simp only [hin', Bool.not_true, Bool.false_eq_true, if_false]
      exact ⟨hb, fun j hj => hz j (by simp [hj]), hnd'⟩
    · have hin' : (Eus 1 e).contains (UInt64.ofNat a) = false := by
        have : ¬ ((Eus 1 e).contains (UInt64.ofNat a) = true) := hmem ▸ hin
        simpa using this
      rw [if_pos hin] at hbody
      obtain ⟨v, hv, hbody⟩ := bind_ok_inv hbody
      rw [toSpecState_validators] at hv
      obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator a hv
      obtain ⟨sc, hsc, hbody⟩ := bind_ok_inv hbody
      rw [toSpecState_inactivity_scores] at hsc
      obtain ⟨-, rfl⟩ := listGet_map_ok e.inactivityScores.val UInt64.toNat a hsc
      obtain ⟨num, hnum, hbody⟩ := bind_ok_inv hbody
      obtain ⟨den, hden, hbody⟩ := bind_ok_inv hbody
      obtain ⟨cur, hcur, hbody⟩ := bind_ok_inv hbody
      obtain ⟨q, hq, hbody⟩ := bind_ok_inv hbody
      obtain ⟨sm, hsm, hbody⟩ := bind_ok_inv hbody
      obtain ⟨r1, hr1, hbody⟩ := bind_ok_inv hbody
      simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hbody
      subst hbody
      refine ⟨_, rfl, ?_⟩
      rw [hb] at hcur hr1
      obtain ⟨hlta, hcurv⟩ := listGet_map_ok c UInt64.toNat a hcur
      rw [hza] at hcurv
      obtain ⟨hnumv, hnumlt⟩ := uint64Mul_ok_lt hnum
      obtain ⟨hdenv, -⟩ := uint64Mul_ok_lt hden
      have hqv := uint64Div_ok_val hq
      obtain ⟨hsmv, -⟩ := uint64Add_ok_val hsm
      have hX : q = e.validators[a]!.effectiveBalance.toNat *
          e.inactivityScores[a]!.toNat /
          (EthCLSpecs.Gloas.Const.inactivityScoreBias.toNat *
            EthCLSpecs.Gloas.Const.inactivityPenaltyQuotientBellatrix) := by
        rw [hqv, hnumv, hdenv, hpp.inactivityScoreBias, hpp.inactivityPenaltyQuotientBellatrix,
          sszList_getElem!_val, sszList_getElem!_val]
        rfl
      have hXlt : q < 2 ^ 64 := by
        rw [hqv]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hnumv]; exact hnumlt)
      have hsm' : sm = q := by rw [hsmv, hcurv]; simp
      simp only [hin', Bool.not_false, if_true]
      refine ⟨?_, ?_, hnd'⟩
      · unfold Spec.listSet at hr1
        rw [if_pos (by simpa using hlta)] at hr1
        cases hr1
        rw [toList_set!_map, haN, ← hX, UInt64.toNat_ofNat_of_lt' hXlt, hsm']
      · intro j hj
        obtain ⟨z, hj'⟩ := hz j (by simp [hj])
        refine ⟨?_, hj'⟩
        rw [haN, getElem!_set!_ne _ _ _ _ (hrest j hj)]; exact z
  · refine ⟨⟨by simp [toSpecState_validators], ?_, ?_⟩, fun j hj hjr => absurd hj hjr⟩
    · intro j hj
      rw [hel'] at hj
      obtain ⟨vi, hvi, rfl⟩ := List.mem_map.mp hj
      exact ⟨replicate_getElem! _ _, eligible_lt hpp e vi hvi⟩
    · rw [hel']
      exact eligible_nodup hpp e

omit hpp [EthCLSpecs.Gloas.Config] in
/-- A monadic loop over plain states runs as a fold. `I` sees the indices still to run. -/
theorem forIn_run_pureState' {α : Type} (s0 : EthCLSpecs.Gloas.State) (G : α → EtheoremState → EtheoremState)
    (I : List α → EtheoremState → Prop)
    (body : α → EthCLSpecs.Gloas.State → GloasRun (ForInStep EthCLSpecs.Gloas.State))
    (hI : ∀ a rest w, I (a :: rest) w → I rest (G a w))
    (hb : ∀ a rest w, I (a :: rest) w →
      (body a (pureState w)).run s0 = .ok (ForInStep.yield (pureState (G a w)), s0)) :
    ∀ (l : List α) (v : EtheoremState), I l v →
      (forIn l (pureState v) body).run s0 = .ok (pureState (l.foldl (fun w a => G a w) v), s0) ∧
        I [] (l.foldl (fun w a => G a w) v) := by
  intro l
  induction l with
  | nil => intro v hv; exact ⟨rfl, hv⟩
  | cons a l ih =>
    intro v hv
    rw [List.forIn_cons, run_bind, hb a l v hv, except_bind_ok]
    exact ih _ (hI a l v hv)

omit hpp in
/-- One iteration of Etheorem's `applyDeltas`. -/
def applyStepE (rew pen : Array UInt64) (w : EtheoremState) (i : Nat) : EtheoremState :=
  let k := (UInt64.ofNat i).toNat
  let b := w.balances.val[k]! + rew[i]!
  { w with balances := (w.balances.set! k b).set! k (decreasedE b pen[i]!) }

omit hpp [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem foldl_applyStepE (rew pen : Array UInt64) : ∀ (l : List Nat) (w : EtheoremState),
    l.foldl (fun w a => applyStepE rew pen w a) w =
      { w with balances := (l.foldl (fun w a => applyStepE rew pen w a) w).balances } := by
  intro l
  induction l with
  | nil => intro w; rfl
  | cons i l ih => intro w; rw [List.foldl_cons, ih]; rfl

omit hpp [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem getElem?_map_toNat (xs : Array UInt64) (i : Nat) {v : Nat}
    (h : (xs.toList.map UInt64.toNat)[i]? = some v) : v = (xs[i]!).toNat := by
  have hlt : i < xs.size := by
    have := (List.getElem?_eq_some_iff.mp h).1; simpa using this
  rw [getElem!_pos xs i hlt]
  simp [hlt] at h
  exact h.symm

omit hpp [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem decreasedE_toNat (b d : UInt64) :
    (decreasedE b d).toNat = Spec.saturating_sub b.toNat d.toNat := by
  unfold decreasedE Spec.saturating_sub
  by_cases h : d > b
  · have h' : b.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
    rw [if_pos h, if_neg (show ¬ (d.toNat < b.toNat) by omega)]; simp
  · rw [if_neg h]
    have h' : d.toNat ≤ b.toNat := by rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at h; omega
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h')]
    by_cases h2 : b.toNat > d.toNat
    · rw [if_pos h2]
    · have h2' : ¬ d.toNat < b.toNat := h2
      rw [if_neg h2]; omega

omit hpp [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem applyStep_balances (rew pen : Array UInt64) (w : EtheoremState) (a : Nat) {n : Nat} (ha : a < n)
    (hn : n < 2 ^ 64) {v : Nat} (hlt : a < (w.balances.toList.map UInt64.toNat).length)
    (hget : (w.balances.toList.map UInt64.toNat)[a]? = some v) (hfit : v + rew[a]!.toNat < 2 ^ 64) :
    (applyStepE rew pen w a).balances.toList.map UInt64.toNat =
      ((w.balances.toList.map UInt64.toNat).set a (v + rew[a]!.toNat)).set a
        (Spec.saturating_sub (v + rew[a]!.toNat) pen[a]!.toNat) := by
  have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hn)
  have hlt' : a < w.balances.val.size := by simpa using hlt
  have hv' := getElem?_map_toNat w.balances.val a hget
  have hsum : (w.balances.val[a]! + rew[a]!).toNat = v + rew[a]!.toNat := by
    rw [UInt64.toNat_add, hv', Nat.mod_eq_of_lt (by rw [← hv']; exact hfit)]
  unfold applyStepE
  simp only [haN, map_toList_set!]
  rw [decreasedE_toNat, hsum]

omit hpp [EthCLSpecs.Gloas.Config] in
theorem applyDeltas_run (s0 : EthCLSpecs.Gloas.State) (w0 : EtheoremState) (rew pen : Array UInt64)
    (bodyS : Nat → List Nat → Spec.SpecM (ForInStep (List Nat)))
    (hbody : ∀ i B s, bodyS i B = .ok s → ∃ v, i < B.length ∧ B[i]? = some v ∧
      v + rew[i]!.toNat < 2 ^ 64 ∧
      s = .yield ((B.set i (v + rew[i]!.toNat)).set i
        (Spec.saturating_sub (v + rew[i]!.toNat) pen[i]!.toNat)))
    (hn : w0.validators.val.size < 2 ^ 64) {R : List Nat}
    (hS : forIn (List.range w0.validators.val.size) (w0.balances.toList.map UInt64.toNat) bodyS =
      .ok R) :
    (EthCLSpecs.Gloas.applyDeltas (StateTransition := GloasRun) rew pen (pureState w0)).run s0 =
      .ok (pureState ((List.range' 0 w0.validators.val.size).foldl
        (fun w a => applyStepE rew pen w a) w0), s0) ∧
      R = ((List.range' 0 w0.validators.val.size).foldl
        (fun w a => applyStepE rew pen w a) w0).balances.toList.map UInt64.toNat := by
  let I : List Nat → EtheoremState → Prop := fun rest w =>
    w.validators = w0.validators ∧ (∀ i ∈ rest, i < w0.validators.val.size) ∧
      forIn rest (w.balances.toList.map UInt64.toNat) bodyS = .ok R
  have key := forIn_run_pureState' s0 (fun a w => applyStepE rew pen w a) I
    (fun i r => do
      let r ← EthCLSpecs.Gloas.increaseBalance (StateTransition := GloasRun) r (UInt64.ofNat i) rew[i]!
      let r ← EthCLSpecs.Gloas.decreaseBalance (StateTransition := GloasRun) r (UInt64.ofNat i) pen[i]!
      pure PUnit.unit
      pure (ForInStep.yield r)) ?_ ?_ (List.range' 0 w0.validators.val.size) w0
    ⟨rfl, fun i hi => by simpa using hi, by rw [← List.range_eq_range']; exact hS⟩
  · obtain ⟨hrun, hI⟩ := key
    refine ⟨?_, ?_⟩
    · unfold EthCLSpecs.Gloas.applyDeltas
      rw [run_bind, Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [view_uncachedBox, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
        Nat.div_one]
      rw [hrun]
      rfl
    · obtain ⟨-, -, h⟩ := hI
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
  · intro a rest w ⟨hv, hl, h⟩
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_ok_inv h
    obtain ⟨v, hlt, hget, hfit, rfl⟩ := hbody a _ st hst
    refine ⟨?_, fun i hi => hl i (by simp [hi]), ?_⟩
    · unfold applyStepE; exact hv
    · simp only at h
      rw [applyStep_balances rew pen w a (hl a (by simp)) hn hlt hget hfit]
      exact h
  · intro a rest w ⟨hv, hl, h⟩
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, -⟩ := bind_ok_inv h
    obtain ⟨v, hlt, hget, hfit, -⟩ := hbody a _ st hst
    have ha : a < w0.validators.val.size := hl a (by simp)
    have haN : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans ha hn)
    have hlt' : a < w.balances.val.size := by simpa using hlt
    have hv' := getElem?_map_toNat w.balances.val a hget
    have hfit' : (w.balances.val[(UInt64.ofNat a).toNat]!).toNat + (rew[a]!).toNat < 2 ^ 64 := by
      rw [haN, ← hv']; exact hfit
    have hsome : w.balances.val[(UInt64.ofNat a).toNat]? =
        some w.balances.val[(UInt64.ofNat a).toNat]! := by
      rw [haN, getElem!_pos w.balances.val a hlt']; exact Array.getElem?_eq_getElem hlt'
    simp only [run_bind]
    unfold EthCLSpecs.Gloas.increaseBalance
    rw [run_bind, view_uncachedBox, run_sszGetIdx_some _ _ _ hsome, except_bind_ok, run_bind,
      checkedAdd_run_ok _ _ _ _ hfit', except_bind_ok]
    simp only [run_pure, except_bind_ok]
    unfold EthCLSpecs.Gloas.decreaseBalance
    have hsome2 : (w.balances.set! (UInt64.ofNat a).toNat
        (w.balances.val[(UInt64.ofNat a).toNat]! + rew[a]!)).val[
        (UInt64.ofNat a).toNat]? = some (w.balances.val[(UInt64.ofNat a).toNat]! + rew[a]!) := by
      simp [haN, hlt']
    rw [run_bind]
    erw [run_sszGetIdx_some _ _ _ hsome2]
    rw [except_bind_ok]
    unfold applyStepE
    rfl

omit hpp [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem inner_body_spec (rew pen : Array UInt64) (i : Nat) (B : List Nat) (s : ForInStep (List Nat))
    (h : (do
      let a ← Spec.listGet (rew.toList.map UInt64.toNat) i
      let r ← Spec.increase_balance B i a
      let b ← Spec.listGet (pen.toList.map UInt64.toNat) i
      let r ← Spec.decrease_balance r i b
      pure PUnit.unit
      pure (ForInStep.yield r) : Spec.SpecM _) = .ok s) :
    ∃ v, i < B.length ∧ B[i]? = some v ∧ v + rew[i]!.toNat < 2 ^ 64 ∧
      s = .yield ((B.set i (v + rew[i]!.toNat)).set i
        (Spec.saturating_sub (v + rew[i]!.toNat) pen[i]!.toNat)) := by
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  obtain ⟨-, rfl⟩ := listGet_map_ok rew UInt64.toNat i ha
  obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
  obtain ⟨b, hb, h⟩ := bind_ok_inv h
  obtain ⟨-, rfl⟩ := listGet_map_ok pen UInt64.toNat i hb
  obtain ⟨r2, hr2, h⟩ := bind_ok_inv h
  simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at h
  subst h
  unfold Spec.increase_balance at hr1
  obtain ⟨v, hv, hr1⟩ := bind_ok_inv hr1
  obtain ⟨sm, hsm, hr1⟩ := bind_ok_inv hr1
  obtain ⟨rfl, hfit⟩ := uint64Add_ok_val hsm
  have hlt : i < B.length := by
    unfold Spec.listGet at hv; split at hv
    · rename_i x hx; exact (List.getElem?_eq_some_iff.mp hx).1
    · cases hv
  have hgv : B[i]? = some v := by
    unfold Spec.listGet at hv; split at hv
    · rename_i x hx; cases hv; exact hx
    · cases hv
  unfold Spec.listSet at hr1
  rw [if_pos hlt] at hr1
  cases hr1
  unfold Spec.decrease_balance at hr2
  obtain ⟨v2, hv2, hr2⟩ := bind_ok_inv hr2
  have hv2' : v2 = v + rew[i]!.toNat := by
    simp [Spec.listGet, hlt, pure, Except.pure] at hv2; exact hv2.symm
  subst hv2'
  unfold Spec.listSet at hr2
  rw [if_pos (by simpa using hlt)] at hr2
  cases hr2
  exact ⟨v, hlt, hgv, hfit, rfl⟩

omit hpp [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
theorem mapM_three {α : Type} (f : Nat → Spec.SpecM α) {l : List α}
    (h : (List.range 3).mapM f = .ok l) :
    ∃ a b c, f 0 = .ok a ∧ f 1 = .ok b ∧ f 2 = .ok c ∧ l = [a, b, c] := by
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr] at h
  simp only [List.mapM_cons, List.mapM_nil] at h
  obtain ⟨a, ha, h⟩ := bind_ok_inv h
  obtain ⟨t, ht, h⟩ := bind_ok_inv h
  obtain ⟨b, hb, ht⟩ := bind_ok_inv ht
  obtain ⟨t2, ht2, ht⟩ := bind_ok_inv ht
  obtain ⟨c, hc, ht2⟩ := bind_ok_inv ht2
  obtain ⟨t3, ht3, ht2⟩ := bind_ok_inv ht2
  simp only [pure, Except.pure, Except.ok.injEq] at h ht ht2 ht3
  subst ht3 ht2 ht h
  exact ⟨a, b, c, ha, hb, hc, rfl⟩

/-- `process_rewards_and_penalties` equals Etheorem's. -/
theorem rewards_etheorem (e : EtheoremState) {s' : Spec.BeaconState}
    (h : Spec.process_rewards_and_penalties p (etheoremTotalActiveBalance e) (toSpecState e) =
      .ok s') :
    ∃ e' : EtheoremState,
      (EthCLSpecs.Gloas.processRewardsAndPenalties (StateTransition := GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ s' = toSpecState e' := by
  have hp := hpp.toPresetAgrees
  unfold Spec.process_rewards_and_penalties at h
  rw [get_current_epoch_eq hp] at h
  simp only [ok_bind] at h
  have hsize : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  unfold EthCLSpecs.Gloas.processRewardsAndPenalties
  rw [run_bind, show (get : GloasRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  by_cases hg : (EthCLSpecs.Gloas.currentEpochOf (pureState e) ==
      EthCLSpecs.Gloas.Const.genesisEpoch) = true
  · have hg' : ((EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) = true := by
      simp only [beq_iff_eq] at hg ⊢; rw [hg]; rfl
    rw [if_pos hg'] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨e, by rw [if_pos hg]; rfl, rfl⟩
  · have hg' : ((EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h0; apply hg; simp only [beq_iff_eq]
      exact UInt64.toNat_inj.mp h0
    rw [if_neg (by simp [hg'])] at h
    rw [if_neg hg]
    obtain ⟨_, -, h⟩ := bind_ok_inv h
    obtain ⟨fd, hfd, h⟩ := bind_ok_inv h
    obtain ⟨idl, hid, h⟩ := bind_ok_inv h
    obtain ⟨r, hr, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨d0, d1, d2, h0, h1, h2, rfl⟩ := mapM_three _ hfd
    obtain ⟨hE0, hd0r, hd0p⟩ := flag_deltas_etheorem hpp e 0 (by decide) (R := d0.1) (P := d0.2) h0
    obtain ⟨hE1, hd1r, hd1p⟩ := flag_deltas_etheorem hpp e 1 (by decide) (R := d1.1) (P := d1.2) h1
    obtain ⟨hE2, hd2r, hd2p⟩ := flag_deltas_etheorem hpp e 2 (by decide) (R := d2.1) (P := d2.2) h2
    obtain ⟨hEi, hdir, hdip⟩ := inact_deltas_etheorem hpp e (R := idl.1) (P := idl.2) hid
    simp only [List.cons_append, List.nil_append, List.forIn_cons, List.forIn_nil] at hr
    have hlen : (toSpecState e).validators.length = e.validators.val.size := by simp
    rw [hlen] at hr
    -- Peel the four applications.
    obtain ⟨st0, hst0, hr⟩ := bind_ok_inv hr
    obtain ⟨r0, hr0, hst0⟩ := bind_ok_inv hst0
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hst0
    subst hst0
    simp only [] at hr
    obtain ⟨st1, hst1, hr⟩ := bind_ok_inv hr
    obtain ⟨r1, hr1, hst1⟩ := bind_ok_inv hst1
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hst1
    subst hst1
    simp only [] at hr
    obtain ⟨st2, hst2, hr⟩ := bind_ok_inv hr
    obtain ⟨r2, hr2, hst2⟩ := bind_ok_inv hst2
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hst2
    subst hst2
    simp only [] at hr
    obtain ⟨st3, hst3, hr⟩ := bind_ok_inv hr
    obtain ⟨r3, hr3, hst3⟩ := bind_ok_inv hst3
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at hst3
    subst hst3
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    rw [hd0r, hd0p] at hr0
    rw [hd1r, hd1p] at hr1
    rw [hd2r, hd2p] at hr2
    rw [hdir, hdip] at hr3
    rw [show List.replicate e.validators.val.size 0 =
      (Array.replicate e.validators.val.size (0 : UInt64)).toList.map UInt64.toNat by simp] at hr3
    have step := fun (w : EtheoremState) (rew pen : Array UInt64) =>
      applyDeltas_run (pureState w) w rew pen _ (fun i B s hs => inner_body_spec rew pen i B s hs)
    obtain ⟨hrun0, hR0⟩ := step e _ _ hsize hr0
    generalize hW1 : (List.range' 0 e.validators.val.size).foldl
      (fun w a => applyStepE (flagDeltasE e 0).1 (flagDeltasE e 0).2 w a) e = W1 at hrun0 hR0
    have hv1 : W1.validators = e.validators := by rw [← hW1, foldl_applyStepE]
    subst hR0
    rw [← hv1] at hr1
    obtain ⟨hrun1, hR1⟩ := step W1 _ _ (by rw [hv1]; exact hsize) hr1
    generalize hW2 : (List.range' 0 W1.validators.val.size).foldl
      (fun w a => applyStepE (flagDeltasE e 1).1 (flagDeltasE e 1).2 w a) W1 = W2 at hrun1 hR1
    have hv2 : W2.validators = e.validators := by rw [← hW2, foldl_applyStepE]; exact hv1
    subst hR1
    rw [← hv2] at hr2
    obtain ⟨hrun2, hR2⟩ := step W2 _ _ (by rw [hv2]; exact hsize) hr2
    generalize hW3 : (List.range' 0 W2.validators.val.size).foldl
      (fun w a => applyStepE (flagDeltasE e 2).1 (flagDeltasE e 2).2 w a) W2 = W3 at hrun2 hR2
    have hv3 : W3.validators = e.validators := by rw [← hW3, foldl_applyStepE]; exact hv2
    subst hR2
    rw [← hv3] at hr3
    obtain ⟨hrun3, hR3⟩ := step W3 _ _ (by rw [hv3]; exact hsize) hr3
    rw [hv3] at hrun3 hR3
    generalize hW4 : (List.range' 0 e.validators.val.size).foldl
      (fun w a => applyStepE (Array.replicate e.validators.val.size 0) (inactPenE e) w a) W3 = W4
      at hrun3 hR3
    have hv4 : W4.validators = e.validators := by rw [← hW4, foldl_applyStepE]; exact hv3
    subst hR3
    refine ⟨W4, ?_, ?_⟩
    · have hmap : (List.range 3).mapM (fun f => EthCLSpecs.Gloas.getFlagIndexDeltas (pureState e) f) =
          .ok [flagDeltasE e 0, flagDeltasE e 1, flagDeltasE e 2] := by
        simp only [show List.range 3 = [0, 1, 2] from rfl, List.mapM_cons, List.mapM_nil,
          hE0, hE1, hE2]
        rfl
      have hget : ∀ w : EtheoremState, (get : GloasRun _).run (pureState w) = .ok (pureState w, pureState w) :=
        fun _ => rfl
      have hset : ∀ (x y : EthCLSpecs.Gloas.State), (set x : GloasRun PUnit).run y = .ok ((), x) :=
        fun _ _ => rfl
      rw [run_bind, run_liftErr_of_ok _ _ (by rw [hmap]; rfl), except_bind_ok]
      dsimp only
      rw [run_bind, run_liftErr_of_ok _ _ (by rw [hEi]; rfl), except_bind_ok]
      simp only [List.forIn_cons, List.forIn_nil, run_bind, hget, except_bind_ok, hrun0, hrun1, hrun2,
        hset, run_pure, view_uncachedBox]
      rw [show e.validators.size = e.validators.val.size from rfl, hrun3]
      rfl
    · have h4 : W4 = { W3 with balances := W4.balances } := by rw [← hW4]; exact foldl_applyStepE _ _ _ _
      have h3 : W3 = { W2 with balances := W3.balances } := by rw [← hW3]; exact foldl_applyStepE _ _ _ _
      have h2 : W2 = { W1 with balances := W2.balances } := by rw [← hW2]; exact foldl_applyStepE _ _ _ _
      have h1 : W1 = { e with balances := W1.balances } := by rw [← hW1]; exact foldl_applyStepE _ _ _ _
      rw [h4, toSpecState_set_balances, h3, toSpecState_set_balances, h2, toSpecState_set_balances, h1,
        toSpecState_set_balances]
      rfl

end forkproof

