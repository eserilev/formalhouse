import EpochProofs.Etheorem.Fulu.Participation

/-!
# `process_inactivity_updates`: the reference equals Etheorem

The main theorem is `inactivity_updates_etheorem`. `inactivityUpdatesE` is Etheorem's step on a
plain state, and `processInactivityUpdates_run` proves that Etheorem's run gives it.

Etheorem's `score + INACTIVITY_SCORE_BIAS` wraps where the reference raises.
-/

namespace EpochProofs.Etheorem.Fulu
open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Fulu

variable [EthCLSpecs.Fulu.Preset] [HasherTag]

variable [EthCLSpecs.Fulu.Config]

/-- One inactivity score in Etheorem. -/
def inactivityScoreE (matchingTarget : Array UInt64) (leak : Bool) (vi cur : UInt64) : UInt64 :=
  let cur := if matchingTarget.contains vi then cur - umin 1 cur
    else cur + EthCLSpecs.Fulu.Const.inactivityScoreBias
  if !leak then cur - umin EthCLSpecs.Fulu.Const.inactivityScoreRecoveryRate cur else cur

/-- Etheorem's loop over the eligible indices, on the scores alone. -/
def inactivityScoresE (matchingTarget : Array UInt64) (leak : Bool) (l : List UInt64)
    (s : SSZList UInt64 EthCLSpecs.Fulu.Const.validatorRegistryLimit) :
    SSZList UInt64 EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
  l.foldl (fun s vi => s.set! vi.toNat (inactivityScoreE matchingTarget leak vi s[vi.toNat]!)) s

/-- One iteration of Etheorem's inactivity loop. -/
def inactivityStepE (mt : Array UInt64) (leak : Bool) (w : EState) (vi : UInt64) : EState :=
  { w with inactivityScores :=
      w.inactivityScores.set! vi.toNat (inactivityScoreE mt leak vi w.inactivityScores[vi.toNat]!) }

omit [HasherTag] in
theorem foldl_inactivityStepE (mt : Array UInt64) (leak : Bool) : ∀ (l : List UInt64) (w : EState),
    l.foldl (fun w a => inactivityStepE mt leak w a) w =
      { w with inactivityScores := inactivityScoresE mt leak l w.inactivityScores } := by
  intro l
  induction l with
  | nil => intro w; rfl
  | cons a l ih => intro w; rw [List.foldl_cons, ih]; rfl

/-- The state after Etheorem's `process_inactivity_updates`. -/
def inactivityUpdatesE (e : EState) : EState :=
  if EthCLSpecs.Fulu.currentEpochOf (pureState e) == EthCLSpecs.Fulu.Const.genesisEpoch then e
  else
    let mt := EthCLSpecs.Fulu.getUnslashedParticipatingIndices (pureState e)
      EthCLSpecs.Fulu.Const.timelyTargetFlagIndex (EthCLSpecs.Fulu.previousEpochOf (pureState e))
    let leak := EthCLSpecs.Fulu.isInInactivityLeak (pureState e)
    let eligible := (EthCLSpecs.Fulu.getEligibleValidatorIndices (pureState e)).toList
    { e with inactivityScores := inactivityScoresE mt leak eligible e.inactivityScores }

theorem processInactivityUpdates_run (e : EState) :
    (EthCLSpecs.Fulu.processInactivityUpdates (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState (inactivityUpdatesE e)) := by
  unfold EthCLSpecs.Fulu.processInactivityUpdates inactivityUpdatesE
  rw [run_bind, show (get : FuluRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  by_cases h : (EthCLSpecs.Fulu.currentEpochOf (pureState e) == EthCLSpecs.Fulu.Const.genesisEpoch) = true
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]
    unfold EthCLSpecs.Fulu.modifyState
    simp only [modifyThe, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
    rw [← Array.forIn_toList, forIn_pureState (fun vi w => inactivityStepE
        (EthCLSpecs.Fulu.getUnslashedParticipatingIndices (pureState e)
          EthCLSpecs.Fulu.Const.timelyTargetFlagIndex (EthCLSpecs.Fulu.previousEpochOf (pureState e)))
        (EthCLSpecs.Fulu.isInInactivityLeak (pureState e)) w vi)
      _ (fun a w => rfl)]
    rw [foldl_inactivityStepE]
    rfl

omit [EthCLSpecs.Fulu.Preset] [HasherTag] [EthCLSpecs.Fulu.Config] in
theorem saturating_sub_umin (x y : UInt64) :
    (x - umin y x).toNat = Spec.saturating_sub x.toNat y.toNat := by
  have hle : umin y x ≤ x := by rw [UInt64.le_iff_toNat_le, umin_toNat]; omega
  rw [UInt64.toNat_sub_of_le _ _ hle, umin_toNat]
  unfold Spec.saturating_sub
  split
  · rename_i hgt
    have hgt' : y.toNat < x.toNat := hgt
    rw [Nat.min_eq_left (by omega)]
  · rename_i hgt
    have hgt' : ¬ y.toNat < x.toNat := hgt
    rw [Nat.min_eq_right (by omega)]

section Inactivity

variable {p : Spec.Preset} (hpp : PassesPresetAgrees p)
include hpp

omit [HasherTag] in
theorem inactivityScoreStep_ok (mt : Array UInt64) (leak : Bool) (vi cur : UInt64) {n : Nat}
    (h : Spec.inactivityScoreStep p (decide (vi.toNat ∈ mt.toList.map UInt64.toNat)) leak cur.toNat =
      .ok n) :
    n = (inactivityScoreE mt leak vi cur).toNat := by
  unfold Spec.inactivityScoreStep at h
  unfold inactivityScoreE
  simp only [bind, Except.bind] at h
  by_cases hm : mt.contains vi = true
  · have hm' : decide (vi.toNat ∈ mt.toList.map UInt64.toNat) = true := by
      simpa [mem_map_toNat_iff] using hm
    rw [hm'] at h
    simp only [if_true, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [hm]
    cases leak
    · simp only [Bool.not_false, if_true, if_false, Bool.false_eq_true]
      rw [saturating_sub_umin, saturating_sub_umin, hpp.inactivityScoreRecoveryRate, h1]
    · simp only [Bool.not_true, if_true, if_false, Bool.false_eq_true]
      rw [saturating_sub_umin, h1]
  · have hm' : decide (vi.toNat ∈ mt.toList.map UInt64.toNat) = false := by
      simpa [mem_map_toNat_iff] using hm
    rw [hm'] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases hadd : Spec.uint64Add cur.toNat p.INACTIVITY_SCORE_BIAS with
    | error err => rw [hadd] at h; cases h
    | ok m =>
      rw [hadd] at h
      rw [← hpp.inactivityScoreBias] at hadd
      have hm2 := uint64Add_ok hadd
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [hm, Bool.false_eq_true, if_false]
      cases leak
      · simp only [Bool.not_false, if_true]
        rw [saturating_sub_umin, hpp.inactivityScoreRecoveryRate, hm2]
        simp
      · simp [hm2]

omit [HasherTag] in
theorem inactivity_fold (mt : Array UInt64) (leak : Bool) :
    ∀ (l : List UInt64) (S : SSZList UInt64 EthCLSpecs.Fulu.Const.validatorRegistryLimit)
      {R : List Nat},
      (l.map UInt64.toNat).foldlM (Spec.inactivityLoopStep p (mt.toList.map UInt64.toNat) leak)
        (S.toList.map UInt64.toNat) = .ok R →
      R = (inactivityScoresE mt leak l S).toList.map UInt64.toNat := by
  intro l
  induction l with
  | nil => intro S R h; simp only [List.map_nil, List.foldlM_nil, pure, Except.pure] at h; cases h; rfl
  | cons vi l ih =>
    intro S R h
    simp only [List.map_cons, List.foldlM_cons, bind, Except.bind] at h
    cases hstep : Spec.inactivityLoopStep p (mt.toList.map UInt64.toNat) leak
        (S.toList.map UInt64.toNat) vi.toNat with
    | error err => rw [hstep] at h; cases h
    | ok R1 =>
    rw [hstep] at h
    have hR1 : R1 = (S.set! vi.toNat (inactivityScoreE mt leak vi S[vi.toNat]!)).toList.map
        UInt64.toNat := by
      unfold Spec.inactivityLoopStep at hstep
      simp only [bind, Except.bind] at hstep
      cases hg : Spec.listGet (S.toList.map UInt64.toNat) vi.toNat with
      | error err => rw [hg] at hstep; cases hstep
      | ok score =>
      rw [hg] at hstep
      obtain ⟨hlt, rfl⟩ := listGet_map_ok S.val UInt64.toNat vi.toNat hg
      dsimp only at hstep
      cases hs : Spec.inactivityScoreStep p (decide (vi.toNat ∈ mt.toList.map UInt64.toNat)) leak
          (S.val[vi.toNat]!).toNat with
      | error err => rw [hs] at hstep; cases hstep
      | ok n =>
      rw [hs] at hstep
      have hn := inactivityScoreStep_ok hpp mt leak vi _ hs
      dsimp only at hstep
      unfold Spec.listSet at hstep
      rw [if_pos (by simpa using hlt)] at hstep
      cases hstep
      rw [map_toList_set!, sszList_getElem!_val, ← hn]
    rw [hR1] at h
    exact ih _ h

/-- `process_inactivity_updates` equals Etheorem's. -/
theorem inactivity_updates_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_inactivity_updates p (absEState e) = .ok s') :
    (EthCLSpecs.Fulu.processInactivityUpdates (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState (inactivityUpdatesE e)) ∧
      s' = absEState (inactivityUpdatesE e) := by
  refine ⟨processInactivityUpdates_run e, ?_⟩
  have hp := hpp.toPresetAgrees
  unfold inactivityUpdatesE
  have hcur := get_current_epoch_eq hp e
  by_cases hg : (EthCLSpecs.Fulu.currentEpochOf (pureState e) ==
      EthCLSpecs.Fulu.Const.genesisEpoch) = true
  · rw [if_pos hg]
    unfold Spec.process_inactivity_updates at h
    have hg' : ((EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) = true := by
      simp only [beq_iff_eq] at hg ⊢; rw [hg]; rfl
    simp only [hcur, bind, Except.bind, hg', if_true, pure, Except.pure] at h
    cases h; rfl
  · rw [if_neg hg]
    have hg' : (EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat ≠ Spec.GENESIS_EPOCH := by
      intro h0; apply hg; simp only [beq_iff_eq]; exact UInt64.toNat_inj.mp h0
    cases helig : Spec.get_eligible_validator_indices p (absEState e) with
    | error err =>
      unfold Spec.process_inactivity_updates at h
      simp [hcur, bind, Except.bind, hg', helig, pure, Except.pure] at h
    | ok el =>
    have hel := get_eligible_validator_indices_ok hp e helig
    cases hel' : (EthCLSpecs.Fulu.getEligibleValidatorIndices (pureState e)).toList with
    | nil =>
      rw [hel', List.map_nil] at hel
      subst hel
      unfold Spec.process_inactivity_updates at h
      simp [hcur, bind, Except.bind, hg', helig, pure, Except.pure] at h
      subst h
      rfl
    | cons vi rest =>
    rw [hel'] at hel
    subst hel
    have hprev := get_previous_epoch_eq hp e
    cases hpart : Spec.get_unslashed_participating_indices p (absEState e)
        Spec.TIMELY_TARGET_FLAG_INDEX (EthCLSpecs.Fulu.previousEpochOf (pureState e)).toNat with
    | error err =>
      exfalso
      unfold Spec.process_inactivity_updates at h
      have hgb : ((EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) =
          false := by simpa using hg'
      simp [hcur, hgb, helig, hprev, hpart, bind, Except.bind, pure, Except.pure] at h
    | ok part =>
    cases hleak : Spec.is_in_inactivity_leak p (absEState e) with
    | error err =>
      exfalso
      unfold Spec.process_inactivity_updates at h
      have hgb : ((EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) =
          false := by simpa using hg'
      simp only [hcur, hgb, helig, hprev, hpart, hleak, bind, Except.bind, pure, Except.pure,
        List.map_cons, List.forIn_cons, Bool.false_eq_true, if_false] at h
      by_cases hc : vi.toNat ∈ part
      · simp only [hc, if_true] at h
        cases hg1 : Spec.listGet (List.map UInt64.toNat e.inactivityScores.toList) vi.toNat with
        | error e1 => simp [hg1] at h
        | ok v =>
          cases hs1 : Spec.listSet (List.map UInt64.toNat e.inactivityScores.toList) vi.toNat (Spec.saturating_sub v 1) with
          | error e1 => simp [hg1, hs1] at h
          | ok w => simp [hg1, hs1] at h
      · simp only [hc, if_false] at h
        cases hg1 : Spec.listGet (List.map UInt64.toNat e.inactivityScores.toList) vi.toNat with
        | error e1 => simp [hg1] at h
        | ok v =>
          cases ha : Spec.uint64Add v p.INACTIVITY_SCORE_BIAS with
          | error e1 => simp [hg1, ha] at h
          | ok a =>
            cases hs1 : Spec.listSet (List.map UInt64.toNat e.inactivityScores.toList) vi.toNat a with
            | error e1 => simp [hg1, ha, hs1] at h
            | ok w => simp [hg1, ha, hs1] at h
    | ok lk =>
    rw [Spec.process_inactivity_updates_eq p _ _ _ _ _ lk hcur hg' helig hprev hpart hleak] at h
    have hpart' := get_unslashed_participating_indices_ok hp e 1 (by decide) _ hpart
    have hlk := is_in_inactivity_leak_ok hpp e hleak
    subst hpart' hlk
    cases hf : (List.map UInt64.toNat (vi :: rest)).foldlM
        (Spec.inactivityLoopStep p
          ((EthCLSpecs.Fulu.getUnslashedParticipatingIndices (pureState e) 1
            (EthCLSpecs.Fulu.previousEpochOf (pureState e))).toList.map UInt64.toNat)
          (EthCLSpecs.Fulu.isInInactivityLeak (pureState e)))
        (absEState e).inactivity_scores with
    | error err => rw [hf] at h; cases h
    | ok R =>
    rw [hf] at h
    cases h
    have hR := inactivity_fold hpp _ _ (vi :: rest) e.inactivityScores hf
    rw [hR]
    rfl

end Inactivity

end EpochProofs.Etheorem.Fulu
