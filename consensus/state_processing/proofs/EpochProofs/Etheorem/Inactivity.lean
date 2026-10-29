import EpochProofs.Etheorem.Participation

/-!
# `process_inactivity_updates`: the reference equals Etheorem

The main theorem is `inactivity_updates_etheorem`. `inactivityUpdatesE` is Etheorem's step on a
plain state, and `processInactivityUpdates_run` proves that Etheorem's run gives it.

Etheorem raises on a score read past the end and on an overflow of
`score + INACTIVITY_SCORE_BIAS`, as the reference does.
-/

namespace EpochProofs.Etheorem
open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

variable [EthCLSpecs.Gloas.Config]

/-- One inactivity score in Etheorem. -/
def inactivityScoreE (matchingTarget : Array UInt64) (leak : Bool) (vi cur : UInt64) : UInt64 :=
  let cur := if matchingTarget.contains vi then cur - umin 1 cur
    else cur + EthCLSpecs.Gloas.Const.inactivityScoreBias
  if !leak then cur - umin EthCLSpecs.Gloas.Const.inactivityScoreRecoveryRate cur else cur

/-- Etheorem's loop over the eligible indices, on the scores alone. -/
def inactivityScoresE (matchingTarget : Array UInt64) (leak : Bool) (l : List UInt64)
    (s : SSZList UInt64 EthCLSpecs.Gloas.Const.validatorRegistryLimit) :
    SSZList UInt64 EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
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
  if EthCLSpecs.Gloas.currentEpochOf (pureState e) == EthCLSpecs.Gloas.Const.genesisEpoch then e
  else
    let mt := eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
      (EthCLSpecs.Gloas.previousEpochOf (pureState e))
    let leak := EthCLSpecs.Gloas.isInInactivityLeak (pureState e)
    let eligible := (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList
    { e with inactivityScores := inactivityScoresE mt leak eligible e.inactivityScores }

/-- Etheorem's `processInactivityUpdates` at the genesis epoch leaves the state. -/
theorem processInactivityUpdates_run_genesis (e : EState)
    (h : (EthCLSpecs.Gloas.currentEpochOf (pureState e) == EthCLSpecs.Gloas.Const.genesisEpoch) = true) :
    (EthCLSpecs.Gloas.processInactivityUpdates (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState (inactivityUpdatesE e)) := by
  unfold EthCLSpecs.Gloas.processInactivityUpdates inactivityUpdatesE
  rw [run_bind, show (get : GloasRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  rw [if_pos h, if_pos h]; rfl

omit [EthCLSpecs.Gloas.Config] in
/-- A loop over a list on the plain state that runs in step with a reference fold. `R` relates the
reference value to the Etheorem state. Each step that the reference takes, Etheorem takes as
`G`. -/
theorem forIn_run_foldlM {α σ : Type} (R : σ → EState → Prop) (specStep : σ → α → Spec.SpecM σ)
    (body : α → PUnit → GloasRun (ForInStep PUnit)) (G : EState → α → EState)
    (hstep : ∀ a x w x', R x w → specStep x a = .ok x' →
      (body a PUnit.unit).run (pureState w) = .ok (.yield PUnit.unit, pureState (G w a)) ∧
        R x' (G w a)) :
    ∀ (l : List α) (x : σ) (w : EState) {r : σ}, R x w → l.foldlM specStep x = .ok r →
      (forIn l PUnit.unit body).run (pureState w) = .ok (PUnit.unit, pureState (l.foldl G w)) ∧
        R r (l.foldl G w) := by
  intro l
  induction l with
  | nil =>
    intro x w r hR h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, hR⟩
  | cons a l ih =>
    intro x w r hR h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hs : specStep x a with
    | error err => rw [hs] at h; cases h
    | ok x' =>
      rw [hs] at h
      obtain ⟨hrun, hR'⟩ := hstep a x w x' hR hs
      obtain ⟨hrun', hR''⟩ := ih x' (G w a) hR' h
      refine ⟨?_, hR''⟩
      rw [List.forIn_cons, run_bind, hrun, except_bind_ok]
      exact hrun'

omit [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] in
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
/-- One reference step of the inactivity loop reads the score in bounds and adds
`INACTIVITY_SCORE_BIAS` without overflow. These are the read and the sum that Etheorem checks. -/
theorem inactivity_step_facts (mt : Array UInt64) (leak : Bool) (vi : UInt64) (w : EState)
    {R1 : List Nat}
    (hstep : Spec.inactivityLoopStep p (mt.toList.map UInt64.toNat) leak
      (w.inactivityScores.toList.map UInt64.toNat) vi.toNat = .ok R1) :
    vi.toNat < w.inactivityScores.val.size ∧
    (mt.contains vi = false → (w.inactivityScores.val[vi.toNat]!).toNat +
        EthCLSpecs.Gloas.Const.inactivityScoreBias.toNat < 2 ^ 64) ∧
    R1 = (inactivityStepE mt leak w vi).inactivityScores.toList.map UInt64.toNat := by
  unfold Spec.inactivityLoopStep at hstep
  simp only [bind, Except.bind] at hstep
  cases hg : Spec.listGet (w.inactivityScores.toList.map UInt64.toNat) vi.toNat with
  | error err => rw [hg] at hstep; cases hstep
  | ok score =>
  rw [hg] at hstep
  obtain ⟨hlt, rfl⟩ := listGet_map_ok w.inactivityScores.val UInt64.toNat vi.toNat hg
  dsimp only at hstep
  cases hs : Spec.inactivityScoreStep p (decide (vi.toNat ∈ mt.toList.map UInt64.toNat)) leak
      (w.inactivityScores.val[vi.toNat]!).toNat with
  | error err => rw [hs] at hstep; cases hstep
  | ok n =>
  rw [hs] at hstep
  have hn := inactivityScoreStep_ok hpp mt leak vi _ hs
  dsimp only at hstep
  unfold Spec.listSet at hstep
  rw [if_pos (by simpa using hlt)] at hstep
  cases hstep
  refine ⟨hlt, fun hm => ?h1, ?h2⟩
  case h2 =>
    show _ = List.map UInt64.toNat (w.inactivityScores.set! _ _).toList
    rw [map_toList_set!, sszList_getElem!_val, ← hn]
  have hm' : decide (vi.toNat ∈ mt.toList.map UInt64.toNat) = false := by
    simpa [mem_map_toNat_iff] using hm
  unfold Spec.inactivityScoreStep at hs
  rw [hm'] at hs
  simp only [Bool.false_eq_true, if_false, bind, Except.bind] at hs
  cases ha : Spec.uint64Add (w.inactivityScores.val[vi.toNat]!).toNat p.INACTIVITY_SCORE_BIAS with
  | error err => rw [ha] at hs; cases hs
  | ok m => rw [hpp.inactivityScoreBias]; exact uint64Add_lt ha

omit [HasherTag] in
theorem inactivity_fold (mt : Array UInt64) (leak : Bool) :
    ∀ (l : List UInt64) (S : SSZList UInt64 EthCLSpecs.Gloas.Const.validatorRegistryLimit)
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
    (EthCLSpecs.Gloas.processInactivityUpdates (StateTransition := GloasRun)).run (pureState e) =
        .ok ((), pureState (inactivityUpdatesE e)) ∧
      s' = absEState (inactivityUpdatesE e) := by
  have hp := hpp.toPresetAgrees
  have hcur := get_current_epoch_eq hp e
  by_cases hg : (EthCLSpecs.Gloas.currentEpochOf (pureState e) ==
      EthCLSpecs.Gloas.Const.genesisEpoch) = true
  · refine ⟨processInactivityUpdates_run_genesis e hg, ?_⟩
    unfold inactivityUpdatesE
    rw [if_pos hg]
    unfold Spec.process_inactivity_updates at h
    have hg' : ((EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) = true := by
      simp only [beq_iff_eq] at hg ⊢; rw [hg]; rfl
    simp only [hcur, bind, Except.bind, hg', if_true, pure, Except.pure] at h
    cases h; rfl
  · have hg' : (EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat ≠ Spec.GENESIS_EPOCH := by
      intro h0; apply hg; simp only [beq_iff_eq]; exact UInt64.toNat_inj.mp h0
    -- Etheorem's run, from the participating set and a reference fold over the eligible indices.
    have hrun : ∀ {R : List Nat},
        EthCLSpecs.Gloas.getUnslashedParticipatingIndices (pureState e)
          EthCLSpecs.Gloas.Const.timelyTargetFlagIndex (EthCLSpecs.Gloas.previousEpochOf (pureState e)) =
          .ok (eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
            (EthCLSpecs.Gloas.previousEpochOf (pureState e))) →
        ((EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList.map UInt64.toNat).foldlM
          (Spec.inactivityLoopStep p
            ((eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
              (EthCLSpecs.Gloas.previousEpochOf (pureState e))).toList.map UInt64.toNat)
            (EthCLSpecs.Gloas.isInInactivityLeak (pureState e)))
          (e.inactivityScores.toList.map UInt64.toNat) = .ok R →
        (EthCLSpecs.Gloas.processInactivityUpdates (StateTransition := GloasRun)).run (pureState e) =
          .ok ((), pureState (inactivityUpdatesE e)) ∧
        R = (inactivityUpdatesE e).inactivityScores.toList.map UInt64.toNat := by
      intro R hmt hf
      refine ⟨?_, ?_⟩
      · rw [List.foldlM_map] at hf
        unfold EthCLSpecs.Gloas.processInactivityUpdates inactivityUpdatesE
        rw [run_bind, show (get : GloasRun _).run (pureState e) = .ok (pureState e, pureState e)
          from rfl, except_bind_ok]
        dsimp only
        rw [if_neg hg, if_neg hg]
        rw [run_bind, run_liftErr_of_ok _ _ (by rw [hmt]; rfl), except_bind_ok]
        dsimp only
        rw [← Array.forIn_toList]
        rw [run_bind, (forIn_run_foldlM
          (fun x w => x = w.inactivityScores.toList.map UInt64.toNat)
          (fun x vi => Spec.inactivityLoopStep p
              ((eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
                (EthCLSpecs.Gloas.previousEpochOf (pureState e))).toList.map UInt64.toNat)
              (EthCLSpecs.Gloas.isInInactivityLeak (pureState e)) x vi.toNat)
          _ (fun w vi => inactivityStepE (eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
                (EthCLSpecs.Gloas.previousEpochOf (pureState e)))
              (EthCLSpecs.Gloas.isInInactivityLeak (pureState e)) w vi) ?hstep
          _ _ e rfl hf).1, foldl_inactivityStepE]
        · rfl
        case hstep =>
          intro vi x w x' hx hs
          subst hx
          obtain ⟨hlt, hadd, hR1⟩ := inactivity_step_facts hpp _ _ vi w hs
          refine ⟨?_, hR1⟩
          have hq : w.inactivityScores.val[vi.toNat]? = some w.inactivityScores.val[vi.toNat]! := by
            rw [getElem!_pos w.inactivityScores.val _ hlt]; exact Array.getElem?_eq_getElem hlt
          rw [run_bind, show (get : GloasRun _).run (pureState w) = .ok (pureState w, pureState w)
            from rfl, except_bind_ok]
          simp only [view_uncachedBox]
          rw [run_bind, run_sszGetIdx_some _ _ _ hq, except_bind_ok]
          by_cases hm : (eUnslashed e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
              (EthCLSpecs.Gloas.previousEpochOf (pureState e))).contains vi = true
          · rw [if_pos hm]
            simp only [inactivityStepE, inactivityScoreE, if_pos hm]
            rw [run_bind, run_pure, except_bind_ok]
            unfold EthCLSpecs.Gloas.modifyState
            simp only [sszList_getElem!_val]
            rfl
          · rw [if_neg hm]
            rw [run_bind, checkedAdd_of_lt _ _ _ (hadd (by simpa using hm)), run_pure,
              except_bind_ok]
            simp only [inactivityStepE, inactivityScoreE, if_neg hm]
            unfold EthCLSpecs.Gloas.modifyState
            simp only [sszList_getElem!_val]
            rfl
      · have hR := inactivity_fold hpp _ _ _ e.inactivityScores hf
        rw [hR]
        unfold inactivityUpdatesE
        rw [if_neg hg]
    cases helig : Spec.get_eligible_validator_indices p (absEState e) with
    | error err =>
      unfold Spec.process_inactivity_updates at h
      simp [hcur, bind, Except.bind, hg', helig, pure, Except.pure] at h
    | ok el =>
    have hel := get_eligible_validator_indices_ok hp e helig
    cases hel' : (EthCLSpecs.Gloas.getEligibleValidatorIndices (pureState e)).toList with
    | nil =>
      rw [hel', List.map_nil] at hel
      subst hel
      unfold Spec.process_inactivity_updates at h
      simp [hcur, bind, Except.bind, hg', helig, pure, Except.pure] at h
      subst h
      -- No validator is eligible, so none was active in the previous epoch and Etheorem reads
      -- no participation flag.
      have hmt := getUnslashedParticipatingIndices_ok e EthCLSpecs.Gloas.Const.timelyTargetFlagIndex
        (EthCLSpecs.Gloas.previousEpochOf (pureState e))
        (fun i hi => by
          have := active_prev_mem_eligible e i hi
          rw [hel'] at this
          cases this)
      obtain ⟨hr, hR⟩ := hrun (R := e.inactivityScores.toList.map UInt64.toNat) hmt
        (by rw [hel']; rfl)
      refine ⟨hr, ?_⟩
      unfold inactivityUpdatesE at hR ⊢
      rw [if_neg hg] at hR ⊢
      rw [hel'] at hR ⊢
      rfl
    | cons vi rest =>
    rw [hel'] at hel
    subst hel
    have hprev := get_previous_epoch_eq hp e
    cases hpart : Spec.get_unslashed_participating_indices p (absEState e)
        Spec.TIMELY_TARGET_FLAG_INDEX (EthCLSpecs.Gloas.previousEpochOf (pureState e)).toNat with
    | error err =>
      exfalso
      unfold Spec.process_inactivity_updates at h
      have hgb : ((EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) =
          false := by simpa using hg'
      simp [hcur, hgb, helig, hprev, hpart, bind, Except.bind, pure, Except.pure] at h
    | ok part =>
    cases hleak : Spec.is_in_inactivity_leak p (absEState e) with
    | error err =>
      exfalso
      unfold Spec.process_inactivity_updates at h
      have hgb : ((EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat == Spec.GENESIS_EPOCH) =
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
    obtain ⟨hmt, hpart'⟩ := get_unslashed_participating_indices_ok hp e 1 (by decide) _ hpart
    have hlk := is_in_inactivity_leak_ok hpp e hleak
    subst hpart' hlk
    cases hf : (List.map UInt64.toNat (vi :: rest)).foldlM
        (Spec.inactivityLoopStep p
          ((eUnslashed e 1 (EthCLSpecs.Gloas.previousEpochOf (pureState e))).toList.map UInt64.toNat)
          (EthCLSpecs.Gloas.isInInactivityLeak (pureState e)))
        (absEState e).inactivity_scores with
    | error err => rw [hf] at h; cases h
    | ok R =>
    rw [hf] at h
    cases h
    rw [← hel'] at hf
    obtain ⟨hr, hR⟩ := hrun hmt hf
    refine ⟨hr, ?_⟩
    rw [hR]
    unfold inactivityUpdatesE
    rw [if_neg hg]
    rfl

end Inactivity

end EpochProofs.Etheorem
