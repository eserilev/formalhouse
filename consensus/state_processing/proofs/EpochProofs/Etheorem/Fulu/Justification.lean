import EpochProofs.Etheorem.Fulu.Participation

/-!
# `process_justification_and_finalization`: the reference equals Etheorem

The main theorem is `justification_etheorem`. `jfWeighE` is Etheorem's
`weigh_justification_and_finalization` on a plain state, and `weigh_run` proves that Etheorem's
run gives it.

The reference keeps `justification_bits` as a list of four booleans. Etheorem keeps a `BitVec 4`
and shifts it. `absBits_shift` and `absBits_bitSet` relate the two. Etheorem's `epoch + k`
compares wrap only where the reference raises.
-/

namespace EpochProofs.Etheorem.Fulu
open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs EthCLSpecs.Proofs.Fulu

/-! ## Justification bits -/

theorem absBits_four (b : Bitvector 4) :
    absBits b = [bitGet b 0, bitGet b 1, bitGet b 2, bitGet b 3] := by
  simp [absBits, bitGet, List.range_succ]

theorem bitvector_ofNat (b : Bitvector 4) : b = ⟨BitVec.ofNat 4 b.data.toNat⟩ := by
  cases b; simp

set_option maxRecDepth 20000 in
theorem shift_bits_spec : ∀ n < 16,
    absBits (⟨(BitVec.ofNat 4 n) <<< 1⟩ : Bitvector 4) =
      ((absBits (⟨BitVec.ofNat 4 n⟩ : Bitvector 4)).take 1 ++
        (absBits (⟨BitVec.ofNat 4 n⟩ : Bitvector 4)).take 3).set 0 false := by
  decide

theorem absBits_shift (b : Bitvector 4) :
    absBits (⟨b.data <<< 1⟩ : Bitvector 4) = ((absBits b).take 1 ++ (absBits b).take 3).set 0 false := by
  have := shift_bits_spec b.data.toNat b.data.isLt
  rw [← bitvector_ofNat] at this
  simpa using this

set_option maxRecDepth 20000 in
theorem bitSet_spec : ∀ n < 16, ∀ i < 4,
    absBits (bitSet (⟨BitVec.ofNat 4 n⟩ : Bitvector 4) i true) =
      (absBits (⟨BitVec.ofNat 4 n⟩ : Bitvector 4)).set i true := by
  decide

theorem absBits_bitSet (b : Bitvector 4) (i : Nat) (hi : i < 4) :
    absBits (bitSet b i true) = (absBits b).set i true := by
  have := bitSet_spec b.data.toNat b.data.isLt i hi
  rw [← bitvector_ofNat] at this
  exact this

section Plain

variable [EthCLSpecs.Fulu.Preset] [HasherTag]

/-- Etheorem's first two writes: rotate the justified checkpoints and shift the bits. -/
def jfShift (e : EState) : EState :=
  { e with previousJustifiedCheckpoint := e.currentJustifiedCheckpoint,
           justificationBits := ⟨e.justificationBits.data <<< 1⟩ }

/-- Justify `epoch` with `root` and set bit `bit`, when `c` holds. -/
def jfJustify (w : EState) (c : Bool) (epoch : UInt64) (root : EthCLSpecs.Fulu.Root) (bit : Nat) :
    EState :=
  if c then
    { w with currentJustifiedCheckpoint := { epoch := epoch, root := root },
             justificationBits := bitSet w.justificationBits bit true }
  else w

/-- Finalize `cp` when `c` holds. -/
def jfFinalize (w : EState) (c : Bool) (cp : EthCLSpecs.Fulu.Checkpoint) : EState :=
  if c then { w with finalizedCheckpoint := cp } else w

/-- The state after Etheorem's `weigh_justification_and_finalization`. -/
def jfWeighE (e : EState) (jp jc : Bool) (pr cr : EthCLSpecs.Fulu.Root) : EState :=
  let prevEpoch := EthCLSpecs.Fulu.previousEpochOf (pureState e)
  let currEpoch := EthCLSpecs.Fulu.currentEpochOf (pureState e)
  let oldPrev := e.previousJustifiedCheckpoint
  let oldCurr := e.currentJustifiedCheckpoint
  let s3 := jfJustify (jfJustify (jfShift e) jp prevEpoch pr 1) jc currEpoch cr 0
  let bits := s3.justificationBits
  let s4 := jfFinalize s3
    (bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && oldPrev.epoch + 3 == currEpoch) oldPrev
  let s5 := jfFinalize s4 (bitGet bits 1 && bitGet bits 2 && oldPrev.epoch + 2 == currEpoch) oldPrev
  let s6 := jfFinalize s5
    (bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oldCurr.epoch + 2 == currEpoch) oldCurr
  jfFinalize s6 (bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch) oldCurr

/-- Close a `modifyState` run on a pure box against a plain closed form, case by case. -/
local macro "finish_weigh" : tactic => `(tactic| (
  unfold EthCLSpecs.Fulu.modifyState
  simp only [modifyThe, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, if_true, if_false,
    Bool.false_eq_true, jfWeighE, jfFinalize, jfJustify, jfShift, pureState_eq,
    SizzLean.Cache.SSZ.Box.view]
  repeat' split
  all_goals first | rfl | contradiction))

theorem weigh_run (e : EState) (tot pt ct : UInt64) (pr cr : EthCLSpecs.Fulu.Root)
    (hpr : pt.toNat * 3 ≥ tot.toNat * 2 →
      (EthCLSpecs.Fulu.getBlockRoot (StateTransition := FuluRun) (pureState e)
        (EthCLSpecs.Fulu.previousEpochOf (pureState e))).run (pureState e) = .ok (pr, pureState e))
    (hcr : ct.toNat * 3 ≥ tot.toNat * 2 →
      (EthCLSpecs.Fulu.getBlockRoot (StateTransition := FuluRun) (pureState e)
        (EthCLSpecs.Fulu.currentEpochOf (pureState e))).run (pureState e) = .ok (cr, pureState e)) :
    (EthCLSpecs.Fulu.weighJustificationAndFinalization (StateTransition := FuluRun) tot pt ct).run
        (pureState e) =
      .ok ((), pureState (jfWeighE e (decide (pt.toNat * 3 ≥ tot.toNat * 2))
        (decide (ct.toNat * 3 ≥ tot.toNat * 2)) pr cr)) := by
  unfold EthCLSpecs.Fulu.weighJustificationAndFinalization
  rw [run_bind, show (get : FuluRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  by_cases hp : pt.toNat * 3 ≥ tot.toNat * 2 <;> by_cases hc : ct.toNat * 3 ≥ tot.toNat * 2
  · rw [if_pos hp, run_bind, hpr hp, except_bind_ok, if_pos hc, run_bind, hcr hc, except_bind_ok]
    simp only [hp, hc, decide_true]
    finish_weigh
  · rw [if_pos hp, run_bind, hpr hp, except_bind_ok, if_neg hc, run_bind, run_pure, except_bind_ok]
    simp only [hp, hc, decide_true, decide_false]
    finish_weigh
  · rw [if_neg hp, run_bind, run_pure, except_bind_ok, if_pos hc, run_bind, hcr hc, except_bind_ok]
    simp only [hp, hc, decide_true, decide_false]
    finish_weigh
  · rw [if_neg hp, run_bind, run_pure, except_bind_ok, if_neg hc, run_bind, run_pure, except_bind_ok]
    simp only [hp, hc, decide_false]
    finish_weigh

end Plain

variable [EthCLSpecs.Fulu.Preset] [HasherTag] [EthCLSpecs.Fulu.Config]
variable {p : Spec.Preset} (hpp : PassesPresetAgrees p)
include hpp


theorem get_block_root_etheorem (e : EState) (s0 : EthCLSpecs.Fulu.State) (epoch : UInt64)
    {r : Spec.Root} (h : Spec.get_block_root p (absEState e) epoch.toNat = .ok r) :
    (EthCLSpecs.Fulu.getBlockRoot (StateTransition := FuluRun) (pureState e) epoch).run s0 =
      .ok (r, s0) := by
  have hp := hpp.toPresetAgrees
  unfold Spec.get_block_root at h
  simp only [bind, Except.bind] at h
  cases hs : Spec.compute_start_slot_at_epoch p epoch.toNat with
  | error err => rw [hs] at h; cases h
  | ok slot =>
  rw [hs] at h
  have hs' := compute_start_slot_at_epoch_ok hp epoch hs
  dsimp only at h
  have hce : EthCLSpecs.Fulu.computeStartSlotAtEpoch epoch =
      epoch * UInt64.ofNat EthCLSpecs.Fulu.Const.slotsPerEpoch := rfl
  rw [hce] at hs'
  generalize hS : epoch * UInt64.ofNat EthCLSpecs.Fulu.Const.slotsPerEpoch = S at hs'
  subst hs'
  have hsphr : EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot < 2 ^ 64 :=
    EthCLSpecs.Fulu.Const.slotsPerHistoricalRootLt
  have hsphrN : (UInt64.ofNat EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot).toNat =
      p.SLOTS_PER_HISTORICAL_ROOT := by
    rw [UInt64.toNat_ofNat_of_lt' hsphr, hpp.slotsPerHistoricalRoot]
  unfold Spec.get_block_root_at_slot at h
  simp only [bind, Except.bind, absEState_slot] at h
  by_cases c1 : S.toNat < e.slot.toNat
  · rw [if_neg (by simpa using c1)] at h
    cases ha : Spec.uint64Add S.toNat p.SLOTS_PER_HISTORICAL_ROOT with
    | error err => rw [ha] at h; cases h
    | ok b =>
    rw [ha] at h
    rw [← hsphrN] at ha
    have hb := uint64Add_ok ha
    have hsum : S.toNat + (UInt64.ofNat EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot).toNat <
        2 ^ 64 := by
      unfold Spec.uint64Add at ha; split at ha
      · simpa [Spec.UINT64_SIZE] using ‹_›
      · cases ha
    dsimp only at h
    by_cases c2 : e.slot.toNat ≤ b
    · rw [if_neg (by simpa using c2)] at h
      simp only [absEState_block_roots] at h
      unfold EthCLSpecs.Fulu.getBlockRoot EthCLSpecs.Fulu.getBlockRootAtSlot
      rw [hS]
      simp only [view_uncachedBox]
      rw [if_pos (UInt64.lt_iff_toNat_lt.mpr c1), run_bind, run_pure, except_bind_ok,
        run_bind, checkedAdd_run_ok _ _ _ _ hsum, except_bind_ok]
      rw [if_pos (by rw [UInt64.le_iff_toNat_le, hb]; exact c2), run_bind, run_pure, except_bind_ok]
      unfold Spec.listGet at h
      simp only [pure, Except.pure] at h
      have hpos : 0 < EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot :=
        EthCLSpecs.Fulu.Const.slotsPerHistoricalRootPos
      have hk : (S % UInt64.ofNat EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot).toNat =
          S.toNat % p.SLOTS_PER_HISTORICAL_ROOT := by rw [UInt64.toNat_mod, hsphrN]
      have hlt : S.toNat % p.SLOTS_PER_HISTORICAL_ROOT < EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot := by
        rw [hpp.slotsPerHistoricalRoot]; exact Nat.mod_lt _ (by rw [← hpp.slotsPerHistoricalRoot]; exact hpos)
      have hget : e.blockRoots.toList[S.toNat % p.SLOTS_PER_HISTORICAL_ROOT]? =
          some (vmodGet e.blockRoots S EthCLSpecs.Fulu.Const.slotsPerHistoricalRoot) := by
        unfold vmodGet
        simp only [hk]
        rw [Vector.getElem?_toList, Vector.getElem?_eq_getElem hlt]
      rw [hget] at h
      cases h
      rfl
    · rw [if_pos (by simpa using c2)] at h; cases h
  · rw [if_pos (by simpa using c1)] at h; cases h

omit [HasherTag] [EthCLSpecs.Fulu.Config] hpp in
theorem fin_step (s : Spec.BeaconState) (w : EState) (hs : s = absEState w) (bitsAll : Bool)
    (old : EthCLSpecs.Fulu.Checkpoint) (k : UInt64) (cur : UInt64) {s'' : Spec.BeaconState}
    (h : (if bitsAll then (do
        if (← Spec.uint64Add (absCheckpoint old).epoch k.toNat) == cur.toNat then
          pure { s with finalized_checkpoint := absCheckpoint old }
        else pure s) else pure s : Spec.SpecM Spec.BeaconState) = .ok s'') :
    s'' = absEState (jfFinalize w (bitsAll && old.epoch + k == cur) old) := by
  subst hs
  unfold jfFinalize
  cases bitsAll
  · simp only [Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq] at h
    simp [h]
  · simp only [if_true, bind, Except.bind] at h
    cases ha : Spec.uint64Add (absCheckpoint old).epoch k.toNat with
    | error err => rw [ha] at h; cases h
    | ok v =>
      rw [ha] at h
      have hv := uint64Add_ok (a := old.epoch) (b := k) ha
      simp only at h
      by_cases hc : old.epoch + k = cur
      · have hc' : (v == cur.toNat) = true := by rw [← hv, hc]; simp
        rw [if_pos hc'] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.true_and, hc, beq_self_eq_true, if_true]
        rfl
      · have hc' : (v == cur.toNat) = false := by
          rw [← hv]; simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact hc (UInt64.toNat_inj.mp h')
        rw [if_neg (by simp [hc'])] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have : (old.epoch + k == cur) = false := by simpa using hc
        simp [this]

omit [HasherTag] [EthCLSpecs.Fulu.Config] hpp in
theorem get_block_root_absEState_congr (w e : EState) (hs : w.slot = e.slot)
    (hb : w.blockRoots = e.blockRoots) (ep : Nat) :
    Spec.get_block_root p (absEState w) ep = Spec.get_block_root p (absEState e) ep := by
  have h1 : (absEState w).slot = (absEState e).slot := by simp [hs]
  have h2 : (absEState w).block_roots = (absEState e).block_roots := by simp [hb]
  unfold Spec.get_block_root Spec.get_block_root_at_slot
  rw [h1, h2]

omit [HasherTag] [EthCLSpecs.Fulu.Config] hpp in
theorem just_step (w : EState) (tot x epoch : UInt64) (bit : Nat) (hbit : bit < 4)
    {s4 : Spec.BeaconState}
    (h : (do
      let m1 ← Spec.uint64Mul x.toNat 3
      let m2 ← Spec.uint64Mul tot.toNat 2
      if m1 ≥ m2 then do
        let r ← Spec.get_block_root p (absEState w) epoch.toNat
        let b ← Spec.listSet (absEState w).justification_bits bit true
        pure { absEState w with
          current_justified_checkpoint := { epoch := epoch.toNat, root := r },
          justification_bits := b }
      else pure (absEState w) : Spec.SpecM Spec.BeaconState) = .ok s4) :
    ∃ r, (x.toNat * 3 ≥ tot.toNat * 2 → Spec.get_block_root p (absEState w) epoch.toNat = .ok r) ∧
      s4 = absEState (jfJustify w (decide (x.toNat * 3 ≥ tot.toNat * 2)) epoch r bit) := by
  obtain ⟨m1, hm1, h⟩ := bind_ok_inv h
  obtain ⟨m2, hm2, h⟩ := bind_ok_inv h
  rw [uint64Mul_ok_val hm1, uint64Mul_ok_val hm2] at h
  by_cases hj : x.toNat * 3 ≥ tot.toNat * 2
  · rw [if_pos hj] at h
    obtain ⟨r, hr, h⟩ := bind_ok_inv h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    refine ⟨r, fun _ => hr, ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hlen : bit < (absEState w).justification_bits.length := by
      simp [absEState_justification_bits, absBits_length]; omega
    simp only [Spec.listSet, hlen, if_true, pure, Except.pure, Except.ok.injEq] at hb
    subst hb
    simp only [jfJustify, hj, decide_true, if_true]
    rw [absEState_justification_bits, ← absBits_bitSet _ _ hbit]
    rfl
  · rw [if_neg hj] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨default, fun h' => absurd h' hj, by simp [jfJustify, hj]⟩

theorem weigh_etheorem (e : EState) (tot pt ct : UInt64) {s' : Spec.BeaconState}
    (h : Spec.weigh_justification_and_finalization p (absEState e) tot.toNat pt.toNat ct.toNat =
      .ok s') :
    ∃ pr cr : EthCLSpecs.Fulu.Root,
      (pt.toNat * 3 ≥ tot.toNat * 2 → Spec.get_block_root p (absEState e)
        (EthCLSpecs.Fulu.previousEpochOf (pureState e)).toNat = .ok pr) ∧
      (ct.toNat * 3 ≥ tot.toNat * 2 → Spec.get_block_root p (absEState e)
        (EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat = .ok cr) ∧
      s' = absEState (jfWeighE e (decide (pt.toNat * 3 ≥ tot.toNat * 2))
        (decide (ct.toNat * 3 ≥ tot.toNat * 2)) pr cr) := by
  have hp := hpp.toPresetAgrees
  unfold Spec.weigh_justification_and_finalization at h
  rw [get_previous_epoch_eq hp, get_current_epoch_eq hp] at h
  have hl0 : Spec.listSet ((absEState e).justification_bits.take 1 ++
      (absEState e).justification_bits.take (Spec.JUSTIFICATION_BITS_LENGTH - 1)) 0 false =
      .ok (absBits (⟨e.justificationBits.data <<< 1⟩ : Bitvector 4)) := by
    rw [absBits_shift]
    simp [Spec.listSet, absEState_justification_bits, absBits_four, Spec.JUSTIFICATION_BITS_LENGTH,
      pure, Except.pure]
  simp only [ok_bind] at h
  rw [hl0] at h
  simp only [ok_bind] at h
  obtain ⟨s4, h4, h⟩ := bind_ok_inv h
  obtain ⟨pr, hpr, rfl⟩ := just_step (jfShift e) tot pt
    (EthCLSpecs.Fulu.previousEpochOf (pureState e)) 1 (by decide) h4
  obtain ⟨s5, h5, h⟩ := bind_ok_inv h
  obtain ⟨cr, hcr, rfl⟩ := just_step _ tot ct
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) 0 (by decide) h5
  have hw4 : ∀ c r, (jfJustify (jfShift e) c (EthCLSpecs.Fulu.previousEpochOf (pureState e)) r 1).slot
      = e.slot ∧ (jfJustify (jfShift e) c (EthCLSpecs.Fulu.previousEpochOf (pureState e)) r 1).blockRoots
      = e.blockRoots := by
    intro c r; unfold jfJustify jfShift; split <;> exact ⟨rfl, rfl⟩
  refine ⟨pr, cr, hpr, fun hc => by
    rw [← get_block_root_absEState_congr _ _ (hw4 _ _).1 (hw4 _ _).2]; exact hcr hc, ?_⟩
  generalize hW : jfJustify (jfJustify (jfShift e) (decide (pt.toNat * 3 ≥ tot.toNat * 2))
    (EthCLSpecs.Fulu.previousEpochOf (pureState e)) pr 1) (decide (ct.toNat * 3 ≥ tot.toNat * 2))
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) cr 0 = W at h
  obtain ⟨s6, h6, h⟩ := bind_ok_inv h
  have e6 := fin_step (absEState W) W rfl _ e.previousJustifiedCheckpoint 3
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) h6
  subst e6
  obtain ⟨s7, h7, h⟩ := bind_ok_inv h
  have e7 := fin_step _ _ rfl _ e.previousJustifiedCheckpoint 2
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) h7
  subst e7
  obtain ⟨s8, h8, h⟩ := bind_ok_inv h
  have e8 := fin_step _ _ rfl _ e.currentJustifiedCheckpoint 2
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) h8
  subst e8
  have e9 := fin_step _ _ rfl _ e.currentJustifiedCheckpoint 1
    (EthCLSpecs.Fulu.currentEpochOf (pureState e)) h
  subst e9
  subst hW
  simp only [absEState_justification_bits, absBits_four, jfWeighE, List.extract_eq_take_drop,
    List.drop, List.take, List.all_cons, List.all_nil, id, Nat.reduceSub, Bool.and_true,
    Bool.and_assoc]

/-- `process_justification_and_finalization` equals Etheorem's. -/
theorem justification_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_justification_and_finalization p (absEState e) = .ok s') :
    ∃ e' : EState,
      (EthCLSpecs.Fulu.processJustificationAndFinalization (StateTransition := FuluRun)).run
          (pureState e) = .ok ((), pureState e') ∧
        s' = absEState e' := by
  have hp := hpp.toPresetAgrees
  unfold Spec.process_justification_and_finalization at h
  rw [get_current_epoch_eq hp] at h
  simp only [ok_bind] at h
  unfold EthCLSpecs.Fulu.processJustificationAndFinalization
  rw [run_bind, show (get : FuluRun _).run (pureState e) = .ok (pureState e, pureState e) from rfl,
    except_bind_ok]
  dsimp only
  have hge : (EthCLSpecs.Fulu.Const.genesisEpoch + 1 : UInt64).toNat = Spec.GENESIS_EPOCH + 1 := rfl
  by_cases hg : (EthCLSpecs.Fulu.currentEpochOf (pureState e)).toNat ≤ Spec.GENESIS_EPOCH + 1
  · rw [if_pos (by simpa using hg)] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨e, ?_, rfl⟩
    rw [if_pos (by rw [UInt64.le_iff_toNat_le, hge]; exact hg)]
    rfl
  · rw [if_neg (by simpa using hg)] at h
    rw [if_neg (by rw [UInt64.le_iff_toNat_le, hge]; exact hg)]
    rw [get_previous_epoch_eq hp] at h
    simp only [ok_bind] at h
    obtain ⟨_, -, h⟩ := bind_ok_inv h
    obtain ⟨pi, hpi, h⟩ := bind_ok_inv h
    obtain ⟨ci, hci, h⟩ := bind_ok_inv h
    obtain ⟨tab, htab, h⟩ := bind_ok_inv h
    obtain ⟨ptb, hptb, h⟩ := bind_ok_inv h
    obtain ⟨ctb, hctb, h⟩ := bind_ok_inv h
    have hpi' := get_unslashed_participating_indices_ok hp e 1 (by decide) _ hpi
    have hci' := get_unslashed_participating_indices_ok hp e 1 (by decide) _ hci
    rw [hpi'] at hptb
    rw [hci'] at hctb
    have htab' := get_total_active_balance_ok hp e htab
    have hptb' := get_total_balance_ok hp e _ hptb
    have hctb' := get_total_balance_ok hp e _ hctb
    rw [← htab', ← hptb', ← hctb'] at h
    obtain ⟨pr, cr, hpr, hcr, rfl⟩ := weigh_etheorem hpp e _ _ _ h
    refine ⟨_, weigh_run e _ _ _ pr cr
      (fun hc => get_block_root_etheorem hpp e (pureState e) _ (hpr hc))
      (fun hc => get_block_root_etheorem hpp e (pureState e) _ (hcr hc)), rfl⟩

end EpochProofs.Etheorem.Fulu
