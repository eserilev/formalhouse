import EpochProofs.Equiv.Justification
import EpochProofs.Sanity.Invariants.LighthouseOrder

/-!
# Justification and finalization, composed from the translated function

`justification` is `process_justification_and_finalization` of `altair.rs` with
`weigh_justification_and_finalization.rs`: the reads of the epochs, the bits and the balances,
the translated `weigh_justification`, and the checkpoint and bit writes. The reads and the writes
are untranslated glue (`JustificationGlue`), each with the fact that links it to the spec
(`JustificationLinks`). `justification_spec` shows that it returns the state of the model
`lhJustificationAndFinalization`.
-/

namespace EpochProofs.Spec

/-- The writes of `weigh_justification_and_finalization.rs` after `weigh_justification`: the
checkpoints, the block roots they read, and the bits. -/
def lhJustificationWrite (p : Preset) (s : BeaconState) (previous_epoch current_epoch : Epoch)
    (outcome : LhJustificationOutcome) : SpecM BeaconState := do
  let state := s
  let old_previous_justified_checkpoint := state.previous_justified_checkpoint
  let old_current_justified_checkpoint := state.current_justified_checkpoint
  let state := { state with previous_justified_checkpoint := old_current_justified_checkpoint }
  let state ← (do
    if outcome.justify_previous then
      pure { state with
        current_justified_checkpoint :=
          { epoch := previous_epoch, root := ← get_block_root p s previous_epoch } }
    else pure state)
  let state ← (do
    if outcome.justify_current then
      pure { state with
        current_justified_checkpoint :=
          { epoch := current_epoch, root := ← get_block_root p s current_epoch } }
    else pure state)
  let state := { state with
    justification_bits :=
      [outcome.bits.bit0, outcome.bits.bit1, outcome.bits.bit2, outcome.bits.bit3] }
  match outcome.finalized with
  | .unchanged => pure state
  | .oldPreviousJustified =>
    pure { state with finalized_checkpoint := old_previous_justified_checkpoint }
  | .oldCurrentJustified =>
    pure { state with finalized_checkpoint := old_current_justified_checkpoint }

theorem lhWeighJustificationAndFinalization_eq (p : Preset) (s : BeaconState)
    (tab x y : Gwei) :
    lhWeighJustificationAndFinalization p s tab x y = (do
      let previous_epoch ← get_previous_epoch p s
      let current_epoch ← get_current_epoch p s
      let bits : LhJustificationBits :=
        { bit0 := ← listGet s.justification_bits 0, bit1 := ← listGet s.justification_bits 1,
          bit2 := ← listGet s.justification_bits 2, bit3 := ← listGet s.justification_bits 3 }
      let outcome ← lhWeighJustification current_epoch s.previous_justified_checkpoint.epoch
        s.current_justified_checkpoint.epoch bits tab x y
      lhJustificationWrite p s previous_epoch current_epoch outcome) := rfl

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open per_epoch_processing.justification

/-- The untranslated Rust of `process_justification_and_finalization`: the genesis check, the
reads passed to `weigh_justification`, and the writes of its outcome. -/
structure JustificationGlue (σ : Type) where
  /-- `state.current_epoch() <= genesis_epoch + 1`. -/
  early : σ → Bool
  currentEpoch : σ → U64
  previousJustifiedEpoch : σ → U64
  currentJustifiedEpoch : σ → U64
  bits : σ → JustificationBits
  /-- The total active balance and the two target balances of the caches. -/
  totalActiveBalance : σ → U64
  previousTargetBalance : σ → U64
  currentTargetBalance : σ → U64
  /-- The checkpoint and bit writes. `none`: a block root read fails. -/
  write : σ → JustificationOutcome → Option σ

variable {σ : Type}

/-- `process_justification_and_finalization`, as the call of the translated
`weigh_justification` joined by the glue `G`. `none`: the Rust returns an error. -/
def justification (G : JustificationGlue σ) (st : σ) : Result (Option σ) :=
  if G.early st then ok (some st) else do
  let r ← weigh_justification (G.currentEpoch st) (G.previousJustifiedEpoch st)
    (G.currentJustifiedEpoch st) (G.bits st) (G.totalActiveBalance st)
    (G.previousTargetBalance st) (G.currentTargetBalance st)
  match r with
  | .Err _ => ok none
  | .Ok outcome => ok (G.write st outcome)

variable [Spec.PresetCfg]

/-- The trusted facts about the glue `G` at the state `st`: each read is the spec value, and the
writes are the spec writes (`lhJustificationWrite`). The balances are cache reads. -/
structure JustificationLinks (G : JustificationGlue σ) (view : σ → Spec.BeaconState) (st : σ) :
    Prop where
  early : ∀ cur, Spec.get_current_epoch Spec.P (view st) = .ok cur →
    G.early st = decide (cur ≤ Spec.GENESIS_EPOCH + 1)
  currentEpoch : ∀ cur, Spec.get_current_epoch Spec.P (view st) = .ok cur →
    (G.currentEpoch st).val = cur
  previousJustifiedEpoch :
    (G.previousJustifiedEpoch st).val = (view st).previous_justified_checkpoint.epoch
  currentJustifiedEpoch :
    (G.currentJustifiedEpoch st).val = (view st).current_justified_checkpoint.epoch
  bits : ∀ b0 b1 b2 b3, (view st).justification_bits = [b0, b1, b2, b3] →
    absJustificationBits (G.bits st) = ⟨b0, b1, b2, b3⟩
  totalActiveBalance : ∀ tab, Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    (G.totalActiveBalance st).val = tab
  previousTargetBalance : ∀ e i x, Spec.get_previous_epoch Spec.P (view st) = .ok e →
    Spec.get_unslashed_participating_indices Spec.P (view st) Spec.TIMELY_TARGET_FLAG_INDEX e =
      .ok i → Spec.get_total_balance Spec.P (view st) i = .ok x →
    (G.previousTargetBalance st).val = x
  currentTargetBalance : ∀ e i x, Spec.get_current_epoch Spec.P (view st) = .ok e →
    Spec.get_unslashed_participating_indices Spec.P (view st) Spec.TIMELY_TARGET_FLAG_INDEX e =
      .ok i → Spec.get_total_balance Spec.P (view st) i = .ok x →
    (G.currentTargetBalance st).val = x
  write : ∀ prev cur outcome t, Spec.get_previous_epoch Spec.P (view st) = .ok prev →
    Spec.get_current_epoch Spec.P (view st) = .ok cur →
    Spec.lhJustificationWrite Spec.P (view st) prev cur (absJustificationOutcome outcome) =
      .ok t →
    ∃ t', G.write st outcome = some t' ∧ view t' = t

/-- The composed justification returns the state of the model: when
`lhJustificationAndFinalization` returns `ok`, the Rust returns `Ok` with that state. -/
theorem justification_spec (G : JustificationGlue σ) (view : σ → Spec.BeaconState) (st : σ)
    (hL : JustificationLinks G view st)
    (hlen : (view st).justification_bits.length = Spec.JUSTIFICATION_BITS_LENGTH)
    (s1 : Spec.BeaconState) (h : Spec.lhJustificationAndFinalization Spec.P (view st) = .ok s1) :
    ∃ st1, justification G st = ok (some st1) ∧ view st1 = s1 := by
  obtain ⟨b0, b1, b2, b3, hbits⟩ : ∃ b0 b1 b2 b3,
      (view st).justification_bits = [b0, b1, b2, b3] := by
    match hb : (view st).justification_bits, hlen with
    | [b0, b1, b2, b3], _ => exact ⟨b0, b1, b2, b3, rfl⟩
  unfold Spec.lhJustificationAndFinalization at h
  rw [if_neg (by rw [hlen]; exact not_not.mpr rfl)] at h
  obtain ⟨cur, hcur, h⟩ := Spec.specM_bind_ok h
  unfold justification
  rw [hL.early cur hcur]
  simp only at h
  by_cases hc : cur ≤ Spec.GENESIS_EPOCH + 1
  · rw [if_pos hc] at h
    cases h
    exact ⟨st, by simp [hc], rfl⟩
  rw [if_neg hc] at h
  simp only [hc, decide_false, Bool.false_eq_true, if_false]
  simp only [pure_bind] at h
  obtain ⟨prev, hprev, h⟩ := Spec.specM_bind_ok h
  obtain ⟨pi, hpi, h⟩ := Spec.specM_bind_ok h
  obtain ⟨cur', hcur', h⟩ := Spec.specM_bind_ok h
  rw [hcur] at hcur'
  cases hcur'
  obtain ⟨ci, hci, h⟩ := Spec.specM_bind_ok h
  obtain ⟨tab, htab, h⟩ := Spec.specM_bind_ok h
  obtain ⟨px, hpx, h⟩ := Spec.specM_bind_ok h
  obtain ⟨cx, hcx, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lhWeighJustificationAndFinalization_eq, hprev, hcur, hbits] at h
  simp only [Spec.listGet, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.getElem?_cons_succ, List.getElem?_cons_zero] at h
  obtain ⟨r, hr, habs⟩ := spec_imp_exists (weigh_justification_equiv (G.currentEpoch st)
    (G.previousJustifiedEpoch st) (G.currentJustifiedEpoch st) (G.bits st)
    (G.totalActiveBalance st) (G.previousTargetBalance st) (G.currentTargetBalance st))
  rw [hL.currentEpoch cur hcur, hL.previousJustifiedEpoch, hL.currentJustifiedEpoch,
    hL.bits b0 b1 b2 b3 hbits, hL.totalActiveBalance tab htab,
    hL.previousTargetBalance prev pi px hprev hpi hpx,
    hL.currentTargetBalance cur ci cx hcur hci hcx] at habs
  rw [hr]
  simp only [bind_tc_ok]
  rw [← habs] at h
  cases r with
  | Err e => cases h
  | Ok out =>
    obtain ⟨t', hw, hv⟩ := hL.write prev cur out s1 hprev hcur h
    exact ⟨t', by simp only [hw], hv⟩

end EpochProofs.Compose
