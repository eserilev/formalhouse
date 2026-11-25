import EpochProofs.AeneasCompat
import EpochProofs.TranslatedSteps.Justification
import EpochProofs.LighthouseModel.Order

/-!
# Justification and finalization, composed from the translated function

`justification` is `process_justification_and_finalization` of `altair.rs` with
`weigh_justification_and_finalization.rs`: the reads of the epochs, the bits and the balances,
the translated `weigh_justification`, and the checkpoint and bit writes. The reads and the writes
are untranslated code (`UntranslatedJustification`), each with the fact that links it to the spec
(`UntranslatedJustificationFacts`). `translatedJustification_matches_model` shows that it returns
the state of the model `lighthouseJustificationAndFinalization`.
-/

namespace EpochProofs.Spec

/-- The writes of `weigh_justification_and_finalization.rs` after `weigh_justification`: the
checkpoints, the block roots they read, and the bits. -/
def lighthouseJustificationWrite (p : Preset) (s : BeaconState)
    (previous_epoch current_epoch : Epoch)
    (outcome : LighthouseJustificationOutcome) : SpecM BeaconState := do
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

theorem lighthouseWeighJustificationAndFinalization_eq (p : Preset) (s : BeaconState)
    (tab x y : Gwei) :
    lighthouseWeighJustificationAndFinalization p s tab x y = (do
      let previous_epoch ← get_previous_epoch p s
      let current_epoch ← get_current_epoch p s
      let bits : LighthouseJustificationBits :=
        { bit0 := ← listGet s.justification_bits 0, bit1 := ← listGet s.justification_bits 1,
          bit2 := ← listGet s.justification_bits 2, bit3 := ← listGet s.justification_bits 3 }
      let outcome ← lighthouseWeighJustification current_epoch s.previous_justified_checkpoint.epoch
        s.current_justified_checkpoint.epoch bits tab x y
      lighthouseJustificationWrite p s previous_epoch current_epoch outcome) := rfl

end EpochProofs.Spec

namespace EpochProofs.TranslatedEpoch

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open per_epoch_processing.justification

/-- The untranslated Rust of `process_justification_and_finalization`: the genesis check, the
reads passed to `weigh_justification`, and the writes of its outcome. -/
structure UntranslatedJustification (RustState : Type) where
  /-- `state.current_epoch() <= genesis_epoch + 1`. -/
  skippedNearGenesis : RustState → Bool
  currentEpoch : RustState → U64
  previousJustifiedEpoch : RustState → U64
  currentJustifiedEpoch : RustState → U64
  bits : RustState → JustificationBits
  /-- The total active balance and the two target balances of the caches. -/
  totalActiveBalance : RustState → U64
  previousTargetBalance : RustState → U64
  currentTargetBalance : RustState → U64
  /-- The checkpoint and bit writes. `none`: a block root read fails. -/
  writeOutcome : RustState → JustificationOutcome → Option RustState

variable {RustState : Type}

/-- `process_justification_and_finalization`, as the call of the translated
`weigh_justification` joined by the untranslated code. `none`: the Rust returns an error. -/
def translatedJustification (code : UntranslatedJustification RustState)
    (rustState : RustState) : Result (Option RustState) :=
  if code.skippedNearGenesis rustState then ok (some rustState) else do
  let r ← weigh_justification (code.currentEpoch rustState) (code.previousJustifiedEpoch rustState)
    (code.currentJustifiedEpoch rustState) (code.bits rustState) (code.totalActiveBalance rustState)
    (code.previousTargetBalance rustState) (code.currentTargetBalance rustState)
  match r with
  | .Err _ => ok none
  | .Ok outcome => ok (code.writeOutcome rustState outcome)

variable [Spec.CurrentPreset]

/-- The trusted facts about the untranslated code at the state `rustState`: each read is the spec
value, and the writes are the spec writes (`lighthouseJustificationWrite`). The balances are cache
reads. -/
structure UntranslatedJustificationFacts (code : UntranslatedJustification RustState)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState) :
    Prop where
  /-- The genesis check is the spec check. -/
  skippedNearGenesis : ∀ current, Spec.get_current_epoch Spec.P (rustStateToSpec rustState) =
    .ok current →
    code.skippedNearGenesis rustState = decide (current ≤ Spec.GENESIS_EPOCH + 1)
  currentEpoch : ∀ current, Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current
    →
    (code.currentEpoch rustState).val = current
  previousJustifiedEpoch :
    (code.previousJustifiedEpoch rustState).val =
      (rustStateToSpec rustState).previous_justified_checkpoint.epoch
  currentJustifiedEpoch :
    (code.currentJustifiedEpoch rustState).val =
      (rustStateToSpec rustState).current_justified_checkpoint.epoch
  /-- The justification bits. -/
  bits : ∀ b0 b1 b2 b3, (rustStateToSpec rustState).justification_bits = [b0, b1, b2, b3] →
    justificationBitsToSpec (code.bits rustState) = ⟨b0, b1, b2, b3⟩
  /-- The three balances are cache reads. -/
  totalActiveBalance : ∀ total, Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) =
    .ok total →
    (code.totalActiveBalance rustState).val = total
  previousTargetBalance : ∀ e i x, Spec.get_previous_epoch Spec.P (rustStateToSpec rustState) =
    .ok e →
    Spec.get_unslashed_participating_indices Spec.P (rustStateToSpec rustState)
      Spec.TIMELY_TARGET_FLAG_INDEX e =
      .ok i → Spec.get_total_balance Spec.P (rustStateToSpec rustState) i = .ok x →
    (code.previousTargetBalance rustState).val = x
  currentTargetBalance : ∀ e i x, Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok e
    →
    Spec.get_unslashed_participating_indices Spec.P (rustStateToSpec rustState)
      Spec.TIMELY_TARGET_FLAG_INDEX e =
      .ok i → Spec.get_total_balance Spec.P (rustStateToSpec rustState) i = .ok x →
    (code.currentTargetBalance rustState).val = x
  /-- The writes are the spec writes. -/
  writeOutcome : ∀ prev current outcome t,
    Spec.get_previous_epoch Spec.P (rustStateToSpec rustState) = .ok prev →
    Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current →
    Spec.lighthouseJustificationWrite Spec.P (rustStateToSpec rustState) prev current
      (justificationOutcomeToSpec outcome) =
      .ok t →
    ∃ t', code.writeOutcome rustState outcome = some t' ∧ rustStateToSpec t' = t

/-- The composed justification returns the state of the model: when
`lighthouseJustificationAndFinalization` returns `ok`, the Rust returns `Ok` with that state. -/
theorem translatedJustification_matches_model (code : UntranslatedJustification RustState)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedJustificationFacts code rustStateToSpec rustState)
    (hlen : (rustStateToSpec rustState).justification_bits.length = Spec.JUSTIFICATION_BITS_LENGTH)
    (s1 : Spec.BeaconState) (h : Spec.lighthouseJustificationAndFinalization Spec.P
    (rustStateToSpec rustState) = .ok s1) :
    ∃ rustState1, translatedJustification code rustState = ok (some rustState1) ∧
      rustStateToSpec rustState1 = s1 := by
  obtain ⟨b0, b1, b2, b3, hbits⟩ : ∃ b0 b1 b2 b3,
      (rustStateToSpec rustState).justification_bits = [b0, b1, b2, b3] := by
    match hb : (rustStateToSpec rustState).justification_bits, hlen with
    | [b0, b1, b2, b3], _ => exact ⟨b0, b1, b2, b3, rfl⟩
  unfold Spec.lighthouseJustificationAndFinalization at h
  rw [if_neg (by rw [hlen]; exact not_not.mpr rfl)] at h
  obtain ⟨current, hcur, h⟩ := Spec.specM_bind_ok h
  unfold translatedJustification
  rw [hL.skippedNearGenesis current hcur]
  by_cases hc : current ≤ Spec.GENESIS_EPOCH + 1
  · rw [if_pos hc] at h
    cases h
    exact ⟨rustState, by simp [hc], rfl⟩
  rw [if_neg hc] at h
  simp only [hc, decide_false, Bool.false_eq_true, if_false]
  obtain ⟨prev, hprev, h⟩ := Spec.specM_bind_ok h
  obtain ⟨pi, hpi, h⟩ := Spec.specM_bind_ok h
  obtain ⟨current', hcur', h⟩ := Spec.specM_bind_ok h
  rw [hcur] at hcur'
  cases hcur'
  obtain ⟨ci, hci, h⟩ := Spec.specM_bind_ok h
  obtain ⟨total, htab, h⟩ := Spec.specM_bind_ok h
  obtain ⟨px, hpx, h⟩ := Spec.specM_bind_ok h
  obtain ⟨cx, hcx, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lighthouseWeighJustificationAndFinalization_eq, hprev, hcur, hbits] at h
  simp only [Spec.listGet, Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.getElem?_cons_succ, List.getElem?_cons_zero] at h
  obtain ⟨r, hr, habs⟩ := spec_imp_exists (weigh_justification_equiv (code.currentEpoch rustState)
    (code.previousJustifiedEpoch rustState) (code.currentJustifiedEpoch rustState)
      (code.bits rustState)
    (code.totalActiveBalance rustState) (code.previousTargetBalance rustState)
      (code.currentTargetBalance rustState))
  rw [hL.currentEpoch current hcur, hL.previousJustifiedEpoch, hL.currentJustifiedEpoch,
    hL.bits b0 b1 b2 b3 hbits, hL.totalActiveBalance total htab,
    hL.previousTargetBalance prev pi px hprev hpi hpx,
    hL.currentTargetBalance current ci cx hcur hci hcx] at habs
  rw [hr]
  simp only [bind_tc_ok]
  rw [← habs] at h
  cases r with
  | Err e => cases h
  | Ok out =>
    obtain ⟨t', hw, hv⟩ := hL.writeOutcome prev current out s1 hprev hcur h
    exact ⟨t', by simp only [hw], hv⟩

end EpochProofs.TranslatedEpoch
