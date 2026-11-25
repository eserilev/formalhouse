import EpochProofs.Compose.Justification
import EpochProofs.Compose.SinglePass
import EpochProofs.Compose.Committees
import EpochProofs.Compose.Tail

/-!
# The Gloas epoch, composed from the translated functions

`epoch` is Lighthouse's Gloas `process_epoch` (`altair.rs` with `process_epoch_single_pass`) as
one Lean function: the calls of the translated functions of `Generated.lean`, in Lighthouse's
order, joined by the untranslated code (`UntranslatedEpochCode`). `translatedEpoch_matches_model`
shows that, under the trusted facts about the untranslated code (`UntranslatedEpochFacts`), `epoch`
returns `Ok` with the state of the model `process_epoch_lighthouse` whenever the model returns `ok`.

The cache builds at the start of `process_epoch` and `process_epoch_single_pass`, and the cache
writes that do not change the state's fields (`set_total_active_balance`, the epoch cache, the
lookahead committee cache, `advance_caches`, the progressive balances update), are not in
`epoch`. They can only make the Rust return an error.
-/

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The untranslated Rust of the Gloas epoch, by step. -/
structure UntranslatedEpochCode (RustState RustError : Type) where
  justification : UntranslatedJustification RustState
  singlePass : UntranslatedSinglePass RustState RustError
  builderPayments : UntranslatedBuilderPayments RustState RustError
  lookahead : UntranslatedLookahead RustState
  ptcWindow : UntranslatedPtcWindow RustState RustError
  endOfEpoch : UntranslatedEndOfEpoch RustState

variable {RustState RustError : Type}

/-! ## The epoch

`OptionT Result` stops at the first `none`. `none` means that the Rust returns an error. -/

/-- The Rust state after justification and finalization. -/
def afterJustification (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState :=
  OptionT.mk (translatedJustification code.justification rustState)

/-- The Rust state after the single pass: the loop, the deposits, the consolidations and the
builder payments. -/
def afterSinglePass (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState1 ← afterJustification code rustState
  OptionT.mk (translatedSinglePass code.singlePass code.builderPayments rustState1)

/-- The Rust state after the proposer lookahead. -/
def afterLookahead (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState2 ← afterSinglePass code rustState
  OptionT.mk (translatedLookahead code.lookahead rustState2)

/-- The Rust state after the PTC window. -/
def afterPtcWindow (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState3 ← afterLookahead code rustState
  OptionT.mk (translatedPtcWindow code.lookahead code.ptcWindow rustState3)

/-- The Rust state after the resets, the historical summaries and the participation rotation. -/
def afterResets (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState4 ← afterPtcWindow code rustState
  OptionT.mk (translatedResets code.endOfEpoch rustState4)

/-- Lighthouse's Gloas `process_epoch`, as the calls of the translated functions joined by the
untranslated code. -/
def translatedEpoch (code : UntranslatedEpochCode RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState4 ← afterPtcWindow code rustState
  OptionT.mk (translatedEndOfEpoch code.endOfEpoch rustState4)

/-- Two steps that both return a state. -/
theorem run_bind_ok {α β : Type} {x : OptionT Result α} {f : α → OptionT Result β} {a : α} {b : β}
    (hx : x.run = ok (some a)) (hf : (f a).run = ok (some b)) : (x >>= f).run = ok (some b) := by
  rw [OptionT.run_bind, hx]
  simpa [Option.elimM] using hf

variable [Spec.CurrentPreset]

/-- What the proofs assume about the untranslated code of the epoch with input `rustState`. The
facts that read a state in the middle of the epoch are stated at that state. -/
structure UntranslatedEpochFacts (code : UntranslatedEpochCode RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (rustState : RustState) : Prop where
  /-- Justification and finalization. -/
  justification : UntranslatedJustificationFacts code.justification rustStateToSpec rustState
  /-- The single pass, at the state after justification. -/
  singlePass : ∀ rustState1, (afterJustification code rustState).run = ok (some rustState1) →
    UntranslatedSinglePassFacts code.singlePass oracle rustStateToSpec rustState1 id
  /-- The builder payments, with the input of the single pass. -/
  builderPayments : ∀ rustState1, (afterJustification code rustState).run = ok (some rustState1) →
    UntranslatedBuilderPaymentsFacts code.builderPayments rustStateToSpec rustState1
  /-- `registry_constants` for Gloas. -/
  registryConstants : RegistryConstantsMatchGloas Spec.P code.singlePass.registryConstants
  /-- The proposer lookahead. -/
  lookahead : UntranslatedLookaheadFacts code.lookahead oracle rustStateToSpec
  /-- The proposer candidates are the active, unslashed validators. -/
  proposerIndices : ProposerCandidatesGloas code.lookahead rustStateToSpec
  /-- The PTC window. -/
  ptcWindow : UntranslatedPtcWindowFacts code.lookahead code.ptcWindow oracle rustStateToSpec
  /-- The resets, the historical summaries, the participation rotation and the sync committees. -/
  endOfEpoch : UntranslatedEndOfEpochFacts code.endOfEpoch oracle rustStateToSpec
  /-- At most `2^24` proposer candidates enter the shuffle. -/
  proposersFitShuffle : ∀ rustState2, (afterSinglePass code rustState).run = ok (some rustState2) →
    (code.lookahead.proposerIndices rustState2).val.length ≤ 2 ^ 24
  /-- At most `2^24` validators of each slot enter the PTC selection. -/
  ptcCommitteesFitSelection : ∀ rustState3, (afterLookahead code rustState).run =
    ok (some rustState3) →
    ∀ k (hk : k < (code.ptcWindow.committees rustState3).val.length),
      ((code.ptcWindow.committees rustState3).val[k]).val.length ≤ 2 ^ 24
  /-- At most `2^24` sync committee candidates enter the shuffle. -/
  syncCandidatesFitShuffle : ∀ rustState5, (afterResets code rustState).run = ok (some rustState5) →
    ∀ rustState6, code.endOfEpoch.writeCurrentSync rustState5 = some rustState6 →
      (code.endOfEpoch.syncIndices rustState6).val.length ≤ 2 ^ 24

/-- The composed Gloas epoch returns the state of the model: when `process_epoch_lighthouse`
returns `ok`, the Rust returns `Ok` with a state whose spec state is the model's. The facts
about the input are the vector lengths and the slot bound. -/
theorem translatedEpoch_matches_model [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds]
    (code : UntranslatedEpochCode RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedEpochFacts code oracle rustStateToSpec rustState)
    (hslot : (rustStateToSpec rustState).slot < 2 ^ 64)
    (hvec : (rustStateToSpec rustState).VectorLengths Spec.P)
    (s' : Spec.BeaconState) (h : Spec.process_epoch_lighthouse oracle (rustStateToSpec rustState) =
      .ok s') :
    ∃ rustState', (translatedEpoch code rustState).run = ok (some rustState') ∧
      rustStateToSpec rustState' = s' := by
  obtain ⟨-, -, -, -, hjb, -, -, hpl, -, hbpp, hptc, -⟩ := hvec
  unfold Spec.process_epoch_lighthouse at h
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lighthouseSinglePassThen_order_eq] at h
  obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lighthouseStepsAfterPayments_eq] at h
  obtain ⟨t1, ht1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t2, ht2, h⟩ := Spec.specM_bind_ok h
  -- Justification and finalization writes only the checkpoints and the bits.
  obtain ⟨a, b, c, d, hs1⟩ := Spec.process_justification_and_finalization_shape _ _ _
    ((Spec.lighthouseJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1)
  obtain ⟨rustState1, hj, hv1⟩ :=
    translatedJustification_matches_model code.justification rustStateToSpec rustState
    hL.justification hjb s1 h1
  obtain ⟨rustState2, hsp, hv2⟩ :=
    translatedSinglePass_matches_model code.singlePass code.builderPayments oracle rustStateToSpec
    rustState1
    (hL.singlePass rustState1 hj) (hL.builderPayments rustState1 hj) hL.registryConstants
    (by rw [hv1, hs1]; exact hslot) (by rw [hv1, hs1]; exact hbpp) T (by rw [hv1]; exact hT)
  have r2 : (afterSinglePass code rustState).run = ok (some rustState2) := run_bind_ok hj hsp
  obtain ⟨hTpl, hTptc⟩ := Spec.lighthouseSinglePass_keep oracle s1 T hT
  obtain ⟨rustState3, hla, hv3⟩ :=
    translatedLookahead_matches_model code.lookahead oracle rustStateToSpec hL.lookahead
    hL.proposerIndices rustState2
    (hL.proposersFitShuffle rustState2 r2) (by rw [hv2, hTpl, hs1]; exact hpl) t1
    (by rw [hv2]; exact ht1)
  have r3 : (afterLookahead code rustState).run = ok (some rustState3) := run_bind_ok r2 hla
  have ht1ptc : t1.ptc_window = T.ptc_window := by
    obtain ⟨l, -, hl⟩ := Spec.map_ok_inv
      ((Spec.process_proposer_lookahead_eq oracle T).symm.trans ht1)
    rw [hl]; rfl
  obtain ⟨rustState4, hpw, hv4⟩ :=
    translatedPtcWindow_matches_model code.lookahead code.ptcWindow oracle rustStateToSpec
    hL.lookahead hL.ptcWindow rustState3
    (hL.ptcCommitteesFitSelection rustState3 r3) (by rw [hv3, ht1ptc, hTptc, hs1]; exact hptc) t2
    (by rw [hv3]; exact ht2)
  have r4 : (afterPtcWindow code rustState).run = ok (some rustState4) := run_bind_ok r3 hpw
  obtain ⟨rustState5, ht, hv5⟩ :=
    translatedEndOfEpoch_matches_model code.endOfEpoch oracle rustStateToSpec hL.endOfEpoch
    rustState4
    (fun rustState5 hr => hL.syncCandidatesFitShuffle rustState5 (run_bind_ok r4 hr)) s'
      (by rw [hv4]; exact h)
  exact ⟨rustState5, run_bind_ok r4 ht, hv5⟩

end EpochProofs.Compose
