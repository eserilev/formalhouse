import EpochProofs.Compose.Justification
import EpochProofs.Compose.SinglePass
import EpochProofs.Compose.Committees
import EpochProofs.Compose.Tail

/-!
# The Gloas epoch, composed from the translated functions

`epoch` is Lighthouse's Gloas `process_epoch` (`altair.rs` with `process_epoch_single_pass`) as
one Lean function: the calls of the translated functions of `Generated.lean`, in Lighthouse's
order, joined by the untranslated code (`EpochGlue`). `epoch_spec` shows that, under the trusted
facts about the untranslated code (`EpochLinks`), `epoch` returns `Ok` with the state of the model
`process_epoch_lighthouse` whenever the model returns `ok`.

The cache builds at the start of `process_epoch` and `process_epoch_single_pass`, and the cache
writes that do not change the state's fields (`set_total_active_balance`, the epoch cache, the
lookahead committee cache, `advance_caches`, the progressive balances update), are not in
`epoch`. They can only make the Rust return an error.
-/

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The untranslated Rust of the Gloas epoch, by step. -/
structure EpochGlue (σ E : Type) where
  justification : JustificationGlue σ
  singlePass : SinglePassGlue σ E
  payments : PaymentsGlue σ E
  lookahead : LookaheadGlue σ
  ptc : PtcGlue σ E
  tail : TailGlue σ

variable {σ E : Type}

/-! ## The epoch

`OptionT Result` stops at the first `none`. `none` means that the Rust returns an error. -/

/-- The Rust state after justification and finalization. -/
def afterJustification (G : EpochGlue σ E) (st : σ) : OptionT Result σ :=
  OptionT.mk (justification G.justification st)

/-- The Rust state after the single pass: the loop, the deposits, the consolidations and the
builder payments. -/
def afterSinglePass (G : EpochGlue σ E) (st : σ) : OptionT Result σ := do
  let st1 ← afterJustification G st
  OptionT.mk (singlePass G.singlePass G.payments st1)

/-- The Rust state after the proposer lookahead. -/
def afterLookahead (G : EpochGlue σ E) (st : σ) : OptionT Result σ := do
  let st2 ← afterSinglePass G st
  OptionT.mk (lookahead G.lookahead st2)

/-- The Rust state after the PTC window. -/
def afterPtcWindow (G : EpochGlue σ E) (st : σ) : OptionT Result σ := do
  let st3 ← afterLookahead G st
  OptionT.mk (ptcWindow G.lookahead G.ptc st3)

/-- The Rust state after the resets, the historical summaries and the participation rotation. -/
def afterResets (G : EpochGlue σ E) (st : σ) : OptionT Result σ := do
  let st4 ← afterPtcWindow G st
  OptionT.mk (resets G.tail st4)

/-- Lighthouse's Gloas `process_epoch`, as the calls of the translated functions joined by the
untranslated code `G`. -/
def epoch (G : EpochGlue σ E) (st : σ) : OptionT Result σ := do
  let st4 ← afterPtcWindow G st
  OptionT.mk (tail G.tail st4)

/-- Two steps that both return a state. -/
theorem run_bind_ok {α β : Type} {x : OptionT Result α} {f : α → OptionT Result β} {a : α} {b : β}
    (hx : x.run = ok (some a)) (hf : (f a).run = ok (some b)) : (x >>= f).run = ok (some b) := by
  rw [OptionT.run_bind, hx]
  simpa [Option.elimM] using hf

variable [Spec.CurrentPreset]

/-- What the proofs assume about the untranslated code `G` of the epoch with input `st`. The facts
that read a state in the middle of the epoch are stated at that state. -/
structure EpochLinks (G : EpochGlue σ E) (o : Spec.Oracle) (view : σ → Spec.BeaconState)
    (st : σ) : Prop where
  /-- Justification and finalization. -/
  justification : JustificationLinks G.justification view st
  /-- The single pass, at the state after justification. -/
  singlePass : ∀ st1, (afterJustification G st).run = ok (some st1) →
    SinglePassLinks G.singlePass o view st1 id
  /-- The builder payments, with the input of the single pass. -/
  payments : ∀ st1, (afterJustification G st).run = ok (some st1) →
    PaymentsLinks G.payments view st1
  /-- `registry_constants` for Gloas. -/
  registryConstants : ConstantsMatch Spec.P G.singlePass.registryConstants
  /-- The proposer lookahead. -/
  lookahead : LookaheadLinks G.lookahead o view
  /-- The proposer candidates are the active, unslashed validators. -/
  proposerIndices : GloasProposerIndices G.lookahead view
  /-- The PTC window. -/
  ptc : PtcLinks G.lookahead G.ptc o view
  /-- The resets, the historical summaries, the participation rotation and the sync committees. -/
  tail : TailLinks G.tail o view
  /-- At most `2^24` proposer candidates enter the shuffle. -/
  proposersFitShuffle : ∀ st2, (afterSinglePass G st).run = ok (some st2) →
    (G.lookahead.proposerIndices st2).val.length ≤ 2 ^ 24
  /-- At most `2^24` validators of each slot enter the PTC selection. -/
  ptcCommitteesFitSelection : ∀ st3, (afterLookahead G st).run = ok (some st3) →
    ∀ k (hk : k < (G.ptc.committees st3).val.length),
      ((G.ptc.committees st3).val[k]).val.length ≤ 2 ^ 24
  /-- At most `2^24` sync committee candidates enter the shuffle. -/
  syncCandidatesFitShuffle : ∀ st5, (afterResets G st).run = ok (some st5) →
    ∀ st6, G.tail.writeCurrentSync st5 = some st6 →
      (G.tail.syncIndices st6).val.length ≤ 2 ^ 24

/-- The composed Gloas epoch returns the state of the model: when `process_epoch_lighthouse`
returns `ok`, the Rust returns `Ok` with a state whose view is the model's. The facts about the
input are the vector lengths and the slot bound. -/
theorem epoch_spec [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds] (G : EpochGlue σ E)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (st : σ) (hL : EpochLinks G o view st)
    (hslot : (view st).slot < 2 ^ 64) (hvec : (view st).VectorLengths Spec.P)
    (s' : Spec.BeaconState) (h : Spec.process_epoch_lighthouse o (view st) = .ok s') :
    ∃ st', (epoch G st).run = ok (some st') ∧ view st' = s' := by
  obtain ⟨-, -, -, -, hjb, -, -, hpl, -, hbpp, hptc, -⟩ := hvec
  unfold Spec.process_epoch_lighthouse at h
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lhFullTailWith_order_eq] at h
  obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lhRestOrder_eq] at h
  obtain ⟨t1, ht1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t2, ht2, h⟩ := Spec.specM_bind_ok h
  -- Justification and finalization writes only the checkpoints and the bits.
  obtain ⟨a, b, c, d, hs1⟩ := Spec.process_justification_and_finalization_shape _ _ _
    ((Spec.lhJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1)
  obtain ⟨st1, hj, hv1⟩ := justification_spec G.justification view st hL.justification hjb s1 h1
  obtain ⟨st2, hsp, hv2⟩ := singlePass_spec G.singlePass G.payments o view st1
    (hL.singlePass st1 hj) (hL.payments st1 hj) hL.registryConstants
    (by rw [hv1, hs1]; exact hslot) (by rw [hv1, hs1]; exact hbpp) T (by rw [hv1]; exact hT)
  have r2 : (afterSinglePass G st).run = ok (some st2) := run_bind_ok hj hsp
  obtain ⟨hTpl, hTptc⟩ := Spec.lhSinglePass_keep o s1 T hT
  obtain ⟨st3, hla, hv3⟩ := lookahead_spec G.lookahead o view hL.lookahead hL.proposerIndices st2
    (hL.proposersFitShuffle st2 r2) (by rw [hv2, hTpl, hs1]; exact hpl) t1
    (by rw [hv2]; exact ht1)
  have r3 : (afterLookahead G st).run = ok (some st3) := run_bind_ok r2 hla
  have ht1ptc : t1.ptc_window = T.ptc_window := by
    obtain ⟨l, -, hl⟩ := Spec.map_ok_inv ((Spec.process_proposer_lookahead_eq o T).symm.trans ht1)
    rw [hl]; rfl
  obtain ⟨st4, hpw, hv4⟩ := ptcWindow_spec G.lookahead G.ptc o view hL.lookahead hL.ptc st3
    (hL.ptcCommitteesFitSelection st3 r3) (by rw [hv3, ht1ptc, hTptc, hs1]; exact hptc) t2
    (by rw [hv3]; exact ht2)
  have r4 : (afterPtcWindow G st).run = ok (some st4) := run_bind_ok r3 hpw
  obtain ⟨st5, ht, hv5⟩ := tail_spec G.tail o view hL.tail st4
    (fun st5 hr => hL.syncCandidatesFitShuffle st5 (run_bind_ok r4 hr)) s' (by rw [hv4]; exact h)
  exact ⟨st5, run_bind_ok r4 ht, hv5⟩

end EpochProofs.Compose
