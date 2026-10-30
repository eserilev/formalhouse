import EpochProofs.Compose.Justification
import EpochProofs.Compose.SinglePass
import EpochProofs.Compose.Committees
import EpochProofs.Compose.Tail

/-!
# The Gloas epoch, composed from the translated functions

`epoch` is Lighthouse's Gloas `process_epoch` (`altair.rs` with `process_epoch_single_pass`) as
one Lean function: the calls of the translated functions of `Generated.lean`, in Lighthouse's
order, joined by the untranslated glue (`EpochGlue`). `epoch_spec` shows that, under the trusted
facts about the glue (`EpochLinks`), `epoch` returns `Ok` with the state of the model
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

/-- Lighthouse's Gloas `process_epoch`, as the calls of the translated functions joined by the
glue `G`: justification and finalization, the single pass (the loop, the deposits, the
consolidations, the builder payments), the proposer lookahead, the PTC window, then the resets,
the historical summaries, the participation rotation and the sync committee update. `none`: the
Rust returns an error. -/
def epoch (G : EpochGlue σ E) (st : σ) : Result (Option σ) := do
  let r ← justification G.justification st
  match r with
  | none => ok none
  | some st1 =>
  let r ← singlePass G.singlePass G.payments st1
  match r with
  | none => ok none
  | some st2 =>
  let r ← lookahead G.lookahead st2
  match r with
  | none => ok none
  | some st3 =>
  let r ← ptcWindow G.lookahead G.ptc st3
  match r with
  | none => ok none
  | some st4 => tail G.tail st4

variable [Spec.PresetCfg]

/-- The trusted facts about the glue `G` with input `st`. The facts about the reads of the single
pass and N1 are stated at the states where the Rust makes these reads. -/
structure EpochLinks (G : EpochGlue σ E) (o : Spec.Oracle) (view : σ → Spec.BeaconState)
    (st : σ) : Prop where
  justification : JustificationLinks G.justification view st
  singlePass : ∀ st1, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    SinglePassLinks G.singlePass o view st1 id ∧ PaymentsLinks G.payments view st1
  /-- `registry_constants` for Gloas. -/
  registryConstants : ConstantsMatch Spec.P G.singlePass.registryConstants
  lookahead : LookaheadLinks G.lookahead o view
  proposerIndices : GloasProposerIndices G.lookahead view
  ptc : PtcLinks G.lookahead G.ptc o view
  tail : TailLinks G.tail o view
  /-- N1, at the three shuffles of the epoch. -/
  lookaheadN1 : ∀ st1 st2, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    EpochProofs.Compose.singlePass G.singlePass G.payments st1 = ok (some st2) → LookaheadN1 G.lookahead st2
  ptcN1 : ∀ st1 st2 st3, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    EpochProofs.Compose.singlePass G.singlePass G.payments st1 = ok (some st2) →
    EpochProofs.Compose.lookahead G.lookahead st2 = ok (some st3) → PtcN1 G.ptc st3
  syncN1 : ∀ st1 st2 st3 st4 st5, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    EpochProofs.Compose.singlePass G.singlePass G.payments st1 = ok (some st2) →
    EpochProofs.Compose.lookahead G.lookahead st2 = ok (some st3) → ptcWindow G.lookahead G.ptc st3 = ok (some st4) →
    resets G.tail st4 = ok (some st5) → SyncN1 G.tail st5

/-- The composed Gloas epoch returns the state of the model: when `process_epoch_lighthouse`
returns `ok`, the Rust returns `Ok` with a state whose view is the model's. The facts about the
input are the vector lengths and the slot bound. -/
theorem epoch_spec [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] (G : EpochGlue σ E)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (st : σ) (hL : EpochLinks G o view st)
    (hslot : (view st).slot < 2 ^ 64) (hvec : (view st).VectorLengths Spec.P)
    (s' : Spec.BeaconState) (h : Spec.process_epoch_lighthouse o (view st) = .ok s') :
    ∃ st', epoch G st = ok (some st') ∧ view st' = s' := by
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
    (hL.singlePass st1 hj).1 (hL.singlePass st1 hj).2 hL.registryConstants
    (by rw [hv1, hs1]; exact hslot) (by rw [hv1, hs1]; exact hbpp) T (by rw [hv1]; exact hT)
  obtain ⟨hTpl, hTptc⟩ := Spec.lhSinglePass_keep o s1 T hT
  obtain ⟨st3, hla, hv3⟩ := lookahead_spec G.lookahead o view hL.lookahead hL.proposerIndices st2
    (hL.lookaheadN1 st1 st2 hj hsp) (by rw [hv2, hTpl, hs1]; exact hpl) t1
    (by rw [hv2]; exact ht1)
  have ht1ptc : t1.ptc_window = T.ptc_window := by
    obtain ⟨l, -, hl⟩ := Spec.map_ok_inv ((Spec.process_proposer_lookahead_eq o T).symm.trans ht1)
    rw [hl]; rfl
  obtain ⟨st4, hpw, hv4⟩ := ptcWindow_spec G.lookahead G.ptc o view hL.lookahead hL.ptc st3
    (hL.ptcN1 st1 st2 st3 hj hsp hla) (by rw [hv3, ht1ptc, hTptc, hs1]; exact hptc) t2
    (by rw [hv3]; exact ht2)
  obtain ⟨st5, ht, hv5⟩ := tail_spec G.tail o view hL.tail st4
    (fun st5 hr => hL.syncN1 st1 st2 st3 st4 st5 hj hsp hla hpw hr) s' (by rw [hv4]; exact h)
  refine ⟨st5, ?_, hv5⟩
  unfold epoch
  rw [hj]
  simp only [bind_tc_ok]
  rw [hsp]
  simp only [bind_tc_ok]
  rw [hla]
  simp only [bind_tc_ok]
  rw [hpw]
  simp only [bind_tc_ok]
  exact ht

end EpochProofs.Compose
