import EpochProofs.Compose.Epoch
import EpochProofs.Equiv.FuluRegistry
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder

/-!
# The Fulu epoch, composed from the translated functions

`epochFulu` is Lighthouse's Fulu `process_epoch`: the Gloas composition without the builder
payments and the PTC window, with the Fulu registry constants and the Fulu proposer candidates
(every active validator). `epochFulu_spec` shows that, under `EpochLinksFulu`, it returns the
state of the model `process_epoch_lh_order_fulu` whenever the model returns `ok`.
-/

namespace EpochProofs.Spec

/-- The Lighthouse Fulu model from the start of the single pass to the effective balance updates
after the consolidations. -/
def lhSinglePassFulu [PresetCfg] [FuluCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState :=
  lhFullTailWithFulu (fun s _ plan x => lhMidCore o s plan (s.withRowsChurn x.1 x.2)) s

theorem lhFullTailWithFulu_order_eq [PresetCfg] [FuluCfg] (o : Oracle) (s : BeaconState) :
    lhFullTailWithFulu (lhAfterPassOrderFulu o) s = lhSinglePassFulu o s >>= lhRestOrderFulu o := by
  unfold lhSinglePassFulu lhFullTailWithFulu lhAfterPassOrderFulu lhMidFulu lhMidCore
  simp only [bind, Except.bind]
  repeat' split
  all_goals rfl

/-- The Fulu single pass does not write the proposer lookahead. -/
theorem lhSinglePassFulu_keep [PresetCfg] [FuluCfg] (o : Oracle) (s T : BeaconState)
    (h : lhSinglePassFulu o s = .ok T) : T.proposer_lookahead = s.proposer_lookahead := by
  unfold lhSinglePassFulu lhFullTailWithFulu at h
  obtain ⟨cur, -, h⟩ := specM_bind_ok h
  obtain ⟨tab, -, h⟩ := specM_bind_ok h
  obtain ⟨rctx, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨adj, per⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨plan, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨dn, up⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨x, -, h⟩ := specM_bind_ok h
  exact (lhMidCore_keep o s plan x T h).2.1

theorem lhRestOrderFulu_eq [PresetCfg] (o : Oracle) (t : BeaconState) :
    lhRestOrderFulu o t = process_proposer_lookahead_fulu P o t >>= lhTailOrder o := rfl

/-- `process_proposer_lookahead_fulu` keeps the length of the lookahead. -/
theorem process_proposer_lookahead_fulu_len (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead_fulu p o s = .ok s') :
    s'.proposer_lookahead.length = s.proposer_lookahead.length := by
  unfold process_proposer_lookahead_fulu at h
  simp only [glue_bind_ok_iff] at h
  obtain ⟨les, hles, ce, -, e1, -, e, -, props, hprops, hfin⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at hfin
  subst hfin
  have hrl : props.length = p.SLOTS_PER_EPOCH := by
    unfold get_beacon_proposer_indices_fulu compute_proposer_indices_fulu at hprops
    simp only [glue_bind_ok_iff] at hprops
    obtain ⟨seed, -, st, -, seeds, hseeds, h⟩ := hprops
    rw [mapM_length_ok _ _ _ h, mapM_length_ok _ _ _ hseeds, List.length_range]
  unfold uint64Sub at hles
  by_cases hle : p.SLOTS_PER_EPOCH ≤ s.proposer_lookahead.length
  · rw [if_pos hle] at hles
    simp only [pure, Except.pure, Except.ok.injEq] at hles
    subst hles
    simp only [List.length_append, List.length_take, List.length_drop, hrl]
    omega
  · rw [if_neg hle] at hles
    cases hles

/-- The start slot of the lookahead epoch computes when `process_proposer_lookahead_fulu`
succeeds. -/
theorem process_proposer_lookahead_fulu_start (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead_fulu p o s = .ok s') (ce : Nat)
    (hce : get_current_epoch p s = .ok ce) :
    ∃ n, compute_start_slot_at_epoch p (ce + p.MIN_SEED_LOOKAHEAD + 1) = .ok n := by
  unfold process_proposer_lookahead_fulu at h
  simp only [glue_bind_ok_iff] at h
  obtain ⟨les, -, ce', hce', e1, he1, e, he, props, hprops, -⟩ := h
  have hc : ce' = ce := by
    rw [get_current_epoch_ok_eq hce', get_current_epoch_ok_eq hce]
  subst hc
  rw [uint64Add_ok_sum he, uint64Add_ok_sum he1] at hprops
  unfold get_beacon_proposer_indices_fulu compute_proposer_indices_fulu at hprops
  simp only [glue_bind_ok_iff] at hprops
  obtain ⟨-, -, n, hn, -⟩ := hprops
  exact ⟨n, hn⟩

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open state_processing.per_epoch_processing.single_pass_step (ExitChurn StepContext)

/-- `rowsContract_stepSpec` with the Fulu step: under `RowsContract`, one `apply_step` call
runs `lhRowStepFull` with the registry total `fuluTab`. -/
theorem rowsContract_stepSpec_fulu {R E : Type} (inst : LhRegistryRows R E) (p : Spec.Preset)
    (f : Spec.FuluConfig) (hcompat : Spec.FuluCompat p f) (view : R → List Spec.Row)
    (inputsOf : Spec.Row → Spec.LhRowInputs) (hc : RowsContract inst p view inputsOf)
    (c : StepContext) (ctx : Spec.LhStepContext) (hcm : ContextMatches p c ctx)
    (downward upward : Spec.Uint64) (hdownward : c.downward_threshold.val = downward)
    (hupward : c.upward_threshold.val = upward)
    (k : per_epoch_processing.registry_update.RegistryConstants) (hk : ConstantsMatchBase p k)
    (hkf : FuluChurnMatch p f k) :
    StepSpec inst view (fun churn r => Spec.lhRowStepFull p
      { ctx with total_active_balance := Spec.fuluTab p f ctx.total_active_balance }
      downward upward (inputsOf r) churn r) c k := by
  intro s i ch r hr
  obtain ⟨lr, ri, hm, hi, hrun⟩ := hc.apply_step s i ch c k r hr
  have hi' : InputsMatches p ri { inputsOf r with base_reward := ri.base_reward.val } r :=
    ⟨rfl, hi.deposit, hi.in_consolidation, hi.effective_balance_limit⟩
  obtain ⟨res, hres, habs⟩ := spec_imp_exists (single_pass_step_equiv_fulu p f hcompat lr r hm ri _
    hi' ch c ctx hcm downward upward hdownward hupward k hk hkf)
  have hirr : Spec.lhRowStepFull p
      { ctx with total_active_balance := Spec.fuluTab p f ctx.total_active_balance }
      downward upward { inputsOf r with base_reward := ri.base_reward.val }
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r =
      Spec.lhRowStepFull p
      { ctx with total_active_balance := Spec.fuluTab p f ctx.total_active_balance }
      downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r := by
    rcases hi.base_reward with h | h
    · rw [h]
    · rw [hcm.previous_epoch] at h
      exact lhRowStepFull_base_reward p _ downward upward _ _ _ r h
  obtain ⟨s', happ, hview⟩ := hrun res hres
  cases res with
  | Ok v =>
    obtain ⟨lr', ch'⟩ := v
    left
    refine ⟨ch', rowAfter r lr', s', happ, ?_, hview lr' ch' rfl⟩
    show Spec.lhRowStepFull p _ downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl
  | Err e =>
    right
    refine ⟨e, s', happ, ?_⟩
    show Spec.lhRowStepFull p _ downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl

variable {σ E : Type}

variable [Spec.PresetCfg] [Spec.FuluCfg]

/-- The Fulu proposer candidates: the active validators at the lookahead epoch. -/
def FuluProposerIndices (L : LookaheadGlue σ) (view : σ → Spec.BeaconState) : Prop :=
  ∀ t, (L.proposerIndices t).val.map (·.val) =
    Spec.get_active_validator_indices (view t) (L.epoch t).val

/-- A probability fact at the lookahead input: each Electra proposer loop ends before its last
pass. -/
def LookaheadFin (L : LookaheadGlue σ) (o : Spec.Oracle) (view : σ → Spec.BeaconState)
    (st : σ) : Prop :=
  ∀ s, Spec.ProposerFin Spec.P o (view st)
    (Spec.get_active_validator_indices (view st) (L.epoch st).val) s

omit [Spec.FuluCfg] in
/-- The composed Fulu lookahead returns the state of `process_proposer_lookahead_fulu`. -/
theorem lookahead_spec_fulu [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] (L : LookaheadGlue σ)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (hL : LookaheadLinks L o view)
    (hpi : FuluProposerIndices L view) (st : σ) (hn1 : LookaheadN1 L st)
    (hfin : LookaheadFin L o view st)
    (hpl : (view st).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s1 : Spec.BeaconState)
    (h1 : Spec.process_proposer_lookahead_fulu Spec.P o (view st) = .ok s1) :
    ∃ st1, lookahead L st = ok (some st1) ∧ view st1 = s1 := by
  obtain ⟨l1, -, hs1⟩ :=
    Spec.map_ok_inv ((Spec.process_proposer_lookahead_fulu_eq o (view st)).symm.trans h1)
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (L.epoch st).val =
      .ok (L.startSlot st).val := by
    obtain ⟨n, hn⟩ := Spec.process_proposer_lookahead_fulu_start _ _ _ _ h1 _
      (Spec.get_current_epoch_mainnet (view st))
    rw [← hL.epoch st _ (Spec.get_current_epoch_mainnet (view st))] at hn
    rw [hL.startSlot st n hn, hn]
  have hla := next_proposer_lookahead_spec_fulu L.hash L.effectiveBalances st Spec.P o hL.hash
    (view st) (hL.effectiveBalances st) (L.lookahead st) (hL.lookahead st) (L.proposerIndices st)
    L.proposerDomain hL.proposerDomain (L.epoch st) (hL.epoch st) (hpi st) hfin (L.mix st)
    (hL.mix st) (L.startSlot st) hstart (L.constants st) (hL.constants st)
    slots_lt_2_32 hn1 hL.usize64 s1 h1
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hla
  unfold lookahead
  rw [hr]
  simp only [bind_tc_ok]
  have hlen : v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := (·.val)), hv,
      Spec.process_proposer_lookahead_fulu_len _ _ _ _ h1, hpl]
  obtain ⟨st1, hw, hv1⟩ := hL.writeLookahead st v hlen
  refine ⟨st1, by rw [hw], ?_⟩
  rw [hv1, hv, hs1]
  rfl

/-- The composed Fulu single pass returns the state of the model `lhSinglePassFulu`. -/
theorem singlePassFulu_spec [Spec.PresetCfg.Ok] [Spec.FuluCfg.Ok] (G : SinglePassGlue σ E)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (st : σ)
    (hL : SinglePassLinks G o view st Spec.fuluTabM)
    (hk : ConstantsMatchBase Spec.P G.registryConstants)
    (hkf : FuluChurnMatch Spec.P Spec.FC G.registryConstants)
    (hslot : (view st).slot < 2 ^ 64)
    (T : Spec.BeaconState) (hT : Spec.lhSinglePassFulu o (view st) = .ok T) :
    ∃ st', singlePassCore G st = ok (some st') ∧ view st' = T := by
  unfold Spec.lhSinglePassFulu Spec.lhFullTailWithFulu at hT
  obtain ⟨cur, hcur, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨tab, htab, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨rctx, hr, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨adj, per⟩, hpre, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨plan, hplan, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨dn, up⟩, hh, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨x, hx, hT⟩ := Spec.specM_bind_ok hT
  have htarget : cur + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE := by
    rw [Spec.get_current_epoch_ok_eq hcur]; exact Spec.P_slot_target_lt hslot
  -- The step context.
  obtain ⟨r0, hr0, c, rfl, hcm, hd, hu⟩ := spec_imp_exists
    (step_context_spec (view st) cur hcur tab rctx hr adj per hpre dn up hh htarget
      (G.contextInputs st) (hL.contextInputs cur tab hcur htab))
  -- The loop, with the Fulu step.
  have hloop := single_pass_rows_spec G.rows G.rowsView _ c G.registryConstants
    (hL.rowsContract tab cur plan htab hcur hplan).row_count
    (rowsContract_stepSpec_fulu G.rows Spec.P Spec.FC Spec.fuluCompat G.rowsView _
      (hL.rowsContract tab cur plan htab hcur hplan) c _ hcm dn up hd hu G.registryConstants hk
      hkf) (G.rowsBorrow st) (G.churn st)
  rw [hL.rowsBorrow, hL.churn] at hloop
  obtain ⟨⟨res, rows'⟩, hres, hpost⟩ := spec_imp_exists hloop
  obtain ⟨ch, rfl⟩ : ∃ ch, res = .Ok ch := by
    cases res with
    | Ok ch => exact ⟨ch, rfl⟩
    | Err e =>
      cases e with
      | Step e =>
        have := hx.symm.trans hpost
        cases this
      | Rows e => exact absurd hpost id
  have hxv : x = (absChurn ch, G.rowsView rows') := by
    have := hx.symm.trans hpost
    cases this; rfl
  subst hxv
  -- The steps after the loop.
  obtain ⟨st4, ha, hv4⟩ := afterLoop_spec G o view st Spec.fuluTabM hL tab cur htab hcur plan
    hplan (G.rowsReturn st rows' ch) _ (hL.rowsReturn rows' ch) T hT
  refine ⟨st4, ?_, hv4⟩
  unfold singlePassCore
  rw [hr0]
  simp only [bind_tc_ok]
  rw [hres]
  simp only [bind_tc_ok, uncurry_apply_pair]
  exact ha

/-- The untranslated Rust of the Fulu epoch, by step. -/
structure EpochGlueFulu (σ E : Type) where
  justification : JustificationGlue σ
  singlePass : SinglePassGlue σ E
  lookahead : LookaheadGlue σ
  tail : TailGlue σ

omit [Spec.PresetCfg] [Spec.FuluCfg] in
/-- Lighthouse's Fulu `process_epoch`, as the calls of the translated functions joined by the
glue `G`: justification and finalization, the single pass (the loop, the deposits, the
consolidations), the proposer lookahead, then the resets, the historical summaries, the
participation rotation and the sync committee update. `none`: the Rust returns an error. -/
def epochFulu (G : EpochGlueFulu σ E) (st : σ) : Result (Option σ) := do
  let r ← justification G.justification st
  match r with
  | none => ok none
  | some st1 =>
  let r ← singlePassCore G.singlePass st1
  match r with
  | none => ok none
  | some st2 =>
  let r ← lookahead G.lookahead st2
  match r with
  | none => ok none
  | some st3 => tail G.tail st3

/-- The trusted facts about the glue `G` with input `st`, as `EpochLinks`. -/
structure EpochLinksFulu (G : EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) : Prop where
  justification : JustificationLinks G.justification view st
  singlePass : ∀ st1, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    SinglePassLinks G.singlePass o view st1 Spec.fuluTabM
  /-- `registry_constants` for Fulu. -/
  registryConstants : ConstantsMatchBase Spec.P G.singlePass.registryConstants
  registryConstantsFulu : FuluChurnMatch Spec.P Spec.FC G.singlePass.registryConstants
  lookahead : LookaheadLinks G.lookahead o view
  proposerIndices : FuluProposerIndices G.lookahead view
  tail : TailLinks G.tail o view
  /-- N1, and the end of the Electra proposer loops, at the lookahead input. -/
  lookaheadN1 : ∀ st1 st2, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    singlePassCore G.singlePass st1 = ok (some st2) →
    LookaheadN1 G.lookahead st2 ∧ LookaheadFin G.lookahead o view st2
  /-- N1 at the sync committee update. -/
  syncN1 : ∀ st1 st2 st3 st5, EpochProofs.Compose.justification G.justification st = ok (some st1) →
    singlePassCore G.singlePass st1 = ok (some st2) →
    EpochProofs.Compose.lookahead G.lookahead st2 = ok (some st3) →
    resets G.tail st3 = ok (some st5) → SyncN1 G.tail st5

/-- The composed Fulu epoch returns the state of the model: when
`process_epoch_lh_order_fulu` returns `ok`, the Rust returns `Ok` with a state whose view is the
model's. -/
theorem epochFulu_spec [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg.Ok]
    (G : EpochGlueFulu σ E) (o : Spec.Oracle) (view : σ → Spec.BeaconState) (st : σ)
    (hL : EpochLinksFulu G o view st) (hslot : (view st).slot < 2 ^ 64)
    (hjb : (view st).justification_bits.length = Spec.JUSTIFICATION_BITS_LENGTH)
    (hpl : (view st).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s' : Spec.BeaconState) (h : Spec.process_epoch_lh_order_fulu o (view st) = .ok s') :
    ∃ st', epochFulu G st = ok (some st') ∧ view st' = s' := by
  unfold Spec.process_epoch_lh_order_fulu at h
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lhFullTailWithFulu_order_eq] at h
  obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lhRestOrderFulu_eq] at h
  obtain ⟨t1, ht1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨a, b, c, d, hs1⟩ := Spec.process_justification_and_finalization_shape _ _ _
    ((Spec.lhJustificationAndFinalization_sameOk _ _ s1).mp h1)
  obtain ⟨st1, hj, hv1⟩ := justification_spec G.justification view st hL.justification hjb s1 h1
  obtain ⟨st2, hsp, hv2⟩ := singlePassFulu_spec G.singlePass o view st1 (hL.singlePass st1 hj)
    hL.registryConstants hL.registryConstantsFulu (by rw [hv1, hs1]; exact hslot) T
    (by rw [hv1]; exact hT)
  have hTpl := Spec.lhSinglePassFulu_keep o s1 T hT
  obtain ⟨hn1, hfin⟩ := hL.lookaheadN1 st1 st2 hj hsp
  obtain ⟨st3, hla, hv3⟩ := lookahead_spec_fulu G.lookahead o view hL.lookahead
    hL.proposerIndices st2 hn1 hfin (by rw [hv2, hTpl, hs1]; exact hpl) t1
    (by rw [hv2]; exact ht1)
  obtain ⟨st4, ht, hv4⟩ := tail_spec G.tail o view hL.tail st3
    (fun st5 hr => hL.syncN1 st1 st2 st3 st5 hj hsp hla hr) s' (by rw [hv3]; exact h)
  refine ⟨st4, ?_, hv4⟩
  unfold epochFulu
  rw [hj]
  simp only [bind_tc_ok]
  rw [hsp]
  simp only [bind_tc_ok]
  rw [hla]
  simp only [bind_tc_ok]
  exact ht

end EpochProofs.Compose
