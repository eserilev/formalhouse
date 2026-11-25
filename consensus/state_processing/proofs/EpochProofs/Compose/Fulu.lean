import EpochProofs.AeneasCompat
import EpochProofs.Compose.Epoch
import EpochProofs.Equiv.FuluRegistry
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder

/-!
# The Fulu epoch, composed from the translated functions

`epochFulu` is Lighthouse's Fulu `process_epoch`: the Gloas composition without the builder
payments and the PTC window, with the Fulu registry constants and the Fulu proposer candidates
(every active validator). `translatedEpochFulu_matches_model` shows that, under
`UntranslatedEpochFactsFulu`, it returns the state of the model `process_epoch_lighthouse_fulu`
whenever the model returns `ok`.
-/

namespace EpochProofs.Spec

/-- The Lighthouse Fulu model from the start of the single pass to the effective balance updates
after the consolidations. -/
def lighthouseSinglePassFulu [CurrentPreset] [CurrentFuluConfig] (oracle : Oracle)
    (s : BeaconState) : SpecM BeaconState :=
  lighthouseSinglePassThenFulu (fun s _ plan x =>
    lighthouseDepositsConsolidations oracle s plan (s.withRowsChurn x.1 x.2)) s

theorem lighthouseSinglePassThenFulu_order_eq [CurrentPreset] [CurrentFuluConfig] (oracle : Oracle)
    (s : BeaconState) :
    lighthouseSinglePassThenFulu (lighthouseStepsAfterSinglePassFulu oracle) s =
      lighthouseSinglePassFulu oracle s >>=
      lighthouseStepsAfterPaymentsFulu oracle := by
  unfold lighthouseSinglePassFulu lighthouseSinglePassThenFulu lighthouseStepsAfterSinglePassFulu
    lighthouseDepositsConsolidationsFulu lighthouseDepositsConsolidations
  simp only [bind, Except.bind]
  repeat' split
  all_goals rfl

/-- The Fulu single pass does not write the proposer lookahead. -/
theorem lighthouseSinglePassFulu_keep [CurrentPreset] [CurrentFuluConfig] (oracle : Oracle)
    (s T : BeaconState)
    (h : lighthouseSinglePassFulu oracle s = .ok T) : T.proposer_lookahead =
    s.proposer_lookahead := by
  unfold lighthouseSinglePassFulu lighthouseSinglePassThenFulu at h
  obtain ⟨cur, -, h⟩ := specM_bind_ok h
  obtain ⟨tab, -, h⟩ := specM_bind_ok h
  obtain ⟨rctx, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨adj, per⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨plan, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨dn, up⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨x, -, h⟩ := specM_bind_ok h
  exact (lighthouseDepositsConsolidations_keep oracle s plan x T h).2.1

theorem lighthouseStepsAfterPaymentsFulu_eq [CurrentPreset] (oracle : Oracle) (t : BeaconState) :
    lighthouseStepsAfterPaymentsFulu oracle t = process_proposer_lookahead_fulu P oracle t >>=
      lighthouseStepsAfterPtcWindow oracle :=
      rfl

/-- `process_proposer_lookahead_fulu` keeps the length of the lookahead. -/
theorem process_proposer_lookahead_fulu_len (p : Preset) (oracle : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead_fulu p oracle s = .ok s') :
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
theorem process_proposer_lookahead_fulu_start (p : Preset) (oracle : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead_fulu p oracle s = .ok s') (ce : Nat)
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

/-- `rowsContract_stepSpec` with the Fulu step: under `ValidatorRowsMatchSpec`, one `apply_step`
call runs `lighthouseValidatorStep` with the registry total `fuluTotalActiveBalance`. -/
theorem rowsContract_stepSpec_fulu {R RustError : Type} (inst : LighthouseRegistryRows R RustError)
    (p : Spec.Preset)
    (f : Spec.FuluConfig) (hcompat : Spec.FuluCompat p f) (rustStateToSpec : R → List Spec.Row)
    (inputsOf : Spec.Row → Spec.LighthouseRowInputs)
    (hc : ValidatorRowsMatchSpec inst p rustStateToSpec inputsOf)
    (c : StepContext) (ctx : Spec.LighthouseStepContext) (hcm : ContextMatches p c ctx)
    (downward upward : Spec.Uint64) (hdownward : c.downward_threshold.val = downward)
    (hupward : c.upward_threshold.val = upward)
    (k : per_epoch_processing.registry_update.RegistryConstants) (hk : RegistryConstantsMatch p k)
    (hkf : ChurnConstantsMatchFulu p f k) :
    StepMatchesModel inst rustStateToSpec (fun churn r => Spec.lighthouseValidatorStep p
      { ctx with total_active_balance := Spec.fuluTotalActiveBalance p f ctx.total_active_balance }
      downward upward (inputsOf r) churn r) c k := by
  intro s i ch r hr
  obtain ⟨lr, ri, hm, hi, hrun⟩ := hc.apply_step s i ch c k r hr
  have hi' : InputsMatches p ri { inputsOf r with base_reward := ri.base_reward.val } r :=
    ⟨rfl, hi.deposit, hi.in_consolidation, hi.effective_balance_limit⟩
  obtain ⟨res, hres, habs⟩ := spec_imp_exists (single_pass_step_equiv_fulu p f hcompat lr r hm ri _
    hi' ch c ctx hcm downward upward hdownward hupward k hk hkf)
  have hirr : Spec.lighthouseValidatorStep p
      { ctx with total_active_balance := Spec.fuluTotalActiveBalance p f ctx.total_active_balance }
      downward upward { inputsOf r with base_reward := ri.base_reward.val }
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r =
      Spec.lighthouseValidatorStep p
      { ctx with total_active_balance := Spec.fuluTotalActiveBalance p f ctx.total_active_balance }
      downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r := by
    rcases hi.base_reward with h | h
    · rw [h]
    · rw [hcm.previous_epoch] at h
      exact lighthouseValidatorStep_base_reward p _ downward upward _ _ _ r h
  obtain ⟨s', happ, hview⟩ := hrun res hres
  cases res with
  | Ok v =>
    obtain ⟨lr', ch'⟩ := v
    left
    refine ⟨ch', rowAfter r lr', s', happ, ?_, hview lr' ch' rfl⟩
    show Spec.lighthouseValidatorStep p _ downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl
  | Err e =>
    right
    refine ⟨e, s', happ, ?_⟩
    show Spec.lighthouseValidatorStep p _ downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl

variable {RustState RustError : Type}

variable [Spec.CurrentPreset] [Spec.CurrentFuluConfig]

/-- The Fulu proposer candidates: the active validators at the lookahead epoch. -/
def ProposerCandidatesFulu (lookaheadCode : UntranslatedLookahead RustState)
    (rustStateToSpec : RustState → Spec.BeaconState) : Prop :=
  ∀ t, (lookaheadCode.proposerIndices t).val.map (·.val) =
    Spec.get_active_validator_indices (rustStateToSpec t) (lookaheadCode.epoch t).val

/-- A probability fact at the lookahead input: each Electra proposer loop ends before its last
pass. -/
def LookaheadFin (lookaheadCode : UntranslatedLookahead RustState) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState)
    (rustState : RustState) : Prop :=
  ∀ s, Spec.ProposerSelectionEnds Spec.P oracle (rustStateToSpec rustState)
    (Spec.get_active_validator_indices (rustStateToSpec rustState)
      (lookaheadCode.epoch rustState).val) s

omit [Spec.CurrentFuluConfig] in
/-- The composed Fulu lookahead returns the state of `process_proposer_lookahead_fulu`. -/
theorem translatedLookaheadFulu_matches_model [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds]
    (lookaheadCode : UntranslatedLookahead RustState)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedLookaheadFacts lookaheadCode oracle rustStateToSpec)
    (hpi : ProposerCandidatesFulu lookaheadCode rustStateToSpec) (rustState : RustState)
    (hn1 : LookaheadN1 lookaheadCode rustState)
    (hfin : LookaheadFin lookaheadCode oracle rustStateToSpec rustState)
    (hpl : (rustStateToSpec rustState).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s1 : Spec.BeaconState)
    (h1 : Spec.process_proposer_lookahead_fulu Spec.P oracle (rustStateToSpec rustState) = .ok s1) :
    ∃ rustState1, translatedLookahead lookaheadCode rustState = ok (some rustState1) ∧
      rustStateToSpec rustState1 = s1 := by
  obtain ⟨l1, -, hs1⟩ :=
    Spec.map_ok_inv ((Spec.process_proposer_lookahead_fulu_eq oracle
      (rustStateToSpec rustState)).symm.trans h1)
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (lookaheadCode.epoch rustState).val =
      .ok (lookaheadCode.startSlot rustState).val := by
    obtain ⟨n, hn⟩ := Spec.process_proposer_lookahead_fulu_start _ _ _ _ h1 _
      (Spec.get_current_epoch_mainnet (rustStateToSpec rustState))
    rw [← hL.epoch rustState _ (Spec.get_current_epoch_mainnet (rustStateToSpec rustState))] at hn
    rw [hL.startSlot rustState n hn, hn]
  have hla := next_proposer_lookahead_spec_fulu lookaheadCode.hash lookaheadCode.effectiveBalances
    rustState Spec.P oracle hL.hash
    (rustStateToSpec rustState) (hL.effectiveBalances rustState) (lookaheadCode.lookahead rustState)
      (hL.lookahead rustState) (lookaheadCode.proposerIndices rustState)
    lookaheadCode.proposerDomain hL.proposerDomain (lookaheadCode.epoch rustState)
      (hL.epoch rustState) (hpi rustState) hfin (lookaheadCode.mix rustState)
    (hL.mix rustState) (lookaheadCode.startSlot rustState) hstart
      (lookaheadCode.constants rustState) (hL.constants rustState)
    slots_lt_2_32 hn1 hL.usize64 s1 h1
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hla
  unfold translatedLookahead
  rw [hr]
  simp only [bind_tc_ok]
  have hlen : v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := (·.val)), hv,
      Spec.process_proposer_lookahead_fulu_len _ _ _ _ h1, hpl]
  obtain ⟨rustState1, hw, hv1⟩ := hL.writeLookahead rustState v hlen
  refine ⟨rustState1, by rw [hw], ?_⟩
  rw [hv1, hv, hs1]
  rfl

/-- The composed Fulu single pass returns the state of the model `lighthouseSinglePassFulu`. -/
theorem translatedSinglePassFulu_matches_model [Spec.CurrentPreset.Valid]
    [Spec.CurrentFuluConfig.Valid] (code : UntranslatedSinglePass RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedSinglePassFacts code oracle rustStateToSpec rustState Spec.fuluChurnTotal)
    (hk : RegistryConstantsMatch Spec.P code.registryConstants)
    (hkf : ChurnConstantsMatchFulu Spec.P Spec.FC code.registryConstants)
    (hslot : (rustStateToSpec rustState).slot < 2 ^ 64)
    (T : Spec.BeaconState) (hT : Spec.lighthouseSinglePassFulu oracle (rustStateToSpec rustState) =
    .ok T) :
    ∃ rustState', translatedSinglePassBeforePayments code rustState = ok (some rustState') ∧
      rustStateToSpec rustState' = T := by
  unfold Spec.lighthouseSinglePassFulu Spec.lighthouseSinglePassThenFulu at hT
  obtain ⟨current, hcur, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨total, htab, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨rctx, hr, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨adj, per⟩, hpre, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨plan, hplan, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨dn, up⟩, hh, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨x, hx, hT⟩ := Spec.specM_bind_ok hT
  have hxlen : x.2.length = (rustStateToSpec rustState).validators.length := by
    rw [(Spec.passM_rows _ _ _ _ hx).1, Spec.rowsOf_length]
  have htarget : current + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE := by
    rw [Spec.get_current_epoch_ok_eq hcur]; exact Spec.P_slot_target_lt hslot
  -- The step context.
  obtain ⟨r0, hr0, c, rfl, hcm, hd, hu⟩ := spec_imp_exists
    (step_context_spec (rustStateToSpec rustState) current hcur total rctx hr adj per hpre dn up hh
      htarget
      (code.contextInputs rustState) (hL.contextInputs current total hcur htab))
  -- The loop, with the Fulu step.
  have hloop := single_pass_rows_spec code.rowOperations code.rowsToSpec _ c code.registryConstants
    (hL.rowsContract total current plan htab hcur hplan).row_count
    (rowsContract_stepSpec_fulu code.rowOperations Spec.P Spec.FC Spec.fuluCompat code.rowsToSpec _
      (hL.rowsContract total current plan htab hcur hplan) c _ hcm dn up hd hu
        code.registryConstants hk
      hkf) (code.rowsBorrow rustState) (code.exitChurn rustState)
  rw [hL.rowsBorrow, hL.exitChurn] at hloop
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
  have hxv : x = (exitChurnToSpec ch, code.rowsToSpec rows') := by
    have := hx.symm.trans hpost
    cases this; rfl
  subst hxv
  -- The steps after the loop.
  obtain ⟨rustState4, ha, hv4⟩ :=
    translatedStepsAfterLoop_spec code oracle rustStateToSpec rustState Spec.fuluChurnTotal hL total
    current htab hcur plan
    hplan (code.rowsReturn rustState rows' ch) _ (hL.rowsReturn rows' ch) (by rw [← hxlen]) T hT
  refine ⟨rustState4, ?_, hv4⟩
  unfold translatedSinglePassBeforePayments
  rw [hr0]
  simp only [bind_tc_ok]
  rw [hres]
  simp only [bind_tc_ok, uncurry_apply_pair]
  exact ha

/-- The untranslated Rust of the Fulu epoch, by step. -/
structure UntranslatedEpochCodeFulu (RustState RustError : Type) where
  justification : UntranslatedJustification RustState
  singlePass : UntranslatedSinglePass RustState RustError
  lookahead : UntranslatedLookahead RustState
  endOfEpoch : UntranslatedEndOfEpoch RustState

section
omit [Spec.CurrentPreset] [Spec.CurrentFuluConfig]

/-- The Rust state after justification and finalization. -/
def afterJustificationFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (rustState : RustState) : OptionT Result RustState :=
  OptionT.mk (translatedJustification code.justification rustState)

/-- The Rust state after the single pass: the loop, the deposits and the consolidations. -/
def afterSinglePassFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState1 ← afterJustificationFulu code rustState
  OptionT.mk (translatedSinglePassBeforePayments code.singlePass rustState1)

/-- The Rust state after the proposer lookahead. -/
def afterLookaheadFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState2 ← afterSinglePassFulu code rustState
  OptionT.mk (translatedLookahead code.lookahead rustState2)

/-- The Rust state after the resets, the historical summaries and the participation rotation. -/
def afterResetsFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState3 ← afterLookaheadFulu code rustState
  OptionT.mk (translatedResets code.endOfEpoch rustState3)

/-- Lighthouse's Fulu `process_epoch`, as the calls of the translated functions joined by the
untranslated code. -/
def translatedEpochFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (rustState : RustState) : OptionT Result RustState := do
  let rustState3 ← afterLookaheadFulu code rustState
  OptionT.mk (translatedEndOfEpoch code.endOfEpoch rustState3)

end

/-- What the proofs assume about the untranslated code of the Fulu epoch with input `rustState`, as
`UntranslatedEpochFacts`. -/
structure UntranslatedEpochFactsFulu (code : UntranslatedEpochCodeFulu RustState RustError)
    (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState) : Prop where
  /-- Justification and finalization. -/
  justification : UntranslatedJustificationFacts code.justification rustStateToSpec rustState
  /-- The single pass, at the state after justification. -/
  singlePass : ∀ rustState1, (afterJustificationFulu code rustState).run = ok (some rustState1) →
    UntranslatedSinglePassFacts code.singlePass oracle rustStateToSpec rustState1
      Spec.fuluChurnTotal
  /-- `registry_constants` for Fulu. -/
  registryConstants : RegistryConstantsMatch Spec.P code.singlePass.registryConstants
  /-- The churn constants of Fulu. -/
  registryConstantsFulu : ChurnConstantsMatchFulu Spec.P Spec.FC code.singlePass.registryConstants
  /-- The proposer lookahead. -/
  lookahead : UntranslatedLookaheadFacts code.lookahead oracle rustStateToSpec
  /-- The proposer candidates are the active validators. -/
  proposerIndices : ProposerCandidatesFulu code.lookahead rustStateToSpec
  /-- The resets, the historical summaries, the participation rotation and the sync committees. -/
  endOfEpoch : UntranslatedEndOfEpochFacts code.endOfEpoch oracle rustStateToSpec
  /-- At most `2^24` proposer candidates enter the shuffle. -/
  proposersFitShuffle : ∀ rustState2, (afterSinglePassFulu code rustState).run =
    ok (some rustState2) →
    (code.lookahead.proposerIndices rustState2).val.length ≤ 2 ^ 24
  /-- A fact about hash values: each Electra proposer loop ends before its last pass. -/
  proposerSelectionEnds : ∀ rustState2, (afterSinglePassFulu code rustState).run =
    ok (some rustState2) →
    ∀ seed, Spec.ProposerSelectionEnds Spec.P oracle (rustStateToSpec rustState2)
      (Spec.get_active_validator_indices (rustStateToSpec rustState2)
        (code.lookahead.epoch rustState2).val) seed
  /-- At most `2^24` sync committee candidates enter the shuffle. -/
  syncCandidatesFitShuffle : ∀ rustState5, (afterResetsFulu code rustState).run =
    ok (some rustState5) →
    ∀ rustState6, code.endOfEpoch.writeCurrentSync rustState5 = some rustState6 →
      (code.endOfEpoch.syncIndices rustState6).val.length ≤ 2 ^ 24

/-- The composed Fulu epoch returns the state of the model: when
`process_epoch_lighthouse_fulu` returns `ok`, the Rust returns `Ok` with a state whose
rustStateToSpec is the model's. -/
theorem translatedEpochFulu_matches_model [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds]
    [Spec.CurrentFuluConfig.Valid]
    (code : UntranslatedEpochCodeFulu RustState RustError) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedEpochFactsFulu code oracle rustStateToSpec rustState)
    (hslot : (rustStateToSpec rustState).slot < 2 ^ 64)
    (hjb : (rustStateToSpec rustState).justification_bits.length = Spec.JUSTIFICATION_BITS_LENGTH)
    (hpl : (rustStateToSpec rustState).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s' : Spec.BeaconState) (h : Spec.process_epoch_lighthouse_fulu oracle
      (rustStateToSpec rustState) = .ok s') :
    ∃ rustState', (translatedEpochFulu code rustState).run = ok (some rustState') ∧
      rustStateToSpec rustState' = s' := by
  unfold Spec.process_epoch_lighthouse_fulu at h
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lighthouseSinglePassThenFulu_order_eq] at h
  obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
  rw [Spec.lighthouseStepsAfterPaymentsFulu_eq] at h
  obtain ⟨t1, ht1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨a, b, c, d, hs1⟩ := Spec.process_justification_and_finalization_shape _ _ _
    ((Spec.lighthouseJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1)
  obtain ⟨rustState1, hj, hv1⟩ :=
    translatedJustification_matches_model code.justification rustStateToSpec rustState
    hL.justification hjb s1 h1
  obtain ⟨rustState2, hsp, hv2⟩ :=
    translatedSinglePassFulu_matches_model code.singlePass oracle rustStateToSpec rustState1
    (hL.singlePass rustState1 hj)
    hL.registryConstants hL.registryConstantsFulu (by rw [hv1, hs1]; exact hslot) T
    (by rw [hv1]; exact hT)
  have hTpl := Spec.lighthouseSinglePassFulu_keep oracle s1 T hT
  have r2 : (afterSinglePassFulu code rustState).run = ok (some rustState2) := run_bind_ok hj hsp
  obtain ⟨rustState3, hla, hv3⟩ :=
    translatedLookaheadFulu_matches_model code.lookahead oracle rustStateToSpec hL.lookahead
    hL.proposerIndices rustState2 (hL.proposersFitShuffle rustState2 r2)
    (hL.proposerSelectionEnds rustState2 r2) (by rw [hv2, hTpl, hs1]; exact hpl) t1
    (by rw [hv2]; exact ht1)
  have r3 : (afterLookaheadFulu code rustState).run = ok (some rustState3) := run_bind_ok r2 hla
  obtain ⟨rustState4, ht, hv4⟩ :=
    translatedEndOfEpoch_matches_model code.endOfEpoch oracle rustStateToSpec hL.endOfEpoch
    rustState3
    (fun rustState5 hr => hL.syncCandidatesFitShuffle rustState5 (run_bind_ok r3 hr)) s'
      (by rw [hv3]; exact h)
  exact ⟨rustState4, run_bind_ok r3 ht, hv4⟩

end EpochProofs.Compose
