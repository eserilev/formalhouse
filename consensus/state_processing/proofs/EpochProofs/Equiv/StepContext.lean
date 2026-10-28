import EpochProofs.Equiv.SinglePassLoopModel
import EpochProofs.Equiv.EpochContexts
import EpochProofs.Equiv.Slashings

/-!
# The step context is computed by translated code

`single_pass.rs` reads raw values from the state, the caches and the spec into a
`ContextInputs`, and `step_context` in `single_pass_step.rs` computes the `StepContext` from
them. `step_context_spec` shows that when the raw values are the spec's raw values
(`ContextInputsMatch`), the result holds the spec context `lhContextOf` and the spec hysteresis
thresholds (`ContextMatches`). `single_pass_rows_model_inputs` puts this together with the loop:
the context of `single_pass_rows_model` is no longer an assumption, only the raw reads are.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

open state_processing.per_epoch_processing.single_pass_step (ExitChurn StepContext ContextInputs)

/-- The raw values that `single_pass.rs` reads are the spec values for the state `s` at
epoch `cur`, with total active balance `tab`. The flag balances are the previous epoch totals
of `get_unslashed_participating_indices`, which the progressive balances cache holds. All step
switches are on, as in production. -/
structure ContextInputsMatch [Spec.PresetCfg] (s : Spec.BeaconState) (cur tab : Nat)
    (i : ContextInputs) : Prop where
  current_epoch : i.current_epoch.val = cur
  finalized_epoch : i.finalized_epoch.val = s.finalized_checkpoint.epoch
  genesis_epoch : i.genesis_epoch.val = Spec.GENESIS_EPOCH
  total_active_balance : i.total_active_balance.val = tab
  source_balance : (Spec.get_unslashed_participating_indices Spec.P s
    Spec.TIMELY_SOURCE_FLAG_INDEX (cur - 1) >>= Spec.get_total_balance Spec.P s) =
      .ok i.source_balance.val
  target_balance : (Spec.get_unslashed_participating_indices Spec.P s
    Spec.TIMELY_TARGET_FLAG_INDEX (cur - 1) >>= Spec.get_total_balance Spec.P s) =
      .ok i.target_balance.val
  head_balance : (Spec.get_unslashed_participating_indices Spec.P s
    Spec.TIMELY_HEAD_FLAG_INDEX (cur - 1) >>= Spec.get_total_balance Spec.P s) =
      .ok i.head_balance.val
  sum_slashings : i.sum_slashings.val = s.slashings.sum
  min_epochs_to_inactivity_penalty :
    i.min_epochs_to_inactivity_penalty.val = Spec.P.MIN_EPOCHS_TO_INACTIVITY_PENALTY
  bias : i.inactivity_score_bias.val = Spec.P.INACTIVITY_SCORE_BIAS
  recovery_rate : i.inactivity_score_recovery_rate.val = Spec.P.INACTIVITY_SCORE_RECOVERY_RATE
  penalty_quotient :
    i.inactivity_penalty_quotient.val = Spec.P.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
  multiplier :
    i.proportional_slashing_multiplier.val = Spec.P.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX
  vector : i.epochs_per_slashings_vector.val = Spec.P.EPOCHS_PER_SLASHINGS_VECTOR
  effective_balance_increment :
    i.effective_balance_increment.val = Spec.P.EFFECTIVE_BALANCE_INCREMENT
  hysteresis_quotient : i.hysteresis_quotient.val = Spec.P.HYSTERESIS_QUOTIENT
  downward_multiplier :
    i.hysteresis_downward_multiplier.val = Spec.P.HYSTERESIS_DOWNWARD_MULTIPLIER
  upward_multiplier : i.hysteresis_upward_multiplier.val = Spec.P.HYSTERESIS_UPWARD_MULTIPLIER
  inactivity_updates : i.inactivity_updates = true
  rewards_and_penalties : i.rewards_and_penalties = true
  registry_updates : i.registry_updates = true
  slashings : i.slashings = true
  pending_deposits : i.pending_deposits = true
  effective_balance_updates : i.effective_balance_updates = true

theorem saturating_sub_one (a : Nat) : Spec.saturating_sub a 1 = a - 1 := by
  show (if (a : Nat) > (1 : Nat) then a - 1 else a - a) = a - 1
  split <;> omega

/-- A flag increment of the rewards context is the flag balance divided by the increment. -/
theorem rewardsFlagIncrements_of_total (p : Spec.Preset) (s : Spec.BeaconState) (e f v x : Nat)
    (hv : (Spec.get_unslashed_participating_indices p s f e >>= Spec.get_total_balance p s) =
      .ok v)
    (hx : Spec.rewardsFlagIncrements p s e f = .ok x) : x = v / p.EFFECTIVE_BALANCE_INCREMENT := by
  have h : Spec.rewardsFlagIncrements p s e f =
      ((Spec.get_unslashed_participating_indices p s f e >>= Spec.get_total_balance p s) >>=
        fun t => Spec.uint64Div t p.EFFECTIVE_BALANCE_INCREMENT) := by
    simp only [Spec.rewardsFlagIncrements, bind_assoc]
  rw [h, hv] at hx
  by_cases h0 : p.EFFECTIVE_BALANCE_INCREMENT = 0
  · simp [Spec.uint64Div, h0, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hx
  · simp only [Spec.uint64Div, h0, if_false, Bind.bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hx
    exact hx.symm

/-- The previous epoch and the inactivity leak flag of a successful rewards context. -/
theorem rewardsContext_epochs (p : Spec.Preset) (s : Spec.BeaconState) (cur : Nat)
    (hcur : Spec.get_current_epoch p s = .ok cur) (prev : Nat) (leak : Bool)
    (hprev : Spec.get_previous_epoch p s = .ok prev)
    (hleak : Spec.is_in_inactivity_leak p s = .ok leak) :
    prev = cur - 1 ∧ s.finalized_checkpoint.epoch ≤ cur - 1 ∧
      leak = decide (cur - 1 - s.finalized_checkpoint.epoch > p.MIN_EPOCHS_TO_INACTIVITY_PENALTY) := by
  simp only [Spec.get_previous_epoch, hcur, Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, saturating_sub_one] at hprev
  simp only [Spec.is_in_inactivity_leak, Spec.get_finality_delay, Spec.get_previous_epoch, hcur,
    Bind.bind, Except.bind, pure, Except.pure, saturating_sub_one, Spec.uint64Sub] at hleak
  by_cases hle : s.finalized_checkpoint.epoch ≤ cur - 1
  · simp only [hle, if_true, Except.ok.injEq] at hleak
    exact ⟨hprev.symm, hle, hleak.symm⟩
  · simp [hle, throw, throwThe, MonadExceptOf.throw] at hleak

/-- `step_context` returns the spec step context and the spec hysteresis thresholds when its
inputs are the spec's raw values. The hypotheses `hr`, `hpre` and `hh` are the spec
computations of the model (`lhFullTailG`), and `htarget` rules out the overflow of the slashings
target epoch. -/
theorem step_context_spec [Spec.PresetCfg] (s : Spec.BeaconState) (cur : Nat)
    (hcur : Spec.get_current_epoch Spec.P s = .ok cur) (tab : Nat) (rctx : Spec.RewardsContext)
    (hr : Spec.rewardsContextOf Spec.P tab s = .ok rctx) (adjusted per : Nat)
    (hpre : Spec.slashingsPreamble Spec.P tab s.slashings = .ok (adjusted, per))
    (downward upward : Nat) (hh : Spec.hysteresisThresholds Spec.P = .ok (downward, upward))
    (htarget : cur + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE)
    (i : ContextInputs) (hi : ContextInputsMatch s cur tab i) :
    per_epoch_processing.single_pass_step.step_context i ⦃ r => ∃ c, r = .Ok c ∧
      ContextMatches Spec.P c (Spec.lhContextOf s tab cur rctx per) ∧
      c.downward_threshold.val = downward ∧ c.upward_threshold.val = upward ⦄ := by
  obtain ⟨hprev, hsrc, htgt, hhead, hact, hleak, -⟩ := Spec.rewardsContextOf_ok _ _ _ _ hr
  obtain ⟨hpe, hfin, hlk⟩ := rewardsContext_epochs _ _ _ hcur _ _ hprev hleak
  rw [hpe] at hsrc htgt hhead
  have hinc : Spec.P.EFFECTIVE_BALANCE_INCREMENT ≠ 0 := by
    intro h0
    simp [Spec.uint64Div, h0, throw, throwThe, MonadExceptOf.throw] at hact
  have hactv : rctx.active_increments = tab / Spec.P.EFFECTIVE_BALANCE_INCREMENT := by
    simp [Spec.uint64Div, hinc, pure, Except.pure] at hact
    exact hact.symm
  have hsv := rewardsFlagIncrements_of_total _ _ _ _ _ _ hi.source_balance hsrc
  have htv := rewardsFlagIncrements_of_total _ _ _ _ _ _ hi.target_balance htgt
  have hhv := rewardsFlagIncrements_of_total _ _ _ _ _ _ hi.head_balance hhead
  -- The finality delay.
  have hprevR : (core.num.U64.saturating_sub i.current_epoch 1#u64).val = cur - 1 := by
    rw [u64_saturating_sub_val, hi.current_epoch]; rfl
  obtain ⟨r0, h0, hq0⟩ := spec_imp_exists
    (safe_sub_spec (core.num.U64.saturating_sub i.current_epoch 1#u64) i.finalized_epoch)
  obtain ⟨d, rfl, hd⟩ : ∃ d, r0 = .Ok d ∧ d.val = cur - 1 - s.finalized_checkpoint.epoch := by
    cases r0 with
    | Err e =>
      have h1 := (hq0.2 e rfl).2
      rw [hprevR, hi.finalized_epoch] at h1
      exact absurd hfin (Nat.not_le.mpr h1)
    | Ok v => exact ⟨v, rfl, by rw [(hq0.1 v rfl).1, hprevR, hi.finalized_epoch]⟩
  -- The increments.
  obtain ⟨r1, h1, a, b, c, e, rfl, ha, hb, hc, he⟩ := spec_imp_exists
    (participation_increments_ok i.source_balance i.target_balance i.head_balance
      i.total_active_balance i.effective_balance_increment
      (by rw [hi.effective_balance_increment]; exact hinc))
  -- The slashings values.
  obtain ⟨r2, h2, hq2, hq2t⟩ := spec_imp_exists
    (slashings_context_equiv Spec.P s.slashings i.sum_slashings i.proportional_slashing_multiplier
      i.total_active_balance i.current_epoch i.epochs_per_slashings_vector
      i.effective_balance_increment hi.sum_slashings hi.multiplier hi.vector
      hi.effective_balance_increment
      (by rw [hi.current_epoch, hi.vector]; exact htarget))
  rw [hi.total_active_balance, hpre] at hq2
  obtain ⟨x, rfl⟩ : ∃ x, r2 = .Ok x := by
    cases r2 with
    | Err e => simp [absResult] at hq2
    | Ok x => exact ⟨x, rfl⟩
  simp only [absResult, Except.ok.injEq, Prod.mk.injEq] at hq2
  have hx2 := hq2t x rfl
  -- The hysteresis thresholds.
  obtain ⟨r3, h3, hq3⟩ := spec_imp_exists
    (hysteresis_thresholds_equiv Spec.P i.effective_balance_increment i.hysteresis_quotient
      i.hysteresis_downward_multiplier i.hysteresis_upward_multiplier
      hi.effective_balance_increment hi.hysteresis_quotient hi.downward_multiplier
      hi.upward_multiplier)
  rw [hh] at hq3
  obtain ⟨y, rfl⟩ : ∃ y, r3 = .Ok y := by
    cases r3 with
    | Err e => simp [absResult] at hq3
    | Ok y => exact ⟨y, rfl⟩
  simp only [absResult, Except.ok.injEq, Prod.mk.injEq] at hq3
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2⟩ := y
  unfold per_epoch_processing.single_pass_step.step_context
  simp only [lift, bind_tc_ok, h0, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, hq3.1, hq3.2⟩
  all_goals try simp only [Spec.lhContextOf]
  · exact hi.current_epoch
  · rw [hprevR, hpe]
  · exact hi.finalized_epoch
  · rw [hlk]; simp [UScalar.lt_equiv, hd, hi.min_epochs_to_inactivity_penalty]
  · exact hi.bias
  · exact hi.recovery_rate
  · exact hi.penalty_quotient
  · rw [ha, hsv, hi.effective_balance_increment]
  · rw [hb, htv, hi.effective_balance_increment]
  · rw [hc, hhv, hi.effective_balance_increment]
  · rw [he, hactv, hi.total_active_balance, hi.effective_balance_increment]
  · exact hi.total_active_balance
  · rw [hx2, hi.current_epoch]
  · exact hq2.2
  · exact hi.effective_balance_increment
  · have hg := hi.genesis_epoch
    rw [← hi.current_epoch, ← hg]
    by_cases hq : i.current_epoch = i.genesis_epoch
    · rw [hq]; simp
    · have hv : i.current_epoch.val ≠ i.genesis_epoch.val := fun h => hq (UScalar.eq_of_val_eq h)
      rw [bne_iff_ne.mpr hq, bne_iff_ne.mpr hv]
  · exact hi.inactivity_updates
  · exact hi.rewards_and_penalties
  · exact hi.registry_updates
  · exact hi.slashings
  · exact hi.pending_deposits
  · exact hi.effective_balance_updates

/-- The loop of `single_pass_rows_model`, with the context computed by `step_context` from raw
inputs. The context is no longer an assumption: only the raw reads (`ContextInputsMatch`) are. -/
theorem single_pass_rows_model_inputs [Spec.PresetCfg] {R E : Type} (inst : LhRegistryRows R E)
    (s : Spec.BeaconState) (tab : Spec.Gwei) (topups : List Spec.Gwei)
    (named : List Spec.ValidatorIndex) (view : R → List Spec.Row) (rows : R)
    (hview : view rows = Spec.rowsOf s)
    (hc : RowsContract inst Spec.P view (modelRowInputs tab topups named))
    (cur : Nat) (hcur : Spec.get_current_epoch Spec.P s = .ok cur) (rctx : Spec.RewardsContext)
    (hr : Spec.rewardsContextOf Spec.P tab s = .ok rctx) (adjusted per : Nat)
    (hpre : Spec.slashingsPreamble Spec.P tab s.slashings = .ok (adjusted, per))
    (downward upward : Nat) (hh : Spec.hysteresisThresholds Spec.P = .ok (downward, upward))
    (htarget : cur + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE)
    (i : ContextInputs) (hi : ContextInputsMatch s cur tab i)
    (k : per_epoch_processing.registry_update.RegistryConstants)
    (hk : ConstantsMatch Spec.P k) (ch : ExitChurn)
    (hch : absChurn ch = (s.earliest_exit_epoch, s.exit_balance_to_consume)) :
    per_epoch_processing.single_pass_step.step_context i ⦃ r => ∃ c, r = .Ok c ∧
      per_epoch_processing.registry_rows.single_pass_rows inst rows ch c k ⦃ res =>
        LoopPost view (Spec.passM (fun churn r => Spec.lhRowStepFull Spec.P
            (Spec.lhContextOf s tab cur rctx per) downward upward
            ⟨Spec.lhBaseReward tab r, topups.getD r.index 0, decide (r.index ∈ named)⟩ churn r)
          (s.earliest_exit_epoch, s.exit_balance_to_consume) (Spec.rowsOf s)) res ⦄ ⦄ := by
  obtain ⟨r, hres, c, rfl, hcm, hd, hu⟩ := spec_imp_exists
    (step_context_spec s cur hcur tab rctx hr adjusted per hpre downward upward hh htarget i hi)
  rw [hres]
  exact ⟨c, rfl, single_pass_rows_model inst s tab topups named view rows hview hc c _ hcm
    downward upward hd hu k hk ch hch⟩

end EpochProofs
