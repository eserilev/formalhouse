import EpochProofs.Sanity.Invariants.LighthouseEpoch

/-!
# The Lighthouse single pass at the genesis epoch

At the genesis epoch the spec skips `process_inactivity_updates` and
`process_rewards_and_penalties`. Lighthouse runs `single_pass_step` with `after_genesis = false`,
which skips the same two steps. `lighthouse_single_pass_eq_spec_genesis` shows that the pass of
`lhRowStep` with that context gives the same `ok` results as the spec's four steps.
-/

namespace EpochProofs.Spec

/-- At the genesis epoch the spec returns the state unchanged. -/
theorem process_rewards_and_penalties_genesis (p : Preset) (total_active_balance : Gwei)
    (state : BeaconState) (hcurrent : get_current_epoch p state = .ok GENESIS_EPOCH) :
    process_rewards_and_penalties p total_active_balance state = .ok state := by
  unfold process_rewards_and_penalties
  simp [bind, Except.bind, hcurrent, pure, Except.pure]

/-- With `after_genesis = false`, `lhRowStep` is the registry row step, then the slashings row
step. The registry conditions are those of `registryStepIndependent_eq_exclusive`. -/
theorem lhRowStep_genesis (p : Preset) (ctx : LhStepContext) (hgen : ctx.after_genesis = false)
    (base_reward : Gwei) (churn : Epoch × Gwei) (r : Row) (activation_epoch : Epoch)
    (hprev : ctx.previous_epoch + 1 < UINT64_SIZE)
    (hbalances : p.EJECTION_BALANCE < p.MIN_ACTIVATION_BALANCE)
    (hfinalized : ctx.finalized_epoch ≤ ctx.current_epoch)
    (hcurrent : ctx.current_epoch + 1 < UINT64_SIZE)
    (hactivation : compute_activation_exit_epoch p ctx.current_epoch = .ok activation_epoch)
    (hexit : r.validator.exit_epoch ≤ FAR_FUTURE_EPOCH) :
    lhRowStep p ctx base_reward churn r =
      (fun x => (x.1.1, x.2)) <$> bothSteps (registryRowStep p ctx.total_active_balance
        ctx.current_epoch ctx.finalized_epoch activation_epoch)
        (slashingsRowStep p ctx.slashings_target ctx.penalty_per_increment) (churn, ()) r := by
  have helig : ∃ b, validatorEligible ctx.previous_epoch r.validator = .ok b := by
    unfold validatorEligible
    split
    · exact ⟨_, rfl⟩
    split
    · exact ⟨decide (ctx.previous_epoch + 1 < r.validator.withdrawable_epoch),
        by simp [uint64Add, hprev, bind, Except.bind, pure, Except.pure]⟩
    · exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := helig
  have hreg := registryStepIndependent_eq_exclusive p ctx.total_active_balance ctx.current_epoch
    ctx.finalized_epoch activation_epoch r.validator.effective_balance
    (registryFieldsOf r.validator churn) hbalances hfinalized hexit hcurrent hactivation
  unfold lhRowStep
  simp only [hgen, Bool.false_and, hb, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    if_false, bothSteps, registryRowStep, slashingsRowStep, hreg]
  cases registryStepExclusive p ctx.total_active_balance ctx.current_epoch ctx.finalized_epoch
      activation_epoch r.validator.effective_balance (registryFieldsOf r.validator churn) with
  | error e => rfl
  | ok f =>
    dsimp only
    cases slashingBalanceStep p ctx.slashings_target ctx.penalty_per_increment
      (r.validator.withRegistryFields f) r.balance <;> rfl

/-- At the genesis epoch the spec's four steps are the registry pass, then the slashings pass,
and these give the same `ok` results as one pass of both row steps. -/
theorem genesis_passes_eq_single_pass (p : Preset) (total_active_balance : Gwei)
    (state : BeaconState) (hrows : RowsOk state)
    (hcurrent : get_current_epoch p state = .ok GENESIS_EPOCH) (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch p GENESIS_EPOCH = .ok activation_epoch)
    (htarget : GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble p total_active_balance state.slashings = .ok (adjusted, per)) :
    SameOk (do
      let s1 ← process_inactivity_updates p state
      let s2 ← process_rewards_and_penalties p total_active_balance s1
      let s3 ← process_registry_updates p total_active_balance s2
      process_slashings p total_active_balance s3)
    ((fun z => state.withRowsChurn z.1.1 z.2) <$>
      passM (bothSteps (registryRowStep p total_active_balance GENESIS_EPOCH
          state.finalized_checkpoint.epoch activation_epoch)
        (slashingsRowStep p (GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2) per))
        ((state.earliest_exit_epoch, state.exit_balance_to_consume), ()) (rowsOf state)) := by
  rw [process_inactivity_updates_genesis p state hcurrent]
  simp only [bind, Except.bind]
  rw [process_rewards_and_penalties_genesis p total_active_balance state hcurrent]
  dsimp only
  refine SameOk.trans ?_ (passM_seq_bothSteps _ _ _ () (rowsOf state)
    (fun c y => pure (state.withRowsChurn c y.2)))
  apply SameOk.bind_map (process_registry_updates_rows p total_active_balance state
    GENESIS_EPOCH activation_epoch hrows hcurrent hactivation)
  intro y3 hy3
  have hk3 : y3.2.map rowKey = (rowsOf state).map rowKey :=
    passM_rowKey _ (fun a r x h => by
      rw [registryRowStep_preserves p total_active_balance GENESIS_EPOCH
        state.finalized_checkpoint.epoch activation_epoch a r x h]; rfl) _ _ y3 hy3
  have hR3 : rowsOf (state.withRowsChurn y3.1 y3.2) = y3.2 := rowsOf_withRows state y3.2 hk3
  have hok3 : RowsOk (state.withRowsChurn y3.1 y3.2) :=
    rowsOk_withRows_of_key state y3.2 hrows hk3
  have h4 := process_slashings_rows_sameOk p total_active_balance
    (state.withRowsChurn y3.1 y3.2) GENESIS_EPOCH hcurrent htarget adjusted per hpre hok3
  rw [hR3] at h4
  refine SameOk.trans h4 (SameOk.of_eq ?_)
  simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  cases passM (slashingsRowStep p (GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2) per) ()
    y3.2 <;> rfl

/-- On mainnet, at the genesis epoch, one pass of `lhRowStep` with `after_genesis = false`
gives the same `ok` results as the spec's inactivity, rewards, registry and slashings steps. -/
theorem lighthouse_single_pass_eq_spec_genesis (total_active_balance : Gwei)
    (state : BeaconState) (hrows : RowsOk state)
    (hcurrent : get_current_epoch Preset.mainnet state = .ok GENESIS_EPOCH)
    (rctx : RewardsContext) (hprev : rctx.previous_epoch = GENESIS_EPOCH)
    (hexit : ∀ i (h : i < state.validators.length),
      state.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH)
    (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch Preset.mainnet GENESIS_EPOCH =
      .ok activation_epoch)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble Preset.mainnet total_active_balance state.slashings =
      .ok (adjusted, per))
    (hfinalized : state.finalized_checkpoint.epoch ≤ GENESIS_EPOCH)
    (base_reward : Row → Gwei) :
    SameOk (do
      let s1 ← process_inactivity_updates Preset.mainnet state
      let s2 ← process_rewards_and_penalties Preset.mainnet total_active_balance s1
      let s3 ← process_registry_updates Preset.mainnet total_active_balance s2
      process_slashings Preset.mainnet total_active_balance s3)
    ((fun y => state.withRowsChurn y.1 y.2) <$>
      passM (fun churn r => lhRowStep Preset.mainnet
          (lhContextOf state total_active_balance GENESIS_EPOCH rctx per) (base_reward r) churn r)
        (state.earliest_exit_epoch, state.exit_balance_to_consume) (rowsOf state)) := by
  refine SameOk.trans (genesis_passes_eq_single_pass Preset.mainnet total_active_balance state
    hrows hcurrent activation_epoch hactivation (by decide) adjusted per hpre) (SameOk.of_eq ?_)
  have hstep : ∀ churn r, r ∈ rowsOf state →
      lhRowStep Preset.mainnet (lhContextOf state total_active_balance GENESIS_EPOCH rctx per)
        (base_reward r) churn r =
      (fun x => (x.1.1, x.2)) <$> bothSteps (registryRowStep Preset.mainnet total_active_balance
        GENESIS_EPOCH state.finalized_checkpoint.epoch activation_epoch)
        (slashingsRowStep Preset.mainnet
          (GENESIS_EPOCH + Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR / 2) per) (churn, ()) r := by
    intro churn r hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    have hiv : i < state.validators.length := by rw [← rowsOf_length]; exact hi
    have hrow := rowsOf_getElem state i hi
    rw [hri] at hrow
    subst hrow
    exact lhRowStep_genesis Preset.mainnet _ rfl _ churn _ activation_epoch
      (by simp only [lhContextOf, hprev, GENESIS_EPOCH, UINT64_SIZE]; decide) (by decide)
      (by simpa only [lhContextOf] using hfinalized)
      (by simp only [lhContextOf, GENESIS_EPOCH, UINT64_SIZE]; decide) hactivation (hexit i hiv)
  rw [passM_congr _ _ (rowsOf state) (fun churn r hr => hstep churn r hr)]
  rw [passM_proj (bothSteps (registryRowStep Preset.mainnet total_active_balance GENESIS_EPOCH
      state.finalized_checkpoint.epoch activation_epoch)
      (slashingsRowStep Preset.mainnet
        (GENESIS_EPOCH + Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR / 2) per))
    (fun c => (c, ())) (fun b => b.1) (fun _ => rfl) (fun _ => rfl)]
  cases passM _ _ (rowsOf state) <;> rfl

end EpochProofs.Spec
