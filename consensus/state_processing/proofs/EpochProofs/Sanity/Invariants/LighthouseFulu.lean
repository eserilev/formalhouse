import EpochProofs.Sanity.Invariants.LighthouseTail
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluCfg
import EpochProofs.Sanity.FuluEpoch
import EpochProofs.Sanity.FuluSinglePass

/-!
# The Lighthouse Fulu epoch equals the Fulu spec

`process_epoch_lh_full_fulu` is the Fulu epoch as Lighthouse runs it on mainnet, with the steps
after the single pass in the spec order. It is `lhFullTailG` at the Fulu churn total `fuluTab`
and without the Gloas steps (builder payments, PTC window). The sync committee update is the
Gloas function, which is the selection that Lighthouse runs (`next_sync_committee_indices`).

`process_epoch_lh_full_fulu_sameResultOrBothFail'` shows that it gives the same `ok` results as the Fulu
`process_epoch`, under the hypotheses of `process_epoch_lh_full_sameResultOrBothFail'`. The proof is the Gloas
proof with the registry and deposit churn at `fuluTab`, `B = pure` in place of the builder
payments, and the Fulu sync committee update swapped for the Gloas one
(`process_sync_committee_updates_fulu_sameResultOrBothFail`).
-/

namespace EpochProofs.Spec

/-! ## The model -/

/-- The Fulu churn total on mainnet. -/
def fuluTabM [PresetCfg] [FuluCfg] (total_active_balance : Gwei) : Gwei :=
  fuluTab P FC total_active_balance

/-- The Fulu steps after the effective balance updates, in the spec order. The sync committee
update is the Gloas function, which Lighthouse runs from Electra on. -/
def epochRest2Fulu [PresetCfg] (o : Oracle) (state : BeaconState) : SpecM BeaconState := do
  let state ← process_slashings_reset P state
  let state ← process_randao_mixes_reset P state
  let state ← process_historical_summaries_update P o state
  let state := process_participation_flag_updates state
  let state ← process_sync_committee_updates P o state
  process_proposer_lookahead_fulu P o state

/-- The Lighthouse Fulu steps after justification and finalization. -/
def lhFullTailFulu [PresetCfg] [FuluCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState :=
  lhFullTailG o fuluTabM (fun _ => epochRest2Fulu o) s

/-- The Fulu `process_epoch` on mainnet as Lighthouse runs it, with the pending deposits and the
effective balance updates in the single pass. -/
def process_epoch_lh_full_fulu [PresetCfg] [FuluCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let s1 ← lhJustificationAndFinalization P s
  lhFullTailFulu o s1

/-! ## The spec in parts -/

/-- The Fulu inactivity, rewards, registry and slashings steps, with the registry update written
as the Gloas function at `fuluTab`. -/
def specFourStepsFulu [PresetCfg] [FuluCfg] (s : BeaconState) : SpecM BeaconState := do
  let s ← process_inactivity_updates P s
  let s ← process_rewards_and_penalties P
    (← get_total_active_balance P s) s
  let s ← process_registry_updates P
    (fuluTabM (← get_total_active_balance P s)) s
  process_slashings P (← get_total_active_balance P s) s

/-- The Fulu steps after `process_slashings`. -/
def epochRestFulu [PresetCfg] [FuluCfg] (o : Oracle) (state : BeaconState) : SpecM BeaconState := do
  let state ← process_eth1_data_reset P state
  let state ← process_pending_deposits P
    (fuluTabM (← get_total_active_balance P state))
    (apply_pending_deposit P o) state
  let state ← process_pending_consolidations P state
  let state ← process_effective_balance_updates P state
  let state ← process_slashings_reset P state
  let state ← process_randao_mixes_reset P state
  let state ← process_historical_summaries_update P o state
  let state := process_participation_flag_updates state
  let state ← process_sync_committee_updates_fulu P o state
  process_proposer_lookahead_fulu P o state

/-- The Fulu `process_epoch` on mainnet in three parts. -/
theorem process_epoch_fulu_parts [PresetCfg] [FuluCfg] [FuluCfg.Ok] (o : Oracle) (s : BeaconState) :
    process_epoch_fulu P FC o s = (do
      let s1 ← process_justification_and_finalization P s
      let s5 ← specFourStepsFulu s1
      epochRestFulu o s5) := by
  rw [process_epoch_fulu_eq_tab P FC fuluCompat]
  simp only [specFourStepsFulu, epochRestFulu, fuluTabM, bind_assoc]

/-- `specFourStepsFulu` with one total active balance. -/
theorem specFourStepsFulu_sameResultOrBothFail [PresetCfg] [FuluCfg] (s1 : BeaconState) (total_active_balance : Gwei)
    (htab : get_total_active_balance P s1 = .ok total_active_balance)
    (hrows : RowsOk s1) (current_epoch activation_epoch : Epoch)
    (hcurrent : get_current_epoch P s1 = .ok current_epoch)
    (hactivation : compute_activation_exit_epoch P current_epoch =
      .ok activation_epoch)
    (hcur : current_epoch < FAR_FUTURE_EPOCH) :
    SameResultOrBothFail (specFourStepsFulu s1) (do
      let s2 ← process_inactivity_updates P s1
      let s3 ← process_rewards_and_penalties P total_active_balance s2
      let s4 ← process_registry_updates P (fuluTabM total_active_balance) s3
      process_slashings P total_active_balance s4) := by
  unfold specFourStepsFulu
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun s2 h2 => ?_)
  have hv2 := process_inactivity_updates_validators P _ _ h2
  have hslot2 := (process_inactivity_updates_checkpointsStable P _ _ h2).1
  have hl2 := process_inactivity_updates_len P _ _ h2
  have t2 : get_total_active_balance P s2 = .ok total_active_balance := by
    rw [get_total_active_balance_congr_key P s1 s2 current_epoch hcurrent hslot2
      (by rw [hv2])]
    exact htab
  rw [t2, ok_bind'']
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun s3 h3 => ?_)
  have hv3 := process_rewards_and_penalties_validators P _ _ _ h3
  have hslot3 := (process_rewards_and_penalties_checkpointsStable P _ _ _ h3).1
  have hl3 := process_rewards_and_penalties_len P _ _ _ h3
  have hc3 : get_current_epoch P s3 = .ok current_epoch :=
    current_epoch_of_slot' hcurrent (hslot3.trans hslot2)
  have t3 : get_total_active_balance P s3 = .ok total_active_balance := by
    rw [get_total_active_balance_congr_key P s2 s3 current_epoch
      (current_epoch_of_slot' hcurrent hslot2) hslot3 (by rw [hv3])]
    exact t2
  rw [t3, ok_bind'']
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun s4 h4 => ?_)
  have hslot4 := (process_registry_updates_checkpointsStable P _ _ _ h4).1
  have hrows3 : RowsOk s3 := (hl2.trans hl3).rowsOk hrows
  have hkey := process_registry_updates_activeKey P _ s3 s4 hrows3 current_epoch
    activation_epoch hc3 hactivation hcur h4
  have t4 : get_total_active_balance P s4 = .ok total_active_balance := by
    rw [get_total_active_balance_congr_key P s3 s4 current_epoch hc3 hslot4 hkey]
    exact t3
  rw [t4, ok_bind'']
  exact SameResultOrBothFail.refl _

/-- The four Fulu steps with one total keep the total active balance. -/
theorem fourStepsFulu_total [PresetCfg] [FuluCfg] (s1 : BeaconState) (total_active_balance : Gwei)
    (htab : get_total_active_balance P s1 = .ok total_active_balance)
    (hrows : RowsOk s1) (current_epoch activation_epoch : Epoch)
    (hcurrent : get_current_epoch P s1 = .ok current_epoch)
    (hactivation : compute_activation_exit_epoch P current_epoch =
      .ok activation_epoch)
    (hcur : current_epoch < FAR_FUTURE_EPOCH) (S : BeaconState)
    (h : (do
      let s2 ← process_inactivity_updates P s1
      let s3 ← process_rewards_and_penalties P total_active_balance s2
      let s4 ← process_registry_updates P (fuluTabM total_active_balance) s3
      process_slashings P total_active_balance s4) = .ok S) :
    get_total_active_balance P S = .ok total_active_balance := by
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h5⟩ := specM_bind_ok h
  have hv2 := process_inactivity_updates_validators _ _ _ h2
  have hsl2 := (process_inactivity_updates_checkpointsStable _ _ _ h2).1
  have hv3 := process_rewards_and_penalties_validators _ _ _ _ h3
  have hsl3 := (process_rewards_and_penalties_checkpointsStable _ _ _ _ h3).1
  have hsl4 := (process_registry_updates_checkpointsStable _ _ _ _ h4).1
  have hv5 := process_slashings_validators _ _ _ _ h5
  have hsl5 := (process_slashings_checkpointsStable _ _ _ _ h5).1
  have hc2 := current_epoch_of_slot' hcurrent hsl2
  have hc3 := current_epoch_of_slot' hc2 hsl3
  have hc4 := current_epoch_of_slot' hc3 hsl4
  have hrows3 : RowsOk s3 :=
    ((process_inactivity_updates_len _ _ _ h2).trans
      (process_rewards_and_penalties_len _ _ _ _ h3)).rowsOk hrows
  have hkey := process_registry_updates_activeKey _ _ s3 s4 hrows3 current_epoch
    activation_epoch hc3 hactivation hcur h4
  rw [get_total_active_balance_congr_key _ s4 S current_epoch hc4 hsl5 (by rw [hv5]),
    get_total_active_balance_congr_key _ s3 s4 current_epoch hc3 hsl4 hkey,
    get_total_active_balance_congr_key _ s2 s3 current_epoch hc2 hsl3 (by rw [hv3]),
    get_total_active_balance_congr_key _ s1 s2 current_epoch hcurrent hsl2 (by rw [hv2])]
  exact htab

/-- `epochRest2Fulu` with the Fulu sync committee update gives the same `ok` results as with the
Gloas one. -/
theorem epochRest2Fulu_sameResultOrBothFail [PresetCfg] [PresetCfg.Ok] (o : Oracle) (S : BeaconState) :
    SameResultOrBothFail (do
        let state ← process_slashings_reset P S
        let state ← process_randao_mixes_reset P state
        let state ← process_historical_summaries_update P o state
        let state := process_participation_flag_updates state
        let state ← process_sync_committee_updates_fulu P o state
        process_proposer_lookahead_fulu P o state)
      (epochRest2Fulu o S) := by
  unfold epochRest2Fulu
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  exact SameResultOrBothFail.bind (process_sync_committee_updates_fulu_sameResultOrBothFail P o _ P_sync_size_pos)
    (fun _ _ => SameResultOrBothFail.refl _)

/-- In `epochRestFulu`, the deposit churn total is `fuluTab` of the total of the state before
it, and the rest is `specTailG` with no step in place of the builder payments. -/
theorem epochRestFulu_specTail [PresetCfg] [PresetCfg.Ok] [FuluCfg] (o : Oracle) (S4 : BeaconState) (tab : Gwei) (cur : Epoch)
    (hcur : get_current_epoch P S4 = .ok cur) (hfar : cur < FAR_FUTURE_EPOCH)
    (htab : get_total_active_balance P S4 = .ok tab) :
    SameResultOrBothFail (epochRestFulu o S4)
      (process_eth1_data_reset P S4 >>=
        specTailG o (fuluTabM tab) pure (epochRest2Fulu o)) := by
  unfold epochRestFulu
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun S5 h5 => ?_)
  obtain ⟨v, rfl⟩ := eth1_shape h5
  have hcur5 : get_current_epoch P { S4 with eth1_data_votes := v } = .ok cur := hcur
  have htab5 : get_total_active_balance P { S4 with eth1_data_votes := v } =
      .ok tab := by
    rw [get_total_active_balance_append S4 { S4 with eth1_data_votes := v } [] cur hcur rfl
      (by simp) (by simp) hfar]
    exact htab
  rw [htab5, ok_bind']
  unfold specTailG
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun S6 _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun S7 _ => ?_)
  simp only [pure_bind]
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun S9 _ => ?_)
  exact epochRest2Fulu_sameResultOrBothFail o S9

/-! ## The single pass -/

/-- `lighthouse_single_pass_eq_spec_supply` for Fulu: the registry pass reads `fuluTab`, and
Lighthouse's context holds `fuluTab` as its churn total. -/
theorem lighthouse_single_pass_eq_spec_supply_fulu [PresetCfg] [FuluCfg] (total_active_balance : Gwei)
    (state : BeaconState) (hrows : RowsOk state) (current_epoch : Epoch)
    (hcurrent : get_current_epoch P state = .ok current_epoch)
    (hgenesis : current_epoch ≠ GENESIS_EPOCH)
    (rctx : RewardsContext)
    (hctx : rewardsContextOf P total_active_balance state = .ok rctx)
    (heffective : ∀ i (h : i < state.validators.length),
      rewardsEligible rctx.previous_epoch state.validators[i] = .ok true →
        state.validators[i].effective_balance ≤ 256 * state.balances.getD i 0)
    (hexit : ∀ i (h : i < state.validators.length),
      state.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH)
    (hmax : ∀ v ∈ state.validators,
      v.effective_balance ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hbalance : ∀ i (h : i < state.validators.length), state.balances.getD i 0 < 2 ^ 62)
    (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch P current_epoch =
      .ok activation_epoch)
    (htarget : current_epoch + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble P total_active_balance state.slashings =
      .ok (adjusted, per))
    (hfinalized : state.finalized_checkpoint.epoch ≤ current_epoch)
    (hcurrent64 : current_epoch + 1 < UINT64_SIZE)
    (htotal : P.EFFECTIVE_BALANCE_INCREMENT ≤ total_active_balance)
    (k : Nat) (hk : k ≤ 1152921504)
    (hincrements : rctx.source_increments ≤ k * rctx.active_increments ∧
      rctx.target_increments ≤ k * rctx.active_increments ∧
      rctx.head_increments ≤ k * rctx.active_increments)
    (base_reward : Row → Gwei)
    (hbase : ∀ r ∈ rowsOf state, rewardsEligible rctx.previous_epoch r.validator = .ok true →
      rewardsBaseReward P total_active_balance r.validator = .ok (base_reward r)) :
    SameResultOrBothFail (do
      let s1 ← process_inactivity_updates P state
      let s2 ← process_rewards_and_penalties P total_active_balance s1
      let s3 ← process_registry_updates P (fuluTabM total_active_balance) s2
      process_slashings P total_active_balance s3)
    ((fun y => state.withRowsChurn y.1 y.2) <$>
      passM (fun churn r => lhRowStep P
          (lhContextOf state (fuluTabM total_active_balance) current_epoch rctx per)
          (base_reward r) churn r)
        (state.earliest_exit_epoch, state.exit_balance_to_consume) (rowsOf state)) := by
  obtain ⟨hprevious, -, -, -, -, hleak, htab⟩ :=
    rewardsContextOf_ok P total_active_balance state rctx hctx
  refine SameResultOrBothFail.trans (separate_passes_eq_single_pass_tab P total_active_balance
    (fuluTabM total_active_balance) state hrows current_epoch rctx.previous_epoch rctx.in_leak
    hcurrent hgenesis hprevious hleak rctx hctx activation_epoch hactivation htarget adjusted per
    hpre) (SameResultOrBothFail.of_eq ?_)
  have hstep : ∀ churn r, r ∈ rowsOf state →
      lhRowStep P (lhContextOf state (fuluTabM total_active_balance) current_epoch
        rctx per) (base_reward r) churn r =
      (fun x => (x.1.1.2, x.2)) <$> singlePassStep P (fuluTabM total_active_balance)
        rctx.previous_epoch rctx.in_leak rctx current_epoch state.finalized_checkpoint.epoch
        activation_epoch (current_epoch + P.EPOCHS_PER_SLASHINGS_VECTOR / 2) per
        ((((), ()), churn), ()) r := by
    intro churn r hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    have hiv : i < state.validators.length := by rw [← rowsOf_length]; exact hi
    have hrow := rowsOf_getElem state i hi
    rw [hri] at hrow
    subst hrow
    exact lhRowStep_eq_singlePassStep_of_supply _ (by simpa [lhContextOf] using hgenesis) rctx _
      churn (base_reward _) activation_epoch
      rfl rfl rfl rfl rfl rfl
      (by rw [htab]; exact hbase _ hr) (by rw [htab]; exact htotal) k hk hincrements
      (heffective i hiv) (hmax _ (List.getElem_mem hiv)) (hbalance i hiv) hfinalized hcurrent64
      hactivation (hexit i hiv)
  rw [passM_congr _ _ (rowsOf state) (fun churn r hr => hstep churn r hr)]
  rw [passM_proj (singlePassStep P (fuluTabM total_active_balance)
    rctx.previous_epoch rctx.in_leak rctx current_epoch state.finalized_checkpoint.epoch
    activation_epoch (current_epoch + P.EPOCHS_PER_SLASHINGS_VECTOR / 2) per)
    (fun c => ((((), ()), c), ())) (fun b => b.1.2) (fun _ => rfl) (fun _ => rfl)]
  cases passM _ _ (rowsOf state) <;> rfl

/-- `genesis_passes_eq_single_pass` with the registry total `registry_total`. -/
theorem genesis_passes_eq_single_pass_tab (p : Preset) (total_active_balance registry_total : Gwei)
    (state : BeaconState) (hrows : RowsOk state)
    (hcurrent : get_current_epoch p state = .ok GENESIS_EPOCH) (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch p GENESIS_EPOCH = .ok activation_epoch)
    (htarget : GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble p total_active_balance state.slashings = .ok (adjusted, per)) :
    SameResultOrBothFail (do
      let s1 ← process_inactivity_updates p state
      let s2 ← process_rewards_and_penalties p total_active_balance s1
      let s3 ← process_registry_updates p registry_total s2
      process_slashings p total_active_balance s3)
    ((fun z => state.withRowsChurn z.1.1 z.2) <$>
      passM (bothSteps (registryRowStep p registry_total GENESIS_EPOCH
          state.finalized_checkpoint.epoch activation_epoch)
        (slashingsRowStep p (GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2) per))
        ((state.earliest_exit_epoch, state.exit_balance_to_consume), ()) (rowsOf state)) := by
  rw [process_inactivity_updates_genesis p state hcurrent]
  simp only [bind, Except.bind]
  rw [process_rewards_and_penalties_genesis p total_active_balance state hcurrent]
  dsimp only
  refine SameResultOrBothFail.trans ?_ (passM_seq_bothSteps _ _ _ () (rowsOf state)
    (fun c y => pure (state.withRowsChurn c y.2)))
  apply SameResultOrBothFail.bind_map (process_registry_updates_rows p registry_total state
    GENESIS_EPOCH activation_epoch hrows hcurrent hactivation)
  intro y3 hy3
  have hk3 : y3.2.map rowKey = (rowsOf state).map rowKey :=
    passM_rowKey _ (fun a r x h => by
      rw [registryRowStep_preserves p registry_total GENESIS_EPOCH
        state.finalized_checkpoint.epoch activation_epoch a r x h]; rfl) _ _ y3 hy3
  have hR3 : rowsOf (state.withRowsChurn y3.1 y3.2) = y3.2 := rowsOf_withRows state y3.2 hk3
  have hok3 : RowsOk (state.withRowsChurn y3.1 y3.2) :=
    rowsOk_withRows_of_key state y3.2 hrows hk3
  have h4 := process_slashings_rows_sameResultOrBothFail p total_active_balance
    (state.withRowsChurn y3.1 y3.2) GENESIS_EPOCH hcurrent htarget adjusted per hpre hok3
  rw [hR3] at h4
  refine SameResultOrBothFail.trans h4 (SameResultOrBothFail.of_eq ?_)
  simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  cases passM (slashingsRowStep p (GENESIS_EPOCH + p.EPOCHS_PER_SLASHINGS_VECTOR / 2) per) ()
    y3.2 <;> rfl

/-- `lighthouse_single_pass_eq_spec_genesis` for Fulu. -/
theorem lighthouse_single_pass_eq_spec_genesis_fulu [PresetCfg] [PresetCfg.Ok] [FuluCfg] (total_active_balance : Gwei)
    (state : BeaconState) (hrows : RowsOk state)
    (hcurrent : get_current_epoch P state = .ok GENESIS_EPOCH)
    (rctx : RewardsContext) (hprev : rctx.previous_epoch = GENESIS_EPOCH)
    (hexit : ∀ i (h : i < state.validators.length),
      state.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH)
    (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch P GENESIS_EPOCH =
      .ok activation_epoch)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble P total_active_balance state.slashings =
      .ok (adjusted, per))
    (hfinalized : state.finalized_checkpoint.epoch ≤ GENESIS_EPOCH)
    (base_reward : Row → Gwei) :
    SameResultOrBothFail (do
      let s1 ← process_inactivity_updates P state
      let s2 ← process_rewards_and_penalties P total_active_balance s1
      let s3 ← process_registry_updates P (fuluTabM total_active_balance) s2
      process_slashings P total_active_balance s3)
    ((fun y => state.withRowsChurn y.1 y.2) <$>
      passM (fun churn r => lhRowStep P
          (lhContextOf state (fuluTabM total_active_balance) GENESIS_EPOCH rctx per)
          (base_reward r) churn r)
        (state.earliest_exit_epoch, state.exit_balance_to_consume) (rowsOf state)) := by
  refine SameResultOrBothFail.trans (genesis_passes_eq_single_pass_tab P total_active_balance
    (fuluTabM total_active_balance) state hrows hcurrent activation_epoch hactivation
    (P_slashings_target_lt (by decide))
    adjusted per hpre) (SameResultOrBothFail.of_eq ?_)
  have hstep : ∀ churn r, r ∈ rowsOf state →
      lhRowStep P (lhContextOf state (fuluTabM total_active_balance) GENESIS_EPOCH
        rctx per) (base_reward r) churn r =
      (fun x => (x.1.1, x.2)) <$> bothSteps (registryRowStep P
        (fuluTabM total_active_balance) GENESIS_EPOCH state.finalized_checkpoint.epoch
        activation_epoch)
        (slashingsRowStep P
          (GENESIS_EPOCH + P.EPOCHS_PER_SLASHINGS_VECTOR / 2) per) (churn, ()) r := by
    intro churn r hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    have hiv : i < state.validators.length := by rw [← rowsOf_length]; exact hi
    have hrow := rowsOf_getElem state i hi
    rw [hri] at hrow
    subst hrow
    exact lhRowStep_genesis P _ rfl _ churn _ activation_epoch
      (by simp only [lhContextOf, hprev, GENESIS_EPOCH, UINT64_SIZE]; decide) (by pdecide)
      (by simpa only [lhContextOf] using hfinalized)
      (by simp only [lhContextOf, GENESIS_EPOCH, UINT64_SIZE]; decide) hactivation (hexit i hiv)
  rw [passM_congr _ _ (rowsOf state) (fun churn r hr => hstep churn r hr)]
  rw [passM_proj (bothSteps (registryRowStep P (fuluTabM total_active_balance)
      GENESIS_EPOCH state.finalized_checkpoint.epoch activation_epoch)
      (slashingsRowStep P
        (GENESIS_EPOCH + P.EPOCHS_PER_SLASHINGS_VECTOR / 2) per))
    (fun c => (c, ())) (fun b => b.1) (fun _ => rfl) (fun _ => rfl)]
  cases passM _ _ (rowsOf state) <;> rfl

/-- The Fulu spec steps after the four passes give the same `ok` results as `tailNFG` at the
Fulu churn total, with `epochRest2Fulu` after the consolidations. -/
theorem epochRestFulu_nf [PresetCfg] [PresetCfg.Ok] [FuluCfg] (o : Oracle) (s1 : BeaconState) (current_epoch : Epoch)
    (total_active_balance : Gwei) (ctx : LhStepContext) (bf : Row → Gwei)
    (churn : Epoch × Gwei) (rows : List Row) (activation_epoch : Epoch)
    (hpass : passM (fun c r => lhRowStep P ctx (bf r) c r)
      (s1.earliest_exit_epoch, s1.exit_balance_to_consume) (rowsOf s1) = .ok (churn, rows))
    (hctxcur : ctx.current_epoch = current_epoch)
    (hctxfin : ctx.finalized_epoch = s1.finalized_checkpoint.epoch)
    (hcur : get_current_epoch P s1 = .ok current_epoch)
    (hfin : s1.finalized_checkpoint.epoch ≤ current_epoch)
    (hnext : current_epoch + 1 < FAR_FUTURE_EPOCH)
    (hact : compute_activation_exit_epoch P current_epoch = .ok activation_epoch)
    (hexit : ∀ i (h : i < s1.validators.length), s1.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH)
    (hvalid : ∀ v ∈ s1.validators, v.exit_epoch = FAR_FUTURE_EPOCH →
      v.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (htab4 : get_total_active_balance P (s1.withRowsChurn churn rows) =
      .ok total_active_balance)
    (hbal4 : ∀ r ∈ rows, r.balance < 2 ^ 64)
    (hnamed : ∀ i ∈ consolidationIndices s1, i < s1.validators.length) :
    SameResultOrBothFail (epochRestFulu o (s1.withRowsChurn churn rows))
      (tailNFG o (epochRest2Fulu o) s1 (s1.withRowsChurn churn rows)
        (fuluTabM total_active_balance) current_epoch) := by
  have hfar : current_epoch < FAR_FUTURE_EPOCH := Nat.lt_trans (Nat.lt_succ_self _) hnext
  have hcur4 : get_current_epoch P (s1.withRowsChurn churn rows) =
      .ok current_epoch := hcur
  refine SameResultOrBothFail.trans (epochRestFulu_specTail o _ total_active_balance current_epoch hcur4 hfar
    htab4) ?_
  have hK : (fun t => (pure t : SpecM BeaconState) >>= epochRest2Fulu o) = epochRest2Fulu o :=
    funext fun t => pure_bind _ _
  have h := specRest_nf o pure (epochRest2Fulu o) ebBlind_pure s1 current_epoch
    (fuluTabM total_active_balance) ctx bf churn rows activation_epoch hpass hctxcur hctxfin hcur
    hfin hnext hact hexit hvalid hbal4 hnamed
  rw [hK] at h
  exact h

/-- `process_epoch_lh_full_fulu_sameResultOrBothFail'` at the genesis epoch. Justification and finalization return
the state, the spec skips the inactivity and rewards steps, and the single pass skips them
through `after_genesis`. -/
theorem process_epoch_lh_full_fulu_genesis [PresetCfg] [PresetCfg.Ok] [FuluCfg] [FuluCfg.Ok] (o : Oracle) (t : BeaconState) (hb : BoundaryOk t)
    (hexitb : ExitBounds t) (hsupply_t : EpochBalanceBounds t) (hvalid : WithdrawableValid t)
    (hcons : ConsolidationsInRange t)
    (hgen : t.slot / P.SLOTS_PER_EPOCH = GENESIS_EPOCH) :
    SameResultOrBothFail (process_epoch_lh_full_fulu o t)
      (process_epoch_fulu P FC o t) := by
  obtain ⟨hinv, hrows, -⟩ := hb
  obtain ⟨hbalance, hsupply, hslashings⟩ := hsupply_t
  have hcurrent : get_current_epoch P t = .ok GENESIS_EPOCH := by
    rw [← hgen]
    simp [get_current_epoch, compute_epoch_at_slot, uint64Div, Nat.ne_of_gt P_slots_pos, pure,
      Except.pure]
  unfold process_epoch_lh_full_fulu
  rw [process_epoch_fulu_parts]
  refine SameResultOrBothFail.bind (lhJustificationAndFinalization_sameResultOrBothFail _ _) (fun s1 h1 => ?_)
  replace h1 := (lhJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1
  have hs1 : s1 = t := by
    unfold process_justification_and_finalization at h1
    simp [hcurrent, GENESIS_EPOCH, bind, Except.bind, pure, Except.pure] at h1
    exact h1.symm
  subst hs1
  have hfin0 : s1.finalized_checkpoint.epoch = GENESIS_EPOCH := by
    have h := hinv.finalized_le
    simp only [epochOf] at h
    rw [hgen] at h
    exact Nat.le_zero.mp h
  have hS64 : totalEffectiveBalance s1 < 2 ^ 64 := Nat.lt_trans hsupply (by decide)
  obtain ⟨tab, htab, htab_lo, -⟩ :=
    get_total_active_balance_bounds P s1 GENESIS_EPOCH hcurrent hS64
  obtain ⟨rctx, hctx, hprevr⟩ :=
    rewardsContextOf_genesis P tab s1 hrows hcurrent (by pdecide) hS64 hfin0
  have hactivation := compute_activation_exit_epoch_of_lt P GENESIS_EPOCH
    (by pdecide)
  obtain ⟨adj, per, hpre⟩ := slashingsPreamble_ok tab s1.slashings hslashings htab_lo
  have hexit1 : ∀ i (h : i < s1.validators.length),
      s1.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH :=
    fun i h => hexitb _ (List.getElem_mem h)
  have hcfar : GENESIS_EPOCH < FAR_FUTURE_EPOCH := by decide
  -- The four spec steps equal the first Lighthouse pass.
  have hfour := SameResultOrBothFail.trans (specFourStepsFulu_sameResultOrBothFail s1 tab htab hrows
    GENESIS_EPOCH _ hcurrent hactivation hcfar)
    (lighthouse_single_pass_eq_spec_genesis_fulu tab s1 hrows hcurrent rctx hprevr hexit1 _
      hactivation adj per hpre (Nat.le_of_eq hfin0) (lhBaseReward tab))
  -- The Lighthouse tail reaches `tailNF`.
  refine SameResultOrBothFail.trans (lhFullTailG_nf o fuluTabM (fun _ => epochRest2Fulu o) s1 GENESIS_EPOCH tab rctx adj per _ _ hcurrent htab hctx
    hpre hysteresisThresholds_mainnet hrows) ?_
  -- The spec tail reaches `tailNF`.
  refine SameResultOrBothFail.flip ?_
  refine SameResultOrBothFail.trans (SameResultOrBothFail.bind hfour (fun _ _ => SameResultOrBothFail.refl _)) ?_
  rw [map_bind']
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun x hx => ?_)
  have hspec := (hfour (s1.withRowsChurn x.1 x.2)).mpr (by rw [hx]; rfl)
  have htab4 := fourStepsFulu_total s1 tab htab hrows GENESIS_EPOCH _ hcurrent hactivation hcfar _
    ((specFourStepsFulu_sameResultOrBothFail s1 tab htab hrows GENESIS_EPOCH _ hcurrent hactivation
      hcfar _).mp hspec)
  exact epochRestFulu_nf o s1 GENESIS_EPOCH tab _ _ x.1 x.2 _ hx rfl rfl hcurrent
    (Nat.le_of_eq hfin0) (by decide) hactivation hexit1 hvalid htab4
    (pass_balances_lt _ _ s1 _ x
      (fun i h => Nat.lt_trans (hbalance i h) (by decide)) hx)
    (consolidationIndices_lt s1 hcons)

/-- On mainnet, at a state that the Fulu `process_epoch` starts from, the Lighthouse Fulu epoch
with the deposits and effective balance updates in the single pass gives the same `ok` results
as the Fulu spec epoch. Beyond the hypotheses of `process_epoch_lh_sameResultOrBothFail'` it needs `WithdrawableValid`,
for the deposit statuses that Lighthouse predicts, and `ConsolidationsInRange`, so that the
validators that consolidations name are existing validators. -/
theorem process_epoch_lh_full_fulu_sameResultOrBothFail' [PresetCfg] [PresetCfg.Ok] [FuluCfg] [FuluCfg.Ok] (o : Oracle) (t : BeaconState) (hb : BoundaryOk t)
    (hslot : t.slot < 2 ^ 64) (heb : EBOk P t) (hexitb : ExitBounds t)
    (hsupply_t : EpochBalanceBounds t) (hvalid : WithdrawableValid t)
    (hcons : ConsolidationsInRange t) :
    SameResultOrBothFail (process_epoch_lh_full_fulu o t)
      (process_epoch_fulu P FC o t) := by
  obtain ⟨hinv, hrows, heffective⟩ := hb
  obtain ⟨hbalance, hsupply, hslashings⟩ := hsupply_t
  by_cases hgen : t.slot / P.SLOTS_PER_EPOCH = GENESIS_EPOCH
  · exact process_epoch_lh_full_fulu_genesis o t ⟨hinv, hrows, heffective⟩ hexitb
      ⟨hbalance, hsupply, hslashings⟩ hvalid hcons hgen
  unfold process_epoch_lh_full_fulu
  have hcurrent : get_current_epoch P t =
      .ok (t.slot / P.SLOTS_PER_EPOCH) := by
    simp [get_current_epoch, compute_epoch_at_slot, uint64Div, Nat.ne_of_gt P_slots_pos, pure,
      Except.pure]
  have hepoch : t.slot / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE :=
    P_slot_target_lt hslot
  unfold EntryEB at heffective
  generalize hce : t.slot / P.SLOTS_PER_EPOCH = current_epoch
  rw [hce] at hcurrent hepoch hgen heffective
  have h32 : @LT.lt Nat _ (current_epoch + 32) (2 ^ 64) := P_target_bound hepoch
  rw [process_epoch_fulu_parts]
  refine SameResultOrBothFail.bind (lhJustificationAndFinalization_sameResultOrBothFail _ _) (fun s1 h1 => ?_)
  replace h1 := (lhJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1
  obtain ⟨_, _, _, _, hs1⟩ := process_justification_and_finalization_shape _ _ _ h1
  have hcur1 : get_current_epoch P s1 = .ok current_epoch := by
    rw [hs1]; exact hcurrent
  have hfin := process_justification_and_finalization_finalized _ t s1 current_epoch hcurrent
    hgen hinv h1
  have hrows1 : RowsOk s1 := by rw [hs1]; exact hrows
  have heff1 : ∀ i (h : i < s1.validators.length),
      rewardsEligible (current_epoch - 1) s1.validators[i] = .ok true →
        s1.validators[i].effective_balance ≤ 256 * s1.balances.getD i 0 := by
    rw [hs1]; exact heffective
  have hexit1 : ∀ i (h : i < s1.validators.length),
      s1.validators[i].exit_epoch ≤ FAR_FUTURE_EPOCH := by
    rw [hs1]; exact fun i h => hexitb _ (List.getElem_mem h)
  have hmax1 : ∀ v ∈ s1.validators,
      v.effective_balance ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA := by
    rw [hs1]; exact fun v hv => (heb v hv).2
  have hbal1 : ∀ i (h : i < s1.validators.length), s1.balances.getD i 0 < 2 ^ 62 := by
    rw [hs1]; exact hbalance
  have hvalid1 : ∀ v ∈ s1.validators, v.exit_epoch = FAR_FUTURE_EPOCH →
      v.withdrawable_epoch = FAR_FUTURE_EPOCH := by
    rw [hs1]; exact hvalid
  have hnamed : ∀ i ∈ consolidationIndices s1, i < s1.validators.length := by
    intro i hi
    have hi' : i ∈ (s1.pending_consolidations.flatMap fun c =>
        [c.source_index, c.target_index]).eraseDups :=
      (List.mem_mergeSort).mp hi
    have hi'' := List.mem_eraseDups.mp hi'
    obtain ⟨c, hc, hic⟩ := List.mem_flatMap.mp hi''
    have hc' : c ∈ t.pending_consolidations := by rw [hs1] at hc; exact hc
    have hlen : s1.validators.length = t.validators.length := by rw [hs1]
    rw [hlen]
    rcases List.mem_cons.mp hic with rfl | hic
    · exact (hcons c hc').1
    · rcases List.mem_singleton.mp hic with rfl
      exact (hcons c hc').2
  have hS1 : totalEffectiveBalance s1 = totalEffectiveBalance t := by rw [hs1]; rfl
  have hsl1 : s1.slashings = t.slashings := by rw [hs1]
  rw [← hS1] at hsupply
  rw [← hsl1] at hslashings
  simp only [GENESIS_EPOCH] at hgen
  have hS64 : totalEffectiveBalance s1 < 2 ^ 64 := Nat.lt_trans hsupply (by decide)
  obtain ⟨tab, htab, htab_lo, -⟩ :=
    get_total_active_balance_bounds P s1 current_epoch hcur1 hS64
  have hprev : get_previous_epoch P s1 = .ok (current_epoch - 1) := by
    have hsat : saturating_sub current_epoch 1 = current_epoch - 1 :=
      saturating_sub_one' current_epoch
    simp only [get_previous_epoch, hcur1, ok_bind'', hsat]
    rfl
  obtain ⟨rctx, hctx, hsrc, htgt, hhd⟩ := rewardsContextOf_bounds P tab s1 hrows1
    current_epoch (current_epoch - 1) hcur1 hprev (by epoch_omega) (by pdecide) hS64
    (by epoch_omega)
  obtain ⟨hprev', -, -, -, hactive, -, -⟩ := rewardsContextOf_ok _ _ _ rctx hctx
  rw [hprev] at hprev'
  have hpe : rctx.previous_epoch = current_epoch - 1 := (Except.ok.inj hprev').symm
  have hact_eq : rctx.active_increments = tab / P.EFFECTIVE_BALANCE_INCREMENT := by
    simp only [uint64Div] at hactive
    split at hactive
    · cases hactive
    · exact (Except.ok.inj hactive).symm
  have hactivation := compute_activation_exit_epoch_of_lt P current_epoch
    (P_target_activation hepoch)
  obtain ⟨adj, per, hpre⟩ := slashingsPreamble_ok tab s1.slashings hslashings htab_lo
  have hk : max P.EFFECTIVE_BALANCE_INCREMENT (totalEffectiveBalance s1) /
      P.EFFECTIVE_BALANCE_INCREMENT ≤ 1152921504 := by
    have : max P.EFFECTIVE_BALANCE_INCREMENT (totalEffectiveBalance s1) <
        2 ^ 60 := Nat.max_lt.mpr ⟨by pdecide, hsupply⟩
    have hINC : P.EFFECTIVE_BALANCE_INCREMENT = 1000000000 := rfl
    obtain ⟨(m : Nat), hm⟩ : ∃ m : Nat,
        max P.EFFECTIVE_BALANCE_INCREMENT (totalEffectiveBalance s1) = m :=
      ⟨_, rfl⟩
    rw [hm] at this ⊢
    rw [hINC]
    have h60 : m < 1152921504606846976 := this
    show m / 1000000000 ≤ 1152921504
    omega
  have hact1 : 1 ≤ rctx.active_increments := by
    rw [hact_eq]
    exact (Nat.le_div_iff_mul_le (by pdecide)).mpr (by simpa using htab_lo)
  have hle : ∀ x, x ≤ max P.EFFECTIVE_BALANCE_INCREMENT (totalEffectiveBalance s1) /
      P.EFFECTIVE_BALANCE_INCREMENT →
      x ≤ max P.EFFECTIVE_BALANCE_INCREMENT (totalEffectiveBalance s1) /
        P.EFFECTIVE_BALANCE_INCREMENT * rctx.active_increments :=
    fun x hx => Nat.le_trans hx (Nat.le_mul_of_pos_right _ hact1)
  have hcfar : current_epoch < FAR_FUTURE_EPOCH := (P_target_far hepoch).1
  have hnext : current_epoch + 1 < FAR_FUTURE_EPOCH := (P_target_far hepoch).2
  -- The four spec steps equal the first Lighthouse pass.
  have hfour := SameResultOrBothFail.trans (specFourStepsFulu_sameResultOrBothFail s1 tab htab hrows1
    current_epoch _ hcur1 hactivation hcfar)
    (lighthouse_single_pass_eq_spec_supply_fulu tab s1 hrows1 current_epoch hcur1
    (by simpa [GENESIS_EPOCH] using hgen) rctx hctx (hpe ▸ heff1) hexit1 hmax1 hbal1 _
    hactivation hepoch adj per hpre
    (Nat.le_of_succ_le hfin) (P_target_succ hepoch)
    htab_lo
    _ hk ⟨hle _ hsrc, hle _ htgt, hle _ hhd⟩ (lhBaseReward tab) (by
      intro r hr _
      obtain ⟨b, hb⟩ := rewardsBaseReward_ok_mainnet tab r.validator htab_lo
        (hmax1 _ (by rw [← rowsOf_map_validator]; exact List.mem_map_of_mem hr))
      unfold lhBaseReward; rw [hb]))
  -- The Lighthouse tail reaches `tailNF`.
  refine SameResultOrBothFail.trans (lhFullTailG_nf o fuluTabM (fun _ => epochRest2Fulu o) s1 current_epoch tab rctx adj per _ _ hcur1 htab hctx
    hpre hysteresisThresholds_mainnet hrows1) ?_
  -- The spec tail reaches `tailNF`.
  refine SameResultOrBothFail.flip ?_
  refine SameResultOrBothFail.trans (SameResultOrBothFail.bind hfour (fun _ _ => SameResultOrBothFail.refl _)) ?_
  rw [map_bind']
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun x hx => ?_)
  have hspec := (hfour (s1.withRowsChurn x.1 x.2)).mpr (by rw [hx]; rfl)
  have htab4 := fourStepsFulu_total s1 tab htab hrows1 current_epoch _ hcur1 hactivation hcfar _
    ((specFourStepsFulu_sameResultOrBothFail s1 tab htab hrows1 current_epoch _ hcur1 hactivation
      hcfar _).mp hspec)
  exact epochRestFulu_nf o s1 current_epoch tab _ _ x.1 x.2 _ hx rfl rfl hcur1
    (Nat.le_of_succ_le hfin) hnext hactivation hexit1 hvalid1 htab4
    (pass_balances_lt _ _ s1 _ x
      (fun i h => Nat.lt_trans (hbal1 i h) (by decide)) hx) hnamed


end EpochProofs.Spec
