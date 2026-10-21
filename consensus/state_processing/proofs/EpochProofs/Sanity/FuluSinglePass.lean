import EpochProofs.Sanity.LighthouseSinglePass
import EpochProofs.Sanity.FuluRegistry

/-!
# The Lighthouse Fulu single pass equals the Fulu spec passes

`lighthouse_single_pass_eq_spec_fulu` is `lighthouse_single_pass_eq_spec` for Fulu on mainnet.
The spec side runs the Fulu inactivity, rewards, registry and slashings passes. Only the
registry pass differs from Gloas: its churn is `get_activation_exit_churn_limit`. Lighthouse runs
`lhRowStep` with the registry total `fuluTab` (`single_pass_step_equiv_fulu`), and
`process_registry_updates_fulu_eq` makes the Fulu registry pass the Gloas pass at `fuluTab`.
-/

namespace EpochProofs.Spec

/-- On mainnet, one pass of `lhRowStep` with the registry total `fuluTab` gives the same `ok`
results as the Fulu inactivity, rewards, registry and slashings passes. The hypotheses are the
ones of `lighthouse_single_pass_eq_spec`. -/
theorem lighthouse_single_pass_eq_spec_fulu (total_active_balance : Gwei) (state : BeaconState)
    (hrows : RowsOk state) (current_epoch : Epoch)
    (hcurrent : get_current_epoch Preset.mainnet state = .ok current_epoch)
    (hgenesis : current_epoch ≠ GENESIS_EPOCH)
    (rctx : RewardsContext)
    (hctx : rewardsContextOf Preset.mainnet total_active_balance state = .ok rctx)
    (hentry : EpochEntry state rctx.previous_epoch)
    (activation_epoch : Epoch)
    (hactivation : compute_activation_exit_epoch Preset.mainnet current_epoch =
      .ok activation_epoch)
    (htarget : current_epoch + Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE)
    (adjusted per : Gwei)
    (hpre : slashingsPreamble Preset.mainnet total_active_balance state.slashings =
      .ok (adjusted, per))
    (hfinalized : state.finalized_checkpoint.epoch ≤ current_epoch)
    (hcurrent64 : current_epoch + 1 < UINT64_SIZE)
    (htotal : Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT ≤ total_active_balance)
    (hincrements : rctx.source_increments ≤ 256 * rctx.active_increments ∧
      rctx.target_increments ≤ 256 * rctx.active_increments ∧
      rctx.head_increments ≤ 256 * rctx.active_increments)
    (base_reward : Row → Gwei)
    (hbase : ∀ r ∈ rowsOf state, rewardsEligible rctx.previous_epoch r.validator = .ok true →
      rewardsBaseReward Preset.mainnet total_active_balance r.validator = .ok (base_reward r)) :
    SameOk (do
      let s1 ← process_inactivity_updates Preset.mainnet state
      let s2 ← process_rewards_and_penalties Preset.mainnet total_active_balance s1
      let s3 ← process_registry_updates_fulu Preset.mainnet FuluConfig.mainnet total_active_balance
        s2
      process_slashings Preset.mainnet total_active_balance s3)
    ((fun y => state.withRowsChurn y.1 y.2) <$>
      passM (fun churn r => lhRowStep Preset.mainnet
          (lhContextOf state (fuluTab Preset.mainnet FuluConfig.mainnet total_active_balance)
            current_epoch rctx per) (base_reward r) churn r)
        (state.earliest_exit_epoch, state.exit_balance_to_consume) (rowsOf state)) := by
  simp only [process_registry_updates_fulu_eq Preset.mainnet FuluConfig.mainnet fuluCompat_mainnet]
  obtain ⟨hprevious, -, -, -, -, hleak, htab⟩ :=
    rewardsContextOf_ok Preset.mainnet total_active_balance state rctx hctx
  refine SameOk.trans (separate_passes_eq_single_pass_tab Preset.mainnet total_active_balance
    (fuluTab Preset.mainnet FuluConfig.mainnet total_active_balance) state hrows current_epoch
    rctx.previous_epoch rctx.in_leak hcurrent hgenesis hprevious hleak rctx hctx activation_epoch
    hactivation htarget adjusted per hpre) (SameOk.of_eq ?_)
  have hstep : ∀ churn r, r ∈ rowsOf state →
      lhRowStep Preset.mainnet (lhContextOf state
        (fuluTab Preset.mainnet FuluConfig.mainnet total_active_balance) current_epoch rctx per)
        (base_reward r) churn r =
      (fun x => (x.1.1.2, x.2)) <$> singlePassStep Preset.mainnet
        (fuluTab Preset.mainnet FuluConfig.mainnet total_active_balance)
        rctx.previous_epoch rctx.in_leak rctx current_epoch state.finalized_checkpoint.epoch
        activation_epoch (current_epoch + Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR / 2) per
        ((((), ()), churn), ()) r := by
    intro churn r hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    have hiv : i < state.validators.length := by rw [← rowsOf_length]; exact hi
    have hrow := rowsOf_getElem state i hi
    rw [hri] at hrow
    subst hrow
    exact lhRowStep_eq_singlePassStep_of_bounds _ (by simpa [lhContextOf] using hgenesis) rctx _
      churn (base_reward _) activation_epoch
      rfl rfl rfl rfl rfl rfl
      (by rw [htab]; exact hbase _ hr) (by rw [htab]; exact htotal) hincrements
      (hentry.effective_balance i hiv) (hentry.supply i hiv) hfinalized hcurrent64 hactivation
      (hentry.exit_epoch i hiv)
  rw [passM_congr _ _ (rowsOf state) (fun churn r hr => hstep churn r hr)]
  rw [passM_proj (singlePassStep Preset.mainnet
    (fuluTab Preset.mainnet FuluConfig.mainnet total_active_balance) rctx.previous_epoch
    rctx.in_leak rctx current_epoch state.finalized_checkpoint.epoch activation_epoch
    (current_epoch + Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR / 2) per)
    (fun c => ((((), ()), c), ())) (fun b => b.1.2) (fun _ => rfl) (fun _ => rfl)]
  cases passM _ _ (rowsOf state) <;> rfl

end EpochProofs.Spec
