import EpochProofs.Spec.FuluEpoch
import EpochProofs.Sanity.FuluRegistry
import EpochProofs.Sanity.Rows

/-!
# The Fulu `process_epoch` in terms of the Gloas steps

- `process_sync_committee_updates_fulu_sameResultOrBothFail`: the Fulu sync committee update gives the same
  `ok` results as the Gloas one (`get_next_sync_committee_indices_fulu_iff`).
- `process_epoch_fulu_eq_tab`: in Fulu `process_epoch`, the registry update and the pending
  deposits are the Gloas functions at `fuluTab` (`process_registry_updates_fulu_eq`,
  `process_pending_deposits_fulu_tab_eq`).
-/

namespace EpochProofs.Spec

theorem get_next_sync_committee_fulu_sameResultOrBothFail (p : Preset) (o : Oracle) (state : BeaconState)
    (hsize : 0 < p.SYNC_COMMITTEE_SIZE) :
    SameResultOrBothFail (get_next_sync_committee_fulu p o state) (get_next_sync_committee p o state) := by
  unfold get_next_sync_committee_fulu get_next_sync_committee
  exact SameResultOrBothFail.bind (get_next_sync_committee_indices_fulu_iff p o state hsize)
    (fun _ _ => SameResultOrBothFail.refl _)

/-- The Fulu sync committee update gives the same `ok` results as the Gloas one. -/
theorem process_sync_committee_updates_fulu_sameResultOrBothFail (p : Preset) (o : Oracle)
    (state : BeaconState) (hsize : 0 < p.SYNC_COMMITTEE_SIZE) :
    SameResultOrBothFail (process_sync_committee_updates_fulu p o state)
      (process_sync_committee_updates p o state) := by
  unfold process_sync_committee_updates_fulu process_sync_committee_updates
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  split
  · exact SameResultOrBothFail.bind (get_next_sync_committee_fulu_sameResultOrBothFail p o _ hsize) (fun _ _ => SameResultOrBothFail.refl _)
  · exact SameResultOrBothFail.refl _

/-- Fulu `process_epoch` with the registry update and the pending deposits written as the Gloas
functions at `fuluTab`. -/
theorem process_epoch_fulu_eq_tab (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (state : BeaconState) :
    process_epoch_fulu p f o state = (do
      let state ← process_justification_and_finalization p state
      let state ← process_inactivity_updates p state
      let state ← process_rewards_and_penalties p (← get_total_active_balance p state) state
      let state ← process_registry_updates p (fuluTab p f (← get_total_active_balance p state))
        state
      let state ← process_slashings p (← get_total_active_balance p state) state
      let state ← process_eth1_data_reset p state
      let state ← process_pending_deposits p (fuluTab p f (← get_total_active_balance p state))
        (apply_pending_deposit p o) state
      let state ← process_pending_consolidations p state
      let state ← process_effective_balance_updates p state
      let state ← process_slashings_reset p state
      let state ← process_randao_mixes_reset p state
      let state ← process_historical_summaries_update p o state
      let state := process_participation_flag_updates state
      let state ← process_sync_committee_updates_fulu p o state
      process_proposer_lookahead_fulu p o state) := by
  unfold process_epoch_fulu
  simp only [process_registry_updates_fulu_eq p f hc, process_pending_deposits_fulu_tab_eq p f hc]

end EpochProofs.Spec
