import EpochProofs.Spec.Epoch
import EpochProofs.Spec.Fulu

/-!
# Reference: the Fulu `process_epoch`

Transcribed from `specs/fulu/beacon-chain.md` (v1.7.0-beta.2). Fulu has no builder payments and
no PTC window. Its registry update, pending deposits, sync committee update and proposer
lookahead are the Fulu functions of `Spec/Fulu.lean`. The other steps are the shared functions,
which read the same text in Fulu and Gloas.
-/

namespace EpochProofs.Spec

/-- ```python
def process_epoch(state: BeaconState) -> None:
    process_justification_and_finalization(state)
    process_inactivity_updates(state)
    process_rewards_and_penalties(state)
    process_registry_updates(state)
    process_slashings(state)
    process_eth1_data_reset(state)
    process_pending_deposits(state)
    process_pending_consolidations(state)
    process_effective_balance_updates(state)
    process_slashings_reset(state)
    process_randao_mixes_reset(state)
    process_historical_summaries_update(state)
    process_participation_flag_updates(state)
    process_sync_committee_updates(state)
    # [New in Fulu:EIP7917]
    process_proposer_lookahead(state)
```

As in `process_epoch`, the steps that read `get_total_active_balance(state)` take it from the
state right before the step. -/
def process_epoch_fulu (p : Preset) (f : FuluConfig) (o : Oracle) (state : BeaconState) :
    SpecM BeaconState := do
  let state ← process_justification_and_finalization p state
  let state ← process_inactivity_updates p state
  let state ← process_rewards_and_penalties p (← get_total_active_balance p state) state
  let state ← process_registry_updates_fulu p f (← get_total_active_balance p state) state
  let state ← process_slashings p (← get_total_active_balance p state) state
  let state ← process_eth1_data_reset p state
  let state ← process_pending_deposits_fulu p f (← get_total_active_balance p state)
    (apply_pending_deposit p o) state
  let state ← process_pending_consolidations p state
  let state ← process_effective_balance_updates p state
  let state ← process_slashings_reset p state
  let state ← process_randao_mixes_reset p state
  let state ← process_historical_summaries_update p o state
  let state := process_participation_flag_updates state
  let state ← process_sync_committee_updates_fulu p o state
  process_proposer_lookahead_fulu p o state

end EpochProofs.Spec
