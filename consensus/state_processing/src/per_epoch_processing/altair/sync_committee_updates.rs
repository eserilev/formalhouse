use crate::EpochProcessingError;
use crate::per_epoch_processing::epoch_committees;
use crate::per_epoch_processing::single_pass::selection_constants;
use safe_arith::SafeArith;
use std::sync::Arc;
use swap_or_not_shuffle::Sha256Hash;
use typenum::Unsigned;
use types::core::{ChainSpec, Domain, EthSpec};
use types::state::{BeaconState, BeaconStateError};

pub fn process_sync_committee_updates<E: EthSpec>(
    state: &mut BeaconState<E>,
    spec: &ChainSpec,
) -> Result<(), EpochProcessingError> {
    let next_epoch = state.next_epoch()?;
    if next_epoch.safe_rem(spec.epochs_per_sync_committee_period)? == 0 {
        *state.current_sync_committee_mut()? = state.next_sync_committee()?.clone();

        let next_sync_committee = if state.fork_name_unchecked().electra_enabled() {
            let indices = state.get_active_validator_indices(next_epoch, spec)?;
            let mix = *state.get_seed_mix(next_epoch, spec)?;
            let sync_committee_indices =
                epoch_committees::next_sync_committee_indices::<Sha256Hash, _>(
                    &*state,
                    &indices,
                    &spec
                        .get_domain_constant(Domain::SyncCommittee)
                        .to_le_bytes(),
                    next_epoch.as_u64(),
                    &mix.0,
                    E::SyncCommitteeSize::to_usize(),
                    &selection_constants(state, spec),
                )
                .map_err(BeaconStateError::from)?;
            state.sync_committee_from_indices(&sync_committee_indices)?
        } else {
            state.get_next_sync_committee(spec)?
        };
        *state.next_sync_committee_mut()? = Arc::new(next_sync_committee);
    }
    Ok(())
}
