use super::errors::EpochProcessingError;
use super::tail_updates::{
    eth1_data_votes_reset_due, randao_mixes_reset_indices, slashings_reset_index,
};
use milhouse::List;
use typenum::Unsigned;
use types::core::EthSpec;
use types::state::{BeaconState, BeaconStateError};

pub fn process_eth1_data_reset<E: EthSpec>(
    state: &mut BeaconState<E>,
) -> Result<(), EpochProcessingError> {
    if eth1_data_votes_reset_due(state.slot().as_u64(), E::SlotsPerEth1VotingPeriod::to_u64())? {
        *state.eth1_data_votes_mut() = List::empty();
    }
    Ok(())
}

pub fn process_slashings_reset<E: EthSpec>(
    state: &mut BeaconState<E>,
) -> Result<(), EpochProcessingError> {
    let index = slashings_reset_index(
        state.current_epoch().as_u64(),
        E::EpochsPerSlashingsVector::to_u64(),
    )?
    .ok_or(BeaconStateError::EpochOutOfBounds)? as usize;
    *state
        .slashings_mut()
        .get_mut(index)
        .ok_or(BeaconStateError::SlashingsOutOfBounds(index))? = 0;
    Ok(())
}

pub fn process_randao_mixes_reset<E: EthSpec>(
    state: &mut BeaconState<E>,
) -> Result<(), EpochProcessingError> {
    let (source, target) = randao_mixes_reset_indices(
        state.current_epoch().as_u64(),
        E::EpochsPerHistoricalVector::to_u64(),
    )?
    .ok_or(BeaconStateError::EpochOutOfBounds)?;
    let (source, target) = (source as usize, target as usize);
    let mix = *state
        .randao_mixes()
        .get(source)
        .ok_or(BeaconStateError::RandaoMixesOutOfBounds(source))?;
    *state
        .randao_mixes_mut()
        .get_mut(target)
        .ok_or(BeaconStateError::RandaoMixesOutOfBounds(target))? = mix;
    Ok(())
}
