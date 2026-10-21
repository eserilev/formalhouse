use crate::EpochProcessingError;
use crate::per_epoch_processing::tail_updates::historical_summary_due;
use types::state::HistoricalSummary;
use types::{BeaconState, EthSpec};

pub fn process_historical_summaries_update<E: EthSpec>(
    state: &mut BeaconState<E>,
) -> Result<(), EpochProcessingError> {
    // Set historical block root accumulator.
    let next_epoch = state.next_epoch()?;
    if historical_summary_due(
        next_epoch.as_u64(),
        E::slots_per_historical_root() as u64,
        E::slots_per_epoch(),
    )? {
        // We need to flush any pending mutations before hashing.
        state.block_roots_mut().apply_updates()?;
        state.state_roots_mut().apply_updates()?;
        let summary = HistoricalSummary::new(state);
        return state
            .historical_summaries_mut()?
            .push(summary)
            .map_err(Into::into);
    }
    Ok(())
}
