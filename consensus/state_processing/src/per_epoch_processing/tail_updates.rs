//! Pure core of the reset and historical summary steps at the end of the epoch.
//!
//! Aeneas translates this module for the proofs in `../../proofs`.

use safe_arith::{ArithError, SafeArith};

/// `true` when the eth1 data votes reset after `slot`, the last slot of an epoch.
pub fn eth1_data_votes_reset_due(
    slot: u64,
    slots_per_eth1_voting_period: u64,
) -> Result<bool, ArithError> {
    Ok(slot.safe_add(1)?.safe_rem(slots_per_eth1_voting_period)? == 0)
}

/// The position of `epoch` in a vector of `length` items indexed by epoch, or `None` when the
/// state does not keep `epoch`. The state keeps the epochs after `current_epoch - length`, up to
/// `current_epoch`, or up to `current_epoch + 1` when `allow_next_epoch` is set. This is the
/// check of `BeaconState::get_slashings_index` and `BeaconState::get_randao_mix_index`.
pub fn epoch_vector_index(
    current_epoch: u64,
    epoch: u64,
    length: u64,
    allow_next_epoch: bool,
) -> Result<Option<u64>, ArithError> {
    if current_epoch >= epoch.safe_add(length)? {
        return Ok(None);
    }
    let upper_bound = if allow_next_epoch {
        current_epoch.safe_add(1)?
    } else {
        current_epoch
    };
    if epoch > upper_bound {
        return Ok(None);
    }
    let index = epoch.safe_rem(length)?;
    Ok(Some(index))
}

/// The position of the next epoch in the slashings vector, which the slashings reset clears.
pub fn slashings_reset_index(
    current_epoch: u64,
    epochs_per_slashings_vector: u64,
) -> Result<Option<u64>, ArithError> {
    let next_epoch = current_epoch.safe_add(1)?;
    epoch_vector_index(current_epoch, next_epoch, epochs_per_slashings_vector, true)
}

/// The positions in the randao mixes that the randao reset reads (the current epoch) and
/// writes (the next epoch).
pub fn randao_mixes_reset_indices(
    current_epoch: u64,
    epochs_per_historical_vector: u64,
) -> Result<Option<(u64, u64)>, ArithError> {
    let next_epoch = current_epoch.safe_add(1)?;
    let source = epoch_vector_index(
        current_epoch,
        current_epoch,
        epochs_per_historical_vector,
        false,
    )?;
    let target = epoch_vector_index(
        current_epoch,
        next_epoch,
        epochs_per_historical_vector,
        true,
    )?;
    match (source, target) {
        (Some(source), Some(target)) => Ok(Some((source, target))),
        _ => Ok(None),
    }
}

/// `true` when `next_epoch` starts a new historical summary.
pub fn historical_summary_due(
    next_epoch: u64,
    slots_per_historical_root: u64,
    slots_per_epoch: u64,
) -> Result<bool, ArithError> {
    Ok(next_epoch.safe_rem(slots_per_historical_root.safe_div(slots_per_epoch)?)? == 0)
}
