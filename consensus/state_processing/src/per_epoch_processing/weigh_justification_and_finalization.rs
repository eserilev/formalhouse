use crate::per_epoch_processing::justification::{
    JustificationBits, NewFinalized, weigh_justification,
};
use crate::per_epoch_processing::{Error, JustificationAndFinalizationState};
use types::{Checkpoint, EthSpec};

/// Update the justified and finalized checkpoints for matching target attestations.
pub fn weigh_justification_and_finalization<E: EthSpec>(
    mut state: JustificationAndFinalizationState<E>,
    total_active_balance: u64,
    previous_target_balance: u64,
    current_target_balance: u64,
) -> Result<JustificationAndFinalizationState<E>, Error> {
    let previous_epoch = state.previous_epoch();
    let current_epoch = state.current_epoch();

    let old_previous_justified_checkpoint = state.previous_justified_checkpoint();
    let old_current_justified_checkpoint = state.current_justified_checkpoint();

    let old_bits = state.justification_bits();
    let bit = |i| old_bits.get(i).map_err(Error::InvalidJustificationBit);
    let bits = JustificationBits {
        bit0: bit(0)?,
        bit1: bit(1)?,
        bit2: bit(2)?,
        bit3: bit(3)?,
    };

    let outcome = weigh_justification(
        current_epoch.as_u64(),
        old_previous_justified_checkpoint.epoch.as_u64(),
        old_current_justified_checkpoint.epoch.as_u64(),
        bits,
        total_active_balance,
        previous_target_balance,
        current_target_balance,
    )?;

    // Process justifications
    *state.previous_justified_checkpoint_mut() = old_current_justified_checkpoint;
    if outcome.justify_previous {
        *state.current_justified_checkpoint_mut() = Checkpoint {
            epoch: previous_epoch,
            root: state.get_block_root_at_epoch(previous_epoch)?,
        };
    }
    if outcome.justify_current {
        *state.current_justified_checkpoint_mut() = Checkpoint {
            epoch: current_epoch,
            root: state.get_block_root_at_epoch(current_epoch)?,
        };
    }
    let bits = state.justification_bits_mut();
    bits.set(0, outcome.bits.bit0)?;
    bits.set(1, outcome.bits.bit1)?;
    bits.set(2, outcome.bits.bit2)?;
    bits.set(3, outcome.bits.bit3)?;

    // Process finalizations
    match outcome.finalized {
        NewFinalized::Unchanged => {}
        NewFinalized::OldPreviousJustified => {
            *state.finalized_checkpoint_mut() = old_previous_justified_checkpoint;
        }
        NewFinalized::OldCurrentJustified => {
            *state.finalized_checkpoint_mut() = old_current_justified_checkpoint;
        }
    }

    Ok(state)
}
