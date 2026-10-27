//! Pure core of `weigh_justification_and_finalization`.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. The caller reads the block
//! roots and writes the checkpoints, so this module uses plain `u64` epochs.

use safe_arith::{ArithError, SafeArith};

/// The justification bits, most recent epoch first.
#[derive(Clone, Copy)]
pub struct JustificationBits {
    pub bit0: bool,
    pub bit1: bool,
    pub bit2: bool,
    pub bit3: bool,
}

/// The checkpoint that becomes the finalized checkpoint.
#[derive(Clone, Copy)]
pub enum NewFinalized {
    Unchanged,
    OldPreviousJustified,
    OldCurrentJustified,
}

#[derive(Clone, Copy)]
pub struct JustificationOutcome {
    pub justify_previous: bool,
    pub justify_current: bool,
    pub bits: JustificationBits,
    pub finalized: NewFinalized,
}

/// Returns `choice` if `enabled` and `source_epoch + offset` is the current epoch. Adds only if
/// `enabled`, as the spec does.
fn finalize_step(
    enabled: bool,
    source_epoch: u64,
    offset: u64,
    current_epoch: u64,
    choice: NewFinalized,
    finalized: NewFinalized,
) -> Result<NewFinalized, ArithError> {
    if enabled && source_epoch.safe_add(offset)? == current_epoch {
        Ok(choice)
    } else {
        Ok(finalized)
    }
}

pub fn weigh_justification(
    current_epoch: u64,
    old_previous_justified_epoch: u64,
    old_current_justified_epoch: u64,
    bits: JustificationBits,
    total_active_balance: u64,
    previous_target_balance: u64,
    current_target_balance: u64,
) -> Result<JustificationOutcome, ArithError> {
    let threshold = total_active_balance.safe_mul(2)?;
    let justify_previous = previous_target_balance.safe_mul(3)? >= threshold;
    let justify_current = current_target_balance.safe_mul(3)? >= threshold;
    let bits = JustificationBits {
        bit0: justify_current,
        bit1: bits.bit0 | justify_previous,
        bit2: bits.bit1,
        bit3: bits.bit2,
    };

    let finalized = finalize_step(
        bits.bit1 & bits.bit2 & bits.bit3,
        old_previous_justified_epoch,
        3,
        current_epoch,
        NewFinalized::OldPreviousJustified,
        NewFinalized::Unchanged,
    )?;
    let finalized = finalize_step(
        bits.bit1 & bits.bit2,
        old_previous_justified_epoch,
        2,
        current_epoch,
        NewFinalized::OldPreviousJustified,
        finalized,
    )?;
    let finalized = finalize_step(
        bits.bit0 & bits.bit1 & bits.bit2,
        old_current_justified_epoch,
        2,
        current_epoch,
        NewFinalized::OldCurrentJustified,
        finalized,
    )?;
    let finalized = finalize_step(
        bits.bit0 & bits.bit1,
        old_current_justified_epoch,
        1,
        current_epoch,
        NewFinalized::OldCurrentJustified,
        finalized,
    )?;

    Ok(JustificationOutcome {
        justify_previous,
        justify_current,
        bits,
        finalized,
    })
}
