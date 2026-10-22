//! The single-pass loop over the validator rows, after Electra.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. The loop is generic over
//! `RegistryRows`, so Aeneas does not see the milhouse lists. The proofs assume one contract for
//! `RegistryRows::apply_step`: it runs `single_pass_step` on row `index` and writes the new row
//! back.

use super::registry_update::RegistryConstants;
use super::single_pass_step::{ExitChurn, StepContext};
use safe_arith::{ArithError, SafeArith};

/// An error of the single-pass loop.
pub enum RowsError<E> {
    /// `single_pass_step` failed.
    Step(ArithError),
    /// The rows failed to read or write a row.
    Rows(E),
}

/// The per-validator rows of the state.
pub trait RegistryRows<E> {
    /// The number of rows.
    fn row_count(&self) -> usize;

    /// Reads row `index`, runs `single_pass_step` on it, writes the new row and returns the new
    /// churn. The loop calls it once for each row, in index order.
    fn apply_step(
        &mut self,
        index: usize,
        churn: ExitChurn,
        ctx: &StepContext,
        constants: &RegistryConstants,
    ) -> Result<ExitChurn, RowsError<E>>;
}

/// Runs `single_pass_step` on every row in index order and returns the final churn.
pub fn single_pass_rows<E, R: RegistryRows<E>>(
    rows: &mut R,
    churn: ExitChurn,
    ctx: &StepContext,
    constants: &RegistryConstants,
) -> Result<ExitChurn, RowsError<E>> {
    let len = rows.row_count();
    let mut churn = churn;
    let mut index = 0;
    while index < len {
        churn = rows.apply_step(index, churn, ctx, constants)?;
        index = match index.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(RowsError::Step(e)),
        };
    }
    Ok(churn)
}
