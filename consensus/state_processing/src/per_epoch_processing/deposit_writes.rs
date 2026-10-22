//! The pending deposit writes after the single-pass loop, after Electra.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. The writes are generic over
//! `DepositWrites`, so Aeneas does not see the milhouse lists. The proofs assume one contract for
//! each `DepositWrites` method: it does the spec write on the state, and fails only when the spec
//! fails.

use safe_arith::{ArithError, SafeArith};

/// An error of the deposit writes.
pub enum DepositWritesError<E> {
    /// A balance addition overflowed.
    Arith(ArithError),
    /// The state failed to read or write.
    State(E),
}

/// The state that the deposit writes read and write. `D` is a pending deposit.
pub trait DepositWrites<D, E> {
    /// Sets the pending deposits to the deposits from `next_deposit_index` on, followed by the
    /// postponed deposits, and sets `deposit_balance_to_consume`.
    fn write_queue(
        &mut self,
        next_deposit_index: usize,
        deposit_balance_to_consume: u64,
    ) -> Result<(), E>;

    /// The index of the validator with the pubkey of `deposit`, if there is one.
    fn validator_index(&mut self, deposit: &D) -> Result<Option<usize>, E>;

    /// The amount of `deposit`.
    fn amount(&self, deposit: &D) -> u64;

    /// The balance of validator `index`.
    fn balance(&self, index: usize) -> Result<u64, E>;

    /// Sets the balance of validator `index`.
    fn set_balance(&mut self, index: usize, balance: u64) -> Result<(), E>;

    /// Checks the deposit signature (proof of possession).
    fn is_valid_signature(&self, deposit: &D) -> bool;

    /// Adds a new validator for `deposit` and returns its index.
    fn add_validator(&mut self, deposit: &D) -> Result<usize, E>;

    /// Runs the effective balance update of validator `index`.
    fn update_effective_balance(&mut self, index: usize) -> Result<(), E>;
}

/// Applies the new validator deposits in order and returns the indices of the new validators.
pub fn apply_new_validator_deposits<D, E, S: DepositWrites<D, E>>(
    state: &mut S,
    new_validator_deposits: &[D],
) -> Result<Vec<usize>, DepositWritesError<E>> {
    let mut added: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < new_validator_deposits.len() {
        let Some(deposit) = new_validator_deposits.get(i) else {
            return Ok(added);
        };
        let known = match state.validator_index(deposit) {
            Ok(known) => known,
            Err(e) => return Err(DepositWritesError::State(e)),
        };
        match known {
            Some(index) => {
                let balance = match state.balance(index) {
                    Ok(balance) => balance,
                    Err(e) => return Err(DepositWritesError::State(e)),
                };
                let new_balance = match balance.safe_add(state.amount(deposit)) {
                    Ok(new_balance) => new_balance,
                    Err(e) => return Err(DepositWritesError::Arith(e)),
                };
                if let Err(e) = state.set_balance(index, new_balance) {
                    return Err(DepositWritesError::State(e));
                }
            }
            None => {
                if state.is_valid_signature(deposit) {
                    match state.add_validator(deposit) {
                        Ok(index) => added.push(index),
                        Err(e) => return Err(DepositWritesError::State(e)),
                    }
                }
            }
        }
        i = match i.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(DepositWritesError::Arith(e)),
        };
    }
    Ok(added)
}

/// Runs the effective balance update of each validator in `indices`, in order.
pub fn update_effective_balances<D, E, S: DepositWrites<D, E>>(
    state: &mut S,
    indices: &[usize],
) -> Result<(), DepositWritesError<E>> {
    let mut j = 0;
    while j < indices.len() {
        let Some(&index) = indices.get(j) else {
            return Ok(());
        };
        if let Err(e) = state.update_effective_balance(index) {
            return Err(DepositWritesError::State(e));
        }
        j = match j.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(DepositWritesError::Arith(e)),
        };
    }
    Ok(())
}

/// Writes the deposit queue, applies the new validator deposits in order, then runs the effective
/// balance update of each new validator.
pub fn apply_deposit_writes<D, E, S: DepositWrites<D, E>>(
    state: &mut S,
    next_deposit_index: usize,
    deposit_balance_to_consume: u64,
    new_validator_deposits: &[D],
    effective_balance_updates: bool,
) -> Result<(), DepositWritesError<E>> {
    if let Err(e) = state.write_queue(next_deposit_index, deposit_balance_to_consume) {
        return Err(DepositWritesError::State(e));
    }
    let added = apply_new_validator_deposits(state, new_validator_deposits)?;
    if effective_balance_updates {
        update_effective_balances(state, &added)?;
    }
    Ok(())
}
