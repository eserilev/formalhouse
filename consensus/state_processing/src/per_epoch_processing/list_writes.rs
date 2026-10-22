//! The list writes of the epoch tail: the builder pending payments and the PTC window shift.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. The writes are generic over
//! small traits, so Aeneas does not see the milhouse lists. The proofs assume one contract for
//! each trait method.

use super::builder_pending_payments::{
    get_builder_payment_quorum_threshold, process_builder_pending_payments,
};
use safe_arith::{ArithError, SafeArith};
use types::{BuilderPendingPayment, BuilderPendingWithdrawal};

/// An error of the list writes.
pub enum ListWritesError<E> {
    /// An arithmetic step overflowed.
    Arith(ArithError),
    /// The state failed to read or write.
    State(E),
}

/// The builder payment lists of the state.
pub trait BuilderPaymentWrites<E> {
    /// The builder pending payments.
    fn payments(&self) -> Result<Vec<BuilderPendingPayment>, E>;

    /// Appends a builder pending withdrawal.
    fn push_withdrawal(&mut self, withdrawal: BuilderPendingWithdrawal) -> Result<(), E>;

    /// Sets the builder pending payments.
    fn set_payments(&mut self, payments: Vec<BuilderPendingPayment>) -> Result<(), E>;
}

/// Appends `withdrawals` in order.
pub fn push_withdrawals<E, S: BuilderPaymentWrites<E>>(
    state: &mut S,
    withdrawals: &[BuilderPendingWithdrawal],
) -> Result<(), ListWritesError<E>> {
    let mut i = 0;
    while i < withdrawals.len() {
        let Some(withdrawal) = withdrawals.get(i) else {
            return Ok(());
        };
        if let Err(e) = state.push_withdrawal(withdrawal.clone()) {
            return Err(ListWritesError::State(e));
        }
        i = match i.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(ListWritesError::Arith(e)),
        };
    }
    Ok(())
}

/// `process_builder_pending_payments`: queues the withdrawal of each payment of the previous
/// epoch that reached the quorum, then shifts the payment window.
pub fn apply_builder_pending_payments<E, S: BuilderPaymentWrites<E>>(
    state: &mut S,
    total_active_balance: u64,
    slots_per_epoch: u64,
    slots_per_epoch_usize: usize,
    threshold_numerator: u64,
    threshold_denominator: u64,
) -> Result<(), ListWritesError<E>> {
    let quorum = match get_builder_payment_quorum_threshold(
        total_active_balance,
        slots_per_epoch,
        threshold_numerator,
        threshold_denominator,
    ) {
        Ok(quorum) => quorum,
        Err(e) => return Err(ListWritesError::Arith(e)),
    };
    let payments = match state.payments() {
        Ok(payments) => payments,
        Err(e) => return Err(ListWritesError::State(e)),
    };
    let (withdrawals, updated_payments) =
        process_builder_pending_payments(&payments, slots_per_epoch_usize, quorum);
    push_withdrawals(state, &withdrawals)?;
    if let Err(e) = state.set_payments(updated_payments) {
        return Err(ListWritesError::State(e));
    }
    Ok(())
}

/// A window of fixed length that drops entries at the front and appends at the back.
pub trait WindowWrites<T, E> {
    /// Drops the first `n` entries.
    fn pop_front(&mut self, n: usize) -> Result<(), E>;

    /// Appends `item`.
    fn push(&mut self, item: &T) -> Result<(), E>;

    /// Writes the window back to the state.
    fn commit(&mut self) -> Result<(), E>;
}

/// Appends `items` in order.
pub fn push_items<T, E, W: WindowWrites<T, E>>(
    window: &mut W,
    items: &[T],
) -> Result<(), ListWritesError<E>> {
    let mut i = 0;
    while i < items.len() {
        let Some(item) = items.get(i) else {
            return Ok(());
        };
        if let Err(e) = window.push(item) {
            return Err(ListWritesError::State(e));
        }
        i = match i.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(ListWritesError::Arith(e)),
        };
    }
    Ok(())
}

/// Drops the first `shift` entries of the window, appends `items` and writes the window back.
pub fn shift_window<T, E, W: WindowWrites<T, E>>(
    window: &mut W,
    shift: usize,
    items: &[T],
) -> Result<(), ListWritesError<E>> {
    if let Err(e) = window.pop_front(shift) {
        return Err(ListWritesError::State(e));
    }
    push_items(window, items)?;
    if let Err(e) = window.commit() {
        return Err(ListWritesError::State(e));
    }
    Ok(())
}

/// The effective balances of the state.
pub trait EffectiveBalanceWrites<E> {
    /// Runs the effective balance update of validator `index`.
    fn update_effective_balance(&mut self, index: usize) -> Result<(), E>;
}

/// Runs the effective balance update of each validator in `indices`, in order.
pub fn update_effective_balances_at<E, S: EffectiveBalanceWrites<E>>(
    state: &mut S,
    indices: &[usize],
) -> Result<(), ListWritesError<E>> {
    let mut j = 0;
    while j < indices.len() {
        let Some(&index) = indices.get(j) else {
            return Ok(());
        };
        if let Err(e) = state.update_effective_balance(index) {
            return Err(ListWritesError::State(e));
        }
        j = match j.safe_add(1) {
            Ok(next) => next,
            Err(e) => return Err(ListWritesError::Arith(e)),
        };
    }
    Ok(())
}
