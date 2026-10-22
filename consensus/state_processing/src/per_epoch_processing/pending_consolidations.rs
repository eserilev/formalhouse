//! Pure core of the pending consolidations balance moves.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. So it works on a small table
//! of the validators that consolidations reference, uses `while` loops and has no `?` inside a
//! loop. `process_on_table` builds the table, runs the moves and writes the balances back. It is
//! generic over `ConsolidationState`, so Aeneas does not see the milhouse lists.

use std::cmp::min;

/// One pending consolidation, as positions in the local tables.
pub struct ConsolidationView {
    pub source: usize,
    pub target: usize,
}

/// What the moves read from a validator. `exists` is `false` for an index past the registry.
pub struct LocalValidator {
    pub exists: bool,
    pub slashed: bool,
    pub withdrawable_epoch: u64,
    pub effective_balance: u64,
}

pub enum ConsolidationError {
    /// A position in the local tables whose validator does not exist.
    UnknownValidator(usize),
    Overflow,
}

// Aeneas has no model of `Option::copied` or `Option::map`.
#[allow(clippy::manual_map)]
pub fn get_balance(balances: &[u64], i: usize) -> Option<u64> {
    match balances.get(i) {
        Some(balance) => Some(*balance),
        None => None,
    }
}

pub fn set_balance(balances: Vec<u64>, i: usize, value: u64) -> Vec<u64> {
    let mut balances = balances;
    if let Some(balance) = balances.get_mut(i) {
        *balance = value;
    }
    balances
}

fn validator_exists(validators: &[LocalValidator], i: usize) -> bool {
    match validators.get(i) {
        Some(validator) => validator.exists,
        None => false,
    }
}

/// Moves the balances of the consolidations that are ready. Returns the number of handled
/// consolidations and the new local balances.
pub fn process_pending_consolidations(
    consolidations: &[ConsolidationView],
    validators: &[LocalValidator],
    balances: Vec<u64>,
    next_epoch: u64,
) -> Result<(usize, Vec<u64>), ConsolidationError> {
    let mut balances = balances;
    let mut next_pending_consolidation: usize = 0;
    let mut error: Option<ConsolidationError> = None;
    let mut i = 0;
    while i < consolidations.len() {
        if let Some(consolidation) = consolidations.get(i) {
            let source = consolidation.source;
            let target = consolidation.target;
            if !validator_exists(validators, source) {
                error = Some(ConsolidationError::UnknownValidator(source));
                break;
            }
            if let Some(source_validator) = validators.get(source) {
                if source_validator.slashed {
                    next_pending_consolidation = next_pending_consolidation.saturating_add(1);
                } else if source_validator.withdrawable_epoch > next_epoch {
                    break;
                } else if let Some(source_balance) = get_balance(&balances, source) {
                    let source_effective_balance =
                        min(source_balance, source_validator.effective_balance);
                    balances = set_balance(
                        balances,
                        source,
                        source_balance.saturating_sub(source_effective_balance),
                    );
                    if !validator_exists(validators, target) {
                        error = Some(ConsolidationError::UnknownValidator(target));
                        break;
                    }
                    if let Some(target_balance) = get_balance(&balances, target) {
                        match target_balance.checked_add(source_effective_balance) {
                            None => {
                                error = Some(ConsolidationError::Overflow);
                                break;
                            }
                            Some(new_target_balance) => {
                                balances = set_balance(balances, target, new_target_balance);
                            }
                        }
                    }
                    next_pending_consolidation = next_pending_consolidation.saturating_add(1);
                }
            }
        }
        i = i.saturating_add(1);
    }
    match error {
        Some(error) => Err(error),
        None => Ok((next_pending_consolidation, balances)),
    }
}

/// One pending consolidation, as validator indices.
pub struct PendingPair {
    pub source: u64,
    pub target: u64,
}

/// The state that `process_on_table` reads and writes.
pub trait ConsolidationState<E> {
    /// The epoch after the current epoch.
    fn next_epoch(&self) -> Result<u64, E>;

    /// The pending consolidations, in order.
    fn pending(&self) -> Result<Vec<PendingPair>, E>;

    /// The table row of validator `index`. `exists` is `false` past the registry.
    fn local_validator(&self, index: usize) -> LocalValidator;

    /// The balance of validator `index`, or 0 past the registry.
    fn balance(&self, index: usize) -> u64;

    /// Sets the balance of validator `index`. Does nothing past the registry.
    fn set_balance(&mut self, index: usize, value: u64);

    /// Drops the first `n` pending consolidations.
    fn pop_pending(&mut self, n: usize) -> Result<(), E>;
}

/// An error of `process_on_table`.
pub enum TableError<E> {
    /// The state failed to read or write.
    State(E),
    /// A consolidation names a validator that does not exist.
    UnknownValidator(usize),
    /// A balance overflowed.
    Overflow,
}

/// The position of `index` in `sorted`, which is sorted with no duplicates.
pub fn position(sorted: &[usize], index: usize) -> Option<usize> {
    let mut low: usize = 0;
    let mut high: usize = sorted.len();
    let mut found: Option<usize> = None;
    while low < high {
        let mid = low.saturating_add(high.saturating_sub(low) / 2);
        match sorted.get(mid) {
            None => break,
            Some(value) => {
                if *value == index {
                    found = Some(mid);
                    break;
                }
                if *value < index {
                    low = mid.saturating_add(1);
                } else {
                    high = mid;
                }
            }
        }
    }
    found
}

fn build_table<E, S: ConsolidationState<E>>(
    state: &S,
    local_indices: &[usize],
) -> (Vec<LocalValidator>, Vec<u64>) {
    let mut validators = Vec::with_capacity(local_indices.len());
    let mut balances = Vec::with_capacity(local_indices.len());
    let mut k = 0;
    while k < local_indices.len() {
        if let Some(index) = local_indices.get(k) {
            validators.push(state.local_validator(*index));
            balances.push(state.balance(*index));
        }
        k = k.saturating_add(1);
    }
    (validators, balances)
}

fn build_views(
    pairs: &[PendingPair],
    local_indices: &[usize],
) -> Result<Vec<ConsolidationView>, usize> {
    let mut views = Vec::with_capacity(pairs.len());
    let mut missing: Option<usize> = None;
    let mut i = 0;
    while i < pairs.len() {
        if let Some(pair) = pairs.get(i) {
            let source_index = pair.source as usize;
            let target_index = pair.target as usize;
            match position(local_indices, source_index) {
                None => {
                    missing = Some(source_index);
                    break;
                }
                Some(source) => match position(local_indices, target_index) {
                    None => {
                        missing = Some(target_index);
                        break;
                    }
                    Some(target) => views.push(ConsolidationView { source, target }),
                },
            }
        }
        i = i.saturating_add(1);
    }
    match missing {
        Some(index) => Err(index),
        None => Ok(views),
    }
}

fn write_back<E, S: ConsolidationState<E>>(
    state: &mut S,
    local_indices: &[usize],
    balances: &[u64],
) {
    let mut k = 0;
    while k < local_indices.len() {
        if let Some(index) = local_indices.get(k)
            && let Some(balance) = balances.get(k)
        {
            state.set_balance(*index, *balance);
        }
        k = k.saturating_add(1);
    }
}

/// Runs `process_pending_consolidations` on a table of the validators in `local_indices`, then
/// writes the balances back and drops the handled consolidations. `local_indices` is sorted with
/// no duplicates and holds every source and target index.
pub fn process_on_table<E, S: ConsolidationState<E>>(
    state: &mut S,
    local_indices: &[usize],
) -> Result<(), TableError<E>> {
    let next_epoch = match state.next_epoch() {
        Ok(next_epoch) => next_epoch,
        Err(e) => return Err(TableError::State(e)),
    };
    let pairs = match state.pending() {
        Ok(pairs) => pairs,
        Err(e) => return Err(TableError::State(e)),
    };
    let (validators, balances) = build_table(state, local_indices);
    let views = match build_views(&pairs, local_indices) {
        Ok(views) => views,
        Err(index) => return Err(TableError::UnknownValidator(index)),
    };
    let (next, new_balances) =
        match process_pending_consolidations(&views, &validators, balances, next_epoch) {
            Ok(result) => result,
            Err(ConsolidationError::UnknownValidator(position)) => {
                let index = match local_indices.get(position) {
                    Some(index) => *index,
                    None => position,
                };
                return Err(TableError::UnknownValidator(index));
            }
            Err(ConsolidationError::Overflow) => return Err(TableError::Overflow),
        };
    write_back(state, local_indices, &new_balances);
    match state.pop_pending(next) {
        Ok(()) => Ok(()),
        Err(e) => Err(TableError::State(e)),
    }
}
