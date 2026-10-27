//! The seed and the balance-weighted selection of validators, after Gloas: the proposers, the
//! sync committee and the PTC.
//!
//! Aeneas translates this module for the proofs in `consensus/state_processing/proofs`. So it
//! takes plain values, uses `while` loops and has no `?` inside a loop. The hash function is a
//! type parameter.

use safe_arith::{ArithError, SafeArith};
use swap_or_not_shuffle::{ShuffleHash, compute_shuffled_index_with};

/// `MAX_RANDOM_VALUE` of `compute_balance_weighted_selection`.
pub const MAX_RANDOM_VALUE: u64 = 65535;

/// The effective balance of each validator.
pub trait EffectiveBalances {
    /// Returns the effective balance of the validator `index`, or `None` if it is unknown.
    fn effective_balance(&self, index: usize) -> Option<u64>;
}

/// A failure of the selection.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SelectionError {
    EmptyIndices,
    UnableToShuffle,
    IndexOutOfBounds(usize),
    UnknownValidator(usize),
    Arith(ArithError),
}

impl From<ArithError> for SelectionError {
    fn from(e: ArithError) -> Self {
        SelectionError::Arith(e)
    }
}

/// Returns `uint_to_bytes(x)`: the 8 little-endian bytes of `x`.
#[allow(clippy::arithmetic_side_effects)]
fn le_bytes8(x: u64) -> [u8; 8] {
    [
        x as u8,
        (x >> 8) as u8,
        (x >> 16) as u8,
        (x >> 24) as u8,
        (x >> 32) as u8,
        (x >> 40) as u8,
        (x >> 48) as u8,
        (x >> 56) as u8,
    ]
}

/// Returns `sha256(seed + uint_to_bytes(x))`.
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub fn hash_with_u64<H: ShuffleHash>(seed: &[u8; 32], x: u64) -> [u8; 32] {
    let bytes = le_bytes8(x);
    let mut buf = [0u8; 40];
    let mut k = 0;
    while k < 32 {
        buf[k] = seed[k];
        k += 1;
    }
    while k < 40 {
        buf[k] = bytes[k - 32];
        k += 1;
    }
    H::hash(&buf)
}

/// Returns `get_seed`: `sha256(domain_type + uint_to_bytes(epoch) + mix)`.
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub fn compute_seed<H: ShuffleHash>(domain_type: &[u8; 4], epoch: u64, mix: &[u8; 32]) -> [u8; 32] {
    let bytes = le_bytes8(epoch);
    let mut buf = [0u8; 44];
    let mut k = 0;
    while k < 4 {
        buf[k] = domain_type[k];
        k += 1;
    }
    while k < 12 {
        buf[k] = bytes[k - 4];
        k += 1;
    }
    while k < 44 {
        buf[k] = mix[k - 12];
        k += 1;
    }
    H::hash(&buf)
}

/// Returns the random value of pass `i`: the 2 little-endian bytes at `i % 16 * 2` of
/// `sha256(seed + uint_to_bytes(i // 16))`.
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub fn random_value<H: ShuffleHash>(seed: &[u8; 32], i: usize) -> u64 {
    let random_bytes = hash_with_u64::<H>(seed, (i / 16) as u64);
    let offset = i % 16 * 2;
    (random_bytes[offset] as u64) | (random_bytes[offset + 1] as u64) << 8
}

/// One pass of the selection loop: returns the candidate of pass `i` if it is accepted.
#[allow(clippy::too_many_arguments)]
fn selection_pass<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    seed: &[u8; 32],
    shuffle_indices: bool,
    shuffle_round_count: u8,
    max_effective_balance: u64,
    i: usize,
) -> Result<Option<usize>, SelectionError> {
    let total = indices.len();
    let mut next_index = i.safe_rem(total)?;
    if shuffle_indices {
        next_index = compute_shuffled_index_with::<H>(next_index, total, seed, shuffle_round_count)
            .ok_or(SelectionError::UnableToShuffle)?;
    }
    let candidate = *indices
        .get(next_index)
        .ok_or(SelectionError::IndexOutOfBounds(next_index))?;
    let effective_balance = balances
        .effective_balance(candidate)
        .ok_or(SelectionError::UnknownValidator(candidate))?;
    let weight = effective_balance.safe_mul(MAX_RANDOM_VALUE)?;
    let threshold = max_effective_balance.safe_mul(random_value::<H>(seed, i))?;
    if weight >= threshold {
        Ok(Some(candidate))
    } else {
        Ok(None)
    }
}

/// Returns `compute_balance_weighted_selection(state, indices, seed, size, shuffle_indices)`.
///
/// `max_effective_balance` is `MAX_EFFECTIVE_BALANCE_ELECTRA`.
#[allow(clippy::too_many_arguments)]
pub fn compute_balance_weighted_selection<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    seed: &[u8; 32],
    size: usize,
    shuffle_indices: bool,
    shuffle_round_count: u8,
    max_effective_balance: u64,
) -> Result<Vec<usize>, SelectionError> {
    if indices.is_empty() {
        return Err(SelectionError::EmptyIndices);
    }
    let mut selected = Vec::new();
    let mut i: usize = 0;
    let mut error = None;
    while selected.len() < size {
        match selection_pass::<H, B>(
            balances,
            indices,
            seed,
            shuffle_indices,
            shuffle_round_count,
            max_effective_balance,
            i,
        ) {
            Ok(Some(candidate)) => selected.push(candidate),
            Ok(None) => {}
            Err(e) => {
                error = Some(e);
                break;
            }
        }
        match i.checked_add(1) {
            Some(next) => i = next,
            None => {
                error = Some(SelectionError::Arith(ArithError::Overflow));
                break;
            }
        }
    }
    match error {
        Some(e) => Err(e),
        None => Ok(selected),
    }
}

/// Returns the proposer of slot `start_slot + i`, as `compute_proposer_indices` selects it.
#[allow(clippy::too_many_arguments)]
fn proposer_at<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    seed: &[u8; 32],
    start_slot: u64,
    i: u64,
    shuffle_round_count: u8,
    max_effective_balance: u64,
) -> Result<usize, SelectionError> {
    let slot_seed = hash_with_u64::<H>(seed, start_slot.safe_add(i)?);
    let selected = compute_balance_weighted_selection::<H, B>(
        balances,
        indices,
        &slot_seed,
        1,
        true,
        shuffle_round_count,
        max_effective_balance,
    )?;
    #[allow(clippy::get_first)]
    match selected.get(0) {
        Some(proposer) => Ok(*proposer),
        None => Err(SelectionError::EmptyIndices),
    }
}

/// Returns `compute_proposer_indices(state, epoch, seed, indices)` for the epoch that starts at
/// `start_slot`.
#[allow(clippy::too_many_arguments)]
pub fn compute_proposer_indices<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    seed: &[u8; 32],
    start_slot: u64,
    slots_per_epoch: u64,
    shuffle_round_count: u8,
    max_effective_balance: u64,
) -> Result<Vec<usize>, SelectionError> {
    let mut proposers = Vec::new();
    let mut i: u64 = 0;
    let mut error = None;
    while i < slots_per_epoch {
        match proposer_at::<H, B>(
            balances,
            indices,
            seed,
            start_slot,
            i,
            shuffle_round_count,
            max_effective_balance,
        ) {
            Ok(proposer) => proposers.push(proposer),
            Err(e) => {
                error = Some(e);
                break;
            }
        }
        i = i.saturating_add(1);
    }
    match error {
        Some(e) => Err(e),
        None => Ok(proposers),
    }
}

/// Returns `compute_ptc(state, slot)`. `attester_seed` is
/// `get_seed(state, epoch, DOMAIN_PTC_ATTESTER)` and `committee_indices` are the beacon
/// committees of `slot`, joined in order.
#[allow(clippy::too_many_arguments)]
pub fn compute_ptc<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    committee_indices: &[usize],
    attester_seed: &[u8; 32],
    slot: u64,
    ptc_size: usize,
    shuffle_round_count: u8,
    max_effective_balance: u64,
) -> Result<Vec<usize>, SelectionError> {
    let seed = hash_with_u64::<H>(attester_seed, slot);
    compute_balance_weighted_selection::<H, B>(
        balances,
        committee_indices,
        &seed,
        ptc_size,
        false,
        shuffle_round_count,
        max_effective_balance,
    )
}
