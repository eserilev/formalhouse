//! The committee steps of the epoch transition after Gloas, on plain values: the proposer
//! lookahead, the PTC window and the next sync committee.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. So it takes plain values,
//! uses `while` loops and has no `?` inside a loop. The hash function is a type parameter.

use swap_or_not_shuffle::ShuffleHash;
use types::state::balance_weighted_selection::{
    EffectiveBalances, SelectionError, compute_balance_weighted_selection,
    compute_proposer_indices, compute_ptc, compute_seed,
};

/// The chain constants that the selection reads.
#[derive(Clone, Copy)]
pub struct SelectionConstants {
    pub shuffle_round_count: u8,
    /// `MAX_EFFECTIVE_BALANCE_ELECTRA`.
    pub max_effective_balance: u64,
    pub slots_per_epoch: u64,
}

/// Returns `lookahead[slots_per_epoch..] + proposers`, or `None` if the result does not have
/// the length of `lookahead`.
pub fn shift_lookahead(
    lookahead: &[u64],
    slots_per_epoch: usize,
    proposers: &[usize],
) -> Option<Vec<u64>> {
    let mut shifted = Vec::new();
    let mut k = slots_per_epoch;
    while k < lookahead.len() {
        if let Some(proposer) = lookahead.get(k) {
            shifted.push(*proposer);
        }
        k = k.saturating_add(1);
    }
    let mut j = 0;
    while j < proposers.len() {
        if let Some(proposer) = proposers.get(j) {
            shifted.push(*proposer as u64);
        }
        j = j.saturating_add(1);
    }
    if shifted.len() == lookahead.len() {
        Some(shifted)
    } else {
        None
    }
}

/// Returns the proposer lookahead after `process_proposer_lookahead`.
///
/// `indices` are the active, unslashed validators of `epoch`, the last epoch of the lookahead.
/// `mix` is the RANDAO mix that `get_seed(state, epoch, DOMAIN_BEACON_PROPOSER)` reads.
#[allow(clippy::too_many_arguments)]
pub fn next_proposer_lookahead<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    lookahead: &[u64],
    indices: &[usize],
    domain_beacon_proposer: &[u8; 4],
    epoch: u64,
    mix: &[u8; 32],
    start_slot: u64,
    constants: &SelectionConstants,
) -> Result<Vec<u64>, SelectionError> {
    let seed = compute_seed::<H>(domain_beacon_proposer, epoch, mix);
    let proposers = compute_proposer_indices::<H, B>(
        balances,
        indices,
        &seed,
        start_slot,
        constants.slots_per_epoch,
        constants.shuffle_round_count,
        constants.max_effective_balance,
    )?;
    shift_lookahead(lookahead, constants.slots_per_epoch as usize, &proposers)
        .ok_or(SelectionError::IndexOutOfBounds(lookahead.len()))
}

/// Returns the proposer indices of `epoch`, as `get_beacon_proposer_indices` does.
///
/// `indices` are the proposer candidates of `epoch`. `mix` is the RANDAO mix that
/// `get_seed(state, epoch, DOMAIN_BEACON_PROPOSER)` reads.
#[allow(clippy::too_many_arguments)]
pub fn proposer_indices_for_epoch<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    domain_beacon_proposer: &[u8; 4],
    epoch: u64,
    mix: &[u8; 32],
    start_slot: u64,
    constants: &SelectionConstants,
) -> Result<Vec<usize>, SelectionError> {
    let seed = compute_seed::<H>(domain_beacon_proposer, epoch, mix);
    compute_proposer_indices::<H, B>(
        balances,
        indices,
        &seed,
        start_slot,
        constants.slots_per_epoch,
        constants.shuffle_round_count,
        constants.max_effective_balance,
    )
}

/// Returns the PTC of each slot of `epoch`, the epoch that `process_ptc_window` appends.
///
/// `committees[i]` holds the beacon committees of slot `start_slot + i`, joined in order. `mix`
/// is the RANDAO mix that `get_seed(state, epoch, DOMAIN_PTC_ATTESTER)` reads.
#[allow(clippy::too_many_arguments)]
pub fn ptc_for_epoch<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    committees: &[Vec<usize>],
    domain_ptc_attester: &[u8; 4],
    epoch: u64,
    mix: &[u8; 32],
    start_slot: u64,
    ptc_size: usize,
    constants: &SelectionConstants,
) -> Result<Vec<Vec<usize>>, SelectionError> {
    let attester_seed = compute_seed::<H>(domain_ptc_attester, epoch, mix);
    let mut ptcs = Vec::new();
    let mut error = None;
    let mut i = 0;
    while i < committees.len() {
        if let Some(committee) = committees.get(i) {
            let ptc = match start_slot.checked_add(i as u64) {
                Some(slot) => compute_ptc::<H, B>(
                    balances,
                    committee,
                    &attester_seed,
                    slot,
                    ptc_size,
                    constants.shuffle_round_count,
                    constants.max_effective_balance,
                ),
                None => Err(SelectionError::Arith(safe_arith::ArithError::Overflow)),
            };
            match ptc {
                Ok(ptc) => ptcs.push(ptc),
                Err(e) => {
                    error = Some(e);
                    break;
                }
            }
        }
        i = i.saturating_add(1);
    }
    match error {
        Some(e) => Err(e),
        None => Ok(ptcs),
    }
}

/// Returns `get_next_sync_committee_indices(state)`.
///
/// `indices` are the active validators of `epoch`, the next epoch. `mix` is the RANDAO mix that
/// `get_seed(state, epoch, DOMAIN_SYNC_COMMITTEE)` reads.
#[allow(clippy::too_many_arguments)]
pub fn next_sync_committee_indices<H: ShuffleHash, B: EffectiveBalances>(
    balances: &B,
    indices: &[usize],
    domain_sync_committee: &[u8; 4],
    epoch: u64,
    mix: &[u8; 32],
    sync_committee_size: usize,
    constants: &SelectionConstants,
) -> Result<Vec<usize>, SelectionError> {
    let seed = compute_seed::<H>(domain_sync_committee, epoch, mix);
    compute_balance_weighted_selection::<H, B>(
        balances,
        indices,
        &seed,
        sync_committee_size,
        true,
        constants.shuffle_round_count,
        constants.max_effective_balance,
    )
}
