//! The effective balance of a new validator, after Electra.
//!
//! Aeneas translates this module for the proofs in `consensus/state_processing/proofs`. So it
//! takes plain values.

use safe_arith::SafeArith;

/// `get_max_effective_balance` after Electra.
pub fn max_effective_balance_electra(
    is_compounding: bool,
    max_effective_balance_electra: u64,
    min_activation_balance: u64,
) -> u64 {
    if is_compounding {
        max_effective_balance_electra
    } else {
        min_activation_balance
    }
}

/// The effective balance of `get_validator_from_deposit`: the amount rounded down to a multiple
/// of `increment`, capped at `max_effective_balance`. An `increment` of 0 does not round.
pub fn deposit_effective_balance(amount: u64, increment: u64, max_effective_balance: u64) -> u64 {
    let rounded = match amount.safe_rem(increment) {
        Ok(rem) => amount.saturating_sub(rem),
        Err(_) => amount,
    };
    if rounded < max_effective_balance {
        rounded
    } else {
        max_effective_balance
    }
}
