import EpochProofs.Sanity.GlueBounds

/-!
# The arithmetic and the reads of `single_pass.rs` that Aeneas does not translate

Some `?` sites of `single_pass.rs` are in code that Aeneas does not translate. This file lists the
fact behind each one. It contains no Lean statement.

## Formulas whose bound is proved

`EpochProofs/Sanity/GlueBounds.lean` proves that these formulas do not overflow. Review checks that
the Rust computes the formula.

- `state.next_epoch()` is the epoch of the slot plus one (`glue_epoch_add_fits`).
- The lookahead epoch is the current epoch plus `MIN_SEED_LOOKAHEAD` plus one
  (`glue_epoch_add_fits`).
- `start_slot + i` is slot `i` of the lookahead epoch (`glue_lookahead_slot_fits`).
- `BeaconState::get_seed_mix` reads the RANDAO mix that the spec `get_seed` reads
  (`glue_seed_mix_index`). `SeedMixLink` states the value.
- `Vector::new` accepts the new lookahead (`process_proposer_lookahead_length`).
- `build_exit_cache` counts the exits of each epoch in a `u64` (`glue_exit_count`).
- The pending deposits of one validator sum in a `u64` (`glue_validator_deposit_sum`).

## Facts that only review checks

- At most `2^24` active validators enter the shuffle of the committee cache. The proofs take this as
  a hypothesis at the three shuffles of the epoch (`LookaheadN1`, `PtcN1`, `SyncN1`).
- Each superstruct accessor returns the field of the fork of the state.
- `update_tree_hash_cache` succeeds when the latest block header has no state root yet.
- `safe_sum` of `state.slashings` is the spec sum. The spec sum is proved total
  (`slashingsPreamble_ok`).
-/
