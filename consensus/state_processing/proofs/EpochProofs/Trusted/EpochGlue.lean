import EpochProofs.Sanity.GlueBounds

/-!
# The glue facts of `single_pass.rs`

Some `?` sites in `single_pass.rs` sit in glue that Aeneas does not translate. For each one,
this file names the fact that links the Rust to the proofs. The line numbers refer to
`consensus/state_processing/src/per_epoch_processing/single_pass.rs`.

## Links with a proved bound

The bound that rules out the error is proved in `EpochProofs/Sanity/GlueBounds.lean`. The
trusted part is only that the Rust expression computes the stated formula.

- L1 (lines 170, 221, 1327): `state.next_epoch()` is `slot / 32 + 1`.
  Bound: `glue_epoch_add_fits` with `k = 1`.
- L2 (lines 538, 539, 598, 599): `current_epoch + min_seed_lookahead + 1` is `slot / 32 + 2`,
  computed in two additions. Bound: `glue_epoch_add_fits` with `k = 1` and `k = 2`.
- L3 (line 607): `start_slot + i` is `(slot / 32 + 2) * 32 + i` for `i < 32`.
  Bound: `glue_lookahead_slot_fits`.
- L4 (lines 553, 615): `BeaconState::get_seed_mix` computes
  `(epoch + 65536 - 1 - 1) % randao_mixes.len()` and reads that entry. Bound:
  `glue_seed_mix_index`, with `randao_mixes.len() = 65536` from the vector lengths. The value it
  reads is `SeedMixLink`.
- L5 (line 568): `Vector::new` accepts a vector of exactly 64 entries.
  `next_proposer_lookahead_spec` gives the spec lookahead, and
  `process_proposer_lookahead_length` proves that it has 64 entries.
- L6 (line 163): `build_exit_cache` counts the exits of each epoch in a `u64`. Each count is at
  most the number of validators. Bound: `glue_exit_count`.
- L7 (line 1411): the pending deposits of one validator sum in a `u64`.
  Bound: `glue_validator_deposit_sum`.

## Named facts

No bound is proved for these. Each is one statement that the proofs trust.

- N1 `ShuffleSize` (lines 164, 165): the committee cache shuffles at most `2^24` active
  validators. Activation needs 32 ETH, so the active set stays far below this, but no
  invariant proves it.
- N2 `ForkFields` (lines 243, 284, 287, 451, 455, 534, 568, 629, 1341, 1387, 1352): each
  superstruct accessor returns the field of the state variant, because the field exists from
  that fork on. Line 1352 is not evaluated from Fulu on.
- N3 `TreeHashOk` (line 221): `update_tree_hash_cache` succeeds when the latest block header
  has no state root yet.
- N4 `SlashingsSumLink` (line 190): `safe_sum` of `state.slashings` is the spec `uint64Sum`.
  The spec sum is proved total (`slashingsPreamble_ok`).
-/

namespace EpochProofs.Spec

/-- N1: the active validators of an epoch fit in the shuffle. -/
def ShuffleSize (s : BeaconState) (e : Nat) : Prop :=
  (get_active_validator_indices s e).length ≤ 2 ^ 24

end EpochProofs.Spec
