# Plan: the whole Gloas epoch equals Etheorem

Goal: prove `Spec.process_epoch` equal to Etheorem's `EthCLSpecs.Gloas.processEpoch`. With the
existing proofs, Lighthouse's epoch then equals Etheorem.

## The foundation (done)

- `EpochProofs/Etheorem/State.lean`: `absEState` maps every field of an Etheorem state to the
  reference state. It also has read and write lemmas for each field.
- `EpochProofs/Etheorem/Helpers.lean`:
  - `PresetAgrees p`: the Etheorem preset holds the values of `p`. Proved for both presets.
  - `UInt64` bridges, epoch and slot helpers, active indices, total balance, total active
    balance, `isqrt = integer_squareroot`, base reward per increment, exit and activation churn.
  - `increase_balance`, `decrease_balance`, `compute_exit_epoch_and_update_churn` and
    `initiate_validator_exit`.
- `EpochProofs/Etheorem/Oracle.lean`: `OracleAgrees o` and `etheoremOracle`.

Each arithmetic lemma reads "if the reference returns `n`, then Etheorem gives `n`". Etheorem's
`UInt64` wraps only where the reference raises.

## The steps

Both `process_epoch` functions run the same 17 steps in the same order.

| # | Step | Difficulty | Gaps |
|---|---|---|---|
| 1 | `process_justification_and_finalization` | medium | Etheorem wraps `epoch + k`. Bits are a `BitVec` shift. |
| 2 | `process_inactivity_updates` | medium | `score + bias` wraps. Needs participating and eligible indices. |
| 3 | `process_rewards_and_penalties` | hard | Deltas in `Nat`, then `UInt64.ofNat`. Four rounds of `applyDeltas`. F5. |
| 4 | `process_registry_updates` | medium | Etheorem uses three `if`s on a snapshot. pyspec uses `if`/`elif`/`elif`. Equal under the conditions of `registry_update_equiv`. |
| 5 | `process_slashings` | medium | The sum and `* 3` wrap. |
| 6 | `process_eth1_data_reset` | easy | None. |
| 7 | `process_pending_deposits` | hard | Loop with fuel. F2. Deposit signature through the Oracle. |
| 8 | `process_pending_consolidations` | medium | Loop with fuel. |
| 9 | `process_builder_pending_payments` | done | `builder_pending_payments_etheorem`. |
| 10 | `process_effective_balance_updates` | easy | `balance + downward` wraps. |
| 11 | `process_slashings_reset` | easy | `[i]!` write, index in range. |
| 12 | `process_randao_mixes_reset` | easy | `vmodGet` read. |
| 13 | `process_historical_summaries_update` | easy | Oracle `blockRoots` and `stateRoots`. F6 list limit. |
| 14 | `process_participation_flag_updates` | easy | None. |
| 15 | `process_sync_committee_updates` | hard | Shuffle, F3, F7, `getD` reads, `uint_to_bytes`. |
| 16 | `process_proposer_lookahead` | hard | As 15, and F4. |
| 17 | `process_ptc_window` | hard | As 15. Uses the beacon committees. |

## Work units

Each unit adds only its own files under `EpochProofs/Etheorem/`. The lead owns `State.lean`,
`Helpers.lean`, `Oracle.lean`, `EpochProofs.lean`, `Axioms.lean`, the README and this file. A
unit that needs a new shared lemma puts it in its own file first. The lead moves it later.

1. Tail: steps 6, 10, 11, 12, 13, 14. Files `Resets.lean`, `EffectiveBalance.lean`,
   `HistoricalSummaries.lean`.
2. Passes: steps 1, 2, 3, 5. Files `Participation.lean` (participating and eligible indices),
   `Justification.lean`, `Inactivity.lean`, `Rewards.lean`, `Slashings.lean`.
3. Queues: steps 4, 7, 8. Files `Registry.lean`, `Deposits.lean`, `Consolidations.lean`.
4. Committees: steps 15, 16, 17. Files `Shuffle.lean` (shuffle, seed, balance weighted
   selection), `Committees.lean`.
5. Lead: `Epoch.lean` joins the 17 steps. Then Lighthouse equals Etheorem for the whole epoch.

## Findings

(a) is a bug in our spec, (b) a bug in Etheorem, (c) a pyspec edge case.

- F1 (a, fixed in `3d23532456`). Our spec fixed four config values at mainnet:
  `PENDING_PARTIAL_WITHDRAWALS_LIMIT`, `PENDING_CONSOLIDATIONS_LIMIT`,
  `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` and `MIN_BUILDER_WITHDRAWABILITY_DELAY`. On minimal
  they are 64, 64, 32 and 2. Only block processing reads them. They are now `Preset` fields.
- F2 (b). Etheorem's Fulu and Gloas `process_pending_deposits` keep the Electra eth1 bridge
  check. Fulu removed it. Example: `deposit_requests_start_index = 10`,
  `eth1_deposit_index = 5`, one pending deposit at slot 1, finalized, inside the churn. pyspec
  applies it. Etheorem stops the scan and keeps the deposit pending. Lighthouse and our spec
  follow pyspec. The step proof needs `eth1_deposit_index ≥ deposit_requests_start_index` or
  deposits at slot 0.
- F3 (b). Etheorem's `compute_balance_weighted_selection` stops after 10^7 passes. pyspec loops
  until it has `size` items. Example: every candidate has effective balance 0. A pass selects
  only when `random_value = 0`, one time in 65536. A sync committee then needs about 33.5M
  passes. Etheorem fills the rest with validator 0.
- F4 (b and c). Etheorem has no `assert total > 0`. With no candidates it returns validator 0.
  In pyspec the assert raises. Gloas (EIP-8045) drops slashed validators from the proposer
  candidates. A slashed validator stays active until its exit epoch. So if every validator
  active at epoch `N + 2` is slashed, `process_proposer_lookahead` raises and no state passes
  the epoch boundary. Example: a small devnet where every validator gets slashed.
  Before Gloas the candidates include slashed validators, so the assert does not fire.
- F5 (c). `get_inactivity_penalty_deltas` multiplies `effective_balance * inactivity_score`.
  pyspec raises when the product reaches 2^64. That needs a score of 2^23 at 2048 ETH, about
  2.1M epochs of leak. Etheorem computes in `Nat` and does not raise.
- F6 (version). Etheorem pins alpha.11. In beta.2 every `BeaconState` list is a
  `ProgressiveList` with no limit. Etheorem keeps the alpha.11 limits and drops items past them
  (`builder_pending_withdrawals` 2^20, `historical_summaries` 2^24). The proofs need the lists
  to stay under these limits. Three block-only values also changed:
  `MIN_BUILDER_WITHDRAWABILITY_DELAY` (8192 to 64), `BUILDER_WITHDRAWAL_PREFIX` (0x03 to 0xB0)
  and `MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD` (256 to 64).
- F7 (b, unreachable). Etheorem's `get_next_sync_committee` does not check `KeyValidate` on
  the keys. pyspec's `eth_aggregate_pubkeys` asserts it. A deposit adds a validator only after
  its signature verifies with the key, so every key in the registry passes. Step 15 needs this
  as a hypothesis on `o.bls_KeyValidate`.
- F8 (b, unreachable). Etheorem wraps where pyspec raises: the total balance sum, the
  slashings sum, `epoch + k` compares, `balance + downward`, `score + bias` and
  `get_finality_delay` when the finalized epoch is above the previous epoch. The lemmas assume
  the reference succeeds, so the reachable-state invariants cover these.

## The Oracle

| Field | Etheorem | Status |
|---|---|---|
| `hash` | `sha` (`Sha256Spec` with `pureHasherTag`) | Clean |
| `hash_tree_root_BlockRoots`, `_StateRoots` | `htr` on the vector | Clean |
| `hash_tree_root_ForkData`, `_SigningData`, `_DepositMessage` | `htr` | Clean |
| `bls_Verify`, `bls_AggregatePKs` | `[CryptoBackend]` | Parameter, as in our spec |
| `bls_KeyValidate` | none | Needs a hypothesis (F7) |

`etheoremOracle_agrees` proves `OracleAgrees` for `etheoremOracle`, so the hypothesis holds.
