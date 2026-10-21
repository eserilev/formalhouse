# Epoch processing proofs

Goal: prove that Lighthouse's Gloas epoch processing equals the consensus spec for every state.

```
../src/per_epoch_processing/{builder_pending_payments,effective_balance,inactivity_updates,slashings_penalty,
   rewards_penalties,registry_update,pending_deposits,pending_consolidations,
   single_pass_step,justification,epoch_committees,tail_updates}.rs
../../types/src/state/balance_weighted_selection.rs
../../swap_or_not_shuffle/src/{shuffle_hash,compute_shuffled_index_with}.rs
   --charon--> .llbc --aeneas--> EpochProofs/Generated.lean
                                          |
                     EpochProofs/Equiv/*.lean (equivalence proof)
                                          |
EpochProofs/Spec/*.lean  <-- written by hand from the consensus specs
```

## Status

| Function | Reference | Generated | Equivalence |
|---|---|---|---|
| `process_builder_pending_payments` | Done | Done | Done |
| `process_effective_balance_updates` (per validator) | Done | Done | Done |
| `process_inactivity_updates` (per validator) | Done | Done | Done |
| `process_slashings` (context and per validator) | Done | Done | Done |
| `process_rewards_and_penalties` (per validator) | Done | Done | Done, with a condition |
| `process_registry_updates` (per validator, after Electra) | Done | Done | Done, with conditions |
| `process_pending_deposits` (decisions) | Done | Done | Done |
| `process_pending_consolidations` (balance moves) | Done | Done | Done |
| `process_justification_and_finalization` | Done | Done | Done |
| `process_proposer_lookahead`, `process_ptc_window`, sync committee selection (Gloas) | Done | Done | Done, with glue conditions |
| eth1, slashings and randao resets, historical summaries (checks) | Done | Done | Done |
| Fulu: exit and activation churn, proposer lookahead, sync committee selection | Done | Done (shared with Gloas) | Done, with glue conditions |
| Fulu: registry update and single pass | Done (shared with Gloas) | Done (shared with Gloas) | Done |
| Fulu: whole epoch against Etheorem's Fulu `processEpoch` | Done | - | Done, with conditions |

## The final result

`formalhouse_gloas_epoch` (`EpochProofs/Formalhouse.lean`) joins the epoch results. On mainnet,
at the last slot of an epoch of a reachable run:

1. Lighthouse's epoch model `process_epoch_lh_order` returns `ok`.
2. The result equals Etheorem's Gloas `processEpoch`.
3. The progressive balances, epoch cache and PTC committee reads equal the spec values, given
   the build fact of each cache.
4. The pubkey cache lookup of the pending deposits equals the spec lookup.

`GloasEpochConds` holds the conditions on the epoch start state, by kind:

| Kind | Fields | Where they come from |
|---|---|---|
| Reachable-state invariants | `reachable`, `pubkeys`, `vectors` | `Sanity/Invariants/*` prove them for every state that spec state transitions reach |
| Epoch boundary and time bounds | `boundary` (last slot, next slot in `u64`, fewer than `2^24` historical summaries), `slot` (`slot + 8192 < 2^64`) | time: unreachable for about 1.6M years |
| Supply and time bounds | `rows` (`RowBounds`: inactivity scores (F5), supply, balance sum, exit queue, registry size, participation) | the pyspec also raises without them |
| Etheorem list limits | `etheoremRoom` (deposit room, builder withdrawals room) | Etheorem keeps the alpha.11 limits (F6, F10); beta.2 has none |
| Committee steps | `committees`: `CommConds` (state facts) and `CommPreconds` (a sync candidate, a proposer candidate (F4), at least 32 active validators (F12), selections end within `2^64` passes) | `CommPreconds` are true pyspec preconditions; the pass bound is a fact about the hash values |
| Etheorem output | `selections` (F3: Etheorem stops a selection after `10^7` passes) | a fact about the hash values |
| Oracle | `oracle` (SHA-256, the roots, BLS checks agree with Etheorem), `sha` (32 bytes) | `etheoremOracle_agrees` shows such an Oracle exists |

The caches are arguments with their build facts: the progressive balances cache is `Coherent`
with the state, the epoch cache total is the active effective balance sum, the committee cache
satisfies `CommitteeCacheBuilt`, and the pubkey cache is `Coherent` with the validator pubkeys.

### Every epoch step

| Step | Aeneas-checked Rust | Glue modeled by hand | Cache build fact | Spec precondition |
|---|---|---|---|---|
| Justification and finalization | `justification.rs` | read the bits and roots, write the checkpoints | progressive balances `Coherent` | none |
| Inactivity, rewards, registry, slashings, deposit top-up, effective balance (Gloas and Fulu) | `single_pass_step.rs` and the step modules; Fulu at `fuluTab` | the milhouse loop and the writes after it | epoch cache total and base reward; progressive balances | `RowBounds` |
| Pending deposits | `pending_deposits.rs`, `deposit_balance.rs` | the `Validator` struct build and the five list pushes | pubkey cache `Coherent` | none |
| Pending consolidations | `pending_consolidations.rs` | the index table and the balance write back | none | none |
| Builder pending payments (Gloas) | `builder_pending_payments.rs` | the list writes | epoch cache total | none |
| Proposer lookahead | `epoch_committees.rs`, `balance_weighted_selection.rs`, `compute_shuffled_index_with.rs`; Fulu: the Electra loop | `SeedMixLink`, `EBLink`, the index lists | none (read from the registry) | F4; Fulu: `ProposerFin` |
| PTC window (Gloas) | as the lookahead | the PTC joining loop (`CommitteesFromCache`), the milhouse shift | `CommitteeCacheBuilt` | F12 |
| Next sync committee | as the lookahead; Fulu: the Electra loop | the pubkeys and the aggregate key | none | a sync candidate |
| Eth1, slashings and randao resets, historical summaries | `tail_updates.rs` | the vector writes; the summary root is `hash_tree_root` in the Oracle | none | none |
| Participation flag rotation | none | the whole step | none | none |
| Step order | not Rust | `process_epoch_lh_order` follows `altair.rs` and `single_pass.rs`; `LighthouseOrder*.lean` proves it safe | none | none |
| Genesis epoch | `single_pass_step.rs` with `after_genesis` false | as the other epochs | as the other epochs | none |

Fulu: `process_epoch_fulu_etheorem` proves the Fulu spec epoch equal to Etheorem's Fulu
`processEpoch`, and the Fulu Lighthouse steps are proved per step (see "Fulu"). A whole-epoch
Fulu Lighthouse model, and so a `formalhouse_fulu_epoch`, does not exist yet: the tail model
(`LighthouseTail*.lean`) uses one total for rewards and churn and includes the Gloas-only steps.

## Each epoch step and what checks it

The main result is `lighthouse_order_epoch_etheorem_reachable`. It is a theorem about the model
`process_epoch_lh_order`. The table says, for each step of the model, which Lighthouse Rust
Aeneas translates, and what the model takes on trust. "Glue" is Rust that reads or writes the
state around a translated function, modeled by hand in Lean. "Cache" is a Lighthouse cache whose
value the model takes from the spec. The cache stack (#24 to #29) proves the caches separately.
`EpochProofs/CacheBridge/` joins part of it to the main result: see "The cache proofs" below.

| Step (Lighthouse order) | Aeneas-checked Rust | Glue (by hand) | Cache (trusted here) |
|---|---|---|---|
| Justification and finalization | `justification.rs` (#53) | read the bits and roots, write the checkpoints | progressive balances totals: proved equal to the spec when the cache is `Coherent` (`lh_cache_reads_mainnet`) |
| Inactivity, rewards, registry, slashings, deposit top-up, effective balance | `single_pass_step.rs` and the step modules (#5 to #12, #22) | the milhouse loop in `single_pass.rs` calls the step once per validator, in order | base reward and total active balance: proved equal to the spec when the epoch cache is built from the state (`lh_base_reward_eq`, `lh_cache_reads_mainnet`); the exit cache and the activation queue are not read after Electra |
| Pending deposits | `pending_deposits.rs` (#10); the effective balance of a new validator, `deposit_balance.rs` (#60) | the pubkey map; the `Validator` struct build and the list pushes of `add_validator_to_registry` | pubkey cache (#70) |
| Pending consolidations | `pending_consolidations.rs` (#11) | the index table and the balance write back | none |
| Builder pending payments | `builder_pending_payments.rs` (#4) | the list writes | total active balance |
| Proposer lookahead, PTC window, next sync committee | `epoch_committees.rs`, `balance_weighted_selection.rs`, `compute_shuffled_index_with.rs` (#54) | `SeedMixLink`, `EBLink`, the index lists, the milhouse PTC shift, the sync committee keys and aggregate key | committee cache (#28), shuffle (#29) |
| Eth1, slashings and randao resets, historical summaries | `tail_updates.rs` (#56) | the vector writes (`LighthouseResets.lean`); the summary root is `hash_tree_root` in the Oracle | none |
| Participation flag rotation | none | the whole step | none |
| Step order | not Rust | `process_epoch_lh_order` follows `altair.rs` and `single_pass.rs`; `LighthouseOrder*.lean` proves the order safe | none |
| Genesis epoch | `single_pass_step.rs` with `after_genesis` false (`SinglePassStep.lean`) | same as the other epochs; `LighthouseGenesis.lean` proves the genesis single pass | same as the other epochs |

For the committee steps, the theorems of #54 show that the Rust returns the spec result under the
glue conditions. The model calls the spec function at that step. The glue conditions are not
hypotheses of the main result.

## The theorems

```lean
theorem builder_pending_payments_equiv (p : Spec.Preset)
    (total_active_balance slots_per_epoch : U64) (spe : Usize)
    (hslots : slots_per_epoch.val = p.SLOTS_PER_EPOCH) (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (payments : Slice LhPayment) (withdrawals : List LhWithdrawal)
    (hlen : payments.val.length = 2 * p.SLOTS_PER_EPOCH) :
    lighthouseBuilderPendingPayments total_active_balance slots_per_epoch spe payments withdrawals
      ⦃ r => absResult absState r =
        Spec.process_builder_pending_payments p total_active_balance.val
          (absState (withdrawals, payments.val)) ⦄

theorem new_effective_balance_equiv (p : Spec.Preset) (validator : Spec.Validator)
    (balance effective_balance limit downward upward increment : U64)
    (heffective : effective_balance.val = validator.effective_balance)
    (hlimit : limit.val = Spec.get_max_effective_balance p validator)
    (hincrement : increment.val = p.EFFECTIVE_BALANCE_INCREMENT) :
    per_epoch_processing.effective_balance.new_effective_balance
      balance effective_balance limit downward upward increment ⦃ r =>
        absResult (·.val) r =
          Spec.newEffectiveBalance p downward.val upward.val validator balance.val ⦄

theorem new_inactivity_score_equiv (p : Spec.Preset) (score bias recovery_rate : U64)
    (is_eligible is_participating is_in_leak : Bool)
    (hbias : bias.val = p.INACTIVITY_SCORE_BIAS)
    (hrecovery : recovery_rate.val = p.INACTIVITY_SCORE_RECOVERY_RATE) :
    per_epoch_processing.inactivity_updates.new_inactivity_score
      score is_eligible is_participating is_in_leak bias recovery_rate ⦃ r =>
        absResult (·.val) r =
          if is_eligible then Spec.inactivityScoreStep p is_participating is_in_leak score.val
          else .ok score.val ⦄
```

For every input, Lighthouse returns `ok`, so it does not panic. Its result maps to the
reference result. An overflow or a division by zero maps to the same spec error.

`hysteresis_thresholds_equiv` does the same for the threshold computation.
`slashings_context_equiv` and `new_balance_after_slashing_equiv` do the same for slashings,
after Electra.

`new_balance_after_rewards_equiv` relates `new_balance_after_rewards` to `rewardsCombined`: add all
rewards, then subtract all penalties once. The spec instead applies the four deltas in four
rounds, with `saturating_sub` after each round (`rewardsSequential`).
`new_balance_after_rewards_eq_spec` shows that the two agree when the balance covers all
penalties and no addition overflows. `rewards_saturation_example` shows an input where they
differ: a balance of 3, a source penalty of 5 and a target reward of 10 give 10 in the spec
and 8 in Lighthouse. Prysm uses the same order as Lighthouse.

`registry_update_equiv` relates `registry_update` to `registryStepIndependent`: three
independent steps (queue eligibility, ejection, activation). The spec uses `if`/`elif`/`elif`
instead (`registryStepExclusive`). `registry_update_eq_spec` shows that the two agree when
`EJECTION_BALANCE < MIN_ACTIVATION_BALANCE`, the finalized epoch is not after the current
epoch, and the epochs fit in a `u64`. The theorems cover Gloas, where the exit churn has no
upper limit.

`process_pending_deposits_equiv` relates the deposit decisions to `depositDecisions`: which
deposits to apply, which to postpone, where to stop, and the remaining churn. Lighthouse reads
each deposit's validator before `process_registry_updates` runs and predicts its ejection.
`predictedStatus_eq_post_registry` shows that this prediction equals the spec's flags after the
registry update, on valid states.

`process_pending_consolidations_equiv` relates the consolidation moves to
`stepLoop consolidationStep`: the new balances, the number of processed consolidations, and the
error. Lighthouse runs on a local table of the validators that consolidations reference.
`process_pending_consolidations_eq` shows that the reference equals `stepLoop consolidationStep`
on the full registry, then a drop of the processed consolidations.

## Gloas committee steps

`EpochProofs/Equiv/EpochCommittees.lean` proves the pure functions that the Gloas proposer
lookahead, PTC window and sync committee steps call equal to the reference:

- `next_proposer_lookahead_spec`: `epoch_committees::next_proposer_lookahead` returns the
  `proposer_lookahead` of `process_proposer_lookahead`.
- `ptc_for_epoch_spec`: `epoch_committees::ptc_for_epoch` returns the PTCs that
  `process_ptc_window` appends.
- `next_sync_committee_indices_spec`: `epoch_committees::next_sync_committee_indices` returns
  `get_next_sync_committee_indices`.

They rest on `compute_balance_weighted_selection_spec` (`Equiv/BalanceWeightedSelection.lean`)
and `compute_shuffled_index_with_eq` (`Equiv/ShuffledIndex.lean`). The closed form of the spec
shuffle (`Sanity/ShuffleClosedForm.lean`) is ported from the committee shuffle proof (#29).

## Fulu

Fulu is live on mainnet. Lighthouse runs the Fulu epoch through the same translated functions as
Gloas, with the Fulu constants and the Fulu candidates. `Spec/Fulu.lean` transcribes the Fulu
functions that differ from Gloas. `Sanity/Fulu.lean` reduces them to the Gloas functions, and
`Equiv/Fulu.lean` proves the Lighthouse functions equal to them:

- Churn: the Fulu churn is the Gloas activation churn with `CHURN_LIMIT_QUOTIENT` and
  `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` (`get_activation_churn_limit_fuluView`). So Fulu
  `process_pending_deposits` is Gloas `process_pending_deposits` on `p.fuluView f`
  (`process_pending_deposits_fulu_eq`). `exit_churn_limit_fulu`: `registry_update::exit_churn_limit`
  with the Fulu constants returns `get_activation_exit_churn_limit`. The pending deposits glue
  now computes its churn with the same function (`activation_churn_constants` in
  `single_pass.rs`); `activation_churn_limit_gloas` covers the Gloas constants.
- Sync committee: the Electra `get_next_sync_committee_indices` loop returns what
  `compute_balance_weighted_selection` returns (`get_next_sync_committee_indices_fulu_iff`).
  Lighthouse now uses `epoch_committees::next_sync_committee_indices` from Electra on
  (`next_sync_committee_indices_spec_fulu`).
- Proposer lookahead: an Electra `compute_proposer_index` is the first item of a selection of size
  1 (`compute_proposer_index_selection`), if its loop ends before the last pass (`ProposerFin`, a
  fact about the hash values, like the Gloas selection end facts). Lighthouse now runs the Fulu
  lookahead through `epoch_committees::next_proposer_lookahead` on all the active validators
  (`next_proposer_lookahead_spec_fulu`).

- Registry update and single pass: on mainnet and minimal the Fulu quotient is twice the Gloas
  quotient and the Fulu cap is the Gloas activation cap (`FuluCompat`). So the Fulu churn of a
  total is the Gloas churn of `fuluTab` of it (`fulu_exit_churn_eq`, `fulu_activation_churn_eq`),
  and Fulu `process_registry_updates` and `process_pending_deposits` are the Gloas functions at
  `fuluTab`, with the same preset (`process_registry_updates_fulu_eq`,
  `process_pending_deposits_fulu_tab_eq`). The registry theorems of `Equiv/RegistryUpdates.lean`
  and `single_pass_step_equiv` now take any constants whose exit churn is the Gloas churn of
  `T total` (`ChurnSpec`). With the Fulu constants `T = fuluTab`
  (`single_pass_step_equiv_fulu`). `lighthouse_single_pass_eq_spec_fulu`: one pass of `lhRowStep`
  with the registry total `fuluTab` equals the Fulu inactivity, rewards, registry and slashings
  passes. Only the registry pass reads `fuluTab`; `separate_passes_eq_single_pass_tab` takes the
  registry total apart from the total of the other passes.
- Order: Lighthouse runs the Fulu proposer lookahead inside the single pass, before the resets,
  the historical summaries update, the participation rotation and the sync committee update.
  `specOrderFulu_lhOrderFulu` shows that the two orders give the same `ok` results.
- `Spec/FuluEpoch.lean` transcribes the Fulu `process_epoch`. `process_epoch_fulu_eq_tab` writes
  its registry update and pending deposits as the Gloas functions at `fuluTab`, and
  `process_sync_committee_updates_fulu_sameOk` relates its sync committee update to the Gloas one.

Not yet done for Fulu: the whole-epoch model `process_epoch_lh_order` and its capstones for Fulu,
and Fulu totality. The Etheorem bridge for Fulu is done (see Etheorem below). The tail proofs (`LighthouseTail*.lean`) take one
total for the rewards, the slashings, the registry churn and the deposit churn, and they include
the builder payments and the PTC window. Fulu needs the churn total `fuluTab` apart from the
rewards total, and no builder payments or PTC window.

## Separate passes and the single pass

The spec runs each epoch step as its own pass over the validators. Lighthouse runs all steps
for one validator, then moves to the next validator. `separate_passes_eq_single_pass` shows that the spec's
inactivity, rewards, registry and slashings passes give the same `ok` results as one pass of
`singlePassStep`. That step runs the four row steps on each validator in turn.

The two orders can fail on different validators, so the theorem states `SameOk`: the same `ok`
values, and an error in one order exactly when there is an error in the other order.

Each pass has its own row theorem (`process_*_rows` in `EpochProofs/Sanity/Rows*.lean`). Each
row step uses the per-validator function that the Lighthouse code is proved equal to.
`two_passes_eq_one_pass` shows that two passes equal one pass of both steps.

`single_pass_step.rs` holds the loop body for one validator after Electra. It runs the four
steps in the Lighthouse order. `single_pass_step_equiv` shows that the generated code equals
`lhRowStep`. `lhRowStep_eq_singlePassStep` shows that `lhRowStep` equals `singlePassStep` under
the rewards and registry conditions above, if the base reward from the epoch cache equals
`get_base_reward`.

Not covered yet: pending deposits and consolidations, which run between slashings and effective
balance updates.

## Justification and finalization

`justification.rs` holds the arithmetic and the decisions of
`weigh_justification_and_finalization`. `weigh_justification_equiv` shows that the generated
code equals `Spec.lhWeighJustification`. `lhJustificationAndFinalization` models the caller: it
reads the bits, runs the module, then reads the block roots and writes the checkpoints.
`lhJustificationAndFinalization_sameOk` shows that the model has the same `ok` results as the
spec. Lighthouse does the arithmetic before it reads the block roots, so the two can fail at
different steps. `process_epoch_lh_full` runs this model.

## State conditions

`lighthouse_single_pass_eq_spec` replaces the per-validator conditions with facts about the
state at the start of epoch processing, on mainnet.

The rewards condition is weaker than "the balance covers all penalties". The inactivity penalty
is the last of the four rounds, and no reward follows it. So only the three flag penalties must
fit in the balance (`rewardsCombined_eq_sequential_flags`). These penalties are at most 40/64 of
the base reward, and the base reward is at most 1/256 of the effective balance
(`rewardsBaseReward_bound`). The old condition fails in a long inactivity leak. The new one
does not.

| Fact | Status |
|---|---|
| Effective balance ≤ 256 × balance, for eligible validators | Proved after `process_effective_balance_updates` (`process_effective_balance_updates_floor_mainnet`, in fact 3 × effective balance ≤ 4 × balance). Assumed to hold until the next epoch. |
| `EJECTION_BALANCE < MIN_ACTIVATION_BALANCE` | Proved for mainnet and minimal |
| Balance + effective balance < 2^64 | Assumed. The ETH supply is below 2^57 Gwei. |
| Exit epoch ≤ `FAR_FUTURE_EPOCH`, next epoch < 2^64 | Assumed. These are `u64` values. |
| Finalized epoch ≤ current epoch | Assumed. Justification and finalization are not transcribed. |
| `get_total_active_balance` ≥ one increment | Assumed. It is `max(INCREMENT, sum)` by definition. |
| Each flag's participating increments ≤ 256 × active increments | Assumed. The two sets differ only by validators that activate or exit at this boundary. |
| `base_reward` from the epoch cache = `get_base_reward` | Assumed (cache) |

Block processing between two epochs is not modelled. It lowers balances in three ways:
- Slashing removes 1/4096 of the effective balance.
- A partial withdrawal leaves at least `MIN_ACTIVATION_BALANCE` or the maximum effective balance.
- A full withdrawal applies only to a withdrawable validator, which is no longer eligible. So
  the floor is only required for eligible validators.
None of these breaks the effective balance floor, but no proof covers this argument.

`absState` maps Aeneas types to reference types. Rust `Default` maps to spec `empty()`.

## The epoch succeeds

`SameOk` gives "Lighthouse returns `ok v` exactly when the spec returns `ok v`". It does not say
that either one returns `ok`. `Sanity/Invariants/Totality.lean` proves that the spec epoch
returns `ok` at the last slot of an epoch on mainnet (`process_epoch_total`).
`Etheorem/Total.lean` combines it with `SameOk` and the Etheorem bridge
(`lighthouse_epoch_total_etheorem`): the Lighthouse model returns `ok`, and its state equals
Etheorem's.

| Step | Status |
|---|---|
| Justification and finalization | Proved (`process_justification_and_finalization_total`) |
| Inactivity, rewards, registry, slashings | Proved (`midOk_of_rowBounds`, `RowBounds`) |
| Eth1 data reset | Proved |
| Pending deposits | Proved (`depOk_of_rowBounds`, `RowBounds`) |
| Pending consolidations | Proved. The balance sum does not grow. |
| Builder pending payments | Proved |
| Effective balance updates | Proved |
| Slashings reset, RANDAO mixes reset, historical summaries, participation | Proved |
| Sync committee, proposer lookahead, PTC window | Proved (`committee_steps_total`), from `CommConds` and `CommPreconds` |

Conditions beyond the reachable-state invariants: `slot + 8192 < 2^64` (the pyspec
`get_block_root` adds `SLOTS_PER_HISTORICAL_ROOT` to a slot), and the SSZ vector lengths
(`VectorLengths`).

The committee steps (`Sanity/Invariants/TotalityCommittees.lean`) read two more sets of facts
at the state before them:
- `CommConds`: at most `2^40` validators, `effective_balance ≤ MAX_EFFECTIVE_BALANCE_ELECTRA`,
  the lengths of `proposer_lookahead` and `ptc_window`, and valid public keys. These are
  invariants of reachable states. No proof carries them through the earlier epoch steps yet.
- `CommPreconds`: the pyspec raises without them. A validator is active at the next epoch (sync
  committee). An active validator at `current + 2` is not slashed (F4). At least
  `SLOTS_PER_EPOCH` validators are active at `current + 2`. Each balance weighted selection
  ends within `2^64` passes (a fact about the hash values, like F3).

`process_ptc_window_few_active_error` proves the third one is a real pyspec halt: with fewer than
`SLOTS_PER_EPOCH` validators active at `current + 2`, the first slot of that epoch has no
committee members, and `compute_ptc` raises at `assert total > 0`.

`Sanity/Invariants/TotalityRows.lean` proves the per-validator steps and the pending deposits
under `RowBounds`, a set of time and supply bounds on the epoch input. The pyspec raises
without them too:
- Inactivity scores below `2^22`. Above about `2^23`, `effective_balance * inactivity_score`
  overflows (F5). Scores grow by 4 per epoch of leak.
- Effective balances sum below `2^57` Gwei (about 144M ETH). Above that, the flag reward
  numerator `base_reward * weight * participating_increments` can overflow.
- Balances, pending deposits and `deposit_balance_to_consume` sum below `2^61` Gwei.
- The earliest exit epoch below `2^62`, the exit churn below `2^61`, and fewer than `2^40`
  validators.
- Each flag's previous-epoch participating increments at most `1024` times the current active
  increments. This bounds the sum of the rewards.
`process_epoch_total_rows` and `lighthouse_epoch_total_etheorem` take `RowBounds` and the
committee step conditions (`CommConds`, `CommPreconds`).

## The whole state transition

`lighthouse_state_transition_sameOk` (in `Sanity/Invariants/Capstone.lean`) is the main result.
On mainnet, a state transition that runs Lighthouse's single pass in place of the spec's
inactivity, rewards, registry and slashings passes gives the same `ok` results as the spec.
This holds from every state that spec state transitions reach from a genesis-like state.

`lighthouse_full_epoch_state_transition_sameOk` covers the whole Lighthouse epoch. It uses
`process_epoch_lh_full`, which follows `single_pass.rs`:
- Pending deposits are decided once, before the loop.
- In the loop, each validator gets its top-up sum and its effective balance update. A
  validator that a pending consolidation names keeps its effective balance in the loop.
- After the loop, new validators are added and get their effective balance update. Then
  consolidations run, and the named validators get their effective balance update.

This order equals the spec's deposits, consolidations, builder payments and effective balance
updates if every pending consolidation names an existing validator, and if a validator with no
exit also has no withdrawable epoch. Both hold on every reachable state, and so does pubkey
uniqueness, which Lighthouse's pubkey map relies on.

To get there, `Spec/` transcribes all of Gloas block processing and `process_epoch`, and
`Sanity/Invariants/` proves these invariants on every reachable state:

| Invariant | File |
|---|---|
| Finalized ≤ previous justified ≤ current justified ≤ current epoch | `Sanity/JustificationFinalization.lean`, `Sanity/Driver.lean` |
| Per-validator lists have one entry per validator | `Lengths.lean` |
| `exit_epoch + 256 ≤ withdrawable_epoch` unless withdrawable is far future | `ExitDelay.lean` |
| Exit epochs fit in a `u64` | `ExitEpochs.lean` |
| After each epoch, effective balance ≤ 4/3 × balance, a multiple of 1 ETH, ≤ 2048 ETH | `EpochEnd.lean` |
| At each epoch boundary, effective balance ≤ 256 × balance for eligible validators | `BalanceFloor.lean`, `Reachable.lean` |
| Validator pubkeys are unique | `PubkeysUnique.lean` |
| Pending consolidations name existing validators | `ConsolidationIndices.lean` |
| Withdrawable epochs fit in a `u64` | `WithdrawableEpochs.lean` |

The balance floor survives the blocks of one epoch: at most one slashing of EB/4096 per
validator, and at most 32 sync aggregates. A validator can hold many sync committee seats, so
the sync penalty bound needs the active balance to be at most 139M ETH. That is above the total
ETH supply.

Hypotheses that remain:
- The start state satisfies the invariants above. Genesis does.
- The active balance is at most 139M ETH before each block (`SupplyBound`).
- At each epoch, balances are below 2^62, effective balances sum below 2^60, and three times
  the slashings sum fits in a `u64` (`EpochSupply`).
- Block slots fit in a `u64`, and sync aggregates have at most 512 bits (SSZ types).
- BLS, `hash_tree_root` and the execution engine are parameters (`Spec/Oracle.lean`).
- The base reward that Lighthouse reads from the epoch cache equals `get_base_reward`.

## The Lighthouse order of the epoch tail

`process_epoch_lh_full` calls the spec functions for the resets and runs the steps after the
builder payments in the spec order. Lighthouse runs them in another order:
`process_epoch_single_pass` ends with the proposer lookahead and the PTC window, and then
`altair.rs` runs the eth1, slashings and randao resets, the historical summaries update, the
participation rotation and the sync committee update.

`process_epoch_lh_order` (in `Sanity/Invariants/LighthouseOrder.lean`) follows this order. The
checks of the resets and of the historical summaries update come from `tail_updates.rs`, which
Aeneas translates. `Equiv/TailUpdates.lean` relates each Rust function to a model, and
`LighthouseResets.lean` relates each Lighthouse reset to the spec reset.

| Theorem | Statement |
|---|---|
| `specOrder_lhOrder` | The spec order and the Lighthouse order of the eight tail steps give the same `ok` results. |
| `process_epoch_lh_order_sameOk` | `process_epoch_lh_order` and `process_epoch_lh_full` give the same `ok` results. |
| `lighthouse_order_epoch_state_transition_sameOk` | The whole state transition with `process_epoch_lh_order` equals the spec on every reachable state. |

The steps commute for these reasons:
- The committee steps read `slot`, `validators`, `randao_mixes` and their own field. The other
  steps do not write these fields, except the randao reset. The randao reset writes the mix of
  the next epoch. The committee steps read the mix of the current epoch (`rrNew_seed`).
- The eth1 reset reads only the slot. The deposits, consolidations, payments and committee
  steps keep the slot and do not read `eth1_data_votes`.

Conditions beyond `lighthouse_full_epoch_state_transition_sameOk`:
- `historical_summaries` holds fewer than 2^24 items at each epoch boundary (`HistRoom`).
  Lighthouse pushes to a list with that limit. The beta.2 list has no limit.
- The eth1 reset of Lighthouse tests `(slot + 1) % 2048 == 0`. The spec tests
  `next_epoch % 64 == 0`. They agree at the last slot of an epoch when `slot + 1` fits in a
  `u64`. `reachable_state_transition_sameOk_last` gives both facts.

## The reference

`EpochProofs/Spec/` transcribes the consensus specs (v1.7.0-beta.2) line by line. Each
definition quotes its pyspec. Effective balance updates come from Electra, because Gloas does
not change them.

Rules:

- Write the reference from the spec only. Do not read Lighthouse.
- Keep the spec names and statement order. Do not optimise.
- Model each pyspec raise as `Except.error`. Use the `uint64*` functions for `Uint64` values.
- Python `or` does not evaluate its right side when the left side is true. Keep that order.
- Import Lean core only.

`EpochProofs/Sanity/` proves facts about the reference alone:

| Theorem | Fact |
|---|---|
| `withdrawals_loop` | The loop appends the withdrawals of payments at or above the quorum, in order. It never fails. |
| `process_builder_pending_payments_eq` | A closed form with no loop and no slice assignment |
| `process_builder_pending_payments_wellFormed` | The payments vector keeps length `2 * SLOTS_PER_EPOCH` |
| `get_builder_payment_quorum_threshold_ok` | If `SLOTS_PER_EPOCH ≥ 6`, the quorum does not overflow |
| `process_effective_balance_updates_eq` | The loop is a `mapM` of one step per validator |
| `hysteresisThresholds_mainnet` | Mainnet thresholds are 0.25 ETH down and 1.25 ETH up |
| `newEffectiveBalance_le_max` | A changed effective balance never exceeds `get_max_effective_balance` |
| `newEffectiveBalance_in_band` | Inside the hysteresis band, the effective balance does not change |
| `process_inactivity_updates_eq` | If the eligible set, the participating set and the leak flag evaluate, the loop is a `foldlM` of one step per eligible index |
| `inactivityScoreStep_leak_missed` | In a leak, a validator that missed the target gains exactly `INACTIVITY_SCORE_BIAS` |
| `inactivityScoreStep_participating_le` | The score of a validator that hit the target never goes up |
| `process_slashings_eq` | The loop is a `foldlM` of one step per validator, with the preamble computed once |
| `slashingBalanceStep_not_slashed` | A validator that is not slashed keeps its balance |
| `slashingBalanceStep_le` | The penalty never raises a balance |
| `rewardsSequential_eq_combined` | Without saturation, the four-round order is `balance + rewards - penalties` |
| `rewardsCombined_eq_sequential` | Under the same condition, the Lighthouse order equals the spec order |
| `rewards_saturation_example` | Without the condition, the two orders differ |
| `registryStepIndependent_eq_exclusive` | On valid states, three independent steps equal the spec's `if`/`elif`/`elif` |
| `predictedStatus_eq_post_registry` | Lighthouse's ejection prediction equals the flags after the registry update |
| `depositLoop_append` | The deposit loop over two lists is the loop over the first, then the second |
| `forIn_eq_stepLoop` | A `for` loop with `break` is a `stepLoop`, if each body run is one step |
| `process_pending_consolidations_eq` | If the balances and the validators have the same length, the reference is `stepLoop consolidationStep`, then a drop |
| `process_slots_invariant` | `process_slots` keeps each property that `process_slot`, `processEpoch` and the slot increment keep |
| `process_slots_frame` | If `processEpoch` keeps `validators`, `balances` and `inactivity_scores`, `process_slots` keeps them |
| `process_slots_slot` | If `processEpoch` keeps `slot`, `process_slots` ends at the target slot |
| `process_*_frame` | Slot, block header, RANDAO, eth1 and epoch reset steps keep `validators`, `balances`, `inactivity_scores` and `slot` |

`get_total_active_balance(state)` is a parameter. Lighthouse reads it from a cache.

`Spec/Oracle.lean` holds SHA-256, `hash_tree_root` and BLS as fields of an `Oracle` value. A
field is a parameter, not an axiom. A theorem for every `Oracle` does not depend on hash or
signature values. `process_slots` takes `process_epoch` as the parameter `processEpoch`.

## Etheorem

[Etheorem](https://github.com/etheorem/etheorem) is a Lean spec of the consensus specs that
passes the EF vectors. `EpochProofs/Etheorem/` proves our reference equal to it for the whole
Gloas epoch. The reference is then no longer trusted for the epoch.

| Theorem | Statement |
|---|---|
| `process_epoch_etheorem` | If `Spec.process_epoch` returns `s'`, Etheorem's `processEpoch` succeeds and `absEState` of its result is `s'`. |
| `lighthouse_epoch_etheorem` | The same for `process_epoch_lh_full`, the Lighthouse epoch model, on mainnet. |
| `lighthouse_epoch_etheorem_reachable` | The same at each epoch boundary of a reachable run, with the step conditions read from the epoch start state. |
| `lighthouse_order_epoch_etheorem` | The same for `process_epoch_lh_order`, the Lighthouse epoch in the Lighthouse order. |
| `lighthouse_order_epoch_etheorem_reachable` | The Lighthouse order at each epoch boundary of a reachable run. This is the main result. |

`Etheorem/Conditions.lean` proves three step conditions from the reachable-state invariants: the
finalized epoch is below `FAR_FUTURE_EPOCH`, and the registry lists have equal lengths before
the deposits and the consolidations. Frame lemmas move two conditions to the epoch start: room
in the registry for the `MAX_PENDING_DEPOSITS_PER_EPOCH` new validators of one epoch (F10), and
room in the builder withdrawals under Etheorem's alpha.11 limit (F6). The historical summaries
room is `HistRoom` in `TailPre`: beta.2 keeps the `HISTORICAL_ROOTS_LIMIT` cap, so it is a spec
condition, not an Etheorem one. The F3 conditions are facts about Etheorem's own output and
stay.

The 17 step theorems are in `Etheorem/<Step>.lean`. `etheorem/PLAN.md` lists the conditions of
`process_epoch_etheorem` and the findings.

`lighthouse_builder_pending_payments_etheorem` joins `builder_pending_payments_etheorem` to
`builder_pending_payments_equiv`:
Lighthouse returns `Ok`, Etheorem's run succeeds, and the results agree on the builder payment
fields. The conditions:

- `SLOTS_PER_EPOCH ≥ 6` (both presets), so the quorum does not overflow.
- The new withdrawals fit under the alpha.11 list limit, 2^20. Etheorem's `SSZList.push` drops
  an item past the limit. In beta.2 the list has no limit.
- Lighthouse's total active balance equals Etheorem's `get_total_active_balance`.

Etheorem pins spec v1.7.0-alpha.11. Every Gloas epoch function in alpha.11 has the same meaning
as in beta.2. Only type casts and syntax differ. The `BeaconState` lists have limits in
alpha.11 and none in beta.2.

### Fulu

`Etheorem/Fulu/` proves the reference Fulu `process_epoch` equal to Etheorem's Fulu
`processEpoch`: `process_epoch_fulu_etheorem`. Etheorem's Gloas steps replay the Fulu bodies, so
the Fulu files are copies of the Gloas ones over the Fulu state. The differences:

- `Fulu/State.lean`: the Gloas-only reference fields read as empty, and `latest_block_hash` reads
  the block hash of the latest execution payload header. No Fulu epoch step reads them.
- Churn: `FuluChurnAgrees` holds the Fulu config values and `FuluCompat`. Etheorem's Fulu
  `get_activation_exit_churn_limit` then equals the Gloas exit and activation churn at
  `fuluTab`, so the registry and deposits theorems run at `fuluTab`, as
  `process_epoch_fulu_eq_tab` writes them.
- Proposer lookahead: every active validator is a candidate. The reference uses the Electra loop
  and Etheorem the balance weighted selection. They agree when the loop ends before its last
  pass (`Spec.ProposerFin`, a condition in `FuluEpochConds`).
- Sync committee: the Electra loop gives the same `ok` results as the selection
  (`process_sync_committee_updates_fulu_sameOk`).
- No builder payments and no PTC window: 15 steps.

`FuluEpochConds` holds the step conditions: the Gloas ones without the builder withdrawals and
PTC conditions, plus `proposerFin`. The F2 condition stays, because this Etheorem pin keeps the
eth1 bridge check in its Fulu `process_pending_deposits` too.

The shared parts:

- `Etheorem/State.lean`: `absEState` maps every field of an Etheorem state to the reference.
- `Etheorem/Helpers.lean`: `PresetAgrees` (proved for both presets) and the helpers that many
  steps call, from epoch helpers to `initiate_validator_exit`.
- `Etheorem/Oracle.lean`: `OracleAgrees`, the Oracle fields that equal Etheorem functions.

The dependency is the fork `eserilev/etheorem`, branch `formalhouse-pin`, at the commit in
`lakefile.toml`. The fork is upstream Etheorem plus these changes:

- The v1.7.0-alpha.9 deposit change (F2): no eth1 bridge check in `process_pending_deposits`, no
  start index write in `process_deposit_request`, and no in-block deposits in
  `process_operations`.
- A port to Lean v4.31.0: four proof fixes, no `-march=native`, and a KZG lakefile fix that
  finds the BLS library when Etheorem is a dependency.

`etheorem/setup.sh` fetches blst, c-kzg-4844 and ISA-L at Etheorem's pins. ISA-L needs `nasm`.

## The cache proofs

`lakefile.toml` requires `cache_proofs` (`consensus/types/proofs`) by path.
`EpochProofs/Caches.lean` imports `CacheProofs` with the epoch proofs, so the build checks that
the two libraries load together. `EpochProofs/CacheBridge/` maps the epoch state to the state of
each cache model and proves the cache reads equal to the epoch spec values:

| Cache read in Lighthouse | Bridge theorem | Fact left about the cache |
|---|---|---|
| Progressive balances: current and previous epoch flag totals | `lh_current_flag_balance_eq`, `lh_previous_flag_balance_eq` | the cache is `Coherent` with the state (`build_coherent` and the update theorems of #27) |
| Epoch cache: floored total active balance | `lh_total_active_balance_eq` | the cache total is the active sum of the effective balances (`single_pass_total_active_balance`, #26) |
| Epoch cache: base reward | `lh_base_reward_eq` (equals `rewardsBaseReward`, which `lhBaseReward` uses) | the same total, and the table built from it |
| Exit cache | none | not read after Electra: `initiate_validator_exit` uses `compute_exit_epoch_and_update_churn`. `build_exit_cache` still runs, and it can fail only on a `u64` overflow |
| Activation queue | none | not read after Electra (`single_pass.rs` builds it only before Electra) |
| Committee cache (PTC committees) | `hcomm_of_cache`, `lh_ptc_window_from_cache` (`CacheBridge/Committees.lean`) | `CommitteeCacheBuilt`: the shuffling is the spec shuffling of the active indices with the spec seed, and the count is the spec count. `committeeCacheBuilt_of_rust` gives it from the outputs of the Aeneas-checked `shuffling` (#66) and `committee_count_per_slot` (#65). Also `CommitteesFromCache`: entry `k` joins the cache committees of slot `start + k` (the loop in `process_ptc_window`, glue) |
| Pubkey cache | none | no cache proof |

`lighthouse_order_epoch_etheorem_reachable_cached` states the main result together with the
cache reads (`lh_cache_reads_mainnet`) at the epoch start state.
`lighthouse_order_epoch_etheorem_reachable_cached_ptc` adds the committee cache read of the PTC
window step, for any state at which Lighthouse builds the cache.

The hash link: `natHash o` is `o.hash` on byte values, the hash form of the cache spec.
`csiFold_eq` proves the two closed forms of the shuffle equal for it, with no condition. The
two `Generated.lean` files each translate the `ShuffleHash` trait, so the cache side takes its
own `HashLink` to `natHash o`. Both instances are the same Rust `Sha256Hash`.

The index lists of the proposer lookahead and the sync committee, the seed mix and the effective
balances do not come from a cache. Lighthouse reads them from the validator list.

Both `Generated.lean` files translate `safe_arith::ArithError`. The Aeneas `discriminant`
attribute names its instance after the short type name, so the two files clash.
`aeneas/setup.sh` applies `aeneas/discriminant-instance-name.patch`, which names the instance
after the full type name. It changes no definition and no proof.

## Building

`setup.sh` runs `etheorem/setup.sh` and `aeneas/setup.sh`.

```sh
cd consensus/state_processing/proofs
lake exe cache get
./setup.sh
lake build
lake lean EpochProofs/Axioms.lean
```

Use `lake lean`, not `lake env lean`. Etheorem's modules are precompiled, and only `lake lean`
loads their native code.

## Regenerating after a change to a translated module

Use the Charon and Aeneas revisions in `.github/workflows/proofs.yml`. See
`validator_client/slashing_protection/proofs/README.md` for the build steps.

```sh
cd consensus/state_processing
out=$(mktemp -d)
charon cargo --preset=aeneas \
  --start-from 'state_processing::per_epoch_processing::builder_pending_payments' \
  --start-from 'state_processing::per_epoch_processing::effective_balance' \
  --start-from 'state_processing::per_epoch_processing::inactivity_updates' \
  --start-from 'state_processing::per_epoch_processing::slashings_penalty' \
  --start-from 'state_processing::per_epoch_processing::rewards_penalties' \
  --start-from 'state_processing::per_epoch_processing::registry_update' \
  --start-from 'state_processing::per_epoch_processing::pending_deposits' \
  --start-from 'state_processing::per_epoch_processing::pending_consolidations' \
  --start-from 'state_processing::per_epoch_processing::single_pass_step' \
  --start-from 'state_processing::per_epoch_processing::justification' \
  --start-from 'state_processing::per_epoch_processing::epoch_committees' \
  --start-from 'state_processing::per_epoch_processing::tail_updates' \
  --include safe_arith --include types::validator::deposit_balance \
  --include types::state::balance_weighted_selection \
  --include swap_or_not_shuffle::shuffle_hash --include swap_or_not_shuffle::compute_shuffled_index_with \
  --include types::builder --include alloy_primitives::bits \
  --include types::core::consts \
  --dest-file "$out/pure.llbc" -- --lib
aeneas -backend lean "$out/pure.llbc" -dest "$out"
cp "$out/Pure.lean" proofs/EpochProofs/Generated.lean
```

The `--include` flags translate the bodies of the `safe_arith` functions and the derived `Clone`
and `Default` impls. Without them, these functions become axioms.

If Charon fails with `found crate core compiled by an incompatible version of rustc`, the cached
Miri sysroot is for another nightly. Set `CHARON_MIRI_SYSROOTS` to a sysroot for the nightly in
Charon's `rust-toolchain` file.

## Why the translated modules look the way they do

Aeneas rejected the original code in `single_pass.rs` for two reasons:

- `push(...)?` inside a `for` loop is an early return inside a loop. Aeneas drops the body.
- Iterator adapters (`take`, `filter`, `map`, `chain`) stop Aeneas with an internal error.

`state_processing` denies indexing and unchecked arithmetic, so the module uses `get` and
`saturating_add`.

`registry_update.rs` splits the update into three step functions. In one function, Aeneas
copies the rest of the body into each branch, and the generated code grows exponentially.

`effective_balance.rs` takes plain `u64` values. If a function takes `&Validator` or
`&ChainSpec`, Aeneas turns `Epoch`, `Slot`, `PublicKey`, `Option::map` and more into axioms.

## Trusted base

- Charon and Aeneas.
- Etheorem, for the steps in `EpochProofs/Etheorem/`. It passes the EF vectors. The bridge
  targets the patched fork described in the "Etheorem" section, not upstream Etheorem.
- The Aeneas Lean library. Its four `sorry` warnings are not reachable from these theorems.
- The glue in `single_pass.rs`. It copies the milhouse vector, calls the module, and writes the
  results back. `lighthouseBuilderPendingPayments` models it by hand.
- `ChainSpec` sets the payment threshold to 6/10. The glue model uses these values.
- `state_ctxt.total_active_balance` equals `get_total_active_balance(state)`.
- After Electra, `Validator::get_max_effective_balance` calls `max_effective_balance_electra`
  of `deposit_balance.rs` (`max_effective_balance_electra_equiv`). The input
  `has_compounding_withdrawal_credential` compares the first credential byte with
  `COMPOUNDING_WITHDRAWAL_PREFIX`, as the spec does. `single_pass.rs` passes the result to
  `new_effective_balance`.
- `single_pass.rs` passes three flags to `new_inactivity_score`: `is_eligible`, the timely
  target check, and `is_in_inactivity_leak`. Each equals its spec predicate.
- `single_pass.rs` sums `state.slashings` with `safe_sum`. The theorem takes the sum as an input.
- `single_pass.rs` passes `base_reward` from the epoch cache, the participation flags, the leak
  flag and the participating increments from the progressive balances cache to
  `new_balance_after_rewards`. Each equals its spec value.
- `single_pass.rs` passes the validator epochs, the churn state, the finalized epoch and the
  chain constants to `registry_update`. `ConstantsMatch` states the constants.
- `single_pass.rs` builds the deposit views from the pubkey cache, for at most
  `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits, and applies the decisions. The spec reads the
  pubkeys again in each iteration, so a deposit for a validator added earlier in the same loop
  finds it. Lighthouse takes the same path: such a deposit counts as a new validator, consumes
  churn, and is applied to the added validator after the loop.
- `single_pass.rs` builds the consolidation table from the validators that consolidations
  reference, in index order, and maps each index to its position in the table. The moves read
  and write only these rows, so the table run equals the full-registry run of
  `process_pending_consolidations_eq`. The glue writes the new balances back.
- The loop in `single_pass.rs` calls `single_pass_step` once for each validator, in index order,
  and writes back each changed field.
- `weigh_justification_and_finalization.rs` reads the four bits, calls `weigh_justification`,
  reads the block roots and writes the checkpoints. `lhWeighJustificationAndFinalization`
  models it by hand.
- The progressive balances cache gives the previous and current target balances, and the total
  active balance cache gives the total. `lhJustificationAndFinalization` takes the spec values.
  `lh_cache_reads_mainnet` proves the cache reads equal to them when the caches are built from
  the state.
- `resets.rs` and `historical_summaries_update.rs` write the vector entry or push the summary
  that the checks of `tail_updates.rs` select. `LighthouseResets.lean` models these writes.
  `HistoricalSummary::new` hashes the block and state roots, as `hash_tree_root` in the Oracle.
- `rotate_participation_flags` moves the current participation to the previous one and writes
  one zero flag for each validator, as the spec does. It has no translated module.
- `Validator::from_deposit` computes the effective balance with the two functions of
  `deposit_balance.rs` in the `types` crate (`deposit_effective_balance_equiv`). Charon reaches
  them from `new_validator_effective_balance` in `pending_deposits.rs`. The rest of
  `Validator::from_deposit` copies the inputs and sets the four epochs to `FAR_FUTURE_EPOCH`.
  `BeaconState::add_validator_to_registry` pushes one entry onto each of the five lists.
  `lhApplyPendingDeposit` models both, and `lhApplyPendingDeposit_eq` shows that it equals
  `apply_pending_deposit` when the increment is not 0.
- `apply_pending_deposit` is a parameter of the reference. It verifies a BLS signature.
- The registry proof covers Electra and later. The pre-Electra path is unchanged and not proved.
- Lighthouse computes the slashings target epoch once per epoch. The spec computes it once per
  slashed validator. The theorems assume that `epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2` fits in a
  `u64`.
- The slashings proof covers Electra and later. The pre-Electra branch is translated but not
  proved.
- Lighthouse computes the hysteresis thresholds once per epoch. The spec computes them once per
  validator. The values are the same.
- The Gloas committee steps (`EpochProofs/Equiv/EpochCommittees.lean`) take the glue facts of
  `single_pass.rs` and `sync_committee_updates.rs` as hypotheses:
  - `SeedMixLink`: `BeaconState::get_seed_mix` reads the RANDAO mix that `get_seed` reads.
  - The index lists: the active validators of the epoch, the active and unslashed validators
    for the proposers, and for the PTC the beacon committees of each slot that the committee
    cache holds (see the committee cache proofs, eserilev/lighthouse-aeneas #28).
  - `EBLink`: `BeaconState::get_effective_balance` reads the registry.
  - `HashLink`: `Sha256Hash` computes SHA-256.
  - The shuffle takes at most `2^24` indices, and `usize` has 64 bits.
  - The sync committee pubkeys, the aggregate key and the milhouse PTC window shift stay glue.
- The cache build facts of `formalhouse_gloas_epoch`: the cache proofs (`consensus/types/proofs`)
  prove them for the build and update code, not on the epoch path of `per_epoch_processing`.
- `aeneas/discriminant-instance-name.patch` renames one generated instance so that the two
  `Generated.lean` files load together. It changes no definition.
- The reference matches pyspec.
