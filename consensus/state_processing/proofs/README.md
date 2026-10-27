# Epoch processing proofs

Lean 4 proofs that Lighthouse's epoch processing computes the same state as
[Etheorem](https://github.com/etheorem/etheorem), an independent Lean implementation of the
Ethereum consensus specs that is tested against the EF test vectors. The proofs cover Fulu and
Gloas, on the mainnet and minimal presets, on every reachable state, under the assumptions listed
in [What is trusted](#what-is-trusted). Charon and Aeneas translate the Lighthouse Rust to Lean,
so the proofs are about the code, not a description of it.

`NOTES.md` is the working log: every intermediate theorem, the per-line error site table and the
history of each step. Where the two differ, this file is current.

## What is proved

Take a chain that starts in Fulu and crosses the Gloas fork. At every epoch boundary of that run:

1. Lighthouse's epoch processing returns `Ok`.
2. Etheorem's `processEpoch` succeeds.
3. The two resulting states are equal.
4. Gloas only: the cache reads that Lighthouse's epoch processing makes (progressive balances,
   epoch cache, committee cache, pubkey cache) equal the values that the spec computes, given
   the cache assumptions below. The Fulu model reads the spec values directly, so
   for Fulu the cache reads are assumed, not proved.

The theorems are in `EpochProofs/FormalhouseFinal.lean`:

| Theorem | Fork | Presets | Caches |
|---|---|---|---|
| `formalhouse_gloas_epoch_final` | Gloas, after the fork from Fulu | `_mainnet`, `_minimal` | includes the cache reads |
| `formalhouse_fulu_epoch_final` | Fulu | `_mainnet`, `_minimal` | cache reads assumed |

The Fulu theorem, without its hypotheses:

```lean
theorem formalhouse_fulu_epoch_final ...
    (hin : FuluEpochInput o fo c init (absEState e)) (ha : FuluAssumptions o fo c init e) :
    ∃ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' ∧
      ∃ e', (EthCLSpecs.Fulu.processEpoch ...).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s'
```

Three terms in this statement need a precise meaning.

**Lighthouse's epoch processing** is `process_epoch_lh_order`, a Lean model of
`process_epoch_single_pass` and `altair.rs` in Lighthouse's own order. Each step of the model is
the Aeneas translation of the Rust function. Where the code reads or writes `milhouse` lists or
calls code that Aeneas does not translate, the model stands in for the Rust. The model is only
as faithful as those places, which [What is trusted](#what-is-trusted) lists. The Rust is the
`formalhouse` branch, which is Lighthouse `unstable` with the epoch logic moved into modules that
Aeneas accepts.

**Every epoch boundary** means every state that a run reaches, not every value of the
`BeaconState` type. `FuluEpochInput` and `GloasEpochInput` say that the state comes from a run
of the state transition, starting from a Fulu state with the genesis invariants (`FuluStartOk`).
`fulu_reachable_invariants` and `fulu_then_gloas_reachable_invariants` prove the invariants that
the epoch proof needs at each of these states, through every block, every epoch and the Gloas
fork. The runs are defined by this project's hand-written Lean transcription of the block
processing spec and the fork upgrades (`EpochProofs/Spec/`), not by Etheorem. So the
transcription is trusted for which states count as reachable, though not for the epoch function
itself.

**Etheorem** is the fork `eserilev/etheorem`, branch `formalhouse-pin`, at the commit in
`lakefile.toml`. It pins spec v1.7.0-alpha.11, plus the Fulu deposit change of alpha.9 and a
port to Lean v4.31.0. The transcription follows v1.7.0-beta.4. The Gloas epoch functions have
the same meaning in both versions. Only the list limits differ, and they are assumptions below.

**Equal** means `absEState`, the map from an Etheorem state to the transcription's state, sends
Etheorem's result to the model's. `absEState` covers every field of the state.

### Axiom audit

`EpochProofs/Axioms.lean` prints the axioms of 718 theorems, including all the final ones. Each
depends only on `propext`, `Classical.choice` and `Quot.sound`, so none rests on `sorry`
(`sorryAx`) or `native_decide` (`Lean.ofReduceBool`). CI rebuilds the proofs on every change and
fails if any audited theorem reports another axiom.

### Not covered

- Block processing in Lighthouse. Blocks appear only in the Lean transcription, to define the
  runs.
- Fork choice, networking and the store. The store's cache rebasing (`rebase_caches_on`) is
  outside the proofs; see [Findings](#findings).
- The Fulu cache reads.
- Heze, and the forks before Fulu. The pre-Electra paths of `single_pass.rs` are not checked.
- The genesis state. The Electra state before the Fulu fork is assumed to satisfy the start
  invariants (`FuluStartOk`), because no Electra spec is transcribed.

## What is trusted

The trusted base has three parts: Lighthouse code that the proofs do not check, assumptions
about the chain, and the tools and references. `NOTES.md` lists the same items by their Lean
names.

### Lighthouse code that is not checked

The final theorems are about `process_epoch_lh_order`, a Lean model of the epoch. Where Aeneas
translates the Rust, the model is proved equal to the translation. Where it does not, the model
stands in for the Rust, and the items below say what the model takes that Rust to do. They are
not hypotheses of the final theorems. They are checked by code review.

Paths below are relative to `consensus/`. `single_pass.rs` is
`state_processing/src/per_epoch_processing/single_pass.rs`.

**`milhouse` list access in `single_pass.rs`.** Aeneas cannot translate `milhouse`'s
tree-backed lists. So the code that loops over the validators is generic over traits, Aeneas
translates the loop, and the trait implementations over the real lists are trusted.

- `StateRows::apply_step` reads row `i`, runs `single_pass_step`, writes the changed fields
  back, changes no other row, and never fails. That includes the cache updates inside it
  (`write_back_row`, `record_effective_balance_update`).
- `StateDeposits` (`write_queue`, `validator_index`, `balance`, `set_balance`,
  `is_valid_signature`, `add_validator`, `update_effective_balance`): each method does the spec
  operation of the same name, and the pubkey lookup returns the first matching index.
- `StateBuilderPayments` reads and writes the builder pending payments and appends a builder
  pending withdrawal.
- `PtcWindowWrites` shifts the PTC window: drop the oldest epoch, append the new one, write it
  back.
- `StateEffectiveBalances::update_effective_balance` is the spec effective balance update for
  the validators that consolidations touch.
- `StateConsolidations` returns the pending consolidations and the validator fields, and sets
  balances and pops entries as the spec does.
- In `process_proposer_lookahead`, `Vector::new` accepts the new lookahead. Its length is
  proved; only that `Vector::new` accepts it is trusted.

**Builder onboarding at the Gloas fork (`state_processing/src/upgrade/gloas.rs`).** The same
reason, plus Rust's `HashMap` and `HashSet`, which are not translated.

- `StateOnboarding` (the pubkey cache, the signature cache, and the hash tables) answers each
  onboarding query as the spec would.
- `upgrade_to_fulu` and `upgrade_to_gloas` copy the state fields and write the onboarding
  result as the spec does.

**Standard library and data structures.** Code outside the crate is not translated, so the
proofs assume only the laws they need.

- In `get_validators_in_consolidations`, a `BTreeSet` iterates in increasing order, each member
  once.
- `HashTrieMap` (`types/src/state/pubkey_cache.rs`) behaves as a finite map.
- `BeaconState::update_pubkey_cache` inserts each new pubkey at the next index, in order. It is
  a `milhouse` iterator loop with an early return, which Aeneas does not accept.

**Calls and formulas in `single_pass.rs`.** These take `&BeaconState` or `&ChainSpec`, which
Aeneas turns into axioms, or use iterator adapters, which Aeneas rejects. So `single_pass.rs`
computes them and passes the values into the translated code.

- The epoch and slot arithmetic (the next epoch, the lookahead epoch and slots) and the
  per-validator pending deposit sum compute the formulas the model uses. That they never
  overflow is proved.
- `build_exit_cache` counts the exits per epoch. That the count never overflows is proved.
- `BeaconState::get_seed_mix` reads the RANDAO mix that the spec `get_seed` reads.
- The `EffectiveBalances` implementation for `BeaconState` reads the effective balances from
  the registry.
- The index lists passed to the proposer lookahead and sync committee selection are the spec's
  active validators (for the Gloas proposers, active and unslashed).
- The loop in `process_ptc_window` joins the committees of each slot from the committee cache.
- The superstruct accessors return the field of the state's fork variant. Each field exists
  from its fork on, so the accessor does not fail.
- `BeaconState::is_in_inactivity_leak` computes `previous_epoch - finalized_epoch` as the spec
  does.
- `safe_sum` in `SlashingsContext::new` is the spec sum of `slashings`.
- The values passed to the translated code equal their spec values: the `StepContext` fields,
  the `RowInputs` (base reward from the epoch cache, deposit, consolidation flag, max effective
  balance), and the `DepositView`s from `PendingDepositsContext::new`.
- Lighthouse computes the slashings target epoch and the hysteresis thresholds once per epoch,
  where the spec computes them per validator. The values are the same.
- `registry_constants`, `selection_constants` and the builder payment threshold (6/10) are the
  spec constants.

**Other epoch code.** These are the state-access wrappers around translated logic.

- `weigh_justification_and_finalization.rs` reads the justification bits and block roots and
  writes the checkpoints. The decisions in `justification.rs` are translated.
- `HistoricalSummary::new` (`types/src/state/historical_summary.rs`) hashes the roots as
  `hash_tree_root` does.
- `BeaconState::rotate_participation_flags` moves the current participation to the previous.
- `Validator::from_deposit` (`types/src/validator/validator.rs`) copies its inputs.
- `get_next_sync_committee` collects the pubkeys of the selected validators.
- `BeaconState::update_tree_hash_cache`, called from
  `state_processing/src/epoch_cache.rs`, succeeds.

**Caches.** Lighthouse builds and updates its caches in block processing, slot processing and
the store, outside the epoch code. `consensus/types/proofs` proves the build and update
functions, but not that every caller uses them correctly.

- Gloas: the theorem assumes that the progressive balances cache is coherent with the state at
  the epoch input, that the epoch cache total comes from a state of the same epoch, that the
  committee cache was built for the lookahead epoch, and that the pubkey cache comes from an
  earlier state of the run. `formalhouse_gloas_epoch_final_upkeep` replaces the first with an
  assumption that every write between a coherent state and the epoch runs its cache hook. An
  audit of the call sites supports this.
- The base rewards that `StateRows` reads from the epoch cache are assumed through
  `StateRows::apply_step`.
- Fulu: every cache read is assumed.

The two Lighthouse bugs under [Findings](#findings) are in exactly this part: caches copied
from or not updated for the right state.

**Crypto.** These are external crates in C and assembly.

- `Sha256Hash` (`swap_or_not_shuffle/src/shuffle_hash.rs`) computes SHA-256 and returns 32
  bytes.
- blst's deposit signature check and aggregate public key match the BLS functions of the
  Oracle below.

### Assumptions about the chain

These are hypotheses of the final theorems. When one fails, either the pyspec itself fails, or
the chain is far outside anything physically possible.

**Pyspec halts.** The pyspec raises without these, so no implementation can agree with it.

- Gloas: an unslashed validator is active two epochs ahead (F4).
- Gloas: at least `SLOTS_PER_EPOCH` validators are active two epochs ahead, or the PTC is empty
  (F12). That is 32 validators on mainnet and 8 on minimal.
- A validator is a sync committee candidate at the next epoch.
- Fulu: a validator is active at the next epoch and two epochs ahead.

**Physical limits.** Limits set by the ETH supply and by time.

- At most 139M ETH is active before each block and at each epoch (`SupplyBound`,
  `EpochSupply`).
- Inactivity scores stay below `2^22`, which rules out the `uint64` overflow of
  `effective_balance * inactivity_score` (F5). Scores grow by 4 per epoch of leak, so this takes
  about a million epochs. The same group bounds the effective balance sum, the funds, the exit
  fields and the validator count (`RowBounds`).
- `slot + 8192 < 2^64`, and the epoch runs at the last slot of an epoch.
- `historical_summaries` holds fewer than `2^24` entries, Lighthouse's list limit.
- At most `2^24` validators are active, the committee shuffle limit. Activation needs 32 ETH, so
  this follows from the supply, but no proof carries it.

**Reachable-state facts not yet carried to the epoch.** These hold on every real chain. The
invariant proofs cover most of the state, but not yet these fields:

- validator pubkeys are unique, and each passes `KeyValidate`;
- the SSZ vectors, `proposer_lookahead` and `ptc_window` have their lengths;
- at most `2^40` validators, and each effective balance is at most 2048 ETH;
- the states at which the caches were built agree with the epoch input on the activity and the
  pubkeys they read.

**Hash outputs.** These are facts about hash values. They hold with overwhelming probability,
and no proof can establish them.

- Each Etheorem balance-weighted selection returns all its items within `10^7` passes (F3).
- Each spec selection ends within `2^64` passes.
- The Electra proposer loop ends before its last pass.

**Start state.** The Electra state before the Fulu fork satisfies the genesis invariants
(`FuluStartOk`). A genesis state does, but no Electra spec is transcribed, so the step from
genesis to the Fulu fork is not proved.

### Tools and references

- The Lean kernel.
- Charon and Aeneas, at the revisions in `.github/workflows/proofs.yml`, and the Aeneas Lean
  library. Its four `sorry` warnings are not reachable from these theorems. Aeneas makes no
  end-to-end soundness claim.
- `aeneas/discriminant-instance-name.patch`, which renames one generated instance and changes no
  definition.
- Etheorem at the pin in `lakefile.toml`. It pins spec v1.7.0-alpha.11, whose lists have limits
  that beta.4 removed. The theorems assume room under them: in `builder_pending_withdrawals`
  (F6), in the registry (`validators + 16 <= 2^40`, F10), and for Fulu in
  `historical_summaries`.
- The Oracle (`Spec/Oracle.lean`): BLS, SHA-256 and `hash_tree_root` are parameters, not
  axioms. The theorems hold for every Oracle that agrees with Etheorem.
- The hand-written transcription of block processing and the fork upgrades in
  `EpochProofs/Spec/`. It defines which states are reachable. It is reviewed against the pyspec,
  not run against the EF vectors.

## How the proof is built

```
Lighthouse Rust (per_epoch_processing/*.rs, refactored for Aeneas)
   |  Charon, Aeneas
   v
EpochProofs/Generated.lean
   |  EpochProofs/Equiv/        each translated function equals its model step
   v
process_epoch_lh_order          the steps in Lighthouse's order, joined by the
   |                            Rust contracts and glue facts (EpochProofs/Trusted/)
   |  EpochProofs/Sanity/       Lighthouse's order and single pass equal the spec's
   v                            order and separate passes, on reachable states
EpochProofs/Spec/               a line-by-line transcription of the pyspec
   |  EpochProofs/Etheorem/     the transcription's epoch equals Etheorem's
   v
Etheorem processEpoch
```

The transcription in `EpochProofs/Spec/` is an intermediate step for the epoch: the final
theorems state the result against Etheorem directly, so its epoch functions are not trusted. Its
block functions are, because they define the runs.

### The Rust side

`single_pass.rs` mixes the epoch logic with `milhouse` list access, which Aeneas cannot
translate. The logic is moved into modules that Aeneas accepts: plain `u64` arguments, no
iterator adapters, no early return inside a loop. The loops that touch the state are generic
over traits (`RegistryRows`, `DepositWrites` and others), so Aeneas translates the loop and the
proofs reason about the trait through its contract.

| Step, in Lighthouse's order | Translated Rust | Trusted |
|---|---|---|
| Justification and finalization | `justification.rs` | the reads and checkpoint writes (glue) |
| Inactivity, rewards, registry, slashings, deposit top-ups, effective balances | `single_pass_step.rs`, `registry_rows.rs` and the step modules | `RowsContract` |
| Pending deposits | `pending_deposits.rs`, `deposit_balance.rs`, `deposit_writes.rs` | `DepositWritesContract` |
| Pending consolidations | `pending_consolidations.rs`, `list_writes.rs` | `ConsolidationStateContract`, `BTreeSetIter`, `EffectiveBalanceContract` |
| Builder pending payments (Gloas) | `builder_pending_payments.rs`, `list_writes.rs` | `PaymentWritesContract` |
| Proposer lookahead | `epoch_committees.rs`, `balance_weighted_selection.rs`, `compute_shuffled_index_with.rs` | `SeedMixLink`, `EBLink`, the index lists |
| PTC window (Gloas) | as the lookahead, and `list_writes.rs` | `WindowContract`, `CommitteesFromCache` |
| Next sync committee | as the lookahead | the pubkeys, the aggregate key |
| Eth1, slashings and RANDAO resets, historical summaries | `tail_updates.rs` | the vector writes |
| Participation flag rotation | none | one `types` call (glue) |
| Fork upgrades | `epoch_committees.rs`, `upgrade/builder_onboarding.rs` | the field copies, `OnboardingContract` |

Fulu runs through the same translated functions as Gloas, with the Fulu constants. It has no
builder payments and no PTC window.

### Where Lighthouse differs from the spec

Lighthouse does not run the spec line by line. The proofs show that each difference gives the
same result on reachable states:

- **One pass, not four.** The spec runs inactivity, rewards, registry and slashings as four
  passes over the validators. Lighthouse runs all four for one validator, then the next
  (`separate_passes_eq_single_pass`).
- **Step order.** Lighthouse runs the proposer lookahead and PTC window before the eth1,
  slashings and RANDAO resets. The randao reset writes the mix of the next epoch, and the
  committee steps read the mix of the current one (`specOrder_lhOrder`).
- **Rewards.** The spec applies four reward and penalty deltas, saturating after each.
  Lighthouse adds the rewards and subtracts the penalties once. The two agree when the balance
  covers the flag penalties, which holds on reachable states. `rewards_saturation_example` gives
  an input where they differ.
- **Registry update.** The spec uses `if`/`elif`/`elif`. Lighthouse runs three independent
  steps. They agree when the finalized epoch is not `FAR_FUTURE_EPOCH`.
- **Pending deposits.** Lighthouse decides the deposits before the registry update and predicts
  each validator's ejection (`predictedStatus_eq_post_registry`).
- **Eth1 reset.** Lighthouse tests `(slot + 1) % 2048 == 0`. The spec tests
  `next_epoch % 64 == 0`. They agree at the last slot of an epoch.

## Findings

The proofs found these differences. Each is described in more detail in `NOTES.md`.

In Lighthouse, outside the code these proofs cover:

- `StateCache::rebase_on_finalized` checks only the slot, not ancestry, before it copies the
  finalized state's committee caches. Between `migrate_database` and `prune_hot_db`, a state of
  an abandoned fork can get another chain's committee caches.
- In Gloas, `apply_parent_execution_payload` reads the pubkey cache for the parent's withdrawal
  and consolidation requests without calling `update_pubkey_cache`. The Electra and Fulu path
  calls it. A request for a validator missing from the cache is skipped.
- `initialize_progressive_balances_cache` keeps any cache that `is_initialized`, whatever epoch
  it was built for. The proof needs a cache of the current epoch, so the `formalhouse` branch
  rebuilds a cache of another epoch (commit `9dcec02a0`).

In the spec and Etheorem:

- Gloas halts with fewer than `SLOTS_PER_EPOCH` validators active two epochs ahead
  (`process_ptc_window_few_active_error`), and when all of them are slashed (F4).
- Etheorem kept the eth1 bridge deposit path in Fulu, which the spec removed in alpha.9 (F2).
  Fixed on the pin and proposed upstream in
  [etheorem#144](https://github.com/etheorem/etheorem/pull/144).
- Etheorem's balance-weighted selection gives up after `10^7` passes (F3), and several Etheorem
  functions wrap or return 0 where the pyspec raises. None of these is reachable on a real chain.

## Error sites

`single_pass.rs` has 171 `?` sites. The theorem holds only if none of them returns an error
where the spec succeeds.

| Status | Sites |
|---|---|
| Proved: a translated function whose errors are spec errors, at a step the spec completes | 17 |
| Inside a trusted Rust contract | 53 |
| Fails only if a cache is not built (cache build facts) | 13 |
| Bound proved, Rust formula trusted (glue L1 to L7) | 13 |
| Named fact with no proved bound (glue N1 to N5) | 15 |
| Pre-Electra path, not reached | 60 |

`NOTES.md` lists every site with its line and reason.

## Directory layout

| Path | Contents |
|---|---|
| `EpochProofs/Generated.lean` | The Aeneas output. Do not edit. |
| `EpochProofs/Equiv/` | Each translated function equals its model. |
| `EpochProofs/Trusted/` | The Rust contracts and glue facts. |
| `EpochProofs/Spec/` | The transcription of the pyspec (v1.7.0-beta.4). |
| `EpochProofs/Sanity/` | Facts about the transcription, the reachable-state invariants and the order proofs. |
| `EpochProofs/Etheorem/` | The transcription's epoch equals Etheorem's. |
| `EpochProofs/CacheBridge/` | The cache reads equal the spec values. |
| `EpochProofs/FormalhouseFinal.lean` | The final theorems. |
| `EpochProofs/Axioms.lean` | The axiom audit. |

## Building

`setup.sh` fetches Etheorem's native dependencies (blst, c-kzg-4844 and ISA-L, which needs
`nasm`) and applies the Aeneas patch.

```sh
cd consensus/state_processing/proofs
lake exe cache get
./setup.sh
lake build
lake lean EpochProofs/Axioms.lean
```

Use `lake lean`, not `lake env lean`. Etheorem's modules are precompiled, and only `lake lean`
loads their native code.

## Regenerating `Generated.lean`

After a change to a translated module, run Charon and Aeneas at the revisions in
`.github/workflows/proofs.yml`. `validator_client/slashing_protection/proofs/README.md` gives
the install steps.

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
  --start-from 'state_processing::per_epoch_processing::registry_rows' \
  --start-from 'state_processing::per_epoch_processing::deposit_writes' \
  --start-from 'state_processing::per_epoch_processing::list_writes' \
  --start-from 'state_processing::upgrade::builder_onboarding' \
  --include safe_arith \
  --include types::validator::deposit_balance \
  --include types::state::balance_weighted_selection \
  --include swap_or_not_shuffle::shuffle_hash \
  --include swap_or_not_shuffle::compute_shuffled_index_with \
  --include types::builder \
  --include alloy_primitives::bits \
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

Keep the translated modules in the shape Aeneas accepts:

- No `?` or early return inside a `for` loop. Aeneas drops the body.
- No iterator adapters (`take`, `filter`, `map`, `chain`).
- Take plain `u64` values, not `&Validator` or `&ChainSpec`. Otherwise `Epoch`, `Slot`,
  `PublicKey` and `Option::map` become axioms.
- Split large branching functions. Aeneas copies the rest of the body into each branch, and the
  output grows exponentially.
