# Epoch processing proofs

Lean 4 proofs that Lighthouse's epoch processing computes the same state as
[Etheorem](https://github.com/etheorem/etheorem), an independent Lean implementation of the
Ethereum consensus specs that is tested against the EF test vectors. The proofs cover Fulu and
Gloas, on the mainnet and minimal presets, on every reachable state, under the assumptions listed
in [What is trusted](#what-is-trusted). Charon and Aeneas translate the Lighthouse Rust to Lean,
and the proofs are about that translation wherever Aeneas can reach.

`NOTES.md` is the working log: every intermediate theorem, the per-line error site table and the
history of each step. Where the two differ, this file is current.

## What is proved

Take a chain that starts in Fulu and crosses the Gloas fork. At every epoch boundary of that run:

1. Lighthouse's epoch processing returns `Ok`.
2. Etheorem's `processEpoch` succeeds.
3. The two resulting states are equal.
4. Gloas only: the cache reads that Lighthouse's epoch processing makes (progressive balances,
   epoch cache, committee cache, pubkey cache) equal the values that the spec computes, given
   the [cache assumptions](#lighthouse-code-that-is-not-checked) below. The Fulu model reads
   the spec values directly, so for Fulu the cache reads are assumed, not proved.

The theorems are in `EpochProofs/FormalhouseFinal.lean`:

| Theorem | Fork | Presets | Caches |
|---|---|---|---|
| `formalhouse_gloas_epoch_final` | Gloas, after the fork from Fulu | `_mainnet`, `_minimal` | includes the cache reads |
| `formalhouse_fulu_epoch_final` | Fulu | `_mainnet`, `_minimal` | cache reads assumed |

The Gloas theorem, without its hypotheses and cache conclusions:

```lean
theorem formalhouse_gloas_epoch_final ...
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e) ... :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      (∃ e', (EthCLSpecs.Gloas.processEpoch ...).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s') ∧ ...
```

Four terms in this statement need a precise meaning.

**Lighthouse's epoch processing** is `process_epoch_lh_order`, a Lean model of
`process_epoch_single_pass` and `altair.rs` in Lighthouse's own order. Each step of the model is
the Aeneas translation of the Rust function, except where Aeneas cannot reach (see
[Lighthouse code that is not checked](#lighthouse-code-that-is-not-checked)). The Rust is the
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

Aeneas translates most of the epoch logic: the arithmetic, the decisions, the loops and the
error handling. It cannot translate three kinds of code: reads and writes of the state's
`milhouse` lists, functions that take a whole `&BeaconState` or `&ChainSpec`, and code in other
crates. In those places the Lean model stands in for the Rust, and the proofs say nothing about
whether the Rust matches it. This code is checked only by review.

Most of it is mechanical. Three parts are not, because a mistake in them would make Lighthouse
compute a wrong state without any error.

**1. The state list reads and writes in `single_pass.rs`.** The per-validator loop and the
writes after it are generic over small traits (`RegistryRows`, `DepositWrites` and others), so
Aeneas translates the loop and the order of the calls. The implementations of these traits over
the real `BeaconState` lists are trusted. The main one is `StateRows::apply_step`: it must read
validator `i`, run the translated `single_pass_step`, write back exactly the fields that
changed, touch no other validator, and never fail. The others write the deposits, the
consolidation balances, the builder payments and the PTC window. 53 of the 171 `?` sites in
`single_pass.rs` are inside these implementations or pass on their errors.

**2. The values passed into the translated code.** `single_pass.rs` computes some inputs itself,
because they need the whole state or the `ChainSpec`, and passes them to the translated
functions: the participation flags and rewards inputs (`StepContext`, `RowInputs`), the
pending deposit views (`DepositView`), the churn and selection constants, and the builder
payment threshold. It also computes the slashings target epoch and the hysteresis thresholds
once per epoch, where the spec computes them for each validator. The proofs assume each of these
equals its spec value.

**3. The caches.** Lighthouse reads the progressive balances, epoch, committee and pubkey caches
during the epoch, but builds and updates them elsewhere: in block processing, slot processing
and the store. `consensus/types/proofs` proves the build and update functions, but not that
every caller uses them. So the Gloas theorem assumes that the progressive balances cache is
coherent with the epoch state, that the epoch cache was built at a state of the same epoch, and
that the pubkey cache was built at an earlier state of the run. The Fulu theorem assumes every
cache read. All three Lighthouse issues in [Findings](#findings) are cache bugs: a cache copied
from another fork, a cache read before it is updated, and a cache kept from the wrong epoch.

Five more glue facts have no proof (N1 to N5 in `Trusted/EpochGlue.lean`): the superstruct
accessors return `Ok` on a state of the right fork, `update_tree_hash_cache` succeeds,
`is_in_inactivity_leak` and the `slashings` sum compute what the spec computes, and the active
set fits the committee shuffle. If one of these is false, Lighthouse returns an error rather
than a wrong state.

<details>
<summary>The full list</summary>

Paths are relative to `consensus/`. `single_pass.rs` is
`state_processing/src/per_epoch_processing/single_pass.rs`.

**State list access (`single_pass.rs`).** `milhouse` lists are not translated.

- `StateRows::apply_step`: as above, including the cache updates inside it (`write_back_row`,
  `record_effective_balance_update`).
- `StateDeposits`: the deposit queue write, the pubkey lookup (the first matching index), the
  balance read and write, the signature check, `add_validator` (which pushes one entry onto
  each of the five validator lists), and the effective balance update of a new validator.
- `StateBuilderPayments`: read and write the builder pending payments, append a builder pending
  withdrawal.
- `PtcWindowWrites`: drop the oldest PTC epoch, append the new one, write back.
- `StateEffectiveBalances::update_effective_balance`: the effective balance update of the
  validators that consolidations touch.
- `StateConsolidations`: read the pending consolidations and validator fields, set balances,
  pop entries.
- `Vector::new` in `process_proposer_lookahead` accepts the new lookahead. Its length is proved.

**Values computed outside the translated code.** These need the whole `BeaconState` or
`ChainSpec`, which Aeneas turns into axioms.

- `StepContext`, `RowInputs` and `DepositView`, including the base reward read from the epoch
  cache.
- The slashings target epoch and the hysteresis thresholds.
- `registry_constants`, `selection_constants` and the builder payment threshold (6/10).
- Epoch and slot arithmetic, the per-validator deposit sum and the exit count per epoch: the
  formulas are trusted, and that they never overflow is proved.
- `BeaconState::get_seed_mix` reads the RANDAO mix that the spec `get_seed` reads.
- The effective balances, and the lists of active (for Gloas proposers, active and unslashed)
  validators passed to the proposer and sync committee selection.
- The active indices and seed passed to `shuffling` when the committee cache is built.
- The loop in `process_ptc_window` that joins each slot's committees from the committee cache.

**Caches.** As above. `formalhouse_gloas_epoch_final_upkeep` replaces the progressive balances
assumption with a weaker one: the cache is coherent at some state of the epoch, and every write
after it runs its cache hook (`Trusted/CacheUpkeep.lean`). An audit of the call sites supports
this.

**Wrappers around translated logic.**

- `weigh_justification_and_finalization.rs` reads the justification bits and block roots and
  writes the checkpoints. The decisions are translated (`justification.rs`).
- The eth1, slashings and RANDAO reset writes, and the historical summary push.
  `HistoricalSummary::new` hashes the roots as `hash_tree_root` does.
- `BeaconState::rotate_participation_flags`.
- `Validator::from_deposit` copies its inputs.
- `get_next_sync_committee` collects the selected validators' pubkeys.

**Fork upgrades (`state_processing/src/upgrade/`).** `upgrade_to_fulu` and `upgrade_to_gloas`
copy the state fields. At the Gloas fork, `StateOnboarding` answers each builder onboarding
query as the spec would, using the pubkey cache, the signature cache, a `HashMap` and a
`HashSet`, and the result is written to the state.

**The five glue facts with no proof (`Trusted/EpochGlue.lean`).**

- N1: at most `2^24` validators are active, the committee shuffle limit.
- N2: each superstruct accessor returns the field of the state's fork variant.
- N3: `update_tree_hash_cache` succeeds when the latest block header has no state root yet.
- N4: `is_in_inactivity_leak` computes `previous_epoch - finalized_epoch` as the spec does. The
  spec subtraction is proved total.
- N5: `safe_sum` over `slashings` equals the spec sum, which is proved total.

**Other crates.**

- `BTreeSet` iterates in increasing order (`get_validators_in_consolidations`).
- `HashTrieMap` behaves as a finite map, and `BeaconState::update_pubkey_cache` inserts new
  pubkeys in order.
- `Sha256Hash` computes SHA-256. blst's signature check and aggregate key are BLS.

</details>

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
