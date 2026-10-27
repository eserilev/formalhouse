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
   the cache provenance assumptions below. The Fulu model reads the spec values directly, so
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
the Aeneas translation of the Rust function. The steps are joined by the Rust contracts and glue
assumptions listed below, wherever the code reads or writes `milhouse` lists or calls code that
Aeneas does not translate. The model is only as faithful as those assumptions. The Rust is the
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
- Heze, and the forks before Fulu. The pre-Electra paths of `single_pass.rs` are out of scope.
- The genesis state. The Electra state before the Fulu fork is assumed to satisfy the start
  invariants (`FuluStartOk`), because no Electra spec is transcribed.

## What is trusted

The final theorems take every assumption as a named hypothesis or a named fact. None of the items
below is proved; a reader who accepts them accepts the result. `GloasAssumptions` and
`FuluAssumptions` collect the hypotheses. Each item says how it is justified.

| Group | Count | What it says | Justified by | Size |
|---|---|---|---|---|
| Rust contracts | 9 | What a trait implementation over `milhouse` lists does | code review | covers 53 of the 171 error sites in `single_pass.rs` |
| Glue assumptions | 26 | A Rust expression or call that Aeneas does not translate equals its model | code review | mostly one call or formula each |
| Cache provenance | 4 | Each cache was built from a state of this run | an audit of every cache write | 13 error sites |
| Spec preconditions | 4 | Conditions without which the pyspec itself raises | the pyspec | not Lighthouse assumptions |
| Supply and time bounds | 5 | ETH supply, `u64` slots, list sizes | physical limits | |
| Hash-output assumptions | 3 | Hash-based selection loops end | overwhelming probability | |
| Etheorem list limits | 2 | Room under Etheorem's alpha.11 list limits | far above real chain sizes | |
| Oracle | 3 | BLS, SHA-256, `hash_tree_root` | parameters, not axioms | |
| Start state | 1 | `FuluStartOk` | holds at genesis, not proved | |
| Tools and references | 6 | Lean, Charon, Aeneas, Etheorem, the transcription | external | |

### Rust contracts (9)

The translated code is generic over traits, so Aeneas checks the loop structure, the order of
the calls and the error handling. Each contract states what the `milhouse` implementation of one
trait does. They are in `EpochProofs/Trusted/`.

- `RowsContract` (`RegistryRows.lean`): `StateRows::apply_step` reads row `i`, runs
  `single_pass_step`, writes the changed fields back and changes no other row.
- `DepositWritesContract` (`EpochTail.lean`): the deposit queue write, the pubkey lookup,
  `add_validator` and the effective balance update of a new validator.
- `PaymentWritesContract` (`EpochTail.lean`): the builder payments read and write, and the
  withdrawal append.
- `WindowContract` (`EpochTail.lean`): the PTC window shift.
- `EffectiveBalanceContract` (`EpochTail.lean`): the effective balance updates after the
  consolidations.
- `ConsolidationStateContract` (`Consolidations.lean`): the reads and writes of the
  consolidation step.
- `BTreeSetIter` (`Consolidations.lean`): a `BTreeSet` iterates in increasing order, each member
  once.
- `OnboardingContract` (`Onboarding.lean`): the caches and hash tables of the builder onboarding
  at the Gloas fork.
- `IndexMapLaws`: `HashTrieMap` behaves as a finite map, and `update_pubkey_cache` inserts the
  new pubkeys in order.

### Glue assumptions (26)

- `Trusted/EpochGlue.lean` (12): formulas in `single_pass.rs`. For L1 to L7 the bound that rules
  out an error is proved and only the formula is trusted. N1 to N5 have no proved bound, so they
  are the weakest items here:
  - N1 `ShuffleSize`: at most `2^24` active validators. Activation needs 32 ETH, so the active
    set stays far below this, but no invariant proves it.
  - N2 `ForkFields`: each superstruct accessor returns the field of the state variant, because
    the field exists from that fork on.
  - N3 `TreeHashOk`: `update_tree_hash_cache` succeeds when the latest block header has no state
    root yet.
  - N4 `FinalityDelayLink`: `is_in_inactivity_leak` computes `previous_epoch - finalized_epoch`
    as the spec does.
  - N5 `SlashingsSumLink`: `safe_sum` of `state.slashings` is the spec sum.
- `SeedMixLink`: `get_seed_mix` reads the RANDAO mix that `get_seed` reads.
- `EBLink`: `get_effective_balance` reads the registry.
- `HashLink`: `Sha256Hash` computes SHA-256.
- The index lists of the committee steps: the active validators, and the active unslashed
  validators for the proposers.
- `CommitteesFromCache`: the loop in `process_ptc_window` that joins the committees of each slot.
- The chain constants: `ConstantsMatch`, `SelectionConstantsMatch`, and the payment threshold
  6/10.
- The inputs that `single_pass.rs` passes to the translated functions: the inactivity flags, the
  rewards inputs, the registry inputs, the slashings sum and the deposit views.
- Justification: `weigh_justification_and_finalization.rs` reads the bits and roots and writes
  the checkpoints.
- The reset and historical summary writes. `HistoricalSummary::new` hashes the roots as
  `hash_tree_root` does.
- `rotate_participation_flags` moves the current participation to the previous one.
- The sync committee pubkeys. The aggregate key comes from the BLS Oracle.
- `Validator::from_deposit` copies its inputs, and `add_validator_to_registry` pushes one entry
  onto each of the five lists.
- The field copies of the fork upgrades, and the write of the builder onboarding result.
- Lighthouse computes the slashings target epoch and the hysteresis thresholds once per epoch,
  where the spec computes them once per validator. The values are the same.

### Cache provenance (4)

`consensus/types/proofs` proves the cache build and update code. The Gloas epoch proof assumes
that each cache came from a state of this run:

- The progressive balances cache is `Coherent` at a state of the epoch, and Lighthouse runs the
  update hooks for every write between that state and the epoch input (`CacheUpkeep`,
  `Trusted/CacheUpkeep.lean`).
- The epoch cache total and base rewards come from a state of the same epoch.
- `CommitteeCacheBuilt` holds for the lookahead epoch.
- The pubkey cache is `Coherent` and comes from an earlier state of this run.

### Spec preconditions (4)

The pyspec raises when one of these fails, so no implementation can agree with it there. They
are conditions on the chain, not on Lighthouse.

- Gloas: an unslashed validator is active at `current + 2` (finding F4 in `NOTES.md`).
- Gloas: at least `SLOTS_PER_EPOCH` validators are active at `current + 2` (F12). The PTC is
  empty otherwise. This is 32 validators on mainnet and 8 on minimal.
- A sync committee candidate exists at the next epoch.
- Fulu: a validator is active at the next epoch and at `current + 2`.

### Supply and time bounds (5)

- `RowBounds`: bounds on inactivity scores, the total effective balance, the funds, the exit
  fields and the validator count. Inactivity scores stay below `2^22`, which rules out the
  `uint64` overflow of `effective_balance * inactivity_score` (F5). Scores grow by 4 per epoch
  of inactivity leak, so the bound fails only after about a million epochs of leak.
- `slot + 8192 < 2^64`.
- `SupplyBound`: at most 139M ETH is active before each block.
- `EpochSupply`: the same kind of bound at each epoch input.
- `HistRoom`: `historical_summaries` is below Lighthouse's list limit of `2^24`.

### Hash-output assumptions (3)

These are statements about hash outputs. They hold with overwhelming probability, and no proof
can establish them.

- F3: each Etheorem balance-weighted selection returns all its items within `10^7` passes.
- `SelFin`: each spec selection ends within `2^64` passes.
- `ProposerFin`: the Electra proposer loop ends before its last pass.

### Etheorem list limits (2)

Etheorem pins spec v1.7.0-alpha.11, where some `BeaconState` lists have limits that beta.4
removed. Etheorem drops items past a limit, where the pyspec has no limit.

- F6: room in `builder_pending_withdrawals`.
- F10: `validators + 16 <= 2^40`.

### Oracle (3)

`Spec/Oracle.lean` takes these functions as parameters, not axioms. The theorems hold for every
value of the parameters that agrees with Etheorem.

- BLS: signature verification in `apply_pending_deposit`, and the aggregate key.
- SHA-256.
- `hash_tree_root` of the historical summary roots.

### Start state (1)

- `FuluStartOk`: the Electra state before `upgrade_to_fulu` satisfies the start invariants. A
  genesis state does, but no Electra spec is transcribed, so this is not proved.

### Tools and references (6)

- The Lean kernel.
- Charon and Aeneas, at the revisions in `.github/workflows/proofs.yml`, and the Aeneas Lean
  library. Its four `sorry` warnings are not reachable from these theorems.
- `aeneas/discriminant-instance-name.patch`, which renames one generated instance and changes no
  definition.
- Etheorem at the commit in `lakefile.toml`: branch `formalhouse-pin` of `eserilev/etheorem`.
  It is upstream Etheorem plus a port to Lean v4.31.0 and the removal of the eth1 bridge
  deposit path from Fulu, which consensus-specs v1.7.0-alpha.9 removed
  ([etheorem#144](https://github.com/etheorem/etheorem/pull/144)).
- The Lean transcription of the spec in `EpochProofs/Spec/`, for the parts that Etheorem does
  not replace: block processing, which defines the runs, and the fork upgrades. It is checked
  by review against the pyspec, not by the EF vectors.
- The pre-Electra paths of `single_pass.rs` are out of scope.

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
