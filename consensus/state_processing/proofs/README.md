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
4. Gloas only: the cache reads that Lighthouse's epoch processing makes from the progressive
   balances cache, the epoch cache and the pubkey cache equal the values that the spec computes,
   given the [cache assumptions](#lighthouse-code-that-is-not-checked) below. The committee
   cache read of the PTC window step is a separate theorem, `ptc_committees_from_cache`, because
   it does not depend on the epoch input. The Fulu model reads the spec values directly, so for
   Fulu the cache reads are assumed, not proved.

The statements and their proofs are in `EpochProofs/Headline.lean`, and the mainnet and
minimal versions (`_mainnet`, `_minimal`) in `HeadlinePresets.lean`. `Headline.lean` also defines
the conclusions. Every hypothesis is a bundle defined in `EpochProofs/Assumptions.lean`, with a
docstring on each field. The bundles that the Etheorem step proofs read (the preset, Etheorem and
oracle bundles) are in `EpochProofs/Assumptions/Etheorem.lean`, because those proofs must not
import the Aeneas code that the other bundles need. Reading a claim needs these three files.

The names say what each theorem is about and what it proves. `lighthouse_model_*` is about the
Lean model of Lighthouse's epoch processing (`process_epoch_lighthouse`), and
`lighthouse_rust_*` about the composed Aeneas translation of the Rust. `*_eq_etheorem` proves
the result equal to Etheorem's, and `*_agrees_pyspec` the same result as the hand-written pyspec
transcription, or both fail. Every hypothesis bundle and conclusion of the headline theorems
starts with `Gloas` or `Fulu`. Each name is the name of the definition itself, used in every
proof. The fork-shared names of the Etheorem bridge have one copy per fork namespace
(`Etheorem.toSpecState`, `Etheorem.Fulu.toSpecState`), as `ForkReplay` writes them. The "pyspec" of `_agrees_pyspec` is this project's hand-written Lean transcription
of it (`EpochProofs/Spec/`), not the Python itself.

| Theorem | States | Assumes |
|---|---|---|
| `lighthouse_model_gloas_epoch_eq_etheorem` | `GloasLighthouseModelEqualsEtheorem`, and the cache reads give the spec values (`GloasCacheReadsCorrect`) | `GloasEpochRun`, `GloasChainAssumptions`, `GloasEtheoremDivergenceAssumptions`, `GloasOracleMatchesEtheorem`, `GloasCacheProvenance` |
| `lighthouse_rust_gloas_epoch_eq_etheorem` | `GloasRustEqualsEtheorem`: the same for the composed Rust | as above, and `GloasRustGlueFacts` (the glue) |
| `lighthouse_model_fulu_epoch_eq_etheorem` | `FuluLighthouseModelEqualsEtheorem`; the Fulu cache reads are assumed | `FuluEpochRun`, `FuluChainAssumptions`, `FuluEtheoremBridgeConditions`, `FuluOracleMatchesEtheorem` |
| `lighthouse_rust_fulu_epoch_eq_etheorem` | `FuluRustEqualsEtheorem` | as above, and `FuluRustGlueFacts` |
| `lighthouse_model_gloas_epoch_agrees_pyspec` | `SameResultOrBothFail`: the model and the transcription's `process_epoch` give the same state, or both fail | `GloasEpochRun`, `HistoricalSummariesBelowLimit` |
| `lighthouse_model_fulu_epoch_agrees_pyspec` | the same for Fulu | `FuluEpochRun`, `HistoricalSummariesBelowLimit` |

`lighthouse_model_gloas_epoch_eq_etheorem_upkeep` and
`lighthouse_model_gloas_epoch_eq_etheorem_at_input` differ only in the cache facts
(`GloasCacheProvenanceUpkeep`, `GloasCacheProvenanceAtInput`). The `_at_input` theorem carries the
proof, and the other two carry their cache facts to the epoch input and call it.
`ptc_committees_from_cache` is the committee cache fact of the PTC window step, a separate theorem
because it does not depend on the epoch input.

The headline Gloas statement:

```lean
theorem lighthouse_model_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e)
```

`e` is an Etheorem Gloas state (`EtheoremState`), and `toSpecState e` the same state in the
transcription's types. The run starts from the Fulu state `fuluStart`; `oracle` is BLS, SHA-256 and
`hash_tree_root`; `fuluOracle`, `blockConfig` and `upgradeConfig` parametrize the Fulu blocks and
the Gloas fork upgrade. `Spec.P` is the preset, a parameter (`Spec.PresetCfg`). `hpreset` says that
it has the values of Etheorem's preset, and `hhistLimit` that Lighthouse's `2^24` limit on
`historical_summaries` is at most Etheorem's. Both hold on mainnet and minimal, where
`HeadlinePresets.lean` proves them (`presetMatchesEtheorem_mainnet`, `by decide`). The four cache
arguments are the progressive balances cache (`LhCache`, the `Inner` of
`ProgressiveBalancesCache`), the epoch cache's total active balance, and the pubkey cache's map
operations (`pubkeyMapOps`) and map (`pubkeyMap`).

`GloasLighthouseModelEqualsEtheorem oracle e` unfolds to:

```lean
∃ s', Spec.process_epoch_lighthouse oracle (toSpecState e) = .ok s' ∧
  ∃ e', (EthCLSpecs.Gloas.processEpoch ...).run (pureState e) = .ok ((), pureState e') ∧
    toSpecState e' = s'
```

The hypothesis bundles follow the groups of [What is trusted](#what-is-trusted): the run with
its supply bounds, the chain assumptions, what Etheorem needs because it differs from the pyspec
(its alpha.11 list limits F6 and F10), the oracle, the cache provenance and, for `_rust`,
the glue.

The proofs take the bundles as they are: there is no second set of hypothesis structures. Two
facts are proved from the run instead of assumed: unique pubkeys, and the first two parts of
`AtEpochBoundary` (the last slot of an epoch, the next slot in `u64`).

The `_agrees_pyspec` theorems compare with the hand-written transcription of the pyspec, not with
Etheorem. The transcription is reviewed against the pyspec but not run against the EF vectors,
so the Etheorem theorems remain the externally checked ones. In exchange, the `_agrees_pyspec`
theorems do not assume that the epoch succeeds: see
[Assumptions about the chain](#assumptions-about-the-chain) for what they drop.

Four terms in this statement need a precise meaning.

**Lighthouse's epoch processing** is `process_epoch_lighthouse` (`process_epoch_lighthouse`; Fulu:
`process_epoch_lighthouse_fulu`), a Lean model of `process_epoch_single_pass` and `altair.rs` in
Lighthouse's own order. For each step, a separate theorem proves the model step equal to the Aeneas
translation of the Rust, except where Aeneas cannot reach (see [Lighthouse code that is not
checked](#lighthouse-code-that-is-not-checked)). `EpochProofs/Compose/` writes the same epoch as one
Lean function, `Compose.epoch` (Fulu: `Compose.epochFulu`): the calls of the translated functions of
`Generated.lean`, in Lighthouse's order, with the untranslated code between them as parameters (the
glue). `epoch_spec` and `epochFulu_spec` prove that it returns `Ok` with the model's state whenever
the model returns `ok`, given the trusted facts about the glue (`EpochLinks`, in the bundle
`GloasRustGlueFacts`). So Lean checks that each model step is the one its step theorem covers. What
the glue stands for is still checked only by review, and so is the deposit plan: the composition
takes the plan that `PendingDepositsContext::new` hands to `apply_deposit_writes` as glue, and the
translated `process_pending_deposits` in it is linked to the model's decisions by reading
(`process_pending_deposits_equiv`). The cache builds at the start of the epoch are not in the
composition: they write no field of the state and can only make Lighthouse return an error. The step
table in [How the proof is built](#how-the-proof-is-built) lists the steps. The Rust is the
`formalhouse` branch, which is Lighthouse `unstable` with the epoch logic moved into modules that
Aeneas accepts.

**Every epoch boundary** means every state that a run reaches, not every value of the
`BeaconState` type. `FuluEpochRun` and `GloasEpochRun` say that the state comes from a run
of the state transition, starting from a Fulu state with the genesis invariants (`FuluStartOk`).
`fulu_reachable_invariants` and `fulu_then_gloas_reachable_invariants` prove the invariants that
the epoch proof needs at each of these states, through every block, every epoch and the Gloas
fork. The runs are defined by this project's hand-written Lean transcription of the block
processing spec and the fork upgrades (`EpochProofs/Spec/`), not by Etheorem. So the
transcription is trusted for which states count as reachable, though not for the epoch function
itself.

**Etheorem** is the fork `eserilev/etheorem`, branch `formalhouse-pin-cbws`, at the commit in
`lakefile.toml`. It pins spec v1.7.0-alpha.11, plus the Fulu deposit change of alpha.9, a port
to Lean v4.31.0, and three fixes that make Etheorem raise where the pyspec raises: the
`assert total > 0` of `compute_balance_weighted_selection`, its `uint64` pass counter, and the
checked `uint64` arithmetic and list reads of the epoch steps. The transcription follows v1.7.0-beta.4. The Gloas epoch functions have
the same meaning in both versions. Only the list limits differ, and they are assumptions below.

**Equal** means `toSpecState` (`toSpecState`), the map from an Etheorem state to the
transcription's state, sends Etheorem's result to the model's. It covers every field of the
state.

### The hypotheses can hold together

A theorem whose hypotheses cannot all hold proves nothing. Until 2026-10-27 the headline theorems
had this bug: the committee hypothesis stated the committee conditions at every state with the input's slot,
list lengths and RANDAO length (`CommFrame`), and that includes the input with its validator
lists emptied, where no validator is active. The hypothesis was false for every input. It is now
stated at the one state that the epoch passes to the committee steps
(`Spec.AtCommitteeStepState`, `Spec.FuluAtCommitteeStepState`).

`EpochProofs/NonVacuity.lean` gives a witness on the minimal preset: `witnessState`, a state at the
last slot of epoch 0 with eight active validators at 2048 ETH, `witnessStateFulu` (the same without
the Gloas fields), and the Etheorem states `witnessEtheorem` and `witnessEtheoremFulu` that map to
them. Lean computes the epoch on it. `gloas_bundles_at_witness` and `fulu_bundles_at_witness`
build the chain, Etheorem and oracle bundles of `Assumptions.lean` there, with an oracle that
agrees with Etheorem. They take as given only what no small witness can settle: SHA-256 returning
32 bytes, and for Fulu the Etheorem bridge bundle (`FuluEtheoremBridgeConditions`).
`gloas_spec_witness` and `fulu_spec_witness` add the start-state and reachable-state invariants
(`FuluStartOk`, `ReachableInvariants`) at the same state and show that the spec epoch returns `ok`
there. `agrees_pyspec_hyps_at_witness` and `agrees_pyspec_hyps_at_witness_fulu` give the state
facts that the `_agrees_pyspec` theorems use (`ReachableInvariants`, `AtEpochBoundary`,
`HistoricalSummariesBelowLimit`), and `lighthouse_model_gloas_epoch_agrees_pyspec_at_witness` is
the Gloas agreement at `witnessState`. The runs (`GloasEpochRun`, `FuluEpochRun`), the cache facts
and the glue facts of the `_rust` theorems have no witness.

### Axiom audit

`EpochProofs/Axioms.lean` prints the axioms of 817 theorems, including all the headline ones. Each
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
consolidation balances, the builder payments and the PTC window. 53 of the 165 `?` sites in
`single_pass.rs` are inside these implementations or pass on their errors.

**2. The values passed into the translated code.** The translated functions take plain numbers
and booleans, not the `BeaconState`, because Aeneas cannot handle `&BeaconState` or
`&ChainSpec`. So `single_pass.rs`, which is not translated, reads the state and the spec and
fills in the inputs:

- `ContextInputs`, once per epoch: the current and finalized epochs, the total active balance
  and the previous epoch flag balances from the caches, the `slashings` sum and the spec
  constants. The translated `step_context` computes the `StepContext` from them: the previous
  epoch, the inactivity leak flag, the increments, the slashings values and the hysteresis
  thresholds (`step_context_spec`).
- `RowInputs`, per validator: the base reward, the validator's pending deposit total, whether a
  consolidation names it, and its maximum effective balance.
- `DepositView`, per pending deposit: the deposit and the fields of its validator, including
  whether the pubkey is already a validator.
- The churn and selection constants and the builder payment threshold.

The proofs show the translated code gives the spec result for these inputs, and assume the
inputs are right. A wrong input gives a wrong state with no error: a wrong target flag balance
changes every validator's rewards. Some are partly covered: the cache proofs show the totals in
the caches are right, so only the copy into `ContextInputs` is trusted, and overflow in the
arithmetic formulas is ruled out (glue L1 to L7).

**3. The caches.** There are two questions about a cache, and the proofs answer only the first.

- *Does the cache code compute the right thing?* Proved. `consensus/types/proofs` shows that
  building each cache from a state gives the spec values, and that each update hook keeps the
  cache correct as the state changes.
- *Is the cache in this state the result of that code, run on this state?* Assumed. Epoch
  processing reuses the cache already in the `BeaconState`. That cache may have been built
  blocks earlier and updated by block processing, copied from another state when the store
  loaded this one, or cloned with the state. Whether it is right depends on all of that code,
  which is not translated.

So the Gloas theorem assumes that the progressive balances cache is correct for the epoch state,
that the epoch cache was built at a state of the same epoch, and that the pubkey cache was built
at an earlier state of the run. From the last two, the proofs show the values read at the epoch
are right. The committee cache for the lookahead is built fresh in the epoch, so only its inputs
are trusted. The Fulu theorem assumes every cache read.

Both cache bugs in [Findings](#findings) break this assumption, with correct cache code: a
committee cache built for another fork's state and copied into this one, and a pubkey cache read
before the update function runs.

Four more glue facts have no proof (N1 to N4 in `Trusted/EpochGlue.lean`): the superstruct
accessors return `Ok` on a state of the right fork, `update_tree_hash_cache` succeeds, the
`slashings` sum computes what the spec computes, and the active set fits the committee shuffle.
If one of these is false, Lighthouse returns an error rather than a wrong state.

<details>
<summary>The full list</summary>

Paths are relative to `consensus/`. `single_pass.rs` is
`state_processing/src/per_epoch_processing/single_pass.rs`.

**State list access (`single_pass.rs`).** `milhouse` lists are not translated.

- `StateRows::apply_step`: as above, including the cache updates inside it (`write_back_row`,
  `record_effective_balance_update`).
- `StateDeposits`: the deposit queue write, the pubkey lookup (the first matching index), the
  balance read and write, the signature check, `add_validator` (which pushes one entry onto
  each of the five validator lists, below `2^40` validators), and the effective balance update
  of a new validator.
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

- `ContextInputs`, `RowInputs` and `DepositView`, including the base reward read from the epoch
  cache.
- `registry_constants`, `selection_constants` and the builder payment threshold (6/10).
- Epoch and slot arithmetic, the per-validator deposit sum and the exit count per epoch: the
  formulas are trusted, and that they never overflow is proved.
- `BeaconState::get_seed_mix` reads the RANDAO mix that the spec `get_seed` reads.
- The effective balances, and the lists of active (for Gloas proposers, active and unslashed)
  validators passed to the proposer and sync committee selection.
- The active indices and seed passed to `shuffling` when the committee cache is built.
- The loop in `process_ptc_window` that joins each slot's committees from the committee cache.

**Caches.** As above. `lighthouse_model_gloas_epoch_eq_etheorem_upkeep` replaces the progressive balances
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

**Borrows of the state.** The composition (`Compose/`) makes these explicit. Each wrapper that
`single_pass.rs` builds around the state holds, and writes, only its part of the state:
`StateRows` the validator rows, and the end of its borrow writes the rows and the exit churn
that the loop returns; `StateDeposits` the state and the postponed deposits;
`StateBuilderPayments` the two builder lists; `PtcWindowWrites` the PTC window. `usize` has 64
bits.

**The four glue facts with no proof (`Trusted/EpochGlue.lean`).**

- N1: at most `2^24` validators are active, the committee shuffle limit. The composition
  assumes it at the three states where Lighthouse shuffles: the lookahead, the PTC committees
  and the sync committee.
- N2: each superstruct accessor returns the field of the state's fork variant.
- N3: `update_tree_hash_cache` succeeds when the latest block header has no state root yet.
- N4: `safe_sum` over `slashings` equals the spec sum, which is proved total.

**Other crates.**

- `BTreeSet` iterates in increasing order (`get_validators_in_consolidations`).
- `HashTrieMap` behaves as a finite map, and `BeaconState::update_pubkey_cache` inserts new
  pubkeys in order.
- `Sha256Hash` computes SHA-256. blst's signature check and aggregate key are BLS.

</details>

### Assumptions about the chain

These are hypotheses of the headline theorems (`GloasChainAssumptions`, `FuluChainAssumptions`).
When one fails, either the pyspec itself fails, or
the chain is far outside anything physically possible.

The agreement theorems (`lighthouse_model_gloas_epoch_agrees_pyspec`,
`lighthouse_model_fulu_epoch_agrees_pyspec`) keep only two of them:

- the supply bounds that the run carries (`SupplyBound`, `EpochBalanceBounds` =
  `EpochBalanceBounds`). The reachable-state invariants are proved from them, and
  `EpochBalanceBounds` (each balance below `2^62`) is also needed
  for agreement: Lighthouse adds all rewards before it subtracts the penalties, so near `2^64` it
  overflows where the spec does not (`rewards_overflow_example`).
- `HistoricalSummariesBelowLimit` (`HistoricalSummariesBelowLimit`): fewer than `2^24` historical summaries.
  Lighthouse's list returns an error when full, and the transcription appends without a limit.
  The pyspec's SSZ list would raise at the same length, but the transcription leaves the limit
  out.

They drop the pyspec preconditions (where these fail, both sides fail), `PhysicalLimits`,
`slot + 8192 < 2^64`, the reachable-state facts below, the hash-output facts and everything
about Etheorem and the oracle.

**Pyspec halts.** The pyspec raises without these, so no implementation can agree with it.

These and the committee state facts below are stated at the state that the epoch passes to the
committee steps (`Spec.AtCommitteeStepState`, `Spec.FuluAtCommitteeStepState`), which is a
function of the epoch input. In the chain bundles they are the fields `pyspecPreconditions`,
`selectionsEnd` (hash outputs) and `committeeStepStateFacts`.

- Gloas: an unslashed validator is active two epochs ahead (F4).
- Gloas: at least `SLOTS_PER_EPOCH` validators are active two epochs ahead (F12). With fewer, the
  first slot of that epoch has an empty PTC and `compute_ptc` asserts. That is 32 validators on
  mainnet and 8 on minimal.
- A validator is a sync committee candidate at the next epoch.
- Fulu: a validator is active at the next epoch and two epochs ahead.

**Physical limits.** Limits set by the ETH supply and by time.

- At most 139M ETH is active before each block (`SupplyBound`, `SupplyBoundFulu`).
- At each epoch input (`EpochBalanceBounds`, named `EpochBalanceBounds` in the headline): each balance
  is below `2^62` Gwei, the effective balances sum to less than `2^60` Gwei (about 1.15 billion
  ETH), and three times the `slashings` sum is below `2^64`.
- Inactivity scores stay below `2^22`, which rules out the `uint64` overflow of
  `effective_balance * inactivity_score` (F5). Scores grow by 4 per epoch of leak, so this takes
  about a million epochs. The same group bounds the effective balance sum, the funds, the exit
  fields and the validator count (`PhysicalLimits`, named `PhysicalLimits` in the headline).
- `slot + 8192 < 2^64`. That the epoch runs at the last slot of an epoch, and that the next slot
  fits in `u64`, follow from the run.
- `historical_summaries` holds fewer than `2^24` entries, Lighthouse's list limit.

**Reachable-state facts not yet carried to the epoch.** These hold on every real chain. The
invariant proofs cover most of the state, but not yet these fields:

- validator pubkeys pass `KeyValidate`. For Gloas, that they are unique follows from the run;
- the SSZ vectors, `proposer_lookahead` and `ptc_window` have their lengths;
- at most `2^40` validators, and each effective balance is at most 2048 ETH;
- `_rust` only: the new validators of the epoch fit under `2^40`, where Lighthouse's validator
  list fails (`SinglePassLinks.depositRoom`). This state fact sits inside the glue bundle
  (`EpochLinks`), because it is stated at the state after justification. It is the Lighthouse
  counterpart of Etheorem's `GloasEtheoremDivergenceAssumptions.depositRoom`;
- the states at which the caches were built agree with the epoch input on the activity and the
  pubkeys they read.

**Hash outputs.** These are facts about hash values. They hold with overwhelming probability,
and no proof can establish them.

- Each spec selection ends within `2^64` passes. Etheorem's selection counts its passes with
  the same `uint64` counter, so this also covers Etheorem (F3 is gone).
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
process_epoch_lighthouse          the steps in Lighthouse's order, joined by the
   |                            Rust contracts and glue facts (EpochProofs/Trusted/);
   |                            EpochProofs/Compose/ joins the translated functions
   |                            themselves and proves the result equal to this model
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

| Step, in Lighthouse's order | Translated Rust | Trusted | Composed in Lean |
|---|---|---|---|
| Justification and finalization | `justification.rs` | the reads and checkpoint writes (glue) | `justification_spec` |
| Inactivity, rewards, registry, slashings, deposit top-ups, effective balances | `single_pass_step.rs`, `registry_rows.rs` and the step modules | `RowsContract` | `singlePass_spec` |
| Pending deposits | `pending_deposits.rs`, `deposit_balance.rs`, `deposit_writes.rs` | `DepositWritesContract`, the deposit plan | `afterLoop_spec`, the writes only |
| Pending consolidations | `pending_consolidations.rs`, `list_writes.rs` | `ConsolidationStateContract`, `BTreeSetIter`, `EffectiveBalanceContract` | `afterLoop_spec` |
| Builder pending payments (Gloas) | `builder_pending_payments.rs`, `list_writes.rs` | `PaymentWritesContract` | `payments_spec` |
| Proposer lookahead | `epoch_committees.rs`, `balance_weighted_selection.rs`, `compute_shuffled_index_with.rs` | `SeedMixLink`, `EBLink`, the index lists | `lookahead_spec` |
| PTC window (Gloas) | as the lookahead, and `list_writes.rs` | `WindowContract`, `CommitteesFromCache` | `ptcWindow_spec` |
| Next sync committee | as the lookahead | the pubkeys, the aggregate key | `syncUpdate_spec` |
| Eth1, slashings and RANDAO resets, historical summaries | `tail_updates.rs` | the vector writes | `resets_spec` |
| Participation flag rotation | none | one `types` call (glue) | `resets_spec` |
| Fork upgrades | `epoch_committees.rs`, `upgrade/builder_onboarding.rs` | the field copies, `OnboardingContract` | no, not part of the epoch |

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

None of these came from a failing proof. The proofs need explicit assumptions about the code
around them, and auditing those assumptions by hand found the first two Lighthouse bugs below.
The third came up during the same audit and is outside the scope of the proofs. The spec and
Etheorem findings came from proving the two specs equal. `NOTES.md` has more detail on each.

### In Lighthouse

These are outside the code the proofs cover.

- A state of an abandoned fork can get another chain's committee caches. See
  [Cross-fork committee caches](#cross-fork-committee-caches) below.
- In Gloas, a withdrawal or consolidation request is skipped if the pubkey cache lags, which
  other code prevents on almost every path. See
  [Gloas parent requests skip the pubkey cache update](#gloas-parent-requests-skip-the-pubkey-cache-update)
  below.
- In Gloas, gossip checks a builder's bid against the head state, not the bid's parent state
  advanced to the bid's slot. This is outside the proofs; it was found while auditing which
  state each cache read uses. See
  [Gloas gossip bid checks use the head state](#gloas-gossip-bid-checks-use-the-head-state)
  below.
- `initialize_progressive_balances_cache` keeps any cache that `is_initialized`, whatever epoch
  it was built for, and the cache readers do not check the epoch. No path that produces a stale
  cache is known, so this is hardening rather than a bug. The proof needs a cache of the current
  epoch, so the `formalhouse` branch rebuilds a cache of another epoch (commit `9dcec02a0`).

#### Cross-fork committee caches

**Background.** A `BeaconState` carries caches next to the state itself. The committee cache
holds the committees of the previous, current and next epoch. Building it shuffles the active
validators with a seed from the chain's RANDAO history, so two forks can have different
committees for the same epoch.

When Lighthouse loads a recent state from the hot database, it builds it from a stored snapshot
or diff, or from an earlier stored state plus a replay of blocks. Before any replay, it rebases
that state on the finalized state it keeps in memory: the loaded state reuses the finalized
state's tree nodes wherever they are equal, and `rebase_caches_on` copies the finalized state's
caches into it to avoid rebuilding them. It copies each committee cache whose epoch is also the
loaded state's previous, current or next epoch. A replay then carries the copied caches forward.

**The bug.** `StateCache::rebase_on_finalized` (`beacon_node/store/src/state_cache.rs`) decides
whether to rebase with one check:

```rust
if let Some(finalized_state) = &self.finalized_state
    && state.slot() >= finalized_state.state.slot()
{
    state.rebase_on(&finalized_state.state, spec)?;
}
```

It checks the slot, not ancestry. Once pruning has run, every hot state at or after the finalized
slot does. But there is a window in which states of forks that conflict with finalization are still
on disk.

**The window.** After a finalization, the migrator (`run_migration` in
`beacon_node/beacon_chain/src/migrate.rs`) runs two steps, normally on a background thread:

```
  finalization        migrate_database            prune_hot_db
  notification        ends with                   deletes the states
  arrives             update_finalized_state      of conflicting forks
      │                     │                          │
──────●─────────────────────●━━━━━━━━━━━━━━━━━━━━━━━━━━●──────────►
                            ◄──────── the window ──────►
                       rebasing now uses the        their states are
                       new finalized state          still on disk
```

1. `migrate_database` moves the finalized data to the freezer and ends with
   `update_finalized_state`. From then on, `rebase_on_finalized` rebases on the new finalized
   state.
2. `prune_hot_db` deletes the states and blocks of forks that conflict with the new finalized
   block.

A state of a conflicting fork that is loaded between the two steps passes the slot check and
gets the finalized chain's committee caches. The committees of epoch E depend on the active
validators at E and on the RANDAO mix at the end of epoch E−2. If the fork split before those
were fixed, its own committees can differ, and the copied cache is then wrong. The window is
usually short. It stays open until the next migration when `prune_hot_db` returns an error
(`run_migration` logs it and returns).

The pubkey cache is copied the same way, with only a length check. Validator indices are
assigned in deposit order on every fork, so we expect it to be correct, but no test covers it.

**Test.** `store_tests::abandoned_fork_state_loaded_after_finalization_has_own_committee_caches`
(minimal preset): fork B splits from fork A at epoch 1, and fork A finalizes epoch 4. Fork B's
state at slot 32 is loaded inside the window. It gets fork A's committee cache for epoch 3, not
its own.

**Impact.** Low, as far as we know. Gossip blocks and attestations check that they
descend from the finalized checkpoint before they load a state, and block production and duties
work from the head. The exposure we know of is the HTTP API when a caller asks for such a state
by its root, for example `/eth/v1/beacon/states/{state_id}/committees`. Not every caller that
loads a hot state by root has been audited.

**Fix.** Keep the finalized block root with the finalized state, and rebase only a state that
descends from it (`state.get_block_root(finalized_slot) == finalized_block_root`), or that is the
finalized state itself. With this check the test passes, as do the other `store_tests`.

#### Gloas parent requests skip the pubkey cache update

**Background.** Withdrawal and consolidation requests from the execution layer name validators
by pubkey. The spec scans the registry for the pubkey and ignores the request if none matches.
Lighthouse looks the pubkey up in the state's pubkey cache instead. The cache is filled lazily:
`update_pubkey_cache()` adds the validators past its end. Before Gloas, `process_operations`
calls it right before the requests. In Gloas, a block's payload requests are processed in the
next block, by `apply_parent_execution_payload`, at the start of `per_block_processing`.

**The bug.** `apply_parent_execution_payload`
(`consensus/state_processing/src/per_block_processing.rs`) calls
`process_withdrawal_requests` and `process_consolidation_requests` without
`update_pubkey_cache()`. A validator that exists but is missing from the cache looks absent:

```rust
let Some(validator_index) = state.pubkey_cache().get(&request.validator_pubkey) else {
    continue;
};
```

Lighthouse skips the request, and the spec applies it.

**Where it matters.** Almost nowhere today. States in memory keep their pubkey cache current.
A state rebuilt from disk gets the in-memory finalized state's pubkey cache when it is rebased,
and the replay of its epoch's blocks starts at the epoch boundary. With `update_cache = true`,
as block import, reorgs and the HTTP API use, a replay hook builds all caches on that boundary
state before any block, so the cache is complete. Only loads with `update_cache = false`, such
as the light client server and the store's state iterators, replay with the copied cache. They
skip a request only if its validator was added after the in-memory finalized state, which by
default trails the chain's finalized state by about an epoch. So the bug is a missing call that
other code masks. Gloas is not on mainnet yet.

**Test.** `gloas_parent_requests_do_not_depend_on_pubkey_cache` gives a state a lagging cache
and checks that a parent withdrawal request for the missing validator is applied. It failed on
sigp `unstable` at `ec2442d24b`.

**Fix.** Call `state.update_pubkey_cache()?` at the start of `apply_parent_execution_payload`, as
the Electra path does.

#### Gloas gossip bid checks use the head state

**Background.** In Gloas, builders send bids over gossip: for slot `S`, building on block `P`,
pay the proposer `V`. A bid is valid only if the builder exists, is active and can cover `V`
from its balance, minus what it already owes. The spec runs these checks against the parent
state advanced to the bid's slot (`validate_execution_payload_bid_gossip`):

```python
state = store.block_states[bid.parent_block_root]
process_slots(state, bid.slot)
```

A failed check either IGNOREs the bid (drop it) or REJECTs it (drop it and penalize the peer).

**The bug.** `GossipVerifiedPayloadBid::new`
(`beacon_node/beacon_chain/src/payload_bid_verification/gossip_verified_bid.rs`) runs the checks
against the head snapshot state, advanced only at the Gloas fork. That state differs from
the spec's when the bid builds on the head's parent, which `is_bid_compatible_with_head`
accepts, or when an epoch boundary lies between the head and the bid's slot.

**Example.** Builder X won a slot in epoch 9, but the payment stayed below quorum. The pending
payment counts against X's balance until epoch processing drops it at the start of epoch 11. At the
last slot of epoch 10, X bids for the first slot of epoch 11. The spec advances the state into epoch
11, the payment is dropped, X can cover the bid, so the bid is valid. Lighthouse checks the head
state, where the payment is still pending, returns `BuilderCantCoverBid` and drops a valid bid. A
Lighthouse proposer at that slot never sees it.

Two cases, argued from the code but not tested, REJECT a valid bid and penalize the peer that
sent it: a bid on the head's parent whose builder exits in the bid's parent payload, which the
head block has already applied (the spec IGNOREs), and a builder that becomes active when
finality advances at the epoch boundary before the bid's slot.

**Impact.** Gossip only. Block production checks the chosen bid again against its own state, and
block import validates the block. Valid bids are dropped, and in the REJECT cases honest peers
lose score. Gloas is not on mainnet yet.

**Test.** A local test written during the audit reproduced the example against sigp `unstable`
at `ec2442d24b`. It is not published.

**Fix.** Load the parent state advanced to the bid's slot (`get_advanced_hot_state`) and run the
builder and signature checks on it. A sketch compiles but is not yet tested. Loading a state for
each bid is slow, so a real fix likely caches the advanced state for each parent and slot.

### In the spec and Etheorem

- Gloas halts with fewer than `SLOTS_PER_EPOCH` validators active two epochs ahead
  (`process_ptc_window_few_active_error`), and when all of them are slashed (F4).
- Etheorem kept the eth1 bridge deposit path in Fulu, which the spec removed in alpha.9 (F2).
  Fixed on the pin and proposed upstream in
  [etheorem#144](https://github.com/etheorem/etheorem/pull/144).
- Etheorem's balance-weighted selection gave up after `10^7` passes (F3). The pin now counts
  its passes with the pyspec's `uint64` counter, so F3 is no longer a condition.
- Etheorem's `get_flag_index_deltas` computes `base_reward * weight` for every eligible index,
  where the pyspec computes it only when it adds a reward or a penalty. The product fits in
  `uint64` with the mainnet and minimal increment and base reward factor
  (`get_base_reward_small`), so this changes no result.

## Error sites

`single_pass.rs` has 165 `?` sites. The theorem holds only if none of them returns an error
where the spec succeeds.

| Status | Sites |
|---|---|
| Proved: a translated function whose errors are spec errors, at a step the spec completes | 12 |
| Inside a trusted Rust contract | 53 |
| Fails only if a cache is not built (cache build facts) | 13 |
| Bound proved, Rust formula trusted (glue L1 to L7) | 13 |
| Named fact with no proved bound (glue N1 to N4) | 14 |
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
| `EpochProofs/Etheorem/` | The transcription's epoch equals Etheorem's, for Gloas and Fulu. |
| `ForkReplay.lean` | `forkproof`: a proof written once and elaborated for each fork. |
| `EpochProofs/CacheBridge/` | The cache reads equal the spec values. |
| `EpochProofs/Assumptions.lean` | Every hypothesis bundle of the headline theorems, each field with a docstring. |
| `EpochProofs/Assumptions/Etheorem.lean` | The preset, Etheorem and oracle bundles, which the `Etheorem/` step proofs read. |
| `EpochProofs/Headline.lean` | The conclusions and the headline theorems with their proofs (`HeadlinePresets.lean`: mainnet and minimal). |
| `EpochProofs/NonVacuity.lean` | A witness at which the hypothesis bundles hold together. |
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
