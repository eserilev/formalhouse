# Epoch processing proofs

Lean 4 proofs that Lighthouse's epoch processing gives the same state as
[EthLib](https://github.com/ethereum/EthLib), an independent Lean spec of the consensus layer. They
cover Fulu and Gloas, on the mainnet and minimal presets. Charon and Aeneas translate the Rust to Lean.

## What is proved

Take a chain of EthLib slots and blocks from genesis, with the [assumptions](#the-chain) below. At each
Fulu and Gloas input of `process_epoch` on that chain, Lighthouse's epoch and EthLib's `processEpoch`
both succeed, with the same state. The theorems are in `EpochProofs/EthLib/ResultsFromEthLibRun.lean`,
with their versions for the two presets. Each name has a Fulu form (`fulu` in place of `gloas`).

The chain can also start at a later state, if that state has the facts of `ChainStart`. `Results.lean` and
`ResultsOnPresets.lean` have the same theorems for a chain that our transcription defines
(`FuluThenGloasRun`, `FuluOnlyRun`). That chain starts in Fulu. Those theorems are not necessary for the
ones above, but the proofs share their last steps.

| Theorem | Statement |
|---|---|
| `lighthouse_model_gloas_epoch_eq_ethlib` | The Lean model of Lighthouse's epoch succeeds, and EthLib succeeds with the same state. For Gloas, the cache reads give the spec values. For Fulu, EthLib keeps the payload header |
| `lighthouse_rust_gloas_epoch_eq_ethlib` | The same for the translated Rust. It also assumes facts about the [Rust that Lean does not check](#rust-that-lean-does-not-check) |
| `lighthouse_model_gloas_epoch_agrees_ethlib` | At an epoch input, the model and EthLib give the same state, or both fail |
| `lighthouse_rust_gloas_epoch_of_ethlib_ok` | If EthLib succeeds, the translated Rust returns `Ok` with the same state |
| `lighthouse_model_gloas_epoch_agrees_pyspec` | The model and the transcription of the pyspec give the same state, or both fail |
| `ptc_committees_correct` (Gloas only) | The committees that `process_ptc_window` reads from its committee cache are the spec committees |

**The model** is `process_epoch_lighthouse`: `process_epoch_single_pass` and `altair.rs` in Lighthouse's
order. A theorem for each step proves the model equal to the translated Rust, except where Aeneas cannot
translate. `translatedEpoch` (`TranslatedEpoch/`) is the translated Rust as one function. The cache
builds at the start of the epoch are in neither. They write no field of the state, and can only make
Lighthouse return an error.

**The transcription** (`Spec/`) is a hand-written Lean copy of pyspec v1.7.0-beta.4. The proofs go
through it: Lighthouse equals the transcription, and the transcription equals EthLib (`EthLib/`). The
main theorems do not trust it: EthLib defines the epoch and the chain (`RunToEpochInput`). Only
`Results.lean` uses the block processing of the transcription to define a chain.

**Same state** means equal under `toSpecState`, which reads an EthLib state as a state of the
transcription. No two EthLib states give the same one (`toSpecState_injective`; for Fulu,
`toSpecFuluState_injective`, which includes the payload header).

**Axioms.** `lake build` prints the axioms of 884 theorems here (`Axioms.lean`), and the cache proofs check
1100. CI fails if one uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`.

## What is assumed, and why it is true

`Assumptions.lean` and `Runs.lean` define the assumptions, with a docstring on each field.

### The chain

For an EthLib chain, the start is a genesis state or a state with `ChainStart`, so no fact about a genesis
state is assumed. The supply bounds below then apply only at the epoch input (`SupplyAtInput`). The preset
must have equal `MAX_EFFECTIVE_BALANCE` and `MIN_ACTIVATION_BALANCE`, which both presets have. The fork
epochs are a parameter, because the EthLib configs do not schedule Gloas. The next two items are about the
chain of `Results.lean`.

- The start state has the facts of a genesis state (`GenesisInvariants`). The step from genesis to the
  Fulu fork is not proved, because no Electra spec is transcribed.
- At most 139 million ETH is active before each block. Each balance is below 2^62 Gwei at the epoch
  input, the effective balances sum to less than 2^60 Gwei, and three times the slashings are below 2^64
  (`BalancesFarFromOverflow`). The total supply is about 120.7 million ETH. Near 2^64 Gwei, Lighthouse's
  order of rewards and penalties overflows where the spec does not (`rewards_order_overflow_example`).
- Lighthouse's list of historical summaries has room for 2^24 entries. On mainnet, it grows by one entry
  for each 8192 slots, so it fills after more than 50,000 years.

The theorems that say that the epoch succeeds (`_eq_ethlib`) need more (`GloasChainConditions`,
`FuluChainConditions`):

- The next epoch has a sync committee candidate, and the epoch after it has a proposer candidate. For
  Gloas, the proposer candidate is not slashed, and at least `SLOTS_PER_EPOCH` validators are active.
  Without these, the pyspec raises.
- Each selection ends within 2^64 passes. This is a fact about hash values. It holds with overwhelming
  probability, and no proof can show it.
- `slot + 8192 < 2^64`, inactivity scores below 2^22, and bounds on the exit queue, the funds and the
  validator count (`SupplyAndTimeLimits`). Scores grow by 4 for each epoch of leak, so 2^22 takes about
  a million epochs.
- At most 2^40 validators, and each pubkey passes `KeyValidate`. Each deposit checks this, but the
  proofs do not carry it to the epoch.

### The differences between EthLib and the transcription

Each difference is an assumption about the input state. Lean proves that the two specs agree on all other
inputs, with the same preset values and the same oracle (`EthLib/Epoch.lean`).

- **Full registry** (`RoomForDeposits`): the registry has room for the deposits of one epoch within
  `VALIDATOR_REGISTRY_LIMIT` (2^40). Else EthLib can fail, where the transcription appends.
- **Full historical summaries**: EthLib fails at the limit, where the transcription appends.
  Lighthouse's limit of 2^24 gives this.
- **Last slots** (Gloas): if the new PTCs end at slot 2^64, the transcription fails, and EthLib does not.
  `slot + 8192 < 2^64` excludes this.

`PresetMatchesEthLib` (equal preset values) is proved for both presets. `OracleMatches` says that the
hash, `hash_tree_root` and BLS functions are those of EthLib. `exists_oracle` proves that they exist.

### Rust that Lean does not check

Aeneas cannot translate reads and writes of `milhouse` lists, functions that take a `BeaconState` or
`ChainSpec`, and other crates. Review checks this code. `Trusted/` and `TranslatedEpoch/` state what it
does (`GloasUntranslatedRustFacts`, `FuluUntranslatedRustFacts`). Three parts matter most, because a
mistake there gives a wrong state with no error:

1. The list reads and writes in `single_pass.rs`, first `StateRows::apply_step`. It reads validator `i`,
   runs the translated `single_pass_step`, writes back only the fields that changed, and does not fail.
2. The values that `single_pass.rs` passes to translated code: `ContextInputs`, `RowInputs`,
   `DepositView`, the churn and selection constants, the deposit plan and the sync committee inputs.
3. The caches (below).

Also: `usize` has 64 bits, `BTreeSet` iterates in order, the hash map behaves as a map, and SHA-256 and
BLS are right. `UntranslatedSinglePassFacts.depositRoom` is a state fact: the new validators of the epoch
fit under 2^40. Four facts have no proof:

| Fact | If it is false | In Lean |
|---|---|---|
| At most 2^24 validators enter a shuffle | Error only. The PTC selection does not shuffle: there, only the proof needs the bound | assumption |
| `safe_sum` of the slashings is the spec sum | An overflow gives an error. **A wrong value changes the slashing penalties: wrong state, no error** | value: assumption of the `rust` theorems (`ContextInputsMatch.sum_slashings`); success: no statement |
| A superstruct accessor gives the field of the fork | `Err` gives an error at each `?`. **`Err` from the two exit churn accessors after the loop skips their writes: wrong state, no error.** `Err` for the pending consolidations gives an empty set, and a later read fails. A wrong field gives a wrong state | the churn writes: assumption of the `rust` theorems (`rowsReturn`); the rest: no statement |
| `update_tree_hash_cache` succeeds and changes no field | `Err` gives an error. A wrong root changes only the key of the next epoch cache | no statement |

### Caches

`consensus/types/proofs` proves that the cache build and update code gives the spec values. The Gloas
theorems assume where the cache in this state came from (`GloasCacheAssumptions`). The progressive
balances cache was correct at a state of this epoch, and each later write ran its update. The epoch cache
was built at a state of the same epoch. The pubkey cache was built earlier in the run and then completed.
An audit of the call sites supports this. The Fulu theorems assume all cache reads.

### Tools

The Lean kernel, Charon, Aeneas and its Lean library. Aeneas has no end-to-end soundness proof.
`aeneas/discriminant-instance-name.patch` renames one instance.

## What is not covered

- Block processing in Lighthouse, fork choice, networking and the store. The cache copies in the store
  (`rebase_caches_on`): see `FINDINGS.md`.
- The Fulu cache reads, the forks before Fulu, Heze, the genesis state, part of the fork upgrade code.
- EthLib outside `processEpoch`.

`AssumptionsHoldForExample.lean` gives an example state where the state, preset and oracle assumptions hold
together and the epoch succeeds. `EthLib/EthLibRunExample.lean` adds a run of one slot. A run with a block, a
run from genesis, the caches and the untranslated code have no example.

## Build

Lean v4.36.0. EthLib is pinned to `e73a0744c23b`, Aeneas to `fb44cb400eb6` (`lakefile.toml`).

```sh
lake exe cache get && ./setup.sh && lake build
lake lean EpochProofs/Axioms.lean    # not `lake env lean`: EthLib needs its native code
```

After a change to a translated Rust module, regenerate `Generated.lean` as the "Regenerate" step of
`.github/workflows/proofs.yml` does, with the arguments in `.github/proofs.json`. `NOTES.md` says which
Rust Aeneas accepts. `.github/proofs.json` lists the Rust files.

`Results.lean`, `Assumptions.lean`: theorems and assumptions. `SpecFacts/`, `Invariants/`: facts about the
transcription and reachable states. `LighthouseModel/`: the model. `TranslatedSteps/`: each translated
function. `CacheReads/`: the cache reads. `FINDINGS.md`: bugs found.
