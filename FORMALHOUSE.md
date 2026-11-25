# Formalhouse

Formalhouse is Lighthouse with machine-checked proofs. Aeneas translates parts of the Rust code to
Lean, and Lean proofs show that this code equals the consensus spec.

## Branches

- `unstable` is a copy of sigp/lighthouse `unstable`. Only the sync workflow writes to it. Do not
  commit to it.
- `formalhouse` is `unstable` plus the proofs and the Rust changes that the proofs need.
  Proof pull requests target `formalhouse`.
- The sync merges `unstable` into `formalhouse`. It does not rebase, so the history of
  `formalhouse` does not change.

## Sync

`.github/workflows/sync-unstable.yml` runs every day at 06:00 UTC. You can also start it by hand.

1. It moves `unstable` forward to sigp/lighthouse `unstable`.
2. It merges `unstable` into a branch `sync/<date>` and opens a pull request into
   `formalhouse`. If a sync pull request is already open, it adds the merge to that pull request.
3. The proof workflows run on the pull request. A red check means that a Lighthouse change
   breaks a proof.
4. If the merge has a conflict, it opens an issue with the label `sync-conflict` instead.

The Lighthouse test workflows stay disabled. The sync disables each workflow that a sync push
registers, except the proof workflows.

The sync needs the secret `SYNC_TOKEN`. The default token cannot push changes to workflow files,
and its pull requests do not start other workflows. Make a fine-grained token for
`eserilev/formalhouse` with these permissions set to read and write: Actions, Contents, Issues,
Pull requests and Workflows.

## What is proved

- Index of all proofs: issue #44. Tracking issues: #32 slashing protection, #33 epoch
  processing, #34 Lean spec, #35 caches.
- The main results for epoch processing are `lighthouse_model_gloas_epoch_eq_ethlib` and
  `lighthouse_model_fulu_epoch_eq_ethlib`, with the same theorems for the translated Rust
  (`lighthouse_rust_*`). They are in `EpochProofs/Results.lean` (`ResultsOnPresets.lean` for mainnet
  and minimal), and their assumptions in `EpochProofs/Assumptions.lean`. At every epoch input of a
  run, Lighthouse's epoch processing succeeds and gives the same state as
  [EthLib](https://github.com/ethereum/EthLib), an independent Lean spec.

## Trusted base

The full list is in "What is assumed, and why it is true" in
`consensus/state_processing/proofs/README.md`. In short:

- The Lean kernel, Charon and Aeneas.
- Rust contracts: the milhouse implementations of the traits that the translated code calls,
  for example `ValidatorRowsMatchSpec` for the single-pass loop.
- Rust expressions that Aeneas does not translate, each with a fact that links it to the model.
- Where the caches came from, spec preconditions, supply and time bounds, facts about hash values and
  the registry room that the comparison with EthLib needs.
- The hash function and BLS, given as an Oracle. The theorems against EthLib use the functions of EthLib.
