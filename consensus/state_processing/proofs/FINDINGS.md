# Findings

None of these came from a failing proof. The proofs need explicit assumptions about the code
around them, and auditing those assumptions by hand found the first two Lighthouse bugs below.
The third came up during the same audit and is outside the scope of the proofs. The spec and
Etheorem findings came from proving the two specs equal. `NOTES.md` has more detail on each.

## In Lighthouse

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

### Cross-fork committee caches

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

### Gloas parent requests skip the pubkey cache update

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

### Gloas gossip bid checks use the head state

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

## In the spec and Etheorem

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
