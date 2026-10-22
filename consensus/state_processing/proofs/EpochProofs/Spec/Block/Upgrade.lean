import EpochProofs.Spec.Block.FuluTransition
import EpochProofs.Spec.Block.ExecutionRequests
import EpochProofs.Spec.Fulu

/-!
# Reference: the Fulu and Gloas fork upgrades

Transcribed from `specs/fulu/fork.md` and `specs/gloas/fork.md` (v1.7.0-beta.2).

The Electra state has the fields of the Fulu state except `proposer_lookahead`, so
`upgrade_to_fulu` takes a `FuluState` and ignores its `proposer_lookahead`. The Gloas-only fields
of a Fulu state are unused, and `upgrade_to_gloas` sets each of them.

`UpgradeConfig` holds the fork versions and `hash_tree_root(ExecutionRequests.empty())`, a
constant that `Oracle` does not hold.
-/

namespace EpochProofs.Spec

/-- The config values and the constant root that the upgrades read. -/
structure UpgradeConfig where
  FULU_FORK_VERSION : Version := Version.zero
  GLOAS_FORK_VERSION : Version := Version.zero
  /-- `hash_tree_root(ExecutionRequests.empty())`. -/
  empty_execution_requests_root : Root := Bytes32.zero

/-- ```python
def initialize_proposer_lookahead(
    state: BeaconState,
) -> ProposerLookahead:
    current_epoch = get_current_epoch(state)
    lookahead: list[ValidatorIndex] = []
    for i in range(MIN_SEED_LOOKAHEAD + 1):
        lookahead.extend(get_beacon_proposer_indices(state, current_epoch + i))
    return ProposerLookahead(data=lookahead)
``` -/
def initialize_proposer_lookahead (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM (List ValidatorIndex) := do
  let current_epoch ← get_current_epoch p state
  let per_epoch ← (List.range (p.MIN_SEED_LOOKAHEAD + 1)).mapM fun i => do
    get_beacon_proposer_indices_fulu p o state (← uint64Add current_epoch i)
  pure per_epoch.flatten

/-- ```python
def upgrade_to_fulu(pre: electra.BeaconState) -> BeaconState:
    epoch = electra.get_current_epoch(pre)
    post = BeaconState(
        ...  # every Electra field, unchanged
        fork=Fork(
            previous_version=pre.fork.current_version,
            current_version=FULU_FORK_VERSION,
            epoch=epoch,
        ),
        proposer_lookahead=ProposerLookahead(),
    )
    post.proposer_lookahead = initialize_proposer_lookahead(post)
    return post
``` -/
def upgrade_to_fulu (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre : FuluState) :
    SpecM FuluState := do
  let epoch ← get_current_epoch p pre.state
  let post : BeaconState := { pre.state with
    fork := { previous_version := pre.state.fork.current_version
              current_version := c.FULU_FORK_VERSION
              epoch }
    proposer_lookahead := [] }
  let proposer_lookahead ← initialize_proposer_lookahead p o post
  pure { pre with state := { post with proposer_lookahead } }

/-- ```python
def initialize_ptc_window(
    state: BeaconState,
) -> PayloadTimelinessCommitteeWindow:
    empty_previous_epoch = [
        PayloadTimelinessCommittee(data=[ValidatorIndex(0) for _ in range(PTC_SIZE)])
        for _ in range(SLOTS_PER_EPOCH)
    ]

    ptcs = []
    current_epoch = get_current_epoch(state)
    for e in range(1 + MIN_SEED_LOOKAHEAD):
        epoch = current_epoch + e
        start_slot = compute_start_slot_at_epoch(epoch)
        ptcs += [compute_ptc(state, start_slot + i) for i in range(SLOTS_PER_EPOCH)]

    return PayloadTimelinessCommitteeWindow(data=empty_previous_epoch + ptcs)
``` -/
def initialize_ptc_window (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM (List (List ValidatorIndex)) := do
  let empty_previous_epoch := List.replicate p.SLOTS_PER_EPOCH (List.replicate p.PTC_SIZE 0)
  let current_epoch ← get_current_epoch p state
  let per_epoch ← (List.range (1 + p.MIN_SEED_LOOKAHEAD)).mapM fun e => do
    let epoch ← uint64Add current_epoch e
    let start_slot ← compute_start_slot_at_epoch p epoch
    (List.range p.SLOTS_PER_EPOCH).mapM fun i => do
      compute_ptc p o state (← uint64Add start_slot i)
  pure (empty_previous_epoch ++ per_epoch.flatten)

/-- ```python
def is_pending_validator(pending_deposits: Sequence[PendingDeposit], pubkey: BLSPubkey) -> bool:
    for pending_deposit in pending_deposits:
        if pending_deposit.pubkey != pubkey:
            continue
        if is_valid_deposit_signature(
            pending_deposit.pubkey,
            pending_deposit.withdrawal_credentials,
            pending_deposit.amount,
            pending_deposit.signature,
        ):
            return True
    return False
``` -/
def is_pending_validator (p : Preset) (o : Oracle) (pending_deposits : List PendingDeposit)
    (pubkey : BLSPubkey) : Bool :=
  pending_deposits.any fun d =>
    d.pubkey == pubkey &&
      is_valid_deposit_signature p o d.pubkey d.withdrawal_credentials d.amount d.signature

/-- One pass of the loop of `onboard_builders_from_pending_deposits`. The pair holds the state
and the new pending queue. `validator_pubkeys` is the list of validator pubkeys, which the loop
does not change. -/
def onboard_step (p : Preset) (o : Oracle) (validator_pubkeys : List BLSPubkey)
    (acc : BeaconState × List PendingDeposit) (deposit : PendingDeposit) :
    SpecM (BeaconState × List PendingDeposit) := do
  let state := acc.1
  let pending_deposits := acc.2
  if deposit.pubkey ∈ validator_pubkeys then
    pure (state, pending_deposits ++ [deposit])
  else if deposit.pubkey ∉ state.builders.map (·.pubkey) then
    if !is_builder_withdrawal_credential deposit.withdrawal_credentials then
      pure (state, pending_deposits ++ [deposit])
    else if is_pending_validator p o pending_deposits deposit.pubkey then
      pure (state, pending_deposits ++ [deposit])
    else if !is_valid_deposit_signature p o deposit.pubkey deposit.withdrawal_credentials
        deposit.amount deposit.signature then
      pure (state, pending_deposits)
    else do
      let state ← add_builder_to_registry p state deposit.pubkey PAYLOAD_BUILDER_VERSION
        (withdrawalAddress deposit.withdrawal_credentials) deposit.amount deposit.slot
      pure (state, pending_deposits)
  else do
    let builder_index := (state.builders.map (·.pubkey)).idxOf deposit.pubkey
    let builder ← listGet state.builders builder_index
    let balance ← uint64Add builder.balance deposit.amount
    let builders ← listSet state.builders builder_index { builder with balance }
    pure ({ state with builders }, pending_deposits)

/-- ```python
def onboard_builders_from_pending_deposits(state: BeaconState) -> None:
    validator_pubkeys = [v.pubkey for v in state.validators]

    pending_deposits = PendingDeposits()
    for deposit in state.pending_deposits:
        if deposit.pubkey in validator_pubkeys:
            pending_deposits.append(deposit)
            continue
        builder_pubkeys = [b.pubkey for b in state.builders]
        if deposit.pubkey not in builder_pubkeys:
            if not is_builder_withdrawal_credential(deposit.withdrawal_credentials):
                pending_deposits.append(deposit)
                continue
            if is_pending_validator(pending_deposits, deposit.pubkey):
                pending_deposits.append(deposit)
                continue
            if not is_valid_deposit_signature(
                deposit.pubkey,
                deposit.withdrawal_credentials,
                deposit.amount,
                deposit.signature,
            ):
                continue
            add_builder_to_registry(
                state,
                deposit.pubkey,
                PAYLOAD_BUILDER_VERSION,
                ExecutionAddress(deposit.withdrawal_credentials[12:]),
                deposit.amount,
                deposit.slot,
            )
        else:
            builder_index = BuilderIndex(builder_pubkeys.index(deposit.pubkey))
            state.builders[builder_index].balance += deposit.amount

    state.pending_deposits = pending_deposits
``` -/
def onboard_builders_from_pending_deposits (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM BeaconState := do
  let validator_pubkeys := state.validators.map (·.pubkey)
  let (state', pending_deposits) ←
    state.pending_deposits.foldlM (onboard_step p o validator_pubkeys) (state, [])
  pure { state' with pending_deposits }

/-- ```python
def upgrade_to_gloas(pre: fulu.BeaconState) -> BeaconState:
    epoch = fulu.get_current_epoch(pre)
    post = BeaconState(
        ...  # every Fulu field except `latest_execution_payload_header`, unchanged
        fork=Fork(
            previous_version=pre.fork.current_version,
            current_version=GLOAS_FORK_VERSION,
            epoch=epoch,
        ),
        latest_block_hash=pre.latest_execution_payload_header.block_hash,
        builders=Builders(),
        next_withdrawal_builder_index=BuilderIndex(0),
        execution_payload_availability=ExecutionPayloadAvailability(
            data=[0b1 for _ in range(SLOTS_PER_HISTORICAL_ROOT)]
        ),
        builder_pending_payments=BuilderPendingPayments(),
        builder_pending_withdrawals=BuilderPendingWithdrawals(),
        latest_execution_payload_bid=ExecutionPayloadBid(
            parent_block_hash=pre.latest_execution_payload_header.parent_hash,
            parent_block_root=pre.latest_block_header.parent_root,
            block_hash=pre.latest_execution_payload_header.block_hash,
            prev_randao=pre.latest_execution_payload_header.prev_randao,
            fee_recipient=ExecutionAddress(),
            gas_limit=pre.latest_execution_payload_header.gas_limit,
            builder_index=BUILDER_INDEX_SELF_BUILD,
            slot=pre.latest_block_header.slot,
            value=Gwei(0),
            execution_payment=Gwei(0),
            blob_kzg_commitments=BlobKZGCommitments(),
            execution_requests_root=hash_tree_root(ExecutionRequests.empty()),
        ),
        payload_expected_withdrawals=Withdrawals(),
        ptc_window=PayloadTimelinessCommitteeWindow(),
    )
    post.ptc_window = initialize_ptc_window(post)
    onboard_builders_from_pending_deposits(post)
    return post
```

`BuilderPendingPayments()` is a `Vector` of `2 * SLOTS_PER_EPOCH` empty payments, and
`PayloadTimelinessCommitteeWindow()` is a `Vector` of zero committees until
`initialize_ptc_window` replaces it. -/
def upgrade_to_gloas (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre : FuluState) :
    SpecM BeaconState := do
  let epoch ← get_current_epoch p pre.state
  let header := pre.latest_execution_payload_header
  let post : BeaconState := { pre.state with
    fork := { previous_version := pre.state.fork.current_version
              current_version := c.GLOAS_FORK_VERSION
              epoch }
    latest_block_hash := header.block_hash
    builders := []
    next_withdrawal_builder_index := 0
    execution_payload_availability := List.replicate p.SLOTS_PER_HISTORICAL_ROOT true
    builder_pending_payments := List.replicate (2 * p.SLOTS_PER_EPOCH) .empty
    builder_pending_withdrawals := []
    latest_execution_payload_bid := {
      parent_block_hash := header.parent_hash
      parent_block_root := pre.state.latest_block_header.parent_root
      block_hash := header.block_hash
      prev_randao := header.prev_randao
      fee_recipient := ExecutionAddress.zero
      gas_limit := header.gas_limit
      builder_index := BUILDER_INDEX_SELF_BUILD
      slot := pre.state.latest_block_header.slot
      value := 0
      execution_payment := 0
      blob_kzg_commitments := []
      execution_requests_root := c.empty_execution_requests_root }
    payload_expected_withdrawals := []
    ptc_window := List.replicate ((p.MIN_SEED_LOOKAHEAD + 2) * p.SLOTS_PER_EPOCH)
      (List.replicate p.PTC_SIZE 0) }
  let post := { post with ptc_window := ← initialize_ptc_window p o post }
  onboard_builders_from_pending_deposits p o post

end EpochProofs.Spec
