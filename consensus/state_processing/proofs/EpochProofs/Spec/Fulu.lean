import EpochProofs.Spec.EpochCommittees
import EpochProofs.Spec.PendingDeposits

/-!
# Reference: the Fulu epoch functions that differ from Gloas

Transcribed from `specs/electra/beacon-chain.md` and `specs/fulu/beacon-chain.md`
(v1.7.0-beta.4). Fulu reads the same `BeaconState` fields as Gloas in these functions, so they
take the Gloas `BeaconState` and ignore its Gloas-only fields.

`FuluConfig` holds the two config values that Fulu reads and Gloas does not.
-/

namespace EpochProofs.Spec

/-- The Fulu config values that `Preset` does not hold. The defaults are the mainnet values. -/
structure FuluConfig where
  CHURN_LIMIT_QUOTIENT : Uint64 := 65536
  MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT : Gwei := 256000000000

def FuluConfig.mainnet : FuluConfig := {}
def FuluConfig.minimal : FuluConfig :=
  { CHURN_LIMIT_QUOTIENT := 32, MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := 128000000000 }

/-- ```python
def get_balance_churn_limit(state: BeaconState) -> Gwei:
    churn = max(
        MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA, get_total_active_balance(state) // CHURN_LIMIT_QUOTIENT
    )
    return churn - churn % EFFECTIVE_BALANCE_INCREMENT
``` -/
def get_balance_churn_limit (p : Preset) (f : FuluConfig) (total_active_balance : Gwei) :
    SpecM Gwei := do
  let churn := max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    (← uint64Div total_active_balance f.CHURN_LIMIT_QUOTIENT)
  uint64Sub churn (← uint64Mod churn p.EFFECTIVE_BALANCE_INCREMENT)

/-- ```python
def get_activation_exit_churn_limit(state: BeaconState) -> Gwei:
    return min(MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT, get_balance_churn_limit(state))
``` -/
def get_activation_exit_churn_limit (p : Preset) (f : FuluConfig) (total_active_balance : Gwei) :
    SpecM Gwei := do
  pure (min f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
    (← get_balance_churn_limit p f total_active_balance))

/-- ```python
def compute_exit_epoch_and_update_churn(state: BeaconState, exit_balance: Gwei) -> Epoch:
    earliest_exit_epoch = max(
        state.earliest_exit_epoch, compute_activation_exit_epoch(get_current_epoch(state))
    )
    per_epoch_churn = get_activation_exit_churn_limit(state)
    # New epoch for exits.
    if state.earliest_exit_epoch < earliest_exit_epoch:
        exit_balance_to_consume = per_epoch_churn
    else:
        exit_balance_to_consume = state.exit_balance_to_consume

    # Exit doesn't fit in the current earliest epoch.
    if exit_balance > exit_balance_to_consume:
        balance_to_process = exit_balance - exit_balance_to_consume
        additional_epochs = (balance_to_process - 1) // per_epoch_churn + 1
        earliest_exit_epoch += Epoch(additional_epochs)
        exit_balance_to_consume += additional_epochs * per_epoch_churn

    # Consume the balance and update state variables.
    state.exit_balance_to_consume = exit_balance_to_consume - exit_balance
    state.earliest_exit_epoch = earliest_exit_epoch

    return state.earliest_exit_epoch
``` -/
def compute_exit_epoch_and_update_churn_fulu (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (state : BeaconState) (exit_balance : Gwei) :
    SpecM (Epoch × BeaconState) := do
  let mut earliest_exit_epoch := max state.earliest_exit_epoch
    (← compute_activation_exit_epoch p (← get_current_epoch p state))
  let per_epoch_churn ← get_activation_exit_churn_limit p f total_active_balance
  let mut exit_balance_to_consume :=
    if state.earliest_exit_epoch < earliest_exit_epoch then per_epoch_churn
    else state.exit_balance_to_consume

  if exit_balance > exit_balance_to_consume then
    let balance_to_process ← uint64Sub exit_balance exit_balance_to_consume
    let additional_epochs ←
      uint64Add (← uint64Div (← uint64Sub balance_to_process 1) per_epoch_churn) 1
    earliest_exit_epoch ← uint64Add earliest_exit_epoch additional_epochs
    exit_balance_to_consume ←
      uint64Add exit_balance_to_consume (← uint64Mul additional_epochs per_epoch_churn)

  let state := { state with
    exit_balance_to_consume := ← uint64Sub exit_balance_to_consume exit_balance
    earliest_exit_epoch }
  pure (state.earliest_exit_epoch, state)

/-- ```python
def process_pending_deposits(state: BeaconState) -> None:
    next_epoch = Epoch(get_current_epoch(state) + 1)
    available_for_processing = state.deposit_balance_to_consume + get_activation_exit_churn_limit(
        state
    )
    processed_amount = 0
    next_deposit_index = 0
    deposits_to_postpone = []
    is_churn_limit_reached = False
    finalized_slot = compute_start_slot_at_epoch(state.finalized_checkpoint.epoch)

    for deposit in state.pending_deposits:
        # Check if deposit has been finalized, otherwise, stop processing.
        if deposit.slot > finalized_slot:
            break

        # Check if number of processed deposits has not reached the limit, otherwise, stop processing.
        if next_deposit_index >= MAX_PENDING_DEPOSITS_PER_EPOCH:
            break

        # Read validator state
        is_validator_exited = False
        is_validator_withdrawn = False
        validator_pubkeys = [v.pubkey for v in state.validators]
        if deposit.pubkey in validator_pubkeys:
            validator = state.validators[ValidatorIndex(validator_pubkeys.index(deposit.pubkey))]
            is_validator_exited = validator.exit_epoch < FAR_FUTURE_EPOCH
            is_validator_withdrawn = validator.withdrawable_epoch < next_epoch

        if is_validator_withdrawn:
            # Deposited balance will never become active. Increase balance but do not consume churn
            apply_pending_deposit(state, deposit)
        elif is_validator_exited:
            # Validator is exiting, postpone the deposit until after withdrawable epoch
            deposits_to_postpone.append(deposit)
        else:
            # Check if deposit fits in the churn, otherwise, do no more deposit processing in this epoch.
            is_churn_limit_reached = processed_amount + deposit.amount > available_for_processing
            if is_churn_limit_reached:
                break

            # Consume churn and apply deposit.
            processed_amount += deposit.amount
            apply_pending_deposit(state, deposit)

        # Regardless of how the deposit was handled, we move on in the queue.
        next_deposit_index += 1

    state.pending_deposits = state.pending_deposits[next_deposit_index:] + deposits_to_postpone

    # Accumulate churn only if the churn limit has been hit.
    if is_churn_limit_reached:
        state.deposit_balance_to_consume = available_for_processing - processed_amount
    else:
        state.deposit_balance_to_consume = Gwei(0)
``` -/
def process_pending_deposits_fulu (p : Preset) (f : FuluConfig) (total_active_balance : Gwei)
    (apply_pending_deposit : BeaconState → PendingDeposit → SpecM BeaconState)
    (state : BeaconState) : SpecM BeaconState := do
  let next_epoch ← uint64Add (← get_current_epoch p state) 1
  let available_for_processing ←
    uint64Add state.deposit_balance_to_consume
      (← get_activation_exit_churn_limit p f total_active_balance)
  let mut processed_amount := 0
  let mut next_deposit_index := 0
  let mut deposits_to_postpone := []
  let mut is_churn_limit_reached := false
  let finalized_slot ← compute_start_slot_at_epoch p state.finalized_checkpoint.epoch

  let mut state := state
  for deposit in state.pending_deposits do
    if deposit.slot > finalized_slot then
      break

    if next_deposit_index ≥ p.MAX_PENDING_DEPOSITS_PER_EPOCH then
      break

    let mut is_validator_exited := false
    let mut is_validator_withdrawn := false
    let validator_pubkeys := state.validators.map (·.pubkey)
    if deposit.pubkey ∈ validator_pubkeys then
      let validator ← listGet state.validators (validator_pubkeys.idxOf deposit.pubkey)
      is_validator_exited := validator.exit_epoch < FAR_FUTURE_EPOCH
      is_validator_withdrawn := validator.withdrawable_epoch < next_epoch

    if is_validator_withdrawn then
      state ← apply_pending_deposit state deposit
    else if is_validator_exited then
      deposits_to_postpone := deposits_to_postpone ++ [deposit]
    else
      is_churn_limit_reached :=
        decide ((← uint64Add processed_amount deposit.amount) > available_for_processing)
      if is_churn_limit_reached then
        break
      processed_amount ← uint64Add processed_amount deposit.amount
      state ← apply_pending_deposit state deposit

    next_deposit_index := next_deposit_index + 1

  state := { state with
    pending_deposits := state.pending_deposits.drop next_deposit_index ++ deposits_to_postpone }

  if is_churn_limit_reached then
    state := { state with
      deposit_balance_to_consume := ← uint64Sub available_for_processing processed_amount }
  else
    state := { state with deposit_balance_to_consume := 0 }
  pure state

/-- The `while True` loop of `compute_proposer_index`, with at most `fuel` passes. It reads
`state.validators` as `validators`. `total` is
`Uint64(len(indices))`. As in `compute_balance_weighted_selection`, `UINT64_SIZE` fuel gives the
pyspec result: `i += 1` raises at `2**64 - 1`. -/
def compute_proposer_index_loop (p : Preset) (o : Oracle) (validators : List Validator)
    (indices : List ValidatorIndex) (seed : Bytes32) (total : Uint64) :
    Nat → Uint64 → SpecM ValidatorIndex
  | 0, _ => throw .overflow
  | fuel + 1, i => do
    let MAX_RANDOM_VALUE := 2 ^ 16 - 1
    let candidate_index ←
      listGet indices (← compute_shuffled_index p o (← uint64Mod i total) total seed)
    let random_bytes := o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))
    let offset ← uint64Mul (← uint64Mod i 16) 2
    let random_value ← bytes_to_uint64 ((random_bytes.toList.drop offset).take 2)
    let effective_balance := (← listGet validators candidate_index).effective_balance
    if (← uint64Mul effective_balance MAX_RANDOM_VALUE) ≥
        (← uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA random_value) then
      pure candidate_index
    else
      compute_proposer_index_loop p o validators indices seed total fuel (← uint64Add i 1)

/-- ```python
def compute_proposer_index(
    state: BeaconState, indices: Sequence[ValidatorIndex], seed: Bytes32
) -> ValidatorIndex:
    """
    Return from ``indices`` a random index sampled by effective balance.
    """
    assert len(indices) > 0
    # [Modified in Electra]
    MAX_RANDOM_VALUE = 2**16 - 1
    i = Uint64(0)
    total = Uint64(len(indices))
    while True:
        candidate_index = indices[compute_shuffled_index(i % total, total, seed)]
        # [Modified in Electra]
        random_bytes = sha256(seed + uint_to_bytes(i // 16))
        offset = i % 16 * 2
        random_value = bytes_to_uint64(random_bytes[offset : offset + 2])
        effective_balance = state.validators[candidate_index].effective_balance
        # [Modified in Electra:EIP7251]
        if effective_balance * MAX_RANDOM_VALUE >= MAX_EFFECTIVE_BALANCE_ELECTRA * random_value:
            return candidate_index
        i += 1
``` -/
def compute_proposer_index (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) : SpecM ValidatorIndex := do
  if ¬ indices.length > 0 then throw .assertionFailed
  compute_proposer_index_loop p o state.validators indices seed indices.length UINT64_SIZE 0

/-- ```python
def compute_proposer_indices(
    state: BeaconState, epoch: Epoch, seed: Bytes32, indices: Sequence[ValidatorIndex]
) -> ProposerIndices:
    """
    Return the proposer indices for the given ``epoch``.
    """
    start_slot = compute_start_slot_at_epoch(epoch)
    seeds = [sha256(seed + uint_to_bytes(start_slot + i)) for i in range(SLOTS_PER_EPOCH)]
    return ProposerIndices(data=[compute_proposer_index(state, indices, seed) for seed in seeds])
``` -/
def compute_proposer_indices_fulu (p : Preset) (o : Oracle) (state : BeaconState) (epoch : Epoch)
    (seed : Bytes32) (indices : List ValidatorIndex) : SpecM (List ValidatorIndex) := do
  let start_slot ← compute_start_slot_at_epoch p epoch
  let seeds ← (List.range p.SLOTS_PER_EPOCH).mapM fun i => do
    pure (o.hash (seed.toList ++ uint_to_bytes 8 (← uint64Add start_slot i)))
  seeds.mapM fun seed => compute_proposer_index p o state indices seed

/-- ```python
def get_beacon_proposer_indices(state: BeaconState, epoch: Epoch) -> ProposerIndices:
    """
    Return the proposer indices for the given ``epoch``.
    """
    indices = get_active_validator_indices(state, epoch)
    seed = get_seed(state, epoch, DOMAIN_BEACON_PROPOSER)
    return compute_proposer_indices(state, epoch, seed, indices)
``` -/
def get_beacon_proposer_indices_fulu (p : Preset) (o : Oracle) (state : BeaconState)
    (epoch : Epoch) : SpecM (List ValidatorIndex) := do
  let indices := get_active_validator_indices state epoch
  let seed ← get_seed p o state epoch DOMAIN_BEACON_PROPOSER
  compute_proposer_indices_fulu p o state epoch seed indices

/-- ```python
def process_proposer_lookahead(state: BeaconState) -> None:
    last_epoch_start = len(state.proposer_lookahead) - SLOTS_PER_EPOCH
    # Shift out proposers in the first epoch
    state.proposer_lookahead[:last_epoch_start] = state.proposer_lookahead[SLOTS_PER_EPOCH:]
    # Fill in the last epoch with new proposer indices
    last_epoch_proposers = get_beacon_proposer_indices(
        state, get_current_epoch(state) + MIN_SEED_LOOKAHEAD + 1
    )
    state.proposer_lookahead[last_epoch_start:] = last_epoch_proposers
``` -/
def process_proposer_lookahead_fulu (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM BeaconState := do
  let last_epoch_start ← uint64Sub state.proposer_lookahead.length p.SLOTS_PER_EPOCH
  let state := { state with
    proposer_lookahead := state.proposer_lookahead.drop p.SLOTS_PER_EPOCH ++
      state.proposer_lookahead.drop last_epoch_start }
  let last_epoch_proposers ← get_beacon_proposer_indices_fulu p o state
    (← uint64Add (← uint64Add (← get_current_epoch p state) p.MIN_SEED_LOOKAHEAD) 1)
  pure { state with
    proposer_lookahead := state.proposer_lookahead.take last_epoch_start ++ last_epoch_proposers }

/-- The `while` loop of the Electra `get_next_sync_committee_indices`, with at most `fuel`
passes. -/
def next_sync_committee_indices_loop (p : Preset) (o : Oracle) (validators : List Validator)
    (active_validator_indices : List ValidatorIndex) (seed : Bytes32)
    (active_validator_count : Uint64) :
    Nat → List ValidatorIndex → Uint64 → SpecM (List ValidatorIndex)
  | 0, _, _ => throw .overflow
  | fuel + 1, sync_committee_indices, i => do
    if sync_committee_indices.length < p.SYNC_COMMITTEE_SIZE then
      let MAX_RANDOM_VALUE := 2 ^ 16 - 1
      let shuffled_index ← compute_shuffled_index p o (← uint64Mod i active_validator_count)
        active_validator_count seed
      let candidate_index ← listGet active_validator_indices shuffled_index
      let random_bytes := o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))
      let offset ← uint64Mul (← uint64Mod i 16) 2
      let random_value ← bytes_to_uint64 ((random_bytes.toList.drop offset).take 2)
      let effective_balance := (← listGet validators candidate_index).effective_balance
      let sync_committee_indices ←
        if (← uint64Mul effective_balance MAX_RANDOM_VALUE) ≥
            (← uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA random_value) then
          pure (sync_committee_indices ++ [candidate_index])
        else pure sync_committee_indices
      next_sync_committee_indices_loop p o validators active_validator_indices seed
        active_validator_count fuel sync_committee_indices (← uint64Add i 1)
    else
      pure sync_committee_indices

/-- ```python
def get_next_sync_committee_indices(state: BeaconState) -> Sequence[ValidatorIndex]:
    """
    Return the sync committee indices, with possible duplicates, for the next sync committee.
    """
    epoch = get_current_epoch(state) + 1

    # [Modified in Electra]
    MAX_RANDOM_VALUE = 2**16 - 1
    active_validator_indices = get_active_validator_indices(state, epoch)
    active_validator_count = Uint64(len(active_validator_indices))
    seed = get_seed(state, epoch, DOMAIN_SYNC_COMMITTEE)
    i = Uint64(0)
    sync_committee_indices: list[ValidatorIndex] = []
    while len(sync_committee_indices) < SYNC_COMMITTEE_SIZE:
        shuffled_index = compute_shuffled_index(
            Uint64(i % active_validator_count), active_validator_count, seed
        )
        candidate_index = active_validator_indices[shuffled_index]
        # [Modified in Electra]
        random_bytes = sha256(seed + uint_to_bytes(i // 16))
        offset = i % 16 * 2
        random_value = bytes_to_uint64(random_bytes[offset : offset + 2])
        effective_balance = state.validators[candidate_index].effective_balance
        # [Modified in Electra:EIP7251]
        if effective_balance * MAX_RANDOM_VALUE >= MAX_EFFECTIVE_BALANCE_ELECTRA * random_value:
            sync_committee_indices.append(candidate_index)
        i += 1
    return sync_committee_indices
``` -/
def get_next_sync_committee_indices_fulu (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM (List ValidatorIndex) := do
  let epoch ← uint64Add (← get_current_epoch p state) 1
  let active_validator_indices := get_active_validator_indices state epoch
  let active_validator_count := active_validator_indices.length
  let seed ← get_seed p o state epoch DOMAIN_SYNC_COMMITTEE
  next_sync_committee_indices_loop p o state.validators active_validator_indices seed
    active_validator_count UINT64_SIZE [] 0

/-- ```python
def initiate_validator_exit(state: BeaconState, index: ValidatorIndex) -> None:
    # Return if validator already initiated exit
    validator = state.validators[index]
    if validator.exit_epoch != FAR_FUTURE_EPOCH:
        return

    # Compute exit queue epoch [Modified in Electra:EIP7251]
    exit_queue_epoch = compute_exit_epoch_and_update_churn(state, validator.effective_balance)

    # Set validator exit epoch and withdrawable epoch
    validator.exit_epoch = exit_queue_epoch
    validator.withdrawable_epoch = validator.exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY
``` -/
def initiate_validator_exit_fulu (p : Preset) (f : FuluConfig) (total_active_balance : Gwei)
    (state : BeaconState) (index : ValidatorIndex) : SpecM BeaconState := do
  let validator ← listGet state.validators index
  if validator.exit_epoch != FAR_FUTURE_EPOCH then
    return state

  let (exit_queue_epoch, state) ← compute_exit_epoch_and_update_churn_fulu p f total_active_balance
    state validator.effective_balance

  let validator := { validator with exit_epoch := exit_queue_epoch }
  let validator := { validator with
    withdrawable_epoch := ← uint64Add validator.exit_epoch p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY }
  pure { state with validators := ← listSet state.validators index validator }

/-- ```python
def process_registry_updates(state: BeaconState) -> None:
    current_epoch = get_current_epoch(state)
    activation_epoch = compute_activation_exit_epoch(current_epoch)

    # Process activation eligibility, ejections, and activations
    for index, validator in enumerate(state.validators):
        # [Modified in Electra:EIP7251]
        if is_eligible_for_activation_queue(validator):
            validator.activation_eligibility_epoch = current_epoch + 1
        elif (
            is_active_validator(validator, current_epoch)
            and validator.effective_balance <= EJECTION_BALANCE
        ):
            # [Modified in Electra:EIP7251]
            initiate_validator_exit(state, ValidatorIndex(index))
        elif is_eligible_for_activation(state, validator):
            validator.activation_epoch = activation_epoch
```

This is the Electra text, which Fulu keeps. It differs from Gloas only in the churn that
`initiate_validator_exit` reads. -/
def process_registry_updates_fulu (p : Preset) (f : FuluConfig) (total_active_balance : Gwei)
    (state : BeaconState) : SpecM BeaconState := do
  let current_epoch ← get_current_epoch p state
  let activation_epoch ← compute_activation_exit_epoch p current_epoch

  let mut state := state
  for index in List.range state.validators.length do
    let validator ← listGet state.validators index
    if is_eligible_for_activation_queue p validator then
      let validator := { validator with
        activation_eligibility_epoch := ← uint64Add current_epoch 1 }
      state := { state with validators := ← listSet state.validators index validator }
    else if is_active_validator validator current_epoch
        && validator.effective_balance ≤ p.EJECTION_BALANCE then
      state ← initiate_validator_exit_fulu p f total_active_balance state index
    else if is_eligible_for_activation state validator then
      let validator := { validator with activation_epoch }
      state := { state with validators := ← listSet state.validators index validator }
  pure state

/-- ```python
def get_next_sync_committee(state: BeaconState) -> SyncCommittee:
    """
    Return the next sync committee, with possible pubkey duplicates.
    """
    indices = get_next_sync_committee_indices(state)
    pubkeys = SyncCommitteePubkeys(data=[state.validators[index].pubkey for index in indices])
    aggregate_pubkey = eth_aggregate_pubkeys(pubkeys)
    return SyncCommittee(pubkeys=pubkeys, aggregate_pubkey=aggregate_pubkey)
```

The Altair text, with the Electra `get_next_sync_committee_indices`. -/
def get_next_sync_committee_fulu (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM SyncCommittee := do
  let indices ← get_next_sync_committee_indices_fulu p o state
  let pubkeys ← indices.mapM fun index => do pure (← listGet state.validators index).pubkey
  let aggregate_pubkey ← eth_aggregate_pubkeys o pubkeys
  pure { pubkeys, aggregate_pubkey }

/-- ```python
def process_sync_committee_updates(state: BeaconState) -> None:
    next_epoch = get_current_epoch(state) + 1
    if next_epoch % EPOCHS_PER_SYNC_COMMITTEE_PERIOD == 0:
        state.current_sync_committee = state.next_sync_committee
        state.next_sync_committee = get_next_sync_committee(state)
``` -/
def process_sync_committee_updates_fulu (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM BeaconState := do
  let next_epoch ← uint64Add (← get_current_epoch p state) 1
  if (← uint64Mod next_epoch p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) == 0 then
    let state := { state with current_sync_committee := state.next_sync_committee }
    pure { state with next_sync_committee := ← get_next_sync_committee_fulu p o state }
  else
    pure state

end EpochProofs.Spec
