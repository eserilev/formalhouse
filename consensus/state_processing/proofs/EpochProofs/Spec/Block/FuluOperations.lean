import EpochProofs.Spec.Block.FuluTypes
import EpochProofs.Spec.Block.Exits
import EpochProofs.Spec.Block.ExecutionRequests
import EpochProofs.Spec.Block.Attestations

/-!
# Reference: the Fulu block operations

Transcribed from `specs/phase0`, `specs/deneb`, `specs/electra` and
`specs/fulu/beacon-chain.md` (v1.7.0-beta.2).

Most Fulu operations have the same pyspec text as the Gloas versions in `Block/*`. They differ
because the functions they call differ in Fulu:
- `initiate_validator_exit` and `compute_exit_epoch_and_update_churn` use the Electra
  activation-exit churn (`initiate_validator_exit_fulu`, `compute_exit_epoch_and_update_churn_fulu`
  in `Spec/Fulu`).
- `get_consolidation_churn_limit` is the Electra version.
Each such function here says which text it shares.

Fulu reuses unchanged: `process_bls_to_execution_change`, `process_deposit_request`,
`is_valid_indexed_attestation`, `is_valid_switch_to_compounding_request`,
`switch_to_compounding_validator` and `get_pending_balance_to_withdraw`.

`is_valid_indexed_attestation` gained a length check in Gloas (EIP-7688). In Fulu the
`attesting_indices` list has the same limit as an SSZ type, so the check never fails on a
decodable Fulu block. In the same way, Fulu `process_operations` has no length asserts,
because the SSZ types bound each operation list.
-/

namespace EpochProofs.Spec

/-- `slash_validator` with the Fulu `initiate_validator_exit`. The pyspec text is the Electra
`slash_validator`, quoted at `slash_validator` in `Block/Slashings`. As there, the total
active balance is read only on the path where Python reads it. -/
def slash_validator_fulu (p : Preset) (f : FuluConfig) (state : BeaconState)
    (slashed_index : ValidatorIndex) (whistleblower_index : Option ValidatorIndex := none) :
    SpecM BeaconState := do
  let epoch ← get_current_epoch p state
  let state ← do
    let validator ← listGet state.validators slashed_index
    if validator.exit_epoch != FAR_FUTURE_EPOCH then pure state
    else
      initiate_validator_exit_fulu p f (← get_total_active_balance p state) state slashed_index
  let validator ← listGet state.validators slashed_index
  let validator := { validator with slashed := true }
  let validator := { validator with
    withdrawable_epoch :=
      max validator.withdrawable_epoch (← uint64Add epoch p.EPOCHS_PER_SLASHINGS_VECTOR) }
  let state := { state with validators := ← listSet state.validators slashed_index validator }
  let slashings_index ← uint64Mod epoch p.EPOCHS_PER_SLASHINGS_VECTOR
  let state := { state with
    slashings := ← listSet state.slashings slashings_index
      (← uint64Add (← listGet state.slashings slashings_index) validator.effective_balance) }
  let slashing_penalty ←
    uint64Div validator.effective_balance p.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA
  let state := { state with
    balances := ← decrease_balance state.balances slashed_index slashing_penalty }

  let proposer_index ← get_beacon_proposer_index p state
  let whistleblower_index := match whistleblower_index with
    | none => proposer_index
    | some i => i
  let whistleblower_reward ←
    uint64Div validator.effective_balance p.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA
  let proposer_reward ←
    uint64Div (← uint64Mul whistleblower_reward PROPOSER_WEIGHT) WEIGHT_DENOMINATOR
  let state := { state with
    balances := ← increase_balance state.balances proposer_index proposer_reward }
  let state := { state with
    balances := ← increase_balance state.balances whistleblower_index
      (← uint64Sub whistleblower_reward proposer_reward) }
  pure state

/-- ```python
def process_proposer_slashing(state: BeaconState, proposer_slashing: ProposerSlashing) -> None:
    header_1 = proposer_slashing.signed_header_1.message
    header_2 = proposer_slashing.signed_header_2.message

    # Verify header slots match
    assert header_1.slot == header_2.slot
    # Verify header proposer indices match
    assert header_1.proposer_index == header_2.proposer_index
    # Verify the headers are different
    assert header_1 != header_2
    # Verify the proposer is slashable
    proposer = state.validators[header_1.proposer_index]
    assert is_slashable_validator(proposer, get_current_epoch(state))
    # Verify signatures
    for signed_header in (proposer_slashing.signed_header_1, proposer_slashing.signed_header_2):
        domain = get_domain(
            state, DOMAIN_BEACON_PROPOSER, compute_epoch_at_slot(signed_header.message.slot)
        )
        signing_root = compute_signing_root(signed_header.message, domain)
        assert bls.Verify(proposer.pubkey, signing_root, signed_header.signature)

    slash_validator(state, header_1.proposer_index)
```

This is the phase0 text. Gloas adds the builder payment clearing. -/
def process_proposer_slashing_fulu (p : Preset) (o : Oracle) (f : FuluConfig)
    (state : BeaconState) (proposer_slashing : ProposerSlashing) : SpecM BeaconState := do
  let header_1 := proposer_slashing.signed_header_1.message
  let header_2 := proposer_slashing.signed_header_2.message

  if ¬ header_1.slot = header_2.slot then throw .assertionFailed
  if ¬ header_1.proposer_index = header_2.proposer_index then throw .assertionFailed
  if ¬ header_1 ≠ header_2 then throw .assertionFailed
  let proposer ← listGet state.validators header_1.proposer_index
  if ¬ is_slashable_validator proposer (← get_current_epoch p state) then throw .assertionFailed
  for signed_header in [proposer_slashing.signed_header_1, proposer_slashing.signed_header_2] do
    let domain ← get_domain p o state DOMAIN_BEACON_PROPOSER
      (some (← compute_epoch_at_slot p signed_header.message.slot))
    let signing_root :=
      compute_signing_root o (o.hash_tree_root_BeaconBlockHeader signed_header.message) domain
    if ¬ o.bls_Verify proposer.pubkey signing_root signed_header.signature then
      throw .assertionFailed

  slash_validator_fulu p f state header_1.proposer_index

/-- `process_attester_slashing` with the Fulu `slash_validator`. The pyspec text is the
phase0 text, quoted at `process_attester_slashing` in `Block/Slashings`. -/
def process_attester_slashing_fulu (p : Preset) (o : Oracle) (f : FuluConfig)
    (state : BeaconState) (attester_slashing : AttesterSlashing) : SpecM BeaconState := do
  let attestation_1 := attester_slashing.attestation_1
  let attestation_2 := attester_slashing.attestation_2
  if ¬ is_slashable_attestation_data attestation_1.data attestation_2.data then
    throw .assertionFailed
  if ¬ (← is_valid_indexed_attestation p o state attestation_1) then
    throw .assertionFailed
  if ¬ (← is_valid_indexed_attestation p o state attestation_2) then
    throw .assertionFailed

  let mut slashed_any := false
  let indices := (attestation_1.attesting_indices.filter
    (· ∈ attestation_2.attesting_indices)).eraseDups
  let mut state := state
  for index in indices.mergeSort do
    if is_slashable_validator (← listGet state.validators index) (← get_current_epoch p state) then
      state ← slash_validator_fulu p f state index
      slashed_any := true
  if ¬ slashed_any then throw .assertionFailed
  pure state

/-- ```python
def get_attestation_participation_flag_indices(
    state: BeaconState, data: AttestationData, inclusion_delay: Uint64
) -> Sequence[int]:
    """
    Return the flag indices that are satisfied by an attestation.
    """
    # Matching source
    if data.target.epoch == get_current_epoch(state):
        justified_checkpoint = state.current_justified_checkpoint
    else:
        justified_checkpoint = state.previous_justified_checkpoint
    is_matching_source = data.source == justified_checkpoint

    # Matching target
    target_root = get_block_root(state, data.target.epoch)
    target_root_matches = data.target.root == target_root
    is_matching_target = is_matching_source and target_root_matches

    # Matching head
    head_root = get_block_root_at_slot(state, data.slot)
    head_root_matches = data.beacon_block_root == head_root
    is_matching_head = is_matching_target and head_root_matches

    assert is_matching_source

    participation_flag_indices = []
    if is_matching_source and inclusion_delay <= integer_squareroot(SLOTS_PER_EPOCH):
        participation_flag_indices.append(TIMELY_SOURCE_FLAG_INDEX)
    # [Modified in Deneb:EIP7045]
    if is_matching_target:
        participation_flag_indices.append(TIMELY_TARGET_FLAG_INDEX)
    if is_matching_head and inclusion_delay == MIN_ATTESTATION_INCLUSION_DELAY:
        participation_flag_indices.append(TIMELY_HEAD_FLAG_INDEX)

    return participation_flag_indices
```

This is the Deneb text. Gloas adds the payload match to the head flag. -/
def get_attestation_participation_flag_indices_fulu (p : Preset) (state : BeaconState)
    (data : AttestationData) (inclusion_delay : Uint64) : SpecM (List Nat) := do
  let justified_checkpoint :=
    if data.target.epoch == (← get_current_epoch p state) then state.current_justified_checkpoint
    else state.previous_justified_checkpoint
  let is_matching_source := data.source == justified_checkpoint

  let target_root ← get_block_root p state data.target.epoch
  let target_root_matches := data.target.root == target_root
  let is_matching_target := is_matching_source && target_root_matches

  let head_root ← get_block_root_at_slot p state data.slot
  let head_root_matches := data.beacon_block_root == head_root
  let is_matching_head := is_matching_target && head_root_matches

  if ¬ is_matching_source then throw .assertionFailed

  let mut participation_flag_indices := []
  if is_matching_source && inclusion_delay ≤ integer_squareroot p.SLOTS_PER_EPOCH then
    participation_flag_indices := participation_flag_indices ++ [TIMELY_SOURCE_FLAG_INDEX]
  if is_matching_target then
    participation_flag_indices := participation_flag_indices ++ [TIMELY_TARGET_FLAG_INDEX]
  if is_matching_head && inclusion_delay == p.MIN_ATTESTATION_INCLUSION_DELAY then
    participation_flag_indices := participation_flag_indices ++ [TIMELY_HEAD_FLAG_INDEX]

  pure participation_flag_indices

/-- The asserts of the Electra `process_attestation`, up to the signature check. It returns
`participation_flag_indices`. -/
def process_attestation_checks_fulu (p : Preset) (o : Oracle) (state : BeaconState)
    (attestation : Attestation) : SpecM (List Nat) := do
  let data := attestation.data
  let previous_epoch ← get_previous_epoch p state
  let current_epoch ← get_current_epoch p state
  if !(data.target.epoch == previous_epoch || data.target.epoch == current_epoch) then
    throw .assertionFailed
  if ¬ data.target.epoch = (← compute_epoch_at_slot p data.slot) then throw .assertionFailed
  if ¬ (← uint64Add data.slot p.MIN_ATTESTATION_INCLUSION_DELAY) ≤ state.slot then
    throw .assertionFailed

  if ¬ data.index = 0 then throw .assertionFailed
  let committee_indices := get_committee_indices attestation.committee_bits
  let mut committee_offset := 0
  for committee_index in committee_indices do
    if ¬ committee_index < (← get_committee_count_per_slot p state data.target.epoch) then
      throw .assertionFailed
    let committee ← get_beacon_committee p o state data.slot committee_index
    let attesters ← committee_attesters attestation.aggregation_bits committee_offset committee
    if ¬ attesters.length > 0 then throw .assertionFailed
    committee_offset := committee_offset + committee.length

  if ¬ attestation.aggregation_bits.length = committee_offset then throw .assertionFailed

  let participation_flag_indices ← get_attestation_participation_flag_indices_fulu p state data
    (← uint64Sub state.slot data.slot)

  if ¬ (← is_valid_indexed_attestation p o state (← get_indexed_attestation p o state attestation))
  then throw .assertionFailed

  pure participation_flag_indices

/-- The loop over the attesters of the Electra `process_attestation`. It returns the new
`epoch_participation` and `proposer_reward_numerator`. `get_base_reward` reads `state`, and the
loop writes only `epoch_participation`, so it reads the input `state`. -/
def process_attestation_loop_fulu (p : Preset) (state : BeaconState)
    (participation_flag_indices : List Nat) (attesting_indices : List ValidatorIndex)
    (epoch_participation : List ParticipationFlags) :
    SpecM (List ParticipationFlags × Gwei) := do
  let mut epoch_participation := epoch_participation
  let mut proposer_reward_numerator := 0
  for index in attesting_indices do
    for (weight, flag_index) in PARTICIPATION_FLAG_WEIGHTS.zipIdx do
      if flag_index ∈ participation_flag_indices then
        if !(← has_flag (← listGet epoch_participation index) flag_index) then
          epoch_participation ← listSet epoch_participation index
            (← add_flag (← listGet epoch_participation index) flag_index)
          let base_reward ←
            get_base_reward p (← get_total_active_balance p state) state index
          proposer_reward_numerator ←
            uint64Add proposer_reward_numerator (← uint64Mul base_reward weight)
  pure (epoch_participation, proposer_reward_numerator)

/-- ```python
def process_attestation(state: BeaconState, attestation: Attestation) -> None:
    data = attestation.data
    assert data.target.epoch in (get_previous_epoch(state), get_current_epoch(state))
    assert data.target.epoch == compute_epoch_at_slot(data.slot)
    assert data.slot + MIN_ATTESTATION_INCLUSION_DELAY <= state.slot

    # [Modified in Electra:EIP7549]
    assert data.index == 0
    committee_indices = get_committee_indices(attestation.committee_bits)
    committee_offset = 0
    for committee_index in committee_indices:
        assert committee_index < get_committee_count_per_slot(state, data.target.epoch)
        committee = get_beacon_committee(state, data.slot, committee_index)
        committee_attesters = {
            attester_index
            for i, attester_index in enumerate(committee)
            if attestation.aggregation_bits[committee_offset + i]
        }
        assert len(committee_attesters) > 0
        committee_offset += len(committee)

    # Bitfield length matches total number of participants
    assert len(attestation.aggregation_bits) == committee_offset

    # Participation flag indices
    participation_flag_indices = get_attestation_participation_flag_indices(
        state, data, state.slot - data.slot
    )

    # Verify signature
    assert is_valid_indexed_attestation(state, get_indexed_attestation(state, attestation))

    # Update epoch participation flags
    if data.target.epoch == get_current_epoch(state):
        epoch_participation = state.current_epoch_participation
    else:
        epoch_participation = state.previous_epoch_participation

    proposer_reward_numerator = 0
    for index in get_attesting_indices(state, attestation):
        for flag_index, weight in enumerate(PARTICIPATION_FLAG_WEIGHTS):
            if flag_index in participation_flag_indices and not has_flag(
                epoch_participation[index], flag_index
            ):
                epoch_participation[index] = add_flag(epoch_participation[index], flag_index)
                proposer_reward_numerator += get_base_reward(state, index) * weight

    # Reward proposer
    proposer_reward_denominator = (
        (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR // PROPOSER_WEIGHT
    )
    proposer_reward = Gwei(proposer_reward_numerator // proposer_reward_denominator)
    increase_balance(state, get_beacon_proposer_index(state), proposer_reward)
```

The asserts are `process_attestation_checks_fulu`. The loop is
`process_attestation_loop_fulu`. `epoch_participation` is a view of a state field, so the
reference writes it back to that field. -/
def process_attestation_fulu (p : Preset) (o : Oracle) (state : BeaconState)
    (attestation : Attestation) : SpecM BeaconState := do
  let data := attestation.data
  let participation_flag_indices ← process_attestation_checks_fulu p o state attestation

  let current_epoch_target := data.target.epoch == (← get_current_epoch p state)
  let epoch_participation :=
    if current_epoch_target then state.current_epoch_participation
    else state.previous_epoch_participation

  let (epoch_participation, proposer_reward_numerator) ←
    process_attestation_loop_fulu p state participation_flag_indices
      (← get_attesting_indices p o state attestation) epoch_participation

  let proposer_reward_denominator ← uint64Div
    (← uint64Mul (← uint64Sub WEIGHT_DENOMINATOR PROPOSER_WEIGHT) WEIGHT_DENOMINATOR)
    PROPOSER_WEIGHT
  let proposer_reward ← uint64Div proposer_reward_numerator proposer_reward_denominator
  let balances ←
    increase_balance state.balances (← get_beacon_proposer_index p state) proposer_reward

  if current_epoch_target then
    pure { state with current_epoch_participation := epoch_participation, balances }
  else
    pure { state with previous_epoch_participation := epoch_participation, balances }

/-- `process_voluntary_exit` with the Fulu `initiate_validator_exit`. The pyspec text is the
Electra text, quoted at `process_voluntary_exit` in `Block/Exits`. -/
def process_voluntary_exit_fulu (p : Preset) (o : Oracle) (f : FuluConfig) (state : BeaconState)
    (signed_voluntary_exit : SignedVoluntaryExit) : SpecM BeaconState := do
  let voluntary_exit := signed_voluntary_exit.message
  let validator ← listGet state.validators voluntary_exit.validator_index
  if ¬ is_active_validator validator (← get_current_epoch p state) then throw .assertionFailed
  if ¬ validator.exit_epoch = FAR_FUTURE_EPOCH then throw .assertionFailed
  if ¬ (← get_current_epoch p state) ≥ voluntary_exit.epoch then throw .assertionFailed
  if ¬ (← get_current_epoch p state) ≥
      (← uint64Add validator.activation_epoch p.SHARD_COMMITTEE_PERIOD) then
    throw .assertionFailed
  if ¬ (← get_pending_balance_to_withdraw state voluntary_exit.validator_index) = 0 then
    throw .assertionFailed
  let domain := compute_domain p o DOMAIN_VOLUNTARY_EXIT (some p.CAPELLA_FORK_VERSION)
    (some state.genesis_validators_root)
  let signing_root :=
    compute_signing_root o (o.hash_tree_root_VoluntaryExit voluntary_exit) domain
  if ¬ o.bls_Verify validator.pubkey signing_root signed_voluntary_exit.signature then
    throw .assertionFailed
  initiate_validator_exit_fulu p f (← get_total_active_balance p state) state
    voluntary_exit.validator_index

/-- `process_withdrawal_request` with the Fulu `initiate_validator_exit` and
`compute_exit_epoch_and_update_churn`. The pyspec text is the Electra text, quoted at
`process_withdrawal_request` in `Block/ExecutionRequests`. -/
def process_withdrawal_request_fulu (p : Preset) (f : FuluConfig) (state : BeaconState)
    (withdrawal_request : WithdrawalRequest) : SpecM BeaconState := do
  let amount := withdrawal_request.amount
  let is_full_exit_request := amount == FULL_EXIT_REQUEST_AMOUNT

  if state.pending_partial_withdrawals.length == p.PENDING_PARTIAL_WITHDRAWALS_LIMIT
      && !is_full_exit_request then
    return state

  let validator_pubkeys := state.validators.map (·.pubkey)
  let request_pubkey := withdrawal_request.validator_pubkey
  if request_pubkey ∉ validator_pubkeys then
    return state
  let index := validator_pubkeys.idxOf request_pubkey
  let validator ← listGet state.validators index

  let has_correct_credential := has_execution_withdrawal_credential validator
  let is_correct_source_address :=
    withdrawalAddress validator.withdrawal_credentials
      == withdrawal_request.source_address
  if !(has_correct_credential && is_correct_source_address) then
    return state
  if !is_active_validator validator (← get_current_epoch p state) then
    return state
  if validator.exit_epoch != FAR_FUTURE_EPOCH then
    return state
  if (← get_current_epoch p state)
      < (← uint64Add validator.activation_epoch p.SHARD_COMMITTEE_PERIOD) then
    return state

  let pending_balance_to_withdraw ← get_pending_balance_to_withdraw state index

  if is_full_exit_request then
    if pending_balance_to_withdraw == 0 then
      return ← initiate_validator_exit_fulu p f (← get_total_active_balance p state) state index
    return state

  let has_sufficient_effective_balance := validator.effective_balance ≥ p.MIN_ACTIVATION_BALANCE
  let has_excess_balance := (← listGet state.balances index)
    > (← uint64Add p.MIN_ACTIVATION_BALANCE pending_balance_to_withdraw)

  if has_compounding_withdrawal_credential validator && has_sufficient_effective_balance
      && has_excess_balance then
    let to_withdraw := min (← uint64Sub (← uint64Sub (← listGet state.balances index)
      p.MIN_ACTIVATION_BALANCE) pending_balance_to_withdraw) amount
    let (exit_queue_epoch, state) ← compute_exit_epoch_and_update_churn_fulu p f
      (← get_total_active_balance p state) state to_withdraw
    let withdrawable_epoch ← uint64Add exit_queue_epoch p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
    pure { state with
      pending_partial_withdrawals := state.pending_partial_withdrawals ++ [{
        validator_index := index
        amount := to_withdraw
        withdrawable_epoch }] }
  else
    pure state

/-- ```python
def get_consolidation_churn_limit(state: BeaconState) -> Gwei:
    return get_balance_churn_limit(state) - get_activation_exit_churn_limit(state)
```

This is the Electra text. Gloas uses `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`. -/
def get_consolidation_churn_limit_fulu (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) : SpecM Gwei := do
  uint64Sub (← get_balance_churn_limit p f total_active_balance)
    (← get_activation_exit_churn_limit p f total_active_balance)

/-- `compute_consolidation_epoch_and_update_churn` with the Electra
`get_consolidation_churn_limit`. The pyspec text is the Electra text, quoted at
`compute_consolidation_epoch_and_update_churn` in `Block/ExecutionRequests`. -/
def compute_consolidation_epoch_and_update_churn_fulu (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (state : BeaconState) (consolidation_balance : Gwei) :
    SpecM (Epoch × BeaconState) := do
  let mut earliest_consolidation_epoch := max state.earliest_consolidation_epoch
    (← compute_activation_exit_epoch p (← get_current_epoch p state))
  let per_epoch_consolidation_churn ←
    get_consolidation_churn_limit_fulu p f total_active_balance
  let mut consolidation_balance_to_consume :=
    if state.earliest_consolidation_epoch < earliest_consolidation_epoch then
      per_epoch_consolidation_churn
    else state.consolidation_balance_to_consume

  if consolidation_balance > consolidation_balance_to_consume then
    let balance_to_process ← uint64Sub consolidation_balance consolidation_balance_to_consume
    let additional_epochs ← uint64Add
      (← uint64Div (← uint64Sub balance_to_process 1) per_epoch_consolidation_churn) 1
    earliest_consolidation_epoch ← uint64Add earliest_consolidation_epoch additional_epochs
    consolidation_balance_to_consume ← uint64Add consolidation_balance_to_consume
      (← uint64Mul additional_epochs per_epoch_consolidation_churn)

  let state := { state with
    consolidation_balance_to_consume :=
      ← uint64Sub consolidation_balance_to_consume consolidation_balance
    earliest_consolidation_epoch }
  pure (state.earliest_consolidation_epoch, state)

/-- `process_consolidation_request` with the Electra consolidation churn. The pyspec text is
the Electra text, quoted at `process_consolidation_request` in `Block/ExecutionRequests`. -/
def process_consolidation_request_fulu (p : Preset) (f : FuluConfig) (state : BeaconState)
    (consolidation_request : ConsolidationRequest) : SpecM BeaconState := do
  if ← is_valid_switch_to_compounding_request p state consolidation_request then
    let validator_pubkeys := state.validators.map (·.pubkey)
    let request_source_pubkey := consolidation_request.source_pubkey
    let source_index := validator_pubkeys.idxOf request_source_pubkey
    switch_to_compounding_validator p state source_index
  else

  if consolidation_request.source_pubkey == consolidation_request.target_pubkey then
    pure state else
  if state.pending_consolidations.length == p.PENDING_CONSOLIDATIONS_LIMIT then
    pure state else
  if (← get_consolidation_churn_limit_fulu p f (← get_total_active_balance p state))
      ≤ p.MIN_ACTIVATION_BALANCE then
    pure state else

  let validator_pubkeys := state.validators.map (·.pubkey)
  let request_source_pubkey := consolidation_request.source_pubkey
  let request_target_pubkey := consolidation_request.target_pubkey
  if request_source_pubkey ∉ validator_pubkeys then
    pure state else
  if request_target_pubkey ∉ validator_pubkeys then
    pure state else
  let source_index := validator_pubkeys.idxOf request_source_pubkey
  let target_index := validator_pubkeys.idxOf request_target_pubkey
  let source_validator ← listGet state.validators source_index
  let target_validator ← listGet state.validators target_index

  let has_correct_credential := has_execution_withdrawal_credential source_validator
  let is_correct_source_address :=
    withdrawalAddress source_validator.withdrawal_credentials
      == consolidation_request.source_address
  if !(has_correct_credential && is_correct_source_address) then
    pure state else

  if !has_compounding_withdrawal_credential target_validator then
    pure state else

  let current_epoch ← get_current_epoch p state
  if !is_active_validator source_validator current_epoch then
    pure state else
  if !is_active_validator target_validator current_epoch then
    pure state else
  if source_validator.exit_epoch != FAR_FUTURE_EPOCH then
    pure state else
  if target_validator.exit_epoch != FAR_FUTURE_EPOCH then
    pure state else
  if current_epoch < (← uint64Add source_validator.activation_epoch p.SHARD_COMMITTEE_PERIOD) then
    pure state else
  if (← get_pending_balance_to_withdraw state source_index) > 0 then
    pure state else

  let (exit_epoch, state) ← compute_consolidation_epoch_and_update_churn_fulu p f
    (← get_total_active_balance p state) state source_validator.effective_balance
  let source_validator := { source_validator with exit_epoch }
  let source_validator := { source_validator with
    withdrawable_epoch :=
      ← uint64Add source_validator.exit_epoch p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY }
  let state := { state with
    validators := ← listSet state.validators source_index source_validator }
  pure { state with
    pending_consolidations := state.pending_consolidations ++ [{ source_index, target_index }] }

/-- ```python
def process_operations(state: BeaconState, body: BeaconBlockBody) -> None:
    # [Modified in Fulu]
    assert len(body.deposits) == 0

    def for_ops(operations: Sequence[Any], fn: Callable[[BeaconState, Any], None]) -> None:
        for operation in operations:
            fn(state, operation)

    for_ops(body.proposer_slashings, process_proposer_slashing)
    for_ops(body.attester_slashings, process_attester_slashing)
    for_ops(body.attestations, process_attestation)
    # [Modified in Fulu]
    # Removed `process_deposit`
    for_ops(body.voluntary_exits, process_voluntary_exit)
    for_ops(body.bls_to_execution_changes, process_bls_to_execution_change)
    for_ops(body.execution_requests.deposits, process_deposit_request)
    for_ops(body.execution_requests.withdrawals, process_withdrawal_request)
    for_ops(body.execution_requests.consolidations, process_consolidation_request)
```

Each `for_ops` is a `List.foldlM`. -/
def process_operations_fulu (p : Preset) (o : Oracle) (f : FuluConfig) (state : BeaconState)
    (body : FuluBeaconBlockBody) : SpecM BeaconState := do
  if ¬ body.deposits.length = 0 then throw .assertionFailed

  let state ← body.proposer_slashings.foldlM (process_proposer_slashing_fulu p o f) state
  let state ← body.attester_slashings.foldlM (process_attester_slashing_fulu p o f) state
  let state ← body.attestations.foldlM (process_attestation_fulu p o) state
  let state ← body.voluntary_exits.foldlM (process_voluntary_exit_fulu p o f) state
  let state ← body.bls_to_execution_changes.foldlM (process_bls_to_execution_change p o) state
  let state ← body.execution_requests.deposits.foldlM process_deposit_request state
  let state ← body.execution_requests.withdrawals.foldlM (process_withdrawal_request_fulu p f) state
  body.execution_requests.consolidations.foldlM (process_consolidation_request_fulu p f) state

end EpochProofs.Spec
