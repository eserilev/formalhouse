import EpochProofs.Spec.Block.Types
import EthCLSpecs.Proofs.Gloas.Run
import EpochProofs.Etheorem.Forks
import EthCLSpecs.Proofs.Fulu.Run

/-!
# The map from an Etheorem state to a reference state

Etheorem (https://github.com/etheorem/etheorem) stores numbers as `UInt64` and lists as
`Vector`, `SSZList` and `Bitvector`. The reference stores numbers as `Nat` and lists as `List`.
`absEState` reads an Etheorem `BeaconState` as a reference `BeaconState`. It keeps every field.

Fulu's `absEState` keeps every Fulu field. The reference fields that Gloas adds (builders,
builder payments and withdrawals, the bid, the payload withdrawals, the PTC window) read as
empty, and `latest_block_hash` reads the block hash of the latest execution payload header. No
Fulu epoch step reads or writes them.

Each step proof states that the two runs agree through `absEState`. The `@[simp]` lemmas here
read and write one field through the map.

Each proof here holds for Gloas and for Fulu. `forkproof EpochEtheorem` (see `Forks.lean`)
elaborates the shared text once per fork, and `forkonly` holds the parts that differ.
-/

forkproof EpochEtheorem

open EthCLLib.Spec SizzLean.Repr

/-- A `Bitvector` as a list of bits, bit 0 first. Etheorem reads bit `i` with `getLsbD i`. -/
def absBits {n : Nat} (b : Bitvector n) : List Bool :=
  (List.range n).map b.data.getLsbD

/-! ## List reads and writes through the map -/

theorem getElem?_map_toList {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) (i : Nat) :
    (xs.toList.map f)[i]? = xs.val[i]?.map f := by
  simp

/-- `SSZList.set!` is `List.set` under the map. Past the end both leave the list unchanged. -/
theorem map_toList_set! {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) (i : Nat)
    (a : α) : (xs.set! i a).toList.map f = (xs.toList.map f).set i (f a) := by
  simp [SSZList.toList, List.map_set]

/-- The total read `xs[i]!` on an `SSZList` is the read on its array. -/
theorem sszList_getElem!_val {α : Type} [Inhabited α] {cap : Nat} (xs : SSZList α cap) (i : Nat) :
    xs[i]! = xs.val[i]! := by
  by_cases h : i < xs.val.size
  · rw [getElem!_pos xs i h, getElem!_pos xs.val i h]; rfl
  · rw [getElem!_neg xs i h, getElem!_neg xs.val i h]

theorem length_map_toList {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) :
    (xs.toList.map f).length = xs.val.size := by
  simp

/-- An `SSZList` holds at most `cap` items. -/
theorem length_map_toList_le {α β : Type} {cap : Nat} (f : α → β) (xs : SSZList α cap) :
    (xs.toList.map f).length ≤ cap := by
  simpa using xs.property

theorem absBits_length {n : Nat} (b : Bitvector n) : (absBits b).length = n := by
  simp [absBits]

theorem absBits_getElem? {n : Nat} (b : Bitvector n) (i : Nat) (hi : i < n) :
    (absBits b)[i]? = some (bitGet b i) := by
  simp [absBits, bitGet, hi]

variable [EthCLSpecs.Gloas.Preset]

forkonly Gloas
abbrev EState := EthCLSpecs.Gloas.BeaconState
abbrev EWithdrawal := EthCLSpecs.Gloas.BuilderPendingWithdrawal
abbrev EPayment := EthCLSpecs.Gloas.BuilderPendingPayment
end forkonly

forkonly Fulu
abbrev EState := EthCLSpecs.Fulu.BeaconState
end forkonly

def absValidator (v : EthCLSpecs.Gloas.Validator) : Spec.Validator :=
  { pubkey := v.pubkey
    withdrawal_credentials := v.withdrawalCredentials
    effective_balance := v.effectiveBalance.toNat
    slashed := v.slashed
    activation_eligibility_epoch := v.activationEligibilityEpoch.toNat
    activation_epoch := v.activationEpoch.toNat
    exit_epoch := v.exitEpoch.toNat
    withdrawable_epoch := v.withdrawableEpoch.toNat }

def absPendingDeposit (d : EthCLSpecs.Gloas.PendingDeposit) : Spec.PendingDeposit :=
  { pubkey := d.pubkey
    withdrawal_credentials := d.withdrawalCredentials
    amount := d.amount.toNat
    signature := d.signature
    slot := d.slot.toNat }

def absPendingPartialWithdrawal (w : EthCLSpecs.Gloas.PendingPartialWithdrawal) :
    Spec.PendingPartialWithdrawal :=
  { validator_index := w.validatorIndex.toNat
    amount := w.amount.toNat
    withdrawable_epoch := w.withdrawableEpoch.toNat }

def absPendingConsolidation (c : EthCLSpecs.Gloas.PendingConsolidation) :
    Spec.PendingConsolidation :=
  { source_index := c.sourceIndex.toNat
    target_index := c.targetIndex.toNat }

def absCheckpoint (c : EthCLSpecs.Gloas.Checkpoint) : Spec.Checkpoint :=
  { epoch := c.epoch.toNat, root := c.root }

def absFork (f : EthCLSpecs.Gloas.Fork) : Spec.Fork :=
  { previous_version := f.previousVersion
    current_version := f.currentVersion
    epoch := f.epoch.toNat }

def absHeader (h : EthCLSpecs.Gloas.BeaconBlockHeader) : Spec.BeaconBlockHeader :=
  { slot := h.slot.toNat
    proposer_index := h.proposerIndex.toNat
    parent_root := h.parentRoot
    state_root := h.stateRoot
    body_root := h.bodyRoot }

def absEth1Data (d : EthCLSpecs.Gloas.Eth1Data) : Spec.Eth1Data :=
  { deposit_root := d.depositRoot
    deposit_count := d.depositCount.toNat
    block_hash := d.blockHash }

def absSyncCommittee (c : EthCLSpecs.Gloas.SyncCommittee) : Spec.SyncCommittee :=
  { pubkeys := c.pubkeys.toList, aggregate_pubkey := c.aggregatePubkey }

def absHistoricalSummary (h : EthCLSpecs.Gloas.HistoricalSummary) : Spec.HistoricalSummary :=
  { block_summary_root := h.blockSummaryRoot
    state_summary_root := h.stateSummaryRoot }

forkonly Gloas
def absBuilder (b : EthCLSpecs.Gloas.Builder) : Spec.Builder :=
  { pubkey := b.pubkey
    version := b.version
    execution_address := b.executionAddress
    balance := b.balance.toNat
    deposit_epoch := b.depositEpoch.toNat
    withdrawable_epoch := b.withdrawableEpoch.toNat }

/-- A payload `Withdrawal`. `absWithdrawal` is the builder pending withdrawal. -/
def absPayloadWithdrawal (w : EthCLSpecs.Gloas.Withdrawal) : Spec.Withdrawal :=
  { index := w.index.toNat
    validator_index := w.validatorIndex.toNat
    address := w.address
    amount := w.amount.toNat }

def absBid (b : EthCLSpecs.Gloas.ExecutionPayloadBid) : Spec.ExecutionPayloadBid :=
  { parent_block_hash := b.parentBlockHash
    parent_block_root := b.parentBlockRoot
    block_hash := b.blockHash
    prev_randao := b.prevRandao
    fee_recipient := b.feeRecipient
    gas_limit := b.gasLimit.toNat
    builder_index := b.builderIndex.toNat
    slot := b.slot.toNat
    value := b.value.toNat
    execution_payment := b.executionPayment.toNat
    blob_kzg_commitments := b.blobKzgCommitments.toList
    execution_requests_root := b.executionRequestsRoot }

def absWithdrawal (w : EWithdrawal) : Spec.BuilderPendingWithdrawal :=
  { fee_recipient := w.feeRecipient
    amount := w.amount.toNat
    builder_index := w.builderIndex.toNat }

def absPayment (p : EPayment) : Spec.BuilderPendingPayment :=
  { weight := p.weight.toNat
    withdrawal := absWithdrawal p.withdrawal
    proposer_index := p.proposerIndex.toNat }

/-- An Etheorem state as a reference state. Every field maps. -/
def absEState (e : EState) : Spec.BeaconState :=
  { genesis_time := e.genesisTime.toNat
    genesis_validators_root := e.genesisValidatorsRoot
    slot := e.slot.toNat
    «fork» := absFork e.forkData
    latest_block_header := absHeader e.latestBlockHeader
    block_roots := e.blockRoots.toList
    state_roots := e.stateRoots.toList
    historical_roots := e.historicalRoots.toList
    eth1_data := absEth1Data e.eth1Data
    eth1_data_votes := e.eth1DataVotes.toList.map absEth1Data
    eth1_deposit_index := e.eth1DepositIndex.toNat
    validators := e.validators.toList.map absValidator
    balances := e.balances.toList.map UInt64.toNat
    randao_mixes := e.randaoMixes.toList
    slashings := e.slashings.toList.map UInt64.toNat
    previous_epoch_participation := e.previousEpochParticipation.toList
    current_epoch_participation := e.currentEpochParticipation.toList
    justification_bits := absBits e.justificationBits
    previous_justified_checkpoint := absCheckpoint e.previousJustifiedCheckpoint
    current_justified_checkpoint := absCheckpoint e.currentJustifiedCheckpoint
    finalized_checkpoint := absCheckpoint e.finalizedCheckpoint
    inactivity_scores := e.inactivityScores.toList.map UInt64.toNat
    current_sync_committee := absSyncCommittee e.currentSyncCommittee
    next_sync_committee := absSyncCommittee e.nextSyncCommittee
    latest_block_hash := e.latestBlockHash
    next_withdrawal_index := e.nextWithdrawalIndex.toNat
    next_withdrawal_validator_index := e.nextWithdrawalValidatorIndex.toNat
    historical_summaries := e.historicalSummaries.toList.map absHistoricalSummary
    deposit_requests_start_index := e.depositRequestsStartIndex.toNat
    deposit_balance_to_consume := e.depositBalanceToConsume.toNat
    exit_balance_to_consume := e.exitBalanceToConsume.toNat
    earliest_exit_epoch := e.earliestExitEpoch.toNat
    consolidation_balance_to_consume := e.consolidationBalanceToConsume.toNat
    earliest_consolidation_epoch := e.earliestConsolidationEpoch.toNat
    pending_deposits := e.pendingDeposits.toList.map absPendingDeposit
    pending_partial_withdrawals := e.pendingPartialWithdrawals.toList.map absPendingPartialWithdrawal
    pending_consolidations := e.pendingConsolidations.toList.map absPendingConsolidation
    proposer_lookahead := e.proposerLookahead.toList.map UInt64.toNat
    builders := e.builders.toList.map absBuilder
    next_withdrawal_builder_index := e.nextWithdrawalBuilderIndex.toNat
    execution_payload_availability := absBits e.executionPayloadAvailability
    builder_pending_payments := e.builderPendingPayments.toList.map absPayment
    builder_pending_withdrawals := e.builderPendingWithdrawals.toList.map absWithdrawal
    latest_execution_payload_bid := absBid e.latestExecutionPayloadBid
    payload_expected_withdrawals := e.payloadExpectedWithdrawals.toList.map absPayloadWithdrawal
    ptc_window := e.ptcWindow.toList.map fun ptc => ptc.toList.map UInt64.toNat }
end forkonly

forkonly Fulu
/-- An Etheorem state as a reference state. Every field maps. -/
def absEState (e : EState) : Spec.BeaconState :=
  { genesis_time := e.genesisTime.toNat
    genesis_validators_root := e.genesisValidatorsRoot
    slot := e.slot.toNat
    «fork» := absFork e.forkData
    latest_block_header := absHeader e.latestBlockHeader
    block_roots := e.blockRoots.toList
    state_roots := e.stateRoots.toList
    historical_roots := e.historicalRoots.toList
    eth1_data := absEth1Data e.eth1Data
    eth1_data_votes := e.eth1DataVotes.toList.map absEth1Data
    eth1_deposit_index := e.eth1DepositIndex.toNat
    validators := e.validators.toList.map absValidator
    balances := e.balances.toList.map UInt64.toNat
    randao_mixes := e.randaoMixes.toList
    slashings := e.slashings.toList.map UInt64.toNat
    previous_epoch_participation := e.previousEpochParticipation.toList
    current_epoch_participation := e.currentEpochParticipation.toList
    justification_bits := absBits e.justificationBits
    previous_justified_checkpoint := absCheckpoint e.previousJustifiedCheckpoint
    current_justified_checkpoint := absCheckpoint e.currentJustifiedCheckpoint
    finalized_checkpoint := absCheckpoint e.finalizedCheckpoint
    inactivity_scores := e.inactivityScores.toList.map UInt64.toNat
    current_sync_committee := absSyncCommittee e.currentSyncCommittee
    next_sync_committee := absSyncCommittee e.nextSyncCommittee
    latest_block_hash := e.latestExecutionPayloadHeader.blockHash
    next_withdrawal_index := e.nextWithdrawalIndex.toNat
    next_withdrawal_validator_index := e.nextWithdrawalValidatorIndex.toNat
    historical_summaries := e.historicalSummaries.toList.map absHistoricalSummary
    deposit_requests_start_index := e.depositRequestsStartIndex.toNat
    deposit_balance_to_consume := e.depositBalanceToConsume.toNat
    exit_balance_to_consume := e.exitBalanceToConsume.toNat
    earliest_exit_epoch := e.earliestExitEpoch.toNat
    consolidation_balance_to_consume := e.consolidationBalanceToConsume.toNat
    earliest_consolidation_epoch := e.earliestConsolidationEpoch.toNat
    pending_deposits := e.pendingDeposits.toList.map absPendingDeposit
    pending_partial_withdrawals := e.pendingPartialWithdrawals.toList.map absPendingPartialWithdrawal
    pending_consolidations := e.pendingConsolidations.toList.map absPendingConsolidation
    proposer_lookahead := e.proposerLookahead.toList.map UInt64.toNat
    builders := []
    next_withdrawal_builder_index := 0
    execution_payload_availability := []
    builder_pending_payments := []
    builder_pending_withdrawals := []
    latest_execution_payload_bid := {}
    payload_expected_withdrawals := []
    ptc_window := [] }
end forkonly

/-! ## Reading one field -/

section Read

variable (e : EState)

forkonly Gloas
@[simp] theorem absEState_slot : (absEState e).slot = e.slot.toNat := rfl
@[simp] theorem absEState_validators :
    (absEState e).validators = e.validators.toList.map absValidator := rfl
@[simp] theorem absEState_balances :
    (absEState e).balances = e.balances.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_randao_mixes : (absEState e).randao_mixes = e.randaoMixes.toList := rfl
@[simp] theorem absEState_slashings :
    (absEState e).slashings = e.slashings.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_previous_epoch_participation :
    (absEState e).previous_epoch_participation = e.previousEpochParticipation.toList := rfl
@[simp] theorem absEState_current_epoch_participation :
    (absEState e).current_epoch_participation = e.currentEpochParticipation.toList := rfl
@[simp] theorem absEState_justification_bits :
    (absEState e).justification_bits = absBits e.justificationBits := rfl
@[simp] theorem absEState_previous_justified_checkpoint :
    (absEState e).previous_justified_checkpoint = absCheckpoint e.previousJustifiedCheckpoint := rfl
@[simp] theorem absEState_current_justified_checkpoint :
    (absEState e).current_justified_checkpoint = absCheckpoint e.currentJustifiedCheckpoint := rfl
@[simp] theorem absEState_finalized_checkpoint :
    (absEState e).finalized_checkpoint = absCheckpoint e.finalizedCheckpoint := rfl
@[simp] theorem absEState_inactivity_scores :
    (absEState e).inactivity_scores = e.inactivityScores.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_current_sync_committee :
    (absEState e).current_sync_committee = absSyncCommittee e.currentSyncCommittee := rfl
@[simp] theorem absEState_next_sync_committee :
    (absEState e).next_sync_committee = absSyncCommittee e.nextSyncCommittee := rfl
@[simp] theorem absEState_eth1_data_votes :
    (absEState e).eth1_data_votes = e.eth1DataVotes.toList.map absEth1Data := rfl
@[simp] theorem absEState_block_roots : (absEState e).block_roots = e.blockRoots.toList := rfl
@[simp] theorem absEState_state_roots : (absEState e).state_roots = e.stateRoots.toList := rfl
@[simp] theorem absEState_historical_summaries :
    (absEState e).historical_summaries = e.historicalSummaries.toList.map absHistoricalSummary :=
  rfl
@[simp] theorem absEState_eth1_deposit_index :
    (absEState e).eth1_deposit_index = e.eth1DepositIndex.toNat := rfl
@[simp] theorem absEState_deposit_requests_start_index :
    (absEState e).deposit_requests_start_index = e.depositRequestsStartIndex.toNat := rfl
@[simp] theorem absEState_deposit_balance_to_consume :
    (absEState e).deposit_balance_to_consume = e.depositBalanceToConsume.toNat := rfl
@[simp] theorem absEState_exit_balance_to_consume :
    (absEState e).exit_balance_to_consume = e.exitBalanceToConsume.toNat := rfl
@[simp] theorem absEState_earliest_exit_epoch :
    (absEState e).earliest_exit_epoch = e.earliestExitEpoch.toNat := rfl
@[simp] theorem absEState_consolidation_balance_to_consume :
    (absEState e).consolidation_balance_to_consume = e.consolidationBalanceToConsume.toNat := rfl
@[simp] theorem absEState_earliest_consolidation_epoch :
    (absEState e).earliest_consolidation_epoch = e.earliestConsolidationEpoch.toNat := rfl
@[simp] theorem absEState_pending_deposits :
    (absEState e).pending_deposits = e.pendingDeposits.toList.map absPendingDeposit := rfl
@[simp] theorem absEState_pending_partial_withdrawals :
    (absEState e).pending_partial_withdrawals =
      e.pendingPartialWithdrawals.toList.map absPendingPartialWithdrawal := rfl
@[simp] theorem absEState_pending_consolidations :
    (absEState e).pending_consolidations =
      e.pendingConsolidations.toList.map absPendingConsolidation := rfl
@[simp] theorem absEState_proposer_lookahead :
    (absEState e).proposer_lookahead = e.proposerLookahead.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_builders : (absEState e).builders = e.builders.toList.map absBuilder := rfl
@[simp] theorem absEState_builder_pending_payments :
    (absEState e).builder_pending_payments = e.builderPendingPayments.toList.map absPayment := rfl
@[simp] theorem absEState_builder_pending_withdrawals :
    (absEState e).builder_pending_withdrawals =
      e.builderPendingWithdrawals.toList.map absWithdrawal := rfl
@[simp] theorem absEState_ptc_window :
    (absEState e).ptc_window = e.ptcWindow.toList.map fun ptc => ptc.toList.map UInt64.toNat := rfl
end forkonly

forkonly Fulu
@[simp] theorem absEState_slot : (absEState e).slot = e.slot.toNat := rfl
@[simp] theorem absEState_validators :
    (absEState e).validators = e.validators.toList.map absValidator := rfl
@[simp] theorem absEState_balances :
    (absEState e).balances = e.balances.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_randao_mixes : (absEState e).randao_mixes = e.randaoMixes.toList := rfl
@[simp] theorem absEState_slashings :
    (absEState e).slashings = e.slashings.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_previous_epoch_participation :
    (absEState e).previous_epoch_participation = e.previousEpochParticipation.toList := rfl
@[simp] theorem absEState_current_epoch_participation :
    (absEState e).current_epoch_participation = e.currentEpochParticipation.toList := rfl
@[simp] theorem absEState_justification_bits :
    (absEState e).justification_bits = absBits e.justificationBits := rfl
@[simp] theorem absEState_previous_justified_checkpoint :
    (absEState e).previous_justified_checkpoint = absCheckpoint e.previousJustifiedCheckpoint := rfl
@[simp] theorem absEState_current_justified_checkpoint :
    (absEState e).current_justified_checkpoint = absCheckpoint e.currentJustifiedCheckpoint := rfl
@[simp] theorem absEState_finalized_checkpoint :
    (absEState e).finalized_checkpoint = absCheckpoint e.finalizedCheckpoint := rfl
@[simp] theorem absEState_inactivity_scores :
    (absEState e).inactivity_scores = e.inactivityScores.toList.map UInt64.toNat := rfl
@[simp] theorem absEState_current_sync_committee :
    (absEState e).current_sync_committee = absSyncCommittee e.currentSyncCommittee := rfl
@[simp] theorem absEState_next_sync_committee :
    (absEState e).next_sync_committee = absSyncCommittee e.nextSyncCommittee := rfl
@[simp] theorem absEState_eth1_data_votes :
    (absEState e).eth1_data_votes = e.eth1DataVotes.toList.map absEth1Data := rfl
@[simp] theorem absEState_block_roots : (absEState e).block_roots = e.blockRoots.toList := rfl
@[simp] theorem absEState_state_roots : (absEState e).state_roots = e.stateRoots.toList := rfl
@[simp] theorem absEState_historical_summaries :
    (absEState e).historical_summaries = e.historicalSummaries.toList.map absHistoricalSummary :=
  rfl
@[simp] theorem absEState_eth1_deposit_index :
    (absEState e).eth1_deposit_index = e.eth1DepositIndex.toNat := rfl
@[simp] theorem absEState_deposit_requests_start_index :
    (absEState e).deposit_requests_start_index = e.depositRequestsStartIndex.toNat := rfl
@[simp] theorem absEState_deposit_balance_to_consume :
    (absEState e).deposit_balance_to_consume = e.depositBalanceToConsume.toNat := rfl
@[simp] theorem absEState_exit_balance_to_consume :
    (absEState e).exit_balance_to_consume = e.exitBalanceToConsume.toNat := rfl
@[simp] theorem absEState_earliest_exit_epoch :
    (absEState e).earliest_exit_epoch = e.earliestExitEpoch.toNat := rfl
@[simp] theorem absEState_consolidation_balance_to_consume :
    (absEState e).consolidation_balance_to_consume = e.consolidationBalanceToConsume.toNat := rfl
@[simp] theorem absEState_earliest_consolidation_epoch :
    (absEState e).earliest_consolidation_epoch = e.earliestConsolidationEpoch.toNat := rfl
@[simp] theorem absEState_pending_deposits :
    (absEState e).pending_deposits = e.pendingDeposits.toList.map absPendingDeposit := rfl
@[simp] theorem absEState_pending_partial_withdrawals :
    (absEState e).pending_partial_withdrawals =
      e.pendingPartialWithdrawals.toList.map absPendingPartialWithdrawal := rfl
@[simp] theorem absEState_pending_consolidations :
    (absEState e).pending_consolidations =
      e.pendingConsolidations.toList.map absPendingConsolidation := rfl
@[simp] theorem absEState_proposer_lookahead :
    (absEState e).proposer_lookahead = e.proposerLookahead.toList.map UInt64.toNat := rfl
end forkonly

end Read

/-! ## Writing one field

A write to an Etheorem field is the same write to the reference field. -/

section Write

variable (e : EState)

theorem absEState_set_balances (b : SSZList EthCLSpecs.Gloas.Gwei
      EthCLSpecs.Gloas.Const.validatorRegistryLimit) :
    absEState { e with balances := b } =
      { absEState e with balances := b.toList.map UInt64.toNat } := rfl

theorem absEState_set_validators (v : SSZList EthCLSpecs.Gloas.Validator
      EthCLSpecs.Gloas.Const.validatorRegistryLimit) :
    absEState { e with validators := v } =
      { absEState e with validators := v.toList.map absValidator } := rfl

theorem absEState_set_inactivityScores (s : SSZList UInt64
      EthCLSpecs.Gloas.Const.validatorRegistryLimit) :
    absEState { e with inactivityScores := s } =
      { absEState e with inactivity_scores := s.toList.map UInt64.toNat } := rfl

theorem absEState_set_participation
    (prev cur : SSZList EthCLSpecs.Gloas.ParticipationFlags
      EthCLSpecs.Gloas.Const.validatorRegistryLimit) :
    absEState { e with previousEpochParticipation := prev, currentEpochParticipation := cur } =
      { absEState e with previous_epoch_participation := prev.toList,
                         current_epoch_participation := cur.toList } := rfl

theorem absEState_set_slashings (s : Vector EthCLSpecs.Gloas.Gwei
      EthCLSpecs.Gloas.Const.epochsPerSlashingsVector) :
    absEState { e with slashings := s } =
      { absEState e with slashings := s.toList.map UInt64.toNat } := rfl

theorem absEState_set_randaoMixes (m : Vector EthCLSpecs.Gloas.Bytes32
      EthCLSpecs.Gloas.Const.epochsPerHistoricalVector) :
    absEState { e with randaoMixes := m } = { absEState e with randao_mixes := m.toList } := rfl

theorem absEState_set_eth1DataVotes (v : SSZList EthCLSpecs.Gloas.Eth1Data
      (EthCLSpecs.Gloas.Const.epochsPerEth1VotingPeriod * EthCLSpecs.Gloas.Const.slotsPerEpoch)) :
    absEState { e with eth1DataVotes := v } =
      { absEState e with eth1_data_votes := v.toList.map absEth1Data } := rfl

theorem absEState_set_historicalSummaries (h : SSZList EthCLSpecs.Gloas.HistoricalSummary
      EthCLSpecs.Gloas.Const.historicalRootsLimit) :
    absEState { e with historicalSummaries := h } =
      { absEState e with historical_summaries := h.toList.map absHistoricalSummary } := rfl

theorem absEState_set_syncCommittees (cur next : EthCLSpecs.Gloas.SyncCommittee) :
    absEState { e with currentSyncCommittee := cur, nextSyncCommittee := next } =
      { absEState e with current_sync_committee := absSyncCommittee cur,
                         next_sync_committee := absSyncCommittee next } := rfl

theorem absEState_set_proposerLookahead (l : Vector EthCLSpecs.Gloas.ValidatorIndex
      (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch)) :
    absEState { e with proposerLookahead := l } =
      { absEState e with proposer_lookahead := l.toList.map UInt64.toNat } := rfl

forkonly Gloas
theorem absEState_set_ptcWindow (w : Vector (Vector EthCLSpecs.Gloas.ValidatorIndex
      EthCLSpecs.Gloas.Const.ptcSize) (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch)) :
    absEState { e with ptcWindow := w } =
      { absEState e with ptc_window := w.toList.map fun ptc => ptc.toList.map UInt64.toNat } := rfl
end forkonly

theorem absEState_set_pendingDeposits (d : SSZList EthCLSpecs.Gloas.PendingDeposit
      EthCLSpecs.Gloas.Const.pendingDepositsLimit) :
    absEState { e with pendingDeposits := d } =
      { absEState e with pending_deposits := d.toList.map absPendingDeposit } := rfl

theorem absEState_set_pendingConsolidations (c : SSZList EthCLSpecs.Gloas.PendingConsolidation
      EthCLSpecs.Gloas.Const.pendingConsolidationsLimit) :
    absEState { e with pendingConsolidations := c } =
      { absEState e with pending_consolidations := c.toList.map absPendingConsolidation } := rfl

theorem absEState_set_justification
    (bits : Bitvector EthCLSpecs.Gloas.Const.justificationBitsLength)
    (prev cur fin : EthCLSpecs.Gloas.Checkpoint) :
    absEState { e with justificationBits := bits, previousJustifiedCheckpoint := prev,
                       currentJustifiedCheckpoint := cur, finalizedCheckpoint := fin } =
      { absEState e with justification_bits := absBits bits,
                         previous_justified_checkpoint := absCheckpoint prev,
                         current_justified_checkpoint := absCheckpoint cur,
                         finalized_checkpoint := absCheckpoint fin } := rfl

theorem absEState_set_churn (dbtc ebtc ebc : EthCLSpecs.Gloas.Gwei)
    (eee ece : EthCLSpecs.Gloas.Epoch) :
    absEState { e with depositBalanceToConsume := dbtc, exitBalanceToConsume := ebtc,
                       earliestExitEpoch := eee, consolidationBalanceToConsume := ebc,
                       earliestConsolidationEpoch := ece } =
      { absEState e with deposit_balance_to_consume := dbtc.toNat,
                         exit_balance_to_consume := ebtc.toNat,
                         earliest_exit_epoch := eee.toNat,
                         consolidation_balance_to_consume := ebc.toNat,
                         earliest_consolidation_epoch := ece.toNat } := rfl

forkonly Gloas
theorem absEState_set_builderPayments (pay : Vector EPayment (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch))
    (wd : SSZList EWithdrawal EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit) :
    absEState { e with builderPendingPayments := pay, builderPendingWithdrawals := wd } =
      { absEState e with builder_pending_payments := pay.toList.map absPayment,
                         builder_pending_withdrawals := wd.toList.map absWithdrawal } := rfl
end forkonly

end Write

end forkproof

