import EthLib.Consensus.Containers.State
import EpochProofs.Spec.Block.FuluTypes

/-!
# An EthLib state, read as a reference state

EthLib has one `BeaconState preset fork` for all forks. A field that a fork adds or removes is a
function from the proof that the fork has the field. The reference has one `Spec.BeaconState` for
Gloas, and `Spec.FuluState` adds the payload header of Fulu.

`toSpecState` and `toSpecFuluState` map each field. `StateInjective.lean` proves that two different
EthLib states never map to the same reference state. Thus the maps lose no field.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Serialization.Ssz
open _root_.EthLib.Consensus

/-- Reads a field that only some forks have. The result is `absent` if the fork does not have it. -/
def fieldOr {present : Prop} [Decidable present] {α β : Type} (absent : β) (read : α → β)
    (field : present → α) : β :=
  if h : present then read (field h) else absent

/-- If the fork has the field, `fieldOr` reads it. -/
theorem fieldOr_present {present : Prop} [Decidable present] {α β : Type} (absent : β)
    (read : α → β) (field : present → α) (h : present) :
    fieldOr absent read field = read (field h) := dite_eq_left h

/-- The elements of an SSZ list, each read by `read`. -/
def readList {α β : Type} (read : α → β) (data : Array α) : List β := data.toList.map read

/-- The validator of EthLib, read as the one of the reference. -/
def toSpecValidator (v : Validator) : Spec.Validator :=
  { pubkey := v.pubkey
    withdrawal_credentials := v.withdrawalCredentials
    effective_balance := v.effectiveBalance.toNat
    slashed := v.slashed
    activation_eligibility_epoch := v.activationEligibilityEpoch.toNat
    activation_epoch := v.activationEpoch.toNat
    exit_epoch := v.exitEpoch.toNat
    withdrawable_epoch := v.withdrawableEpoch.toNat }

/-- The pending deposit of EthLib, read as the one of the reference. -/
def toSpecPendingDeposit (d : PendingDeposit) : Spec.PendingDeposit :=
  { pubkey := d.pubkey
    withdrawal_credentials := d.withdrawalCredentials
    amount := d.amount.toNat
    signature := d.signature
    slot := d.slot.toNat }

/-- The pending partial withdrawal of EthLib, read as the one of the reference. -/
def toSpecPendingPartialWithdrawal (w : PendingPartialWithdrawal) :
    Spec.PendingPartialWithdrawal :=
  { validator_index := w.validatorIndex.toNat
    amount := w.amount.toNat
    withdrawable_epoch := w.withdrawableEpoch.toNat }

/-- The pending consolidation of EthLib, read as the one of the reference. -/
def toSpecPendingConsolidation (c : PendingConsolidation) : Spec.PendingConsolidation :=
  { source_index := c.sourceIndex.toNat
    target_index := c.targetIndex.toNat }

/-- The checkpoint of EthLib, read as the one of the reference. -/
def toSpecCheckpoint (c : Checkpoint) : Spec.Checkpoint :=
  { epoch := c.epoch.toNat, root := c.root }

/-- The `Fork` container of EthLib, read as the one of the reference. -/
def toSpecFork (f : ForkVersions) : Spec.Fork :=
  { previous_version := f.previousVersion
    current_version := f.currentVersion
    epoch := f.epoch.toNat }

/-- The block header of EthLib, read as the one of the reference. -/
def toSpecBeaconBlockHeader (h : BeaconBlockHeader) : Spec.BeaconBlockHeader :=
  { slot := h.slot.toNat
    proposer_index := h.proposerIndex.toNat
    parent_root := h.parentRoot
    state_root := h.stateRoot
    body_root := h.bodyRoot }

/-- The `Eth1Data` of EthLib, read as the one of the reference. -/
def toSpecEth1Data (d : Eth1Data) : Spec.Eth1Data :=
  { deposit_root := d.depositRoot
    deposit_count := d.depositCount.toNat
    block_hash := d.blockHash }

/-- The sync committee of EthLib, read as the one of the reference. -/
def toSpecSyncCommittee {preset : Preset} (c : Rooted (SyncCommittee preset)) :
    Spec.SyncCommittee :=
  { pubkeys := c.value.pubkeys.toList
    aggregate_pubkey := c.value.aggregatePubkey }

/-- The historical summary of EthLib, read as the one of the reference. -/
def toSpecHistoricalSummary (h : HistoricalSummary) : Spec.HistoricalSummary :=
  { block_summary_root := h.blockSummaryRoot
    state_summary_root := h.stateSummaryRoot }

/-- The builder of EthLib, read as the one of the reference. -/
def toSpecBuilder (b : Builder) : Spec.Builder :=
  { pubkey := b.pubkey
    version := b.version
    execution_address := b.executionAddress
    balance := b.balance.toNat
    deposit_epoch := b.depositEpoch.toNat
    withdrawable_epoch := b.withdrawableEpoch.toNat }

/-- The payload withdrawal of EthLib, read as the one of the reference. -/
def toSpecWithdrawal (w : Withdrawal) : Spec.Withdrawal :=
  { index := w.index.toNat
    validator_index := w.validatorIndex.toNat
    address := w.address
    amount := w.amount.toNat }

/-- The builder pending withdrawal of EthLib, read as the one of the reference. -/
def toSpecBuilderPendingWithdrawal (w : BuilderPendingWithdrawal) :
    Spec.BuilderPendingWithdrawal :=
  { fee_recipient := w.feeRecipient
    amount := w.amount.toNat
    builder_index := w.builderIndex.toNat }

/-- The builder pending payment of EthLib, read as the one of the reference. -/
def toSpecBuilderPendingPayment (p : BuilderPendingPayment) : Spec.BuilderPendingPayment :=
  { weight := p.weight.toNat
    withdrawal := toSpecBuilderPendingWithdrawal p.withdrawal
    proposer_index := p.proposerIndex.toNat }

/-- The bid of Gloas. Heze adds `inclusionListBits`, which the reference does not have. -/
def toSpecExecutionPayloadBid {preset : Preset} {fork : _root_.EthLib.Base.Fork}
    (b : ExecutionPayloadBid preset fork) : Spec.ExecutionPayloadBid :=
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
    blob_kzg_commitments := readList (·.bytes) b.blobKzgCommitments.data
    execution_requests_root := b.executionRequestsRoot }

/-- The payload header of Fulu of EthLib, read as the one of the reference. -/
def toSpecExecutionPayloadHeader {preset : Preset} {fork : _root_.EthLib.Base.Fork}
    (h : ExecutionPayloadHeader preset fork) : Spec.ExecutionPayloadHeader :=
  { parent_hash := h.parentHash
    fee_recipient := h.feeRecipient
    state_root := h.stateRoot
    receipts_root := h.receiptsRoot
    logs_bloom := h.logsBloom.toList
    prev_randao := h.prevRandao
    block_number := h.blockNumber.toNat
    gas_limit := h.gasLimit.toNat
    gas_used := h.gasUsed.toNat
    timestamp := h.timestamp.toNat
    extra_data := h.extraData.data.toList
    base_fee_per_gas := h.baseFeePerGas.toNat
    block_hash := h.blockHash
    transactions_root := h.transactionsRoot
    withdrawals_root := fieldOr Spec.Bytes32.zero id h.withdrawalsRoot
    blob_gas_used := fieldOr 0 UInt64.toNat h.blobGasUsed
    excess_blob_gas := fieldOr 0 UInt64.toNat h.excessBlobGas }

/-- An EthLib state, read as a reference state. A field that the fork does not have reads as zero
or empty. Before Gloas, `latest_block_hash` reads the block hash of the latest payload header. -/
def toSpecState {preset : Preset} {fork : _root_.EthLib.Base.Fork}
    (s : BeaconState preset fork) : Spec.BeaconState :=
  { genesis_time := s.genesisTime.toNat
    genesis_validators_root := s.genesisValidatorsRoot
    slot := s.slot.toNat
    «fork» := toSpecFork s.forkVersions
    latest_block_header := toSpecBeaconBlockHeader s.latestBlockHeader
    block_roots := s.blockRoots.elements.toList
    state_roots := s.stateRoots.elements.toList
    historical_roots := s.historicalRoots.data.toList
    eth1_data := fieldOr {} toSpecEth1Data s.eth1Data
    eth1_data_votes := fieldOr [] (fun l => readList toSpecEth1Data l.data) s.eth1DataVotes
    eth1_deposit_index := fieldOr 0 UInt64.toNat s.eth1DepositIndex
    validators := readList toSpecValidator s.validators.data
    balances := readList UInt64.toNat s.balances.data
    randao_mixes := s.randaoMixes.elements.toList
    slashings := s.slashings.elements.toList.map UInt64.toNat
    previous_epoch_participation := fieldOr [] (·.data.toList) s.previousEpochParticipation
    current_epoch_participation := fieldOr [] (·.data.toList) s.currentEpochParticipation
    justification_bits := s.justificationBits.bits.toList
    previous_justified_checkpoint := toSpecCheckpoint s.previousJustifiedCheckpoint
    current_justified_checkpoint := toSpecCheckpoint s.currentJustifiedCheckpoint
    finalized_checkpoint := toSpecCheckpoint s.finalizedCheckpoint
    inactivity_scores := fieldOr [] (fun l => readList UInt64.toNat l.data) s.inactivityScores
    current_sync_committee := fieldOr {} toSpecSyncCommittee s.currentSyncCommittee
    next_sync_committee := fieldOr {} toSpecSyncCommittee s.nextSyncCommittee
    latest_block_hash :=
      fieldOr (fieldOr Spec.Bytes32.zero (·.blockHash) s.latestExecutionPayloadHeader) id
        s.latestBlockHash
    next_withdrawal_index := fieldOr 0 UInt64.toNat s.nextWithdrawalIndex
    next_withdrawal_validator_index := fieldOr 0 UInt64.toNat s.nextWithdrawalValidatorIndex
    historical_summaries :=
      fieldOr [] (fun l => readList toSpecHistoricalSummary l.data) s.historicalSummaries
    deposit_requests_start_index := fieldOr 0 UInt64.toNat s.depositRequestsStartIndex
    deposit_balance_to_consume := fieldOr 0 UInt64.toNat s.depositBalanceToConsume
    exit_balance_to_consume := fieldOr 0 UInt64.toNat s.exitBalanceToConsume
    earliest_exit_epoch := fieldOr 0 UInt64.toNat s.earliestExitEpoch
    consolidation_balance_to_consume := fieldOr 0 UInt64.toNat s.consolidationBalanceToConsume
    earliest_consolidation_epoch := fieldOr 0 UInt64.toNat s.earliestConsolidationEpoch
    pending_deposits := fieldOr [] (fun l => readList toSpecPendingDeposit l.data) s.pendingDeposits
    pending_partial_withdrawals :=
      fieldOr [] (fun l => readList toSpecPendingPartialWithdrawal l.data)
        s.pendingPartialWithdrawals
    pending_consolidations :=
      fieldOr [] (fun l => readList toSpecPendingConsolidation l.data) s.pendingConsolidations
    proposer_lookahead := fieldOr [] (·.toList.map UInt64.toNat) s.proposerLookahead
    builders := fieldOr [] (fun l => readList toSpecBuilder l.data) s.builders
    next_withdrawal_builder_index := fieldOr 0 UInt64.toNat s.nextWithdrawalBuilderIndex
    execution_payload_availability := fieldOr [] (·.bits.toList) s.executionPayloadAvailability
    builder_pending_payments :=
      fieldOr [] (·.elements.toList.map toSpecBuilderPendingPayment) s.builderPendingPayments
    builder_pending_withdrawals :=
      fieldOr [] (fun l => readList toSpecBuilderPendingWithdrawal l.data)
        s.builderPendingWithdrawals
    latest_execution_payload_bid :=
      fieldOr {} toSpecExecutionPayloadBid s.latestExecutionPayloadBid
    payload_expected_withdrawals :=
      fieldOr [] (fun l => readList toSpecWithdrawal l.data) s.payloadExpectedWithdrawals
    ptc_window :=
      fieldOr [] (·.elements.toList.map fun committee => committee.toList.map UInt64.toNat)
        s.ptcWindow }

/-- A Fulu EthLib state, read as a Fulu reference state. The payload header is a separate field. -/
def toSpecFuluState {preset : Preset} (s : BeaconState preset .fusaka) : Spec.FuluState :=
  { state := toSpecState s
    latest_execution_payload_header :=
      toSpecExecutionPayloadHeader (s.latestExecutionPayloadHeader (by decide)) }

/-! ## Reads of the fields that only some forks have -/

section Read

variable {preset : Preset} {fork : _root_.EthLib.Base.Fork} (s : BeaconState preset fork)

theorem toSpecState_eth1_data (h : fork < .hegota) :
    (toSpecState s).eth1_data =
      toSpecEth1Data (s.eth1Data h) :=
  fieldOr_present _ _ _ h

theorem toSpecState_eth1_data_votes (h : fork < .hegota) :
    (toSpecState s).eth1_data_votes =
      readList toSpecEth1Data (s.eth1DataVotes h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_eth1_deposit_index (h : fork < .hegota) :
    (toSpecState s).eth1_deposit_index =
      (s.eth1DepositIndex h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_previous_epoch_participation (h : .altair ≤ fork) :
    (toSpecState s).previous_epoch_participation =
      (s.previousEpochParticipation h).data.toList :=
  fieldOr_present _ _ _ h

theorem toSpecState_current_epoch_participation (h : .altair ≤ fork) :
    (toSpecState s).current_epoch_participation =
      (s.currentEpochParticipation h).data.toList :=
  fieldOr_present _ _ _ h

theorem toSpecState_inactivity_scores (h : .altair ≤ fork) :
    (toSpecState s).inactivity_scores =
      readList UInt64.toNat (s.inactivityScores h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_current_sync_committee (h : .altair ≤ fork) :
    (toSpecState s).current_sync_committee =
      toSpecSyncCommittee (s.currentSyncCommittee h) :=
  fieldOr_present _ _ _ h

theorem toSpecState_next_sync_committee (h : .altair ≤ fork) :
    (toSpecState s).next_sync_committee =
      toSpecSyncCommittee (s.nextSyncCommittee h) :=
  fieldOr_present _ _ _ h

theorem toSpecState_historical_summaries (h : .shapella ≤ fork) :
    (toSpecState s).historical_summaries =
      readList toSpecHistoricalSummary (s.historicalSummaries h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_deposit_balance_to_consume (h : .pectra ≤ fork) :
    (toSpecState s).deposit_balance_to_consume =
      (s.depositBalanceToConsume h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_exit_balance_to_consume (h : .pectra ≤ fork) :
    (toSpecState s).exit_balance_to_consume =
      (s.exitBalanceToConsume h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_earliest_exit_epoch (h : .pectra ≤ fork) :
    (toSpecState s).earliest_exit_epoch =
      (s.earliestExitEpoch h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_consolidation_balance_to_consume (h : .pectra ≤ fork) :
    (toSpecState s).consolidation_balance_to_consume =
      (s.consolidationBalanceToConsume h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_earliest_consolidation_epoch (h : .pectra ≤ fork) :
    (toSpecState s).earliest_consolidation_epoch =
      (s.earliestConsolidationEpoch h).toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_pending_deposits (h : .pectra ≤ fork) :
    (toSpecState s).pending_deposits =
      readList toSpecPendingDeposit (s.pendingDeposits h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_pending_partial_withdrawals (h : .pectra ≤ fork) :
    (toSpecState s).pending_partial_withdrawals =
      readList toSpecPendingPartialWithdrawal (s.pendingPartialWithdrawals h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_pending_consolidations (h : .pectra ≤ fork) :
    (toSpecState s).pending_consolidations =
      readList toSpecPendingConsolidation (s.pendingConsolidations h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_proposer_lookahead (h : .fusaka ≤ fork) :
    (toSpecState s).proposer_lookahead =
      (s.proposerLookahead h).toList.map UInt64.toNat :=
  fieldOr_present _ _ _ h

theorem toSpecState_builders (h : .glamsterdam ≤ fork) :
    (toSpecState s).builders =
      readList toSpecBuilder (s.builders h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_builder_pending_payments (h : .glamsterdam ≤ fork) :
    (toSpecState s).builder_pending_payments =
      (s.builderPendingPayments h).elements.toList.map toSpecBuilderPendingPayment :=
  fieldOr_present _ _ _ h

theorem toSpecState_builder_pending_withdrawals (h : .glamsterdam ≤ fork) :
    (toSpecState s).builder_pending_withdrawals =
      readList toSpecBuilderPendingWithdrawal (s.builderPendingWithdrawals h).data :=
  fieldOr_present _ _ _ h

theorem toSpecState_ptc_window (h : .glamsterdam ≤ fork) :
    (toSpecState s).ptc_window =
      (s.ptcWindow h).elements.toList.map fun committee => committee.toList.map UInt64.toNat :=
  fieldOr_present _ _ _ h

end Read

/-! ## Writes of the fields that only some forks have

A write to one field of an EthLib state is a write to the same field of the reference state. -/

section Write

variable {preset : Preset} {fork : _root_.EthLib.Base.Fork} (s : BeaconState preset fork)

theorem toSpecState_with_eth1_data_votes (h : fork < .hegota) (value) :
    toSpecState { s with eth1DataVotes := fun _ => value } =
      { toSpecState s with
        eth1_data_votes := readList toSpecEth1Data value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_previous_epoch_participation (h : .altair ≤ fork) (value) :
    toSpecState { s with previousEpochParticipation := fun _ => value } =
      { toSpecState s with
        previous_epoch_participation := value.data.toList } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_current_epoch_participation (h : .altair ≤ fork) (value) :
    toSpecState { s with currentEpochParticipation := fun _ => value } =
      { toSpecState s with
        current_epoch_participation := value.data.toList } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_inactivity_scores (h : .altair ≤ fork) (value) :
    toSpecState { s with inactivityScores := fun _ => value } =
      { toSpecState s with
        inactivity_scores := readList UInt64.toNat value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_current_sync_committee (h : .altair ≤ fork) (value) :
    toSpecState { s with currentSyncCommittee := fun _ => value } =
      { toSpecState s with
        current_sync_committee := toSpecSyncCommittee value } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_next_sync_committee (h : .altair ≤ fork) (value) :
    toSpecState { s with nextSyncCommittee := fun _ => value } =
      { toSpecState s with
        next_sync_committee := toSpecSyncCommittee value } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_historical_summaries (h : .shapella ≤ fork) (value) :
    toSpecState { s with historicalSummaries := fun _ => value } =
      { toSpecState s with
        historical_summaries := readList toSpecHistoricalSummary value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_deposit_balance_to_consume (h : .pectra ≤ fork) (value) :
    toSpecState { s with depositBalanceToConsume := fun _ => value } =
      { toSpecState s with
        deposit_balance_to_consume := value.toNat } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_exit_balance_to_consume (h : .pectra ≤ fork) (value) :
    toSpecState { s with exitBalanceToConsume := fun _ => value } =
      { toSpecState s with
        exit_balance_to_consume := value.toNat } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_earliest_exit_epoch (h : .pectra ≤ fork) (value) :
    toSpecState { s with earliestExitEpoch := fun _ => value } =
      { toSpecState s with
        earliest_exit_epoch := value.toNat } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_pending_deposits (h : .pectra ≤ fork) (value) :
    toSpecState { s with pendingDeposits := fun _ => value } =
      { toSpecState s with
        pending_deposits := readList toSpecPendingDeposit value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_pending_consolidations (h : .pectra ≤ fork) (value) :
    toSpecState { s with pendingConsolidations := fun _ => value } =
      { toSpecState s with
        pending_consolidations := readList toSpecPendingConsolidation value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_proposer_lookahead (h : .fusaka ≤ fork) (value) :
    toSpecState { s with proposerLookahead := fun _ => value } =
      { toSpecState s with
        proposer_lookahead := value.toList.map UInt64.toNat } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_builder_pending_payments (h : .glamsterdam ≤ fork) (value) :
    toSpecState { s with builderPendingPayments := fun _ => value } =
      { toSpecState s with
        builder_pending_payments := value.elements.toList.map toSpecBuilderPendingPayment } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_builder_pending_withdrawals (h : .glamsterdam ≤ fork) (value) :
    toSpecState { s with builderPendingWithdrawals := fun _ => value } =
      { toSpecState s with
        builder_pending_withdrawals := readList toSpecBuilderPendingWithdrawal value.data } := by
  simp [toSpecState, fieldOr, h]

theorem toSpecState_with_ptc_window (h : .glamsterdam ≤ fork) (value) :
    toSpecState { s with ptcWindow := fun _ => value } =
      { toSpecState s with
        ptc_window :=
          value.elements.toList.map fun committee => committee.toList.map UInt64.toNat } := by
  simp [toSpecState, fieldOr, h]

end Write

end EpochProofs.EthLib
