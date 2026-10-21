import EpochProofs.Spec.Block.Types
import EthCLSpecs.Proofs.Fulu.Run

/-!
# The map from an Etheorem Fulu state to a reference state

Etheorem (https://github.com/etheorem/etheorem) stores numbers as `UInt64` and lists as
`Vector`, `SSZList` and `Bitvector`. The reference stores numbers as `Nat` and lists as `List`.
`absEState` reads an Etheorem Fulu `BeaconState` as a reference `BeaconState`. It keeps every
Fulu field. The reference fields that Gloas adds (builders, builder payments and withdrawals,
the bid, the payload withdrawals, the PTC window) read as empty, and `latest_block_hash` reads
the block hash of the latest execution payload header. No Fulu epoch step reads or writes them.

Each step proof states that the two runs agree through `absEState`. The `@[simp]` lemmas here
read and write one field through the map.
-/

namespace EpochProofs.Etheorem.Fulu

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

variable [EthCLSpecs.Fulu.Preset]

abbrev EState := EthCLSpecs.Fulu.BeaconState

def absValidator (v : EthCLSpecs.Fulu.Validator) : Spec.Validator :=
  { pubkey := v.pubkey
    withdrawal_credentials := v.withdrawalCredentials
    effective_balance := v.effectiveBalance.toNat
    slashed := v.slashed
    activation_eligibility_epoch := v.activationEligibilityEpoch.toNat
    activation_epoch := v.activationEpoch.toNat
    exit_epoch := v.exitEpoch.toNat
    withdrawable_epoch := v.withdrawableEpoch.toNat }

def absPendingDeposit (d : EthCLSpecs.Fulu.PendingDeposit) : Spec.PendingDeposit :=
  { pubkey := d.pubkey
    withdrawal_credentials := d.withdrawalCredentials
    amount := d.amount.toNat
    signature := d.signature
    slot := d.slot.toNat }

def absPendingPartialWithdrawal (w : EthCLSpecs.Fulu.PendingPartialWithdrawal) :
    Spec.PendingPartialWithdrawal :=
  { validator_index := w.validatorIndex.toNat
    amount := w.amount.toNat
    withdrawable_epoch := w.withdrawableEpoch.toNat }

def absPendingConsolidation (c : EthCLSpecs.Fulu.PendingConsolidation) :
    Spec.PendingConsolidation :=
  { source_index := c.sourceIndex.toNat
    target_index := c.targetIndex.toNat }

def absCheckpoint (c : EthCLSpecs.Fulu.Checkpoint) : Spec.Checkpoint :=
  { epoch := c.epoch.toNat, root := c.root }

def absFork (f : EthCLSpecs.Fulu.Fork) : Spec.Fork :=
  { previous_version := f.previousVersion
    current_version := f.currentVersion
    epoch := f.epoch.toNat }

def absHeader (h : EthCLSpecs.Fulu.BeaconBlockHeader) : Spec.BeaconBlockHeader :=
  { slot := h.slot.toNat
    proposer_index := h.proposerIndex.toNat
    parent_root := h.parentRoot
    state_root := h.stateRoot
    body_root := h.bodyRoot }

def absEth1Data (d : EthCLSpecs.Fulu.Eth1Data) : Spec.Eth1Data :=
  { deposit_root := d.depositRoot
    deposit_count := d.depositCount.toNat
    block_hash := d.blockHash }

def absSyncCommittee (c : EthCLSpecs.Fulu.SyncCommittee) : Spec.SyncCommittee :=
  { pubkeys := c.pubkeys.toList, aggregate_pubkey := c.aggregatePubkey }

def absHistoricalSummary (h : EthCLSpecs.Fulu.HistoricalSummary) : Spec.HistoricalSummary :=
  { block_summary_root := h.blockSummaryRoot
    state_summary_root := h.stateSummaryRoot }

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

/-! ## Reading one field -/

section Read

variable (e : EState)

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

end Read

/-! ## Writing one field

A write to an Etheorem field is the same write to the reference field. -/

section Write

variable (e : EState)

theorem absEState_set_balances (b : SSZList EthCLSpecs.Fulu.Gwei
      EthCLSpecs.Fulu.Const.validatorRegistryLimit) :
    absEState { e with balances := b } =
      { absEState e with balances := b.toList.map UInt64.toNat } := rfl

theorem absEState_set_validators (v : SSZList EthCLSpecs.Fulu.Validator
      EthCLSpecs.Fulu.Const.validatorRegistryLimit) :
    absEState { e with validators := v } =
      { absEState e with validators := v.toList.map absValidator } := rfl

theorem absEState_set_inactivityScores (s : SSZList UInt64
      EthCLSpecs.Fulu.Const.validatorRegistryLimit) :
    absEState { e with inactivityScores := s } =
      { absEState e with inactivity_scores := s.toList.map UInt64.toNat } := rfl

theorem absEState_set_participation
    (prev cur : SSZList EthCLSpecs.Fulu.ParticipationFlags
      EthCLSpecs.Fulu.Const.validatorRegistryLimit) :
    absEState { e with previousEpochParticipation := prev, currentEpochParticipation := cur } =
      { absEState e with previous_epoch_participation := prev.toList,
                         current_epoch_participation := cur.toList } := rfl

theorem absEState_set_slashings (s : Vector EthCLSpecs.Fulu.Gwei
      EthCLSpecs.Fulu.Const.epochsPerSlashingsVector) :
    absEState { e with slashings := s } =
      { absEState e with slashings := s.toList.map UInt64.toNat } := rfl

theorem absEState_set_randaoMixes (m : Vector EthCLSpecs.Fulu.Bytes32
      EthCLSpecs.Fulu.Const.epochsPerHistoricalVector) :
    absEState { e with randaoMixes := m } = { absEState e with randao_mixes := m.toList } := rfl

theorem absEState_set_eth1DataVotes (v : SSZList EthCLSpecs.Fulu.Eth1Data
      (EthCLSpecs.Fulu.Const.epochsPerEth1VotingPeriod * EthCLSpecs.Fulu.Const.slotsPerEpoch)) :
    absEState { e with eth1DataVotes := v } =
      { absEState e with eth1_data_votes := v.toList.map absEth1Data } := rfl

theorem absEState_set_historicalSummaries (h : SSZList EthCLSpecs.Fulu.HistoricalSummary
      EthCLSpecs.Fulu.Const.historicalRootsLimit) :
    absEState { e with historicalSummaries := h } =
      { absEState e with historical_summaries := h.toList.map absHistoricalSummary } := rfl

theorem absEState_set_syncCommittees (cur next : EthCLSpecs.Fulu.SyncCommittee) :
    absEState { e with currentSyncCommittee := cur, nextSyncCommittee := next } =
      { absEState e with current_sync_committee := absSyncCommittee cur,
                         next_sync_committee := absSyncCommittee next } := rfl

theorem absEState_set_proposerLookahead (l : Vector EthCLSpecs.Fulu.ValidatorIndex
      (2 * EthCLSpecs.Fulu.Const.slotsPerEpoch)) :
    absEState { e with proposerLookahead := l } =
      { absEState e with proposer_lookahead := l.toList.map UInt64.toNat } := rfl

theorem absEState_set_pendingDeposits (d : SSZList EthCLSpecs.Fulu.PendingDeposit
      EthCLSpecs.Fulu.Const.pendingDepositsLimit) :
    absEState { e with pendingDeposits := d } =
      { absEState e with pending_deposits := d.toList.map absPendingDeposit } := rfl

theorem absEState_set_pendingConsolidations (c : SSZList EthCLSpecs.Fulu.PendingConsolidation
      EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) :
    absEState { e with pendingConsolidations := c } =
      { absEState e with pending_consolidations := c.toList.map absPendingConsolidation } := rfl

theorem absEState_set_justification
    (bits : Bitvector EthCLSpecs.Fulu.Const.justificationBitsLength)
    (prev cur fin : EthCLSpecs.Fulu.Checkpoint) :
    absEState { e with justificationBits := bits, previousJustifiedCheckpoint := prev,
                       currentJustifiedCheckpoint := cur, finalizedCheckpoint := fin } =
      { absEState e with justification_bits := absBits bits,
                         previous_justified_checkpoint := absCheckpoint prev,
                         current_justified_checkpoint := absCheckpoint cur,
                         finalized_checkpoint := absCheckpoint fin } := rfl

theorem absEState_set_churn (dbtc ebtc ebc : EthCLSpecs.Fulu.Gwei)
    (eee ece : EthCLSpecs.Fulu.Epoch) :
    absEState { e with depositBalanceToConsume := dbtc, exitBalanceToConsume := ebtc,
                       earliestExitEpoch := eee, consolidationBalanceToConsume := ebc,
                       earliestConsolidationEpoch := ece } =
      { absEState e with deposit_balance_to_consume := dbtc.toNat,
                         exit_balance_to_consume := ebtc.toNat,
                         earliest_exit_epoch := eee.toNat,
                         consolidation_balance_to_consume := ebc.toNat,
                         earliest_consolidation_epoch := ece.toNat } := rfl

end Write

end EpochProofs.Etheorem.Fulu
