import EpochProofs.Spec.Fulu
import EpochProofs.Spec.Block.Types

/-!
# Fulu block containers, `FuluState` and `FuluOracle`

Transcribed from `specs/deneb`, `specs/electra` and `specs/fulu/beacon-chain.md`
(v1.7.0-beta.4). Names and field order match the spec. Containers that Fulu shares with Gloas
(slashings, attestations, exits, sync aggregate, the three request types) come from
`Block/Types`.

The Fulu `BeaconState` is the Gloas `BeaconState` without the ePBS fields, plus
`latest_execution_payload_header`. `FuluState` is the Gloas `BeaconState` with that one extra
field. The Fulu block functions do not read or write the Gloas-only fields.

The shared `Oracle` has no Fulu types. `FuluOracle` holds the Fulu `hash_tree_root` functions
and the execution engine.
-/

namespace EpochProofs.Spec

/-- The Deneb `ExecutionPayload`, which Electra and Fulu keep. `logs_bloom` is a
`ByteVector[BYTES_PER_LOGS_BLOOM]`. `base_fee_per_gas` is a `Uint256`. -/
structure FuluExecutionPayload where
  parent_hash : Hash32 := Bytes32.zero
  fee_recipient : ExecutionAddress := ExecutionAddress.zero
  state_root : Bytes32 := Bytes32.zero
  receipts_root : Bytes32 := Bytes32.zero
  logs_bloom : List UInt8 := []
  prev_randao : Bytes32 := Bytes32.zero
  block_number : Uint64 := 0
  gas_limit : Uint64 := 0
  gas_used : Uint64 := 0
  timestamp : Uint64 := 0
  extra_data : List UInt8 := []
  base_fee_per_gas : Nat := 0
  block_hash : Hash32 := Bytes32.zero
  transactions : List (List UInt8) := []
  withdrawals : List Withdrawal := []
  blob_gas_used : Uint64 := 0
  excess_blob_gas : Uint64 := 0
  deriving DecidableEq, Repr

/-- The Deneb `ExecutionPayloadHeader`, which Electra and Fulu keep. -/
structure ExecutionPayloadHeader where
  parent_hash : Hash32 := Bytes32.zero
  fee_recipient : ExecutionAddress := ExecutionAddress.zero
  state_root : Bytes32 := Bytes32.zero
  receipts_root : Bytes32 := Bytes32.zero
  logs_bloom : List UInt8 := []
  prev_randao : Bytes32 := Bytes32.zero
  block_number : Uint64 := 0
  gas_limit : Uint64 := 0
  gas_used : Uint64 := 0
  timestamp : Uint64 := 0
  extra_data : List UInt8 := []
  base_fee_per_gas : Nat := 0
  block_hash : Hash32 := Bytes32.zero
  transactions_root : Root := Bytes32.zero
  withdrawals_root : Root := Bytes32.zero
  blob_gas_used : Uint64 := 0
  excess_blob_gas : Uint64 := 0
  deriving DecidableEq, Repr

/-- The Electra `ExecutionRequests`, which Fulu keeps. Gloas adds the builder lists. -/
structure FuluExecutionRequests where
  deposits : List DepositRequest := []
  withdrawals : List WithdrawalRequest := []
  consolidations : List ConsolidationRequest := []
  deriving DecidableEq, Repr

/-- The Electra `BeaconBlockBody`, which Fulu keeps. The operation lists have SSZ limits by
type. -/
structure FuluBeaconBlockBody where
  randao_reveal : BLSSignature := BLSSignature.zero
  eth1_data : Eth1Data := {}
  graffiti : Bytes32 := Bytes32.zero
  proposer_slashings : List ProposerSlashing := []
  attester_slashings : List AttesterSlashing := []
  attestations : List Attestation := []
  deposits : List Deposit := []
  voluntary_exits : List SignedVoluntaryExit := []
  sync_aggregate : SyncAggregate := {}
  execution_payload : FuluExecutionPayload := {}
  bls_to_execution_changes : List SignedBLSToExecutionChange := []
  blob_kzg_commitments : List KZGCommitment := []
  execution_requests : FuluExecutionRequests := {}
  deriving DecidableEq, Repr

structure FuluBeaconBlock where
  slot : Slot := 0
  proposer_index : ValidatorIndex := 0
  parent_root : Root := Bytes32.zero
  state_root : Root := Bytes32.zero
  body : FuluBeaconBlockBody := {}
  deriving DecidableEq, Repr

structure FuluSignedBeaconBlock where
  message : FuluBeaconBlock := {}
  signature : BLSSignature := BLSSignature.zero
  deriving DecidableEq, Repr

/-- The Electra `NewPayloadRequest`, which Fulu keeps. -/
structure FuluNewPayloadRequest where
  execution_payload : FuluExecutionPayload := {}
  versioned_hashes : List Bytes32 := []
  parent_beacon_block_root : Root := Bytes32.zero
  execution_requests : FuluExecutionRequests := {}
  deriving DecidableEq, Repr

/-- The Fulu `BeaconState`: the Gloas `BeaconState` (its Gloas-only fields unused) plus the
payload header. -/
structure FuluState where
  state : BeaconState
  latest_execution_payload_header : ExecutionPayloadHeader := {}

/-- The Fulu `hash_tree_root` functions and the execution engine. -/
structure FuluOracle where
  hash_tree_root_FuluBeaconBlockBody : FuluBeaconBlockBody → Root
  hash_tree_root_FuluBeaconBlock : FuluBeaconBlock → Root
  hash_tree_root_FuluState : FuluState → Root
  /-- `hash_tree_root` on `Transactions`, a `List[Transaction, MAX_TRANSACTIONS_PER_PAYLOAD]`. -/
  hash_tree_root_Transactions : List (List UInt8) → Root
  /-- `hash_tree_root` on the Electra `Withdrawals`, a
  `List[Withdrawal, MAX_WITHDRAWALS_PER_PAYLOAD]`. -/
  hash_tree_root_FuluWithdrawals : List Withdrawal → Root
  /-- `execution_engine.verify_and_notify_new_payload(new_payload_request)`. -/
  verify_and_notify_new_payload : FuluNewPayloadRequest → Bool

/-- The config values that the Fulu block functions read and `Preset` does not hold. The
defaults are the mainnet values. `max_blobs_per_block epoch` is
`get_blob_parameters(epoch).max_blobs_per_block`. -/
structure FuluBlockConfig where
  SLOT_DURATION_MS : Uint64 := 12000
  max_blobs_per_block : Epoch → Uint64

/-- The Gloas `BeaconBlockBody` fields that `process_randao` and `process_eth1_data` read. Those
two functions read only `randao_reveal` and `eth1_data`, so they run on this view of a Fulu
body. -/
def FuluBeaconBlockBody.view (body : FuluBeaconBlockBody) : BeaconBlockBody :=
  { randao_reveal := body.randao_reveal, eth1_data := body.eth1_data }

end EpochProofs.Spec
