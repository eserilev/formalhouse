import EpochProofs.Spec.Block.FuluTypes

/-!
# Reference: the Fulu `process_execution_payload`

Transcribed from `specs/phase0`, `specs/deneb` and `specs/fulu/beacon-chain.md`
(v1.7.0-beta.2). Gloas removes this function. The execution engine and the Fulu
`hash_tree_root` functions come from `FuluOracle`.
-/

namespace EpochProofs.Spec

/-- ```python
def compute_time_at_slot(state: BeaconState, slot: Slot) -> Uint64:
    slots_since_genesis = slot - GENESIS_SLOT
    return Uint64(state.genesis_time + slots_since_genesis * SLOT_DURATION_MS // 1000)
```

The pyspec notes that this function is unsafe for overflows. Each `uint64` step raises on
overflow, as in Python. `GENESIS_SLOT` is 0. -/
def compute_time_at_slot (c : FuluBlockConfig) (state : BeaconState) (slot : Slot) :
    SpecM Uint64 := do
  let slots_since_genesis ← uint64Sub slot 0
  uint64Add state.genesis_time
    (← uint64Div (← uint64Mul slots_since_genesis c.SLOT_DURATION_MS) 1000)

/-- `VERSIONED_HASH_VERSION_KZG`, the Deneb constant `Bytes1('0x01')`. -/
def VERSIONED_HASH_VERSION_KZG : UInt8 := 0x01

/-- ```python
def kzg_commitment_to_versioned_hash(kzg_commitment: KZGCommitment) -> VersionedHash:
    return VersionedHash(VERSIONED_HASH_VERSION_KZG + sha256(kzg_commitment)[1:])
``` -/
def kzg_commitment_to_versioned_hash (o : Oracle) (kzg_commitment : KZGCommitment) : Bytes32 :=
  (#v[VERSIONED_HASH_VERSION_KZG] ++ (o.hash kzg_commitment.toList).extract 1 32).cast
    (by decide)

/-- ```python
def process_execution_payload(
    state: BeaconState, body: BeaconBlockBody, execution_engine: ExecutionEngine
) -> None:
    payload = body.execution_payload

    # Verify consistency of the parent hash with respect to the previous execution payload header
    assert payload.parent_hash == state.latest_execution_payload_header.block_hash
    # Verify prev_randao
    assert payload.prev_randao == get_randao_mix(state, get_current_epoch(state))
    # Verify timestamp
    assert payload.timestamp == compute_time_at_slot(state, state.slot)
    # [Modified in Fulu:EIP7892]
    # Verify commitments are under limit
    assert (
        len(body.blob_kzg_commitments)
        <= get_blob_parameters(get_current_epoch(state)).max_blobs_per_block
    )

    # Compute versioned hashes
    versioned_hashes = VersionedHashes()
    for commitment in body.blob_kzg_commitments:
        versioned_hashes.append(kzg_commitment_to_versioned_hash(commitment))

    # Verify the execution payload is valid
    assert execution_engine.verify_and_notify_new_payload(
        NewPayloadRequest(
            execution_payload=payload,
            versioned_hashes=versioned_hashes,
            parent_beacon_block_root=state.latest_block_header.parent_root,
            execution_requests=body.execution_requests,
        )
    )

    # Cache execution payload header
    state.latest_execution_payload_header = ExecutionPayloadHeader(
        parent_hash=payload.parent_hash,
        fee_recipient=payload.fee_recipient,
        state_root=payload.state_root,
        receipts_root=payload.receipts_root,
        logs_bloom=payload.logs_bloom,
        prev_randao=payload.prev_randao,
        block_number=payload.block_number,
        gas_limit=payload.gas_limit,
        gas_used=payload.gas_used,
        timestamp=payload.timestamp,
        extra_data=payload.extra_data,
        base_fee_per_gas=payload.base_fee_per_gas,
        block_hash=payload.block_hash,
        transactions_root=hash_tree_root(payload.transactions),
        withdrawals_root=hash_tree_root(payload.withdrawals),
        blob_gas_used=payload.blob_gas_used,
        excess_blob_gas=payload.excess_blob_gas,
    )
```

`VersionedHashes` is a list with an SSZ limit of `MAX_BLOB_COMMITMENTS_PER_BLOCK`, the same
limit as `blob_kzg_commitments`, so the appends never raise. -/
def process_execution_payload_fulu (p : Preset) (o : Oracle) (fo : FuluOracle)
    (c : FuluBlockConfig) (fstate : FuluState) (body : FuluBeaconBlockBody) :
    SpecM FuluState := do
  let state := fstate.state
  let payload := body.execution_payload

  if ¬ payload.parent_hash = fstate.latest_execution_payload_header.block_hash then
    throw .assertionFailed
  if ¬ payload.prev_randao = (← get_randao_mix p state (← get_current_epoch p state)) then
    throw .assertionFailed
  if ¬ payload.timestamp = (← compute_time_at_slot c state state.slot) then
    throw .assertionFailed
  if ¬ body.blob_kzg_commitments.length ≤ c.max_blobs_per_block (← get_current_epoch p state) then
    throw .assertionFailed

  let versioned_hashes := body.blob_kzg_commitments.map (kzg_commitment_to_versioned_hash o)

  if ¬ fo.verify_and_notify_new_payload {
      execution_payload := payload
      versioned_hashes
      parent_beacon_block_root := state.latest_block_header.parent_root
      execution_requests := body.execution_requests } then
    throw .assertionFailed

  pure { fstate with
    latest_execution_payload_header := {
      parent_hash := payload.parent_hash
      fee_recipient := payload.fee_recipient
      state_root := payload.state_root
      receipts_root := payload.receipts_root
      logs_bloom := payload.logs_bloom
      prev_randao := payload.prev_randao
      block_number := payload.block_number
      gas_limit := payload.gas_limit
      gas_used := payload.gas_used
      timestamp := payload.timestamp
      extra_data := payload.extra_data
      base_fee_per_gas := payload.base_fee_per_gas
      block_hash := payload.block_hash
      transactions_root := fo.hash_tree_root_Transactions payload.transactions
      withdrawals_root := fo.hash_tree_root_FuluWithdrawals payload.withdrawals
      blob_gas_used := payload.blob_gas_used
      excess_blob_gas := payload.excess_blob_gas } }

end EpochProofs.Spec
