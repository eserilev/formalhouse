import EpochProofs.Spec.Block.FuluWithdrawals
import EpochProofs.Spec.Block.FuluPayload
import EpochProofs.Spec.Block.FuluOperations
import EpochProofs.Spec.Block.Header
import EpochProofs.Spec.Block.Randao
import EpochProofs.Spec.Block.Eth1Data
import EpochProofs.Spec.Block.SyncAggregate

/-!
# Reference: the Fulu `process_block_header` and `process_block`

Transcribed from `specs/phase0` and `specs/fulu/beacon-chain.md` (v1.7.0-beta.4).
`process_randao`, `process_eth1_data` and `process_sync_aggregate` are shared with Gloas.
`process_randao` and `process_eth1_data` read only `randao_reveal` and `eth1_data`, so they run
on `FuluBeaconBlockBody.view`.
-/

namespace EpochProofs.Spec

/-- `process_block_header` on a Fulu block. The pyspec text is the phase0 text, quoted at
`process_block_header` in `Block/Header`. Only the type of `block.body` differs, so its root
comes from `FuluOracle`. -/
def process_block_header_fulu (p : Preset) (o : Oracle) (fo : FuluOracle) (state : BeaconState)
    (block : FuluBeaconBlock) : SpecM BeaconState := do
  if ¬ block.slot = state.slot then throw .assertionFailed
  if ¬ block.slot > state.latest_block_header.slot then throw .assertionFailed
  if ¬ block.proposer_index = (← get_beacon_proposer_index p state) then throw .assertionFailed
  if ¬ block.parent_root = o.hash_tree_root_BeaconBlockHeader state.latest_block_header then
    throw .assertionFailed
  let state := { state with
    latest_block_header := {
      slot := block.slot
      proposer_index := block.proposer_index
      parent_root := block.parent_root
      state_root := Bytes32.zero
      body_root := fo.hash_tree_root_FuluBeaconBlockBody block.body } }

  let proposer ← listGet state.validators block.proposer_index
  if proposer.slashed then throw .assertionFailed
  pure state

/-- ```python
def process_block(state: BeaconState, block: BeaconBlock) -> None:
    process_block_header(state, block)
    process_withdrawals(state, block.body.execution_payload)
    process_execution_payload(state, block.body, EXECUTION_ENGINE)
    process_randao(state, block.body)
    process_eth1_data(state, block.body)
    # [Modified in Fulu]
    process_operations(state, block.body)
    process_sync_aggregate(state, block.body.sync_aggregate)
``` -/
def process_block_fulu (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fstate : FuluState) (block : FuluBeaconBlock) : SpecM FuluState := do
  let state ← process_block_header_fulu p o fo fstate.state block
  let state ← process_withdrawals_fulu p state block.body.execution_payload
  let fstate ← process_execution_payload_fulu p o fo c { fstate with state } block.body
  let state ← process_randao p o fstate.state block.body.view
  let state ← process_eth1_data p state block.body.view
  let state ← process_operations_fulu p o f state block.body
  let state ← process_sync_aggregate p o state block.body.sync_aggregate
  pure { fstate with state }

end EpochProofs.Spec
