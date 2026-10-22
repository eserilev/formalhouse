import EpochProofs.Spec.Block.FuluBlock
import EpochProofs.Spec.FuluEpoch
import EpochProofs.Spec.Slots

/-!
# Reference: the Fulu `process_slot`, `process_slots` and `state_transition`

Transcribed from `specs/phase0/beacon-chain.md` (v1.7.0-beta.4). Fulu keeps the phase0 text of
these functions. Only the types differ: the state is `FuluState`, so its root comes from
`FuluOracle`, and the block is a `FuluSignedBeaconBlock`.

Fulu `process_slot` has no `execution_payload_availability` write. That write is new in Gloas.

`process_epoch` is a parameter `processEpoch` on the shared `BeaconState`. It does not read or
write the payload header, so `process_slots_fulu` runs it on `fstate.state`.
-/

namespace EpochProofs.Spec

/-- ```python
def process_slot(state: BeaconState) -> None:
    slot_index = state.slot % SLOTS_PER_HISTORICAL_ROOT
    # Cache state root
    previous_state_root = hash_tree_root(state)
    state.state_roots[slot_index] = previous_state_root
    # Cache latest block header state root
    if state.latest_block_header.state_root == Bytes32():
        state.latest_block_header.state_root = previous_state_root
    # Cache block root
    previous_block_root = hash_tree_root(state.latest_block_header)
    state.block_roots[slot_index] = previous_block_root
``` -/
def process_slot_fulu (p : Preset) (o : Oracle) (fo : FuluOracle) (fstate : FuluState) :
    SpecM FuluState := do
  let state := fstate.state
  let slot_index ← uint64Mod state.slot p.SLOTS_PER_HISTORICAL_ROOT
  let previous_state_root := fo.hash_tree_root_FuluState fstate
  let state := { state with
    state_roots := ← listSet state.state_roots slot_index previous_state_root }
  let state :=
    if state.latest_block_header.state_root == Bytes32.zero then
      { state with
        latest_block_header := { state.latest_block_header with
          state_root := previous_state_root } }
    else state
  let previous_block_root := o.hash_tree_root_BeaconBlockHeader state.latest_block_header
  pure { fstate with state := { state with
    block_roots := ← listSet state.block_roots slot_index previous_block_root } }

/-- The `while` loop of the Fulu `process_slots`, with at most `fuel` iterations. It has the
shape of `process_slots_loop`. -/
def process_slots_loop_fulu (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (slot : Slot) :
    Nat → FuluState → SpecM FuluState
  | 0, fstate => pure fstate
  | fuel + 1, fstate => do
    if fstate.state.slot < slot then
      let fstate ← process_slot_fulu p o fo fstate
      let fstate ←
        if (← uint64Mod (← uint64Add fstate.state.slot 1) p.SLOTS_PER_EPOCH) == 0 then
          pure { fstate with state := ← processEpoch fstate.state }
        else pure fstate
      let fstate := { fstate with state := { fstate.state with
        slot := ← uint64Add fstate.state.slot 1 } }
      process_slots_loop_fulu p o fo processEpoch slot fuel fstate
    else
      pure fstate

/-- ```python
def process_slots(state: BeaconState, slot: Slot) -> None:
    assert state.slot < slot
    while state.slot < slot:
        process_slot(state)
        # Process epoch on the start slot of the next epoch
        if (state.slot + 1) % SLOTS_PER_EPOCH == 0:
            process_epoch(state)
        state.slot = state.slot + 1
```

The `while` is `process_slots_loop_fulu` with `slot - state.slot` iterations. -/
def process_slots_fulu (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (fstate : FuluState) (slot : Slot) :
    SpecM FuluState := do
  if ¬ fstate.state.slot < slot then throw .assertionFailed
  process_slots_loop_fulu p o fo processEpoch slot (slot - fstate.state.slot) fstate

/-- ```python
def verify_block_signature(state: BeaconState, signed_block: SignedBeaconBlock) -> bool:
    proposer = state.validators[signed_block.message.proposer_index]
    signing_root = compute_signing_root(
        signed_block.message, get_domain(state, DOMAIN_BEACON_PROPOSER)
    )
    return bls.Verify(proposer.pubkey, signing_root, signed_block.signature)
``` -/
def verify_block_signature_fulu (p : Preset) (o : Oracle) (fo : FuluOracle) (state : BeaconState)
    (signed_block : FuluSignedBeaconBlock) : SpecM Bool := do
  let proposer ← listGet state.validators signed_block.message.proposer_index
  let signing_root := compute_signing_root o
    (fo.hash_tree_root_FuluBeaconBlock signed_block.message)
    (← get_domain p o state DOMAIN_BEACON_PROPOSER)
  pure (o.bls_Verify proposer.pubkey signing_root signed_block.signature)

/-- ```python
def state_transition(
    state: BeaconState, signed_block: SignedBeaconBlock, validate_result: bool = True
) -> None:
    block = signed_block.message
    # Process slots (including those with no blocks) since block
    process_slots(state, block.slot)
    # Verify signature
    if validate_result:
        assert verify_block_signature(state, signed_block)
    # Process block
    process_block(state, block)
    # Verify state root
    if validate_result:
        assert block.state_root == hash_tree_root(state)
```

`process_slots_fulu` runs the Fulu `process_epoch` at the end of each epoch. -/
def state_transition_fulu (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fstate : FuluState) (signed_block : FuluSignedBeaconBlock)
    (validate_result : Bool := true) : SpecM FuluState := do
  let block := signed_block.message
  let fstate ← process_slots_fulu p o fo (process_epoch_fulu p f o) fstate block.slot
  if validate_result then
    if ¬ (← verify_block_signature_fulu p o fo fstate.state signed_block) then
      throw .assertionFailed
  let fstate ← process_block_fulu p o fo f c fstate block
  if validate_result then
    if ¬ block.state_root = fo.hash_tree_root_FuluState fstate then throw .assertionFailed
  pure fstate

end EpochProofs.Spec
