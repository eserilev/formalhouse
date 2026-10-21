import EpochProofs.Spec.JustificationFinalization

/-!
# Lighthouse model: `weigh_justification_and_finalization`

`lhWeighJustification` follows `justification.rs`. `lhWeighJustificationAndFinalization` follows
the caller in `weigh_justification_and_finalization.rs`: it reads the four bits, runs the pure
function, then reads the block roots and writes the checkpoints and the bits. Lighthouse reads
the block roots from the state before the update, so the model reads them from `s`.

Lighthouse reads the three balances from the progressive balances cache and the total active
balance cache. `lhJustificationAndFinalization` takes the spec values. Stack #27 proves that the
caches hold these values.

A Lighthouse state always has four justification bits (`BitVector<U4>`). For a list of another
length, `lhJustificationAndFinalization` runs the spec function. No Lighthouse state reaches this
case.
-/

namespace EpochProofs.Spec

structure LhJustificationBits where
  bit0 : Bool
  bit1 : Bool
  bit2 : Bool
  bit3 : Bool
  deriving DecidableEq, Repr

inductive LhNewFinalized where
  | unchanged
  | oldPreviousJustified
  | oldCurrentJustified
  deriving DecidableEq, Repr

structure LhJustificationOutcome where
  justify_previous : Bool
  justify_current : Bool
  bits : LhJustificationBits
  finalized : LhNewFinalized
  deriving DecidableEq, Repr

def lhFinalizeStep (enabled : Bool) (source_epoch offset current_epoch : Uint64)
    (choice finalized : LhNewFinalized) : SpecM LhNewFinalized :=
  if enabled then do
    if (← uint64Add source_epoch offset) = current_epoch then pure choice else pure finalized
  else pure finalized

def lhWeighJustification (current_epoch old_previous_justified_epoch
    old_current_justified_epoch : Uint64) (bits : LhJustificationBits)
    (total_active_balance previous_target_balance current_target_balance : Gwei) :
    SpecM LhJustificationOutcome := do
  let threshold ← uint64Mul total_active_balance 2
  let justify_previous := decide ((← uint64Mul previous_target_balance 3) ≥ threshold)
  let justify_current := decide ((← uint64Mul current_target_balance 3) ≥ threshold)
  let bits : LhJustificationBits :=
    { bit0 := justify_current, bit1 := bits.bit0 || justify_previous, bit2 := bits.bit1,
      bit3 := bits.bit2 }
  let finalized ← lhFinalizeStep (bits.bit1 && bits.bit2 && bits.bit3)
    old_previous_justified_epoch 3 current_epoch .oldPreviousJustified .unchanged
  let finalized ← lhFinalizeStep (bits.bit1 && bits.bit2)
    old_previous_justified_epoch 2 current_epoch .oldPreviousJustified finalized
  let finalized ← lhFinalizeStep (bits.bit0 && bits.bit1 && bits.bit2)
    old_current_justified_epoch 2 current_epoch .oldCurrentJustified finalized
  let finalized ← lhFinalizeStep (bits.bit0 && bits.bit1)
    old_current_justified_epoch 1 current_epoch .oldCurrentJustified finalized
  pure { justify_previous, justify_current, bits, finalized }

def lhWeighJustificationAndFinalization (p : Preset) (s : BeaconState)
    (total_active_balance previous_target_balance current_target_balance : Gwei) :
    SpecM BeaconState := do
  let state := s
  let previous_epoch ← get_previous_epoch p state
  let current_epoch ← get_current_epoch p state
  let old_previous_justified_checkpoint := state.previous_justified_checkpoint
  let old_current_justified_checkpoint := state.current_justified_checkpoint
  let bits : LhJustificationBits :=
    { bit0 := ← listGet state.justification_bits 0, bit1 := ← listGet state.justification_bits 1,
      bit2 := ← listGet state.justification_bits 2, bit3 := ← listGet state.justification_bits 3 }
  let outcome ← lhWeighJustification current_epoch old_previous_justified_checkpoint.epoch
    old_current_justified_checkpoint.epoch bits total_active_balance previous_target_balance
    current_target_balance
  let state := { state with previous_justified_checkpoint := old_current_justified_checkpoint }
  let state ← (do
    if outcome.justify_previous then
      pure { state with
        current_justified_checkpoint :=
          { epoch := previous_epoch, root := ← get_block_root p s previous_epoch } }
    else pure state)
  let state ← (do
    if outcome.justify_current then
      pure { state with
        current_justified_checkpoint :=
          { epoch := current_epoch, root := ← get_block_root p s current_epoch } }
    else pure state)
  let state := { state with
    justification_bits :=
      [outcome.bits.bit0, outcome.bits.bit1, outcome.bits.bit2, outcome.bits.bit3] }
  match outcome.finalized with
  | .unchanged => pure state
  | .oldPreviousJustified =>
    pure { state with finalized_checkpoint := old_previous_justified_checkpoint }
  | .oldCurrentJustified =>
    pure { state with finalized_checkpoint := old_current_justified_checkpoint }

def lhJustificationAndFinalization (p : Preset) (state : BeaconState) : SpecM BeaconState :=
  if state.justification_bits.length ≠ JUSTIFICATION_BITS_LENGTH then
    process_justification_and_finalization p state
  else do
    if (← get_current_epoch p state) ≤ GENESIS_EPOCH + 1 then
      return state
    let previous_indices ← get_unslashed_participating_indices p state TIMELY_TARGET_FLAG_INDEX
      (← get_previous_epoch p state)
    let current_indices ← get_unslashed_participating_indices p state TIMELY_TARGET_FLAG_INDEX
      (← get_current_epoch p state)
    let total_active_balance ← get_total_active_balance p state
    let previous_target_balance ← get_total_balance p state previous_indices
    let current_target_balance ← get_total_balance p state current_indices
    lhWeighJustificationAndFinalization p state total_active_balance previous_target_balance
      current_target_balance

end EpochProofs.Spec
