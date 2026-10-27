import EpochProofs.Spec.Block.FuluTypes
import EpochProofs.Spec.Block.Withdrawals

/-!
# Reference: the Electra `process_withdrawals`, which Fulu keeps

Transcribed from `specs/capella` and `specs/electra/beacon-chain.md` (v1.7.0-beta.4). Gloas
did not change `get_pending_partial_withdrawals`, `get_validators_sweep_withdrawals`,
`update_next_withdrawal_index`, `update_pending_partial_withdrawals` and
`update_next_withdrawal_validator_index`, so this file reuses them from `Block/Withdrawals`.
-/

namespace EpochProofs.Spec

/-- ```python
@dataclass
class ExpectedWithdrawals:
    withdrawals: Sequence[Withdrawal]
    # [New in Electra:EIP7251]
    processed_partial_withdrawals_count: Uint64
    processed_sweep_withdrawals_count: Uint64
``` -/
structure FuluExpectedWithdrawals where
  withdrawals : List Withdrawal
  processed_partial_withdrawals_count : Uint64
  processed_sweep_withdrawals_count : Uint64

/-- ```python
def get_expected_withdrawals(state: BeaconState) -> ExpectedWithdrawals:
    withdrawal_index = state.next_withdrawal_index
    withdrawals: list[Withdrawal] = []

    # [New in Electra:EIP7251]
    # Get partial withdrawals
    partial_withdrawals, withdrawal_index, processed_partial_withdrawals_count = (
        get_pending_partial_withdrawals(state, withdrawal_index, withdrawals)
    )
    withdrawals.extend(partial_withdrawals)

    # Get validators sweep withdrawals
    validators_sweep_withdrawals, withdrawal_index, processed_validators_sweep_count = (
        get_validators_sweep_withdrawals(state, withdrawal_index, withdrawals)
    )
    withdrawals.extend(validators_sweep_withdrawals)

    return ExpectedWithdrawals(
        withdrawals,
        # [New in Electra:EIP7251]
        processed_partial_withdrawals_count,
        processed_validators_sweep_count,
    )
``` -/
def get_expected_withdrawals_fulu (p : Preset) (state : BeaconState) :
    SpecM FuluExpectedWithdrawals := do
  let withdrawal_index := state.next_withdrawal_index
  let withdrawals : List Withdrawal := []

  let (partial_withdrawals, withdrawal_index, processed_partial_withdrawals_count) ←
    get_pending_partial_withdrawals p state withdrawal_index withdrawals
  let withdrawals := withdrawals ++ partial_withdrawals

  let (validators_sweep_withdrawals, _, processed_validators_sweep_count) ←
    get_validators_sweep_withdrawals p state withdrawal_index withdrawals
  let withdrawals := withdrawals ++ validators_sweep_withdrawals

  pure {
    withdrawals
    processed_partial_withdrawals_count
    processed_sweep_withdrawals_count := processed_validators_sweep_count }

/-- ```python
def apply_withdrawals(state: BeaconState, withdrawals: Sequence[Withdrawal]) -> None:
    for withdrawal in withdrawals:
        decrease_balance(state, withdrawal.validator_index, withdrawal.amount)
``` -/
def apply_withdrawals_fulu (state : BeaconState) : List Withdrawal → SpecM BeaconState
  | [] => pure state
  | withdrawal :: rest => do
    let balances ← decrease_balance state.balances withdrawal.validator_index withdrawal.amount
    apply_withdrawals_fulu { state with balances } rest

/-- ```python
def process_withdrawals(state: BeaconState, payload: ExecutionPayload) -> None:
    # Get expected withdrawals
    expected = get_expected_withdrawals(state)
    assert list(payload.withdrawals) == expected.withdrawals

    # Apply expected withdrawals
    apply_withdrawals(state, expected.withdrawals)

    # Update withdrawals fields in the state
    update_next_withdrawal_index(state, expected.withdrawals)
    # [New in Electra:EIP7251]
    update_pending_partial_withdrawals(state, expected.processed_partial_withdrawals_count)
    update_next_withdrawal_validator_index(state, expected.withdrawals)
``` -/
def process_withdrawals_fulu (p : Preset) (state : BeaconState) (payload : FuluExecutionPayload) :
    SpecM BeaconState := do
  let expected ← get_expected_withdrawals_fulu p state
  if ¬ payload.withdrawals = expected.withdrawals then throw .assertionFailed

  let state ← apply_withdrawals_fulu state expected.withdrawals

  let state ← update_next_withdrawal_index state expected.withdrawals
  let state := update_pending_partial_withdrawals state expected.processed_partial_withdrawals_count
  update_next_withdrawal_validator_index p state expected.withdrawals

end EpochProofs.Spec
