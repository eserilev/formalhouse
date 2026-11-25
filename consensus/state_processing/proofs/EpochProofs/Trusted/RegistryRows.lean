import EpochProofs.Equiv.SinglePassStep

/-!
# The `RegistryRows` contract

`single_pass_rows` in `registry_rows.rs` is generic over the trait `RegistryRows`.
`single_pass.rs` implements the trait over the milhouse lists and caches of the state. Aeneas
does not read that implementation, so the theorems take `ValidatorRowsMatchSpec` as a hypothesis.
This file
is the only statement the proofs trust about the single-pass loop.

`ValidatorRowsMatchSpec` says what `StateRows` in `single_pass.rs` does, in spec terms:

- `row_count` returns the number of rows.
- `apply_step` on row `i` reads the row, runs `single_pass_step` on it, writes the new row back
  and changes no other row. A row read or write never fails.

The row inputs are the spec inputs, with one exception: `single_pass.rs` reads the base reward
only for an eligible validator and passes 0 otherwise. The steps read the base reward only for
an eligible validator.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

open state_processing.per_epoch_processing.single_pass_step (ValidatorRow ExitChurn StepContext RowInputs)

/-- The Rust trait `RegistryRows`. -/
abbrev LighthouseRegistryRows (R E : Type) := per_epoch_processing.registry_rows.RegistryRows R E

/-- Row `r` after `single_pass_step` wrote the Lighthouse row `lr'`. -/
def rowAfter (r : Spec.Row) (lr' : ValidatorRow) : Spec.Row :=
  { r with
    balance := lr'.balance.val
    inactivity_score := lr'.inactivity_score.val
    validator := { r.validator with
      effective_balance := lr'.effective_balance.val
      activation_eligibility_epoch := lr'.activation_eligibility_epoch.val
      activation_epoch := lr'.activation_epoch.val
      exit_epoch := lr'.exit_epoch.val
      withdrawable_epoch := lr'.withdrawable_epoch.val } }

/-- The row inputs that `single_pass.rs` reads hold the spec inputs. The base reward is the
spec base reward, or the validator is not eligible. -/
structure RowInputsMatchSpec (p : Spec.Preset) (previous_epoch : Spec.Epoch) (i : RowInputs)
    (inputs : Spec.LighthouseRowInputs) (r : Spec.Row) : Prop where
  base_reward : i.base_reward.val = inputs.base_reward
    ∨ Spec.validatorEligible previous_epoch r.validator ≠ .ok true
  deposit : i.deposit.val = inputs.deposit
  in_consolidation : i.in_consolidation = inputs.in_consolidation
  effective_balance_limit : i.effective_balance_limit.val = Spec.get_max_effective_balance p r.validator

/-- The result of `apply_step` for a `single_pass_step` result. -/
def rowsResult {E : Type} :
    core.result.Result (ValidatorRow × ExitChurn) safe_arith.ArithError →
      core.result.Result ExitChurn (per_epoch_processing.registry_rows.RowsError E)
  | .Ok (_, ch') => .Ok ch'
  | .Err e => .Err (.Step e)

/-- Trusted: what the `RegistryRows` implementation in `single_pass.rs` does. `toSpec` gives the
spec rows that an implementation value holds, and `inputsOf` gives the spec inputs of a row. -/
structure ValidatorRowsMatchSpec {R E : Type} (implementation : LighthouseRegistryRows R E)
    (p : Spec.Preset)
    (toSpec : R → List Spec.Row) (inputsOf : Spec.Row → Spec.LighthouseRowInputs) : Prop where
  /-- One row for each validator. -/
  row_count : ∀ s, ∃ n : Usize, implementation.row_count s = ok n ∧ n.val = (toSpec s).length
  /-- Row `i` gets the result of `single_pass_step`. No other row changes. -/
  apply_step : ∀ (s : R) (i : Usize) (ch : ExitChurn) (c : StepContext)
    (k : per_epoch_processing.registry_update.RegistryConstants) (r : Spec.Row),
    (toSpec s)[i.val]? = some r →
    ∃ lr ri, RowMatches lr r ∧ RowInputsMatchSpec p c.previous_epoch.val ri (inputsOf r) r ∧
      ∀ res, per_epoch_processing.single_pass_step.single_pass_step lr ri ch c k = ok res →
        ∃ s', implementation.apply_step s i ch c k = ok (rowsResult res, s') ∧
          ∀ lr' ch', res = .Ok (lr', ch') → toSpec s' = (toSpec s).set i.val (rowAfter r lr')

end EpochProofs
