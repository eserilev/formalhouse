import EpochProofs.Equiv.Fulu
import EpochProofs.Equiv.SinglePassStep
import EpochProofs.Sanity.FuluRegistry

/-!
# Lighthouse Fulu registry update and single pass step equal the reference

Before Gloas, `registry_constants` in `single_pass.rs` passes the Fulu quotient and the Fulu
cap to the translated `registry_update` and `single_pass_step`. With these constants,
`exit_churn_limit` returns the Fulu churn (`exit_churn_limit_fulu`), which is the Gloas churn at
`fuluTab` (`fulu_exit_churn_eq`). So the Gloas theorems apply with `T = fuluTab`:

- `fulu_churnSpec`: the Fulu constants satisfy `ChurnSpec p c (fuluTab p f)`.
- `registry_update_equiv_fulu`: `registry_update` equals `registryStepIndependent` at `fuluTab`.
- `registry_update_eq_spec_fulu`: on valid states it equals the loop body of Fulu
  `process_registry_updates` (`process_registry_updates_fulu_eq`).
- `single_pass_step_equiv_fulu`: `single_pass_step` equals `lhRowStepFull` with the registry
  total `fuluTab`.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open state_processing.per_epoch_processing.single_pass_step (ValidatorRow ExitChurn StepContext RowInputs)

/-- The Fulu registry constants give the Gloas exit churn at `fuluTab`. -/
theorem fulu_churnSpec (p : Spec.Preset) (f : Spec.FuluConfig) (c : LhRegistryConstants)
    (hcompat : Spec.FuluCompat p f) (hc : FuluChurnMatch p f c) :
    ChurnSpec p c (Spec.fuluTab p f) := by
  intro total_active_balance
  have h := exit_churn_limit_fulu p f total_active_balance c hc
  rw [Spec.fulu_exit_churn_eq p f hcompat] at h
  exact h

theorem registry_update_equiv_fulu (p : Spec.Preset) (f : Spec.FuluConfig)
    (hcompat : Spec.FuluCompat p f) (fields : LhRegistryFields)
    (effective_balance current_epoch finalized_epoch total_active_balance : U64)
    (c : LhRegistryConstants) (hc : ConstantsMatchBase p c) (hfulu : FuluChurnMatch p f c) :
    per_epoch_processing.registry_update.registry_update fields effective_balance current_epoch
      finalized_epoch total_active_balance c ⦃ r => absResult absRegistry r =
        Spec.registryStepIndependent p (Spec.fuluTab p f total_active_balance.val)
          current_epoch.val finalized_epoch.val effective_balance.val (absRegistry fields) ⦄ :=
  registry_update_equiv_churn p fields effective_balance current_epoch finalized_epoch
    total_active_balance c hc (Spec.fuluTab p f) (fulu_churnSpec p f c hcompat hfulu)

/-- On valid states, Lighthouse's Fulu registry update equals the loop body of Fulu
`process_registry_updates`, which is the Gloas loop body at `fuluTab`. -/
theorem registry_update_eq_spec_fulu (p : Spec.Preset) (f : Spec.FuluConfig)
    (hcompat : Spec.FuluCompat p f) (fields : LhRegistryFields)
    (effective_balance current_epoch finalized_epoch total_active_balance : U64)
    (c : LhRegistryConstants) (hc : ConstantsMatchBase p c) (hfulu : FuluChurnMatch p f c)
    (activation_epoch : Nat)
    (hbalances : p.EJECTION_BALANCE < p.MIN_ACTIVATION_BALANCE)
    (hfinalized : finalized_epoch.val ≤ current_epoch.val)
    (hcurrent : current_epoch.val + 1 < Spec.UINT64_SIZE)
    (hactivation : Spec.compute_activation_exit_epoch p current_epoch.val = .ok activation_epoch) :
    per_epoch_processing.registry_update.registry_update fields effective_balance current_epoch
      finalized_epoch total_active_balance c ⦃ r => absResult absRegistry r =
        Spec.registryStepExclusive p (Spec.fuluTab p f total_active_balance.val)
          current_epoch.val finalized_epoch.val activation_epoch effective_balance.val
          (absRegistry fields) ⦄ := by
  apply WP.spec_mono (registry_update_equiv_fulu p f hcompat fields effective_balance
    current_epoch finalized_epoch total_active_balance c hc hfulu)
  intro r hr
  rw [hr]
  apply Spec.registryStepIndependent_eq_exclusive p _ _ _ _ _ _ hbalances hfinalized _ hcurrent
    hactivation
  have hb : fields.exit_epoch.val ≤ 18446744073709551615 := by
    have := fields.exit_epoch.hBounds; simp at this; omega
  simpa [absRegistry, Spec.FAR_FUTURE_EPOCH] using hb

/-- Lighthouse's Fulu `single_pass_step` equals `lhRowStepFull` with the registry total
`fuluTab`. The rewards, the slashings and the effective balance update read the real total. -/
theorem single_pass_step_equiv_fulu (p : Spec.Preset) (f : Spec.FuluConfig)
    (hcompat : Spec.FuluCompat p f) (lr : ValidatorRow) (r : Spec.Row)
    (hm : RowMatches lr r) (i : RowInputs) (inputs : Spec.LhRowInputs)
    (hi : InputsMatches p i inputs r) (churn : ExitChurn) (c : StepContext)
    (ctx : Spec.LhStepContext) (hc : ContextMatches p c ctx) (downward upward : Spec.Uint64)
    (hdownward : c.downward_threshold.val = downward) (hupward : c.upward_threshold.val = upward)
    (consts : LhRegistryConstants) (hconsts : ConstantsMatchBase p consts)
    (hfulu : FuluChurnMatch p f consts) :
    per_epoch_processing.single_pass_step.single_pass_step lr i churn c consts ⦃ res =>
      absStep r res = Spec.lhRowStepFull p
        { ctx with total_active_balance := Spec.fuluTab p f ctx.total_active_balance }
        downward upward inputs
        (churn.earliest_exit_epoch.val, churn.exit_balance_to_consume.val) r ⦄ :=
  single_pass_step_equiv_churn p lr r hm i inputs hi churn c ctx hc downward upward hdownward
    hupward consts hconsts (Spec.fuluTab p f) (fulu_churnSpec p f consts hcompat hfulu)

end EpochProofs
