import EpochProofs.Equiv.SinglePassLoop
import EpochProofs.Spec.PresetCfg
import EpochProofs.Sanity.Invariants.LighthouseTailModel

/-!
# The single-pass loop is the loop of the Lighthouse model

`process_epoch_lh_full` (`LighthouseTailModel.lean`) runs one `passM` of `lhRowStepFull` over
`rowsOf s`, from the exit churn of `s`. `single_pass_rows_model` shows that the Rust loop
`single_pass_rows` computes exactly this `passM`, when the `RegistryRows` value holds `rowsOf s`
and satisfies the trusted `RowsContract`. So the loop in the model is no longer a hand-written
assumption about `single_pass.rs`: only `RowsContract` is.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

open state_processing.per_epoch_processing.single_pass_step (ExitChurn StepContext)

/-- The row inputs of the model loop in `lhFullTail`. -/
def modelRowInputs [EpochProofs.Spec.PresetCfg] (total_active_balance : Spec.Gwei) (topups : List Spec.Gwei)
    (named : List Spec.ValidatorIndex) (r : Spec.Row) : Spec.LhRowInputs :=
  ⟨Spec.lhBaseReward total_active_balance r, topups.getD r.index 0, decide (r.index ∈ named)⟩

theorem single_pass_rows_model [EpochProofs.Spec.PresetCfg] {R E : Type} (inst : LhRegistryRows R E) (s : Spec.BeaconState)
    (total_active_balance : Spec.Gwei) (topups : List Spec.Gwei)
    (named : List Spec.ValidatorIndex) (view : R → List Spec.Row) (rows : R)
    (hview : view rows = Spec.rowsOf s)
    (hc : RowsContract inst Spec.P view
      (modelRowInputs total_active_balance topups named))
    (c : StepContext) (ctx : Spec.LhStepContext) (hcm : ContextMatches Spec.P c ctx)
    (downward upward : Spec.Uint64) (hdownward : c.downward_threshold.val = downward)
    (hupward : c.upward_threshold.val = upward)
    (k : per_epoch_processing.registry_update.RegistryConstants)
    (hk : ConstantsMatch Spec.P k) (ch : ExitChurn)
    (hch : absChurn ch = (s.earliest_exit_epoch, s.exit_balance_to_consume)) :
    per_epoch_processing.registry_rows.single_pass_rows inst rows ch c k ⦃ res =>
      LoopPost view (Spec.passM (fun churn r => Spec.lhRowStepFull Spec.P ctx
          downward upward
          ⟨Spec.lhBaseReward total_active_balance r, topups.getD r.index 0,
            decide (r.index ∈ named)⟩ churn r)
        (s.earliest_exit_epoch, s.exit_balance_to_consume) (Spec.rowsOf s)) res ⦄ := by
  have h := single_pass_rows_eq_passM inst Spec.P view
    (modelRowInputs total_active_balance topups named) hc c ctx hcm downward upward hdownward
    hupward k hk rows ch
  rw [hview, hch] at h
  exact h

end EpochProofs
