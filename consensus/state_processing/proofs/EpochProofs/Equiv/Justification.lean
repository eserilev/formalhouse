import EpochProofs.Equiv.BuilderPendingPayments
import EpochProofs.Spec.JustificationLighthouse

/-!
# Lighthouse justification and finalization equals the model

`weigh_justification_equiv` relates `weigh_justification` in `justification.rs` to
`Spec.lhWeighJustification`. `Sanity/LighthouseJustification.lean` relates the model to the spec.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open per_epoch_processing.justification

def absJustificationBits (bits : JustificationBits) : Spec.LhJustificationBits :=
  { bit0 := bits.bit0, bit1 := bits.bit1, bit2 := bits.bit2, bit3 := bits.bit3 }

def absNewFinalized : NewFinalized → Spec.LhNewFinalized
  | .Unchanged => .unchanged
  | .OldPreviousJustified => .oldPreviousJustified
  | .OldCurrentJustified => .oldCurrentJustified

def absJustificationOutcome (outcome : JustificationOutcome) : Spec.LhJustificationOutcome :=
  { justify_previous := outcome.justify_previous, justify_current := outcome.justify_current,
    bits := absJustificationBits outcome.bits, finalized := absNewFinalized outcome.finalized }

theorem safe_add_cases (a b : U64) :
    (∃ c : U64, U64.Insts.Safe_arithSafeArithU64.safe_add a b = ok (.Ok c) ∧
      Spec.uint64Add a.val b.val = .ok c.val) ∨
    (U64.Insts.Safe_arithSafeArithU64.safe_add a b = ok (.Err .Overflow) ∧
      Spec.uint64Add a.val b.val = .error .overflow) := by
  have h := U64.checked_add_bv_spec a b
  simp only [U64.max_eq] at h
  unfold U64.Insts.Safe_arithSafeArithU64.safe_add
  cases hc : a.checked_add b <;> simp only [hc] at h
  · have hov : ¬ a.val + b.val < Spec.UINT64_SIZE := by simp [Spec.UINT64_SIZE]; omega
    right
    exact ⟨by simp [lift, core.option.Option.ok_or], by simp [Spec.uint64Add, hov]; rfl⟩
  · rename_i c
    have hfit : a.val + b.val < Spec.UINT64_SIZE := by simp [Spec.UINT64_SIZE]; omega
    left
    refine ⟨c, by simp [lift, core.option.Option.ok_or], ?_⟩
    simp [Spec.uint64Add, hfit, h.2.1, pure, Except.pure]

theorem safe_mul_cases (a b : U64) :
    (∃ c : U64, U64.Insts.Safe_arithSafeArithU64.safe_mul a b = ok (.Ok c) ∧
      Spec.uint64Mul a.val b.val = .ok c.val) ∨
    (U64.Insts.Safe_arithSafeArithU64.safe_mul a b = ok (.Err .Overflow) ∧
      Spec.uint64Mul a.val b.val = .error .overflow) := by
  have h := U64.checked_mul_bv_spec a b
  simp only [U64.max_eq] at h
  unfold U64.Insts.Safe_arithSafeArithU64.safe_mul
  cases hc : a.checked_mul b <;> simp only [hc] at h
  · have hov : ¬ a.val * b.val < Spec.UINT64_SIZE := by simp [Spec.UINT64_SIZE]; omega
    right
    exact ⟨by simp [lift, core.option.Option.ok_or], by simp [Spec.uint64Mul, hov]; rfl⟩
  · rename_i c
    have hfit : a.val * b.val < Spec.UINT64_SIZE := by simp [Spec.UINT64_SIZE]; omega
    left
    refine ⟨c, by simp [lift, core.option.Option.ok_or], ?_⟩
    simp [Spec.uint64Mul, hfit, h.2.1, pure, Except.pure]

theorem finalize_step_equiv (enabled : Bool) (source_epoch offset current_epoch : U64)
    (choice finalized : NewFinalized) :
    ∃ r, finalize_step enabled source_epoch offset current_epoch choice finalized = ok r ∧
      absResult absNewFinalized r =
        Spec.lhFinalizeStep enabled source_epoch.val offset.val current_epoch.val
          (absNewFinalized choice) (absNewFinalized finalized) := by
  unfold finalize_step
  cases enabled
  · exact ⟨_, rfl, by simp [Spec.lhFinalizeStep, absResult, pure, Except.pure]⟩
  rcases safe_add_cases source_epoch offset with ⟨c, h1, h2⟩ | ⟨h1, h2⟩
  · by_cases he : c = current_epoch
    · have hv : c.val = current_epoch.val := by rw [he]
      refine ⟨.Ok choice, ?_, ?_⟩
      · simp [h1, core.result.Result.Insts.CoreOpsTry.branch, he]
      · simp [Spec.lhFinalizeStep, h2, hv, absResult, Bind.bind, Except.bind, Pure.pure,
          Except.pure]
    · have hv : c.val ≠ current_epoch.val := fun h => he (by rw [UScalar.eq_equiv]; exact h)
      refine ⟨.Ok finalized, ?_, ?_⟩
      · simp [h1, core.result.Result.Insts.CoreOpsTry.branch, he]
      · simp [Spec.lhFinalizeStep, h2, hv, absResult, Bind.bind, Except.bind, Pure.pure,
          Except.pure]
  · refine ⟨.Err .Overflow, ?_, ?_⟩
    · simp [h1, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    · simp [Spec.lhFinalizeStep, h2, absResult, absArithError, Bind.bind, Except.bind]

/-- Splits the goals on `t` where `t` occurs. -/
local macro "jsplit " t:term : tactic =>
  `(tactic| all_goals (try (by_cases h : $t <;> simp [h, UScalar.eq_equiv])))

set_option maxHeartbeats 4000000 in
theorem weigh_justification_equiv (current_epoch old_previous_justified_epoch
    old_current_justified_epoch : U64) (bits : JustificationBits)
    (total_active_balance previous_target_balance current_target_balance : U64) :
    weigh_justification current_epoch old_previous_justified_epoch old_current_justified_epoch
      bits total_active_balance previous_target_balance current_target_balance ⦃ r =>
        absResult absJustificationOutcome r =
          Spec.lhWeighJustification current_epoch.val old_previous_justified_epoch.val
            old_current_justified_epoch.val (absJustificationBits bits) total_active_balance.val
            previous_target_balance.val current_target_balance.val ⦄ := by
  unfold weigh_justification
  rcases safe_mul_cases total_active_balance 2#u64 with ⟨t, ht, hts⟩ | ⟨ht, hts⟩ <;>
    rw [show (2#u64 : U64).val = 2 from rfl] at hts
  swap
  · simp [ht, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Spec.lhWeighJustification, hts, absResult, absArithError, Bind.bind, Except.bind]
  rcases safe_mul_cases previous_target_balance 3#u64 with ⟨px, hp, hps⟩ | ⟨hp, hps⟩ <;>
    rw [show (3#u64 : U64).val = 3 from rfl] at hps
  swap
  · simp [ht, hp, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Spec.lhWeighJustification, hts, hps, absResult, absArithError, Bind.bind, Except.bind]
  rcases safe_mul_cases current_target_balance 3#u64 with ⟨cx, hc, hcs⟩ | ⟨hc, hcs⟩ <;>
    rw [show (3#u64 : U64).val = 3 from rfl] at hcs
  swap
  · simp [ht, hp, hc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Spec.lhWeighJustification, hts, hps, hcs, absResult, absArithError, Bind.bind, Except.bind]
  rcases safe_add_cases old_previous_justified_epoch 3#u64 with ⟨a3, ha3, hs3⟩ | ⟨ha3, hs3⟩ <;>
  rcases safe_add_cases old_previous_justified_epoch 2#u64 with ⟨a2, ha2, hs2⟩ | ⟨ha2, hs2⟩ <;>
  rcases safe_add_cases old_current_justified_epoch 2#u64 with ⟨b2, hb2, hu2⟩ | ⟨hb2, hu2⟩ <;>
  rcases safe_add_cases old_current_justified_epoch 1#u64 with ⟨b1, hb1, hu1⟩ | ⟨hb1, hu1⟩ <;>
  simp only [show (3#u64 : U64).val = 3 from rfl, show (2#u64 : U64).val = 2 from rfl,
    show (1#u64 : U64).val = 1 from rfl] at hs3 hs2 hu2 hu1 <;>
  simp [ht, hp, hc, ha3, ha2, hb2, hb1, finalize_step, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    Spec.lhWeighJustification, Spec.lhFinalizeStep, hts, hps, hcs, hs3, hs2, hu2, hu1,
    Bind.bind, Except.bind, Pure.pure, Except.pure, absJustificationBits,
    absJustificationOutcome, absResult, absArithError, absNewFinalized]
  all_goals (cases hb0 : bits.bit0 <;> cases hb1 : bits.bit1 <;> cases hb2 : bits.bit2 <;>
    simp)
  jsplit (t.val ≤ px.val)
  jsplit (t.val ≤ cx.val)
  jsplit (a3.val = current_epoch.val)
  jsplit (a2.val = current_epoch.val)
  jsplit (b2.val = current_epoch.val)
  jsplit (b1.val = current_epoch.val)

end EpochProofs
