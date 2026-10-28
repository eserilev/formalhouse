import EpochProofs.Equiv.RegistryUpdates
import EpochProofs.Spec.PresetCfg
import EpochProofs.Equiv.EffectiveBalanceUpdates
import EpochProofs.Sanity.Invariants.Totality

/-!
# The context helpers of `single_pass.rs` cannot fail

`participation_increments` divides the three flag balances and the total active balance by the
effective balance increment. `participation_increments_ok` shows that it returns `Ok` with the
four quotients when the increment is not zero. The increment is a preset constant, so
`participation_increments_ok_preset` needs only that the preset value is not zero.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem checked_div_some (x inc : U64) (hinc : inc.val ≠ 0) :
    ∃ z : U64, U64.checked_div x inc = some z ∧ z.val = x.val / inc.val := by
  have hs := U64.checked_div_bv_spec x inc
  cases hc : U64.checked_div x inc <;> simp only [hc] at hs
  · exact absurd hs hinc
  · exact ⟨_, rfl, hs.2.1⟩

theorem participation_increments_ok (source target head total inc : U64) (hinc : inc.val ≠ 0) :
    per_epoch_processing.rewards_penalties.participation_increments source target head total inc
      ⦃ r => ∃ a b c d : U64, r = .Ok (a, b, c, d) ∧ a.val = source.val / inc.val
        ∧ b.val = target.val / inc.val ∧ c.val = head.val / inc.val
        ∧ d.val = total.val / inc.val ⦄ := by
  obtain ⟨a, ha, hav⟩ := checked_div_some source inc hinc
  obtain ⟨b, hb, hbv⟩ := checked_div_some target inc hinc
  obtain ⟨c, hc, hcv⟩ := checked_div_some head inc hinc
  obtain ⟨d, hd, hdv⟩ := checked_div_some total inc hinc
  unfold per_epoch_processing.rewards_penalties.participation_increments
    U64.Insts.Safe_arithSafeArithU64.safe_div
  simp [ha, hb, hc, hd, lift, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨hav, hbv, hcv, hdv⟩

theorem participation_increments_ok_preset (p : Spec.Preset) (source target head total inc : U64)
    (hinc : inc.val = p.EFFECTIVE_BALANCE_INCREMENT) (hp : p.EFFECTIVE_BALANCE_INCREMENT ≠ 0) :
    per_epoch_processing.rewards_penalties.participation_increments source target head total inc
      ⦃ r => ∃ a b c d : U64, r = .Ok (a, b, c, d) ∧ a.val = source.val / inc.val
        ∧ b.val = target.val / inc.val ∧ c.val = head.val / inc.val
        ∧ d.val = total.val / inc.val ⦄ :=
  participation_increments_ok source target head total inc (by rw [hinc]; exact hp)

/-- `hysteresis_thresholds` cannot fail on mainnet: the thresholds are constants. -/
theorem hysteresis_thresholds_ok_mainnet [EpochProofs.Spec.PresetCfg] :
    ∃ d u : U64, per_epoch_processing.effective_balance.hysteresis_thresholds
        1000000000#u64 4#u64 1#u64 5#u64 = ok (.Ok (d, u))
      ∧ d.val = 250000000 ∧ u.val = 1250000000 := by
  obtain ⟨r, hr, hq⟩ := spec_imp_exists (hysteresis_thresholds_equiv Spec.P
    1000000000#u64 4#u64 1#u64 5#u64 rfl rfl rfl rfl)
  rw [Spec.tot_hysteresis] at hq
  cases r with
  | Ok v =>
    simp only [absResult, Except.ok.injEq, Prod.mk.injEq] at hq
    exact ⟨v.1, v.2, hr, hq.1, hq.2⟩
  | Err e => simp [absResult] at hq

end EpochProofs
