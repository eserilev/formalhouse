import EpochProofs.Equiv.RegistryUpdates

/-!
# Lighthouse reset and historical summary checks equal their models

`tail_updates.rs` holds the checks of the eth1, slashings and randao resets and of the
historical summaries update. Each theorem relates one Rust function to a model in `Spec` that
reads like the Rust. `LighthouseResets.lean` relates the models to the spec steps.
-/

namespace EpochProofs.Spec

/-- `(slot + 1) % slots_per_eth1_voting_period == 0`, the eth1 reset check of Lighthouse. -/
def lhEth1ResetDue (slot slots_per_eth1_voting_period : Uint64) : SpecM Bool := do
  pure ((← uint64Mod (← uint64Add slot 1) slots_per_eth1_voting_period) == 0)

/-- The position of `epoch` in a vector indexed by epoch, as `BeaconState::get_slashings_index`
and `BeaconState::get_randao_mix_index` compute it. `none` is `EpochOutOfBounds`. -/
def epochVectorIndex (current_epoch epoch length : Uint64) (allow_next_epoch : Bool) :
    SpecM (Option Uint64) := do
  let window_end ← uint64Add epoch length
  if current_epoch ≥ window_end then pure none else do
    let upper_bound ← if allow_next_epoch then uint64Add current_epoch 1 else pure current_epoch
    if epoch > upper_bound then pure none else do
      pure (some (← uint64Mod epoch length))

/-- The position that the Lighthouse slashings reset clears. -/
def slashingsResetIndex (current_epoch length : Uint64) : SpecM (Option Uint64) := do
  epochVectorIndex current_epoch (← uint64Add current_epoch 1) length true

/-- The positions that the Lighthouse randao reset reads and writes. -/
def randaoMixesResetIndices (current_epoch length : Uint64) :
    SpecM (Option (Uint64 × Uint64)) := do
  let next_epoch ← uint64Add current_epoch 1
  let source ← epochVectorIndex current_epoch current_epoch length false
  let target ← epochVectorIndex current_epoch next_epoch length true
  match source, target with
  | some source, some target => pure (some (source, target))
  | _, _ => pure none

/-- `next_epoch % (slots_per_historical_root / slots_per_epoch) == 0`. -/
def historicalSummaryDue (next_epoch slots_per_historical_root slots_per_epoch : Uint64) :
    SpecM Bool := do
  pure ((← uint64Mod next_epoch (← uint64Div slots_per_historical_root slots_per_epoch)) == 0)

end EpochProofs.Spec

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem safe_add_abs (a b : U64) :
    U64.Insts.Safe_arithSafeArithU64.safe_add a b ⦃ r =>
      absResult (·.val) r = Spec.uint64Add a.val b.val ⦄ := by
  obtain ⟨r, hr, h⟩ := spec_imp_exists (safe_add_spec a b)
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Ok v =>
    obtain ⟨hv, hfit⟩ := h.1 v rfl
    simp [absResult, Spec.uint64Add, Spec.UINT64_SIZE, hv, hfit, pure, Except.pure]
  | Err e =>
    obtain ⟨he, hov⟩ := h.2 e rfl
    subst he
    simp [absResult, absArithError, Spec.uint64Add, Spec.UINT64_SIZE, hov, throw, throwThe,
      MonadExceptOf.throw]

theorem safe_rem_abs (a b : U64) :
    U64.Insts.Safe_arithSafeArithU64.safe_rem a b ⦃ r =>
      absResult (·.val) r = Spec.uint64Mod a.val b.val ⦄ := by
  obtain ⟨r, hr, h⟩ := spec_imp_exists (safe_rem_spec a b)
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Ok v =>
    obtain ⟨hv, hb⟩ := h.1 v rfl
    simp [absResult, Spec.uint64Mod, hv, hb, pure, Except.pure]
  | Err e =>
    obtain ⟨he, hb⟩ := h.2 e rfl
    subst he
    simp [absResult, absArithError, Spec.uint64Mod, hb, throw, throwThe, MonadExceptOf.throw]

theorem safe_div_abs (a b : U64) :
    U64.Insts.Safe_arithSafeArithU64.safe_div a b ⦃ r =>
      absResult (·.val) r = Spec.uint64Div a.val b.val ⦄ := by
  obtain ⟨r, hr, h⟩ := spec_imp_exists (safe_div_spec a b)
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Ok v =>
    obtain ⟨hv, hb⟩ := h.1 v rfl
    simp [absResult, Spec.uint64Div, hv, hb, pure, Except.pure]
  | Err e =>
    obtain ⟨he, hb⟩ := h.2 e rfl
    subst he
    simp [absResult, absArithError, Spec.uint64Div, hb, throw, throwThe, MonadExceptOf.throw]

/-- The `Err` branch of a `?`: both sides give the same error. `h` relates the Rust call to the
`SpecM` value that the spec side binds first. -/
macro "abs_err" h:ident : tactic =>
  `(tactic| (rw [← $h:ident]; simp only [WP.spec_ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]; rfl))

/-- The `Ok` branch of a `?`: the spec side binds the same value. -/
macro "abs_ok" h:ident : tactic =>
  `(tactic| (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]; rw [← $h:ident]; simp only [absResult, except_ok_bind]))

/-- `decide (m = 0)` on a `U64` is `m.val == 0`. -/
theorem decide_eq_zero (m : U64) : decide (m = 0#u64) = (m.val == 0) := by
  by_cases h : m = 0#u64
  · subst h; rfl
  · have hv : m.val ≠ 0 := fun hv => h (by scalar_tac)
    simp [h, hv]

theorem eth1_data_votes_reset_due_equiv (slot period : U64) :
    per_epoch_processing.tail_updates.eth1_data_votes_reset_due slot period ⦃ r =>
      absResult id r = Spec.lhEth1ResetDue slot.val period.val ⦄ := by
  unfold per_epoch_processing.tail_updates.eth1_data_votes_reset_due Spec.lhEth1ResetDue
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_add_abs slot 1#u64)
  have h1v : (1#u64 : U64).val = 1 := rfl
  rw [h1v] at h1
  simp only [hr1, bind_tc_ok]
  cases r1 with
  | Err e => abs_err h1
  | Ok n =>
    abs_ok h1
    obtain ⟨r2, hr2, h2⟩ := spec_imp_exists (safe_rem_abs n period)
    simp only [hr2, bind_tc_ok]
    cases r2 with
    | Err e => abs_err h2
    | Ok m =>
      abs_ok h2
      simp only [WP.spec_ok, decide_eq_zero]
      rfl

theorem historical_summary_due_equiv (next_epoch root epoch : U64) :
    per_epoch_processing.tail_updates.historical_summary_due next_epoch root epoch ⦃ r =>
      absResult id r = Spec.historicalSummaryDue next_epoch.val root.val epoch.val ⦄ := by
  unfold per_epoch_processing.tail_updates.historical_summary_due Spec.historicalSummaryDue
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_div_abs root epoch)
  simp only [hr1, bind_tc_ok]
  cases r1 with
  | Err e => abs_err h1
  | Ok q =>
    abs_ok h1
    obtain ⟨r2, hr2, h2⟩ := spec_imp_exists (safe_rem_abs next_epoch q)
    simp only [hr2, bind_tc_ok]
    cases r2 with
    | Err e => abs_err h2
    | Ok m =>
      abs_ok h2
      simp only [WP.spec_ok, decide_eq_zero]
      rfl

/-- The last step of `epoch_vector_index`: `epoch % length`. -/
theorem epoch_vector_index_rem (epoch length : U64) :
    (do
      let r ← U64.Insts.Safe_arithSafeArithU64.safe_rem epoch length
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue v => ok (core.result.Result.Ok (some v))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Option U64) (core.convert.FromSame safe_arith.ArithError) residual) ⦃ r =>
        absResult (Option.map (·.val)) r = (do
          pure (some (← Spec.uint64Mod epoch.val length.val)) : Spec.SpecM (Option Nat)) ⦄ := by
  obtain ⟨r, hr, h⟩ := spec_imp_exists (safe_rem_abs epoch length)
  simp only [hr, bind_tc_ok]
  cases r with
  | Err e => abs_err h
  | Ok i =>
    abs_ok h
    simp only [WP.spec_ok]
    rfl

theorem epoch_vector_index_equiv (current_epoch epoch length : U64) (allow : Bool) :
    per_epoch_processing.tail_updates.epoch_vector_index current_epoch epoch length allow ⦃ r =>
      absResult (Option.map (·.val)) r =
        Spec.epochVectorIndex current_epoch.val epoch.val length.val allow ⦄ := by
  unfold per_epoch_processing.tail_updates.epoch_vector_index Spec.epochVectorIndex
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_add_abs epoch length)
  simp only [hr1, bind_tc_ok]
  cases r1 with
  | Err e => abs_err h1
  | Ok w =>
    abs_ok h1
    by_cases hw : current_epoch ≥ w
    · have hw' : current_epoch.val ≥ w.val := by scalar_tac
      simp only [hw, hw', if_true, WP.spec_ok]
      rfl
    have hw' : ¬ current_epoch.val ≥ w.val := by scalar_tac
    simp only [hw, hw', if_false]
    by_cases ha : allow = true
    · simp only [ha, if_true]
      obtain ⟨r2, hr2, h2⟩ := spec_imp_exists (safe_add_abs current_epoch 1#u64)
      have h1v : (1#u64 : U64).val = 1 := rfl
      rw [h1v] at h2
      simp only [hr2, bind_tc_ok]
      cases r2 with
      | Err e => abs_err h2
      | Ok u =>
        abs_ok h2
        by_cases hu : epoch > u
        · have hu' : epoch.val > u.val := by scalar_tac
          simp only [hu, hu', if_true, WP.spec_ok]
          rfl
        have hu' : ¬ epoch.val > u.val := by scalar_tac
        simp only [hu, hu', if_false]
        exact epoch_vector_index_rem epoch length
    · have hf : allow = false := by simpa using ha
      simp only [hf, Bool.false_eq_true, if_false, except_ok_bind, pure, Except.pure]
      by_cases hu : epoch > current_epoch
      · have hu' : epoch.val > current_epoch.val := by scalar_tac
        simp only [hu, hu', if_true, WP.spec_ok]
        rfl
      have hu' : ¬ epoch.val > current_epoch.val := by scalar_tac
      simp only [hu, hu', if_false]
      exact epoch_vector_index_rem epoch length

theorem slashings_reset_index_equiv (current_epoch length : U64) :
    per_epoch_processing.tail_updates.slashings_reset_index current_epoch length ⦃ r =>
      absResult (Option.map (·.val)) r =
        Spec.slashingsResetIndex current_epoch.val length.val ⦄ := by
  unfold per_epoch_processing.tail_updates.slashings_reset_index Spec.slashingsResetIndex
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_add_abs current_epoch 1#u64)
  have h1v : (1#u64 : U64).val = 1 := rfl
  rw [h1v] at h1
  simp only [hr1, bind_tc_ok]
  cases r1 with
  | Err e => abs_err h1
  | Ok n =>
    abs_ok h1
    exact epoch_vector_index_equiv current_epoch n length true

theorem randao_mixes_reset_indices_equiv (current_epoch length : U64) :
    per_epoch_processing.tail_updates.randao_mixes_reset_indices current_epoch length ⦃ r =>
      absResult (Option.map (fun x => (x.1.val, x.2.val))) r =
        Spec.randaoMixesResetIndices current_epoch.val length.val ⦄ := by
  unfold per_epoch_processing.tail_updates.randao_mixes_reset_indices
    Spec.randaoMixesResetIndices
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_add_abs current_epoch 1#u64)
  have h1v : (1#u64 : U64).val = 1 := rfl
  rw [h1v] at h1
  simp only [hr1, bind_tc_ok]
  cases r1 with
  | Err e => abs_err h1
  | Ok n =>
    abs_ok h1
    obtain ⟨r2, hr2, h2⟩ :=
      spec_imp_exists (epoch_vector_index_equiv current_epoch current_epoch length false)
    simp only [hr2, bind_tc_ok]
    cases r2 with
    | Err e => abs_err h2
    | Ok source =>
      abs_ok h2
      obtain ⟨r3, hr3, h3⟩ :=
        spec_imp_exists (epoch_vector_index_equiv current_epoch n length true)
      simp only [hr3, bind_tc_ok]
      cases r3 with
      | Err e => abs_err h3
      | Ok target =>
        abs_ok h3
        cases source <;> cases target <;> simp only [WP.spec_ok, Option.map] <;> rfl

end EpochProofs
