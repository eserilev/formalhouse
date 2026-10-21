import EpochProofs.Trusted.RegistryRows

/-!
# The single-pass loop equals one pass over the rows

`single_pass_rows_spec` relates `single_pass_rows` in `registry_rows.rs` to `Spec.passM` over the
rows of a `RegistryRows` value. `StepSpec` states what one `apply_step` call does.
`rowsContract_stepSpec` derives it from the trusted `RowsContract` and
`single_pass_step_equiv`, with the step `Spec.lhRowStepFull`.

`single_pass_rows_eq_passM` puts the two together: under `RowsContract`, the Lighthouse loop
returns `Ok` exactly when `passM lhRowStepFull` over the rows returns `ok`, with the same churn
and rows. On an error, both fail.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

open state_processing.per_epoch_processing.single_pass_step (ValidatorRow ExitChurn StepContext RowInputs)

abbrev LhRowsError (E : Type) := per_epoch_processing.registry_rows.RowsError E

def absChurn (ch : ExitChurn) : Spec.Epoch × Spec.Gwei :=
  (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val)

theorem passM_append {A R : Type} (f : A → R → Spec.SpecM (A × R)) (a : A) (xs ys : List R) :
    Spec.passM f a (xs ++ ys) = (do
      let x ← Spec.passM f a xs
      let y ← Spec.passM f x.1 ys
      pure (y.1, x.2 ++ y.2)) := by
  induction xs generalizing a with
  | nil =>
    show Spec.passM f a ys = (Except.ok (a, []) >>= _)
    rw [except_ok_bind]
    cases Spec.passM f a ys <;> rfl
  | cons r rs ih =>
    rw [List.cons_append, Spec.passM_cons, Spec.passM_cons]
    cases f a r with
    | error e => rfl
    | ok x =>
      rw [except_ok_bind, except_ok_bind, ih]
      cases Spec.passM f x.1 rs with
      | error e => rfl
      | ok y =>
        simp only [except_ok_bind, pure_bind]
        cases Spec.passM f y.1 ys <;> rfl

theorem passM_singleton_ok {A R : Type} (f : A → R → Spec.SpecM (A × R)) (a a' : A) (r r' : R)
    (h : f a r = .ok (a', r')) : Spec.passM f a [r] = .ok (a', [r']) := by
  rw [Spec.passM_cons, h, except_ok_bind]
  rfl

theorem drop_succ_set {α : Type} (l V : List α) (i : Nat) (x : α)
    (h : l.drop i = V.drop i) : (l.set i x).drop (i + 1) = V.drop (i + 1) := by
  rw [List.drop_set_of_lt (by omega : i < i + 1)]
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

/-- One `apply_step` call on row `i` runs `step` on that row and writes the new row. -/
def StepSpec {R E : Type} (inst : LhRegistryRows R E) (view : R → List Spec.Row)
    (step : Spec.Epoch × Spec.Gwei → Spec.Row → Spec.SpecM ((Spec.Epoch × Spec.Gwei) × Spec.Row))
    (c : StepContext) (k : per_epoch_processing.registry_update.RegistryConstants) : Prop :=
  ∀ (s : R) (i : Usize) (ch : ExitChurn) (r : Spec.Row), (view s)[i.val]? = some r →
    (∃ ch' r' s', inst.apply_step s i ch c k = ok (.Ok ch', s') ∧
        step (absChurn ch) r = .ok (absChurn ch', r') ∧ view s' = (view s).set i.val r')
    ∨ (∃ e s', inst.apply_step s i ch c k = ok (.Err (.Step e), s') ∧
        step (absChurn ch) r = .error (absArithError e))

/-- What the loop returns, in spec terms. -/
def LoopPost {R E : Type} (view : R → List Spec.Row)
    (spec : Spec.SpecM ((Spec.Epoch × Spec.Gwei) × List Spec.Row)) :
    core.result.Result ExitChurn (LhRowsError E) × R → Prop
  | (.Ok ch', s') => spec = .ok (absChurn ch', view s')
  | (.Err (.Step e), _) => spec = .error (absArithError e)
  | (.Err (.Rows _), _) => False

theorem usize_safe_add_one (j : Usize) (h : j.val < Usize.max) :
    ∃ j' : Usize, Usize.Insts.Safe_arithSafeArithUsize.safe_add j 1#usize = ok (.Ok j')
      ∧ j'.val = j.val + 1 := by
  have hs := Usize.checked_add_bv_spec j 1#usize
  unfold Usize.Insts.Safe_arithSafeArithUsize.safe_add
  cases hc : Usize.checked_add j 1#usize with
  | none => simp only [hc] at hs; simp at hs; omega
  | some j' =>
    simp only [hc] at hs
    refine ⟨j', by simp [lift, core.option.Option.ok_or], ?_⟩
    simp at hs
    omega

theorem single_pass_rows_loop_spec {R E : Type} (inst : LhRegistryRows R E)
    (view : R → List Spec.Row)
    (step : Spec.Epoch × Spec.Gwei → Spec.Row → Spec.SpecM ((Spec.Epoch × Spec.Gwei) × Spec.Row))
    (c : StepContext) (k : per_epoch_processing.registry_update.RegistryConstants)
    (hstep : StepSpec inst view step c k) (V : List Spec.Row) (a0 : Spec.Epoch × Spec.Gwei)
    (len : Usize) (hlen : len.val = V.length) (rows : R) (ch : ExitChurn) (j : Usize)
    (hj : j.val ≤ V.length) (hl : (view rows).length = V.length)
    (hd : (view rows).drop j.val = V.drop j.val)
    (hp : Spec.passM step a0 (V.take j.val) = .ok (absChurn ch, (view rows).take j.val)) :
    per_epoch_processing.registry_rows.single_pass_rows_loop inst rows c k len ch j
      ⦃ res => LoopPost view (Spec.passM step a0 V) res ⦄ := by
  unfold per_epoch_processing.registry_rows.single_pass_rows_loop
  apply loop.spec_decr_nat
    (measure := fun (x : R × ExitChurn × Usize) => V.length - x.2.2.val)
    (inv := fun (x : R × ExitChurn × Usize) =>
      x.2.2.val ≤ V.length ∧ (view x.1).length = V.length
      ∧ (view x.1).drop x.2.2.val = V.drop x.2.2.val
      ∧ Spec.passM step a0 (V.take x.2.2.val) = .ok (absChurn x.2.1, (view x.1).take x.2.2.val))
  · rintro ⟨s, chj, i⟩ ⟨hi, hls, hds, hps⟩
    dsimp only at hi hls hds hps ⊢
    unfold per_epoch_processing.registry_rows.single_pass_rows_loop.body
    split
    · rename_i hlt
      have hil : i.val < V.length := by scalar_tac
      have hri : (view s)[i.val]? = some V[i.val] := by
        have h1 : ((view s).drop i.val)[0]? = (V.drop i.val)[0]? := by rw [hds]
        simpa [List.getElem?_drop, List.getElem?_eq_getElem hil] using h1
      rcases hstep s i chj V[i.val] hri with ⟨ch', r', s', happ, hst, hv⟩ | ⟨e, s', happ, hst⟩
      · rw [happ]
        simp only [bind_tc_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch]
        have hmax : i.val < Usize.max := by scalar_tac
        obtain ⟨i', hadd, hi'⟩ := usize_safe_add_one i hmax
        rw [hadd]
        simp only [bind_tc_ok, spec_ok]
        have hls' : (view s').length = V.length := by rw [hv, List.length_set, hls]
        have hil' : i.val < (view s).length := by omega
        refine ⟨⟨by omega, hls', ?_, ?_⟩, by omega⟩
        · rw [hi', hv]
          exact drop_succ_set _ _ _ _ hds
        · rw [hi', List.take_succ_eq_append_getElem hil, passM_append, hps, except_ok_bind,
            passM_singleton_ok _ _ _ _ _ hst, except_ok_bind, hv,
            List.take_succ_eq_append_getElem (by rw [List.length_set]; exact hil'),
            List.take_set_of_le (Nat.le_refl _), List.getElem_set_self]
          rfl
      · rw [happ]
        simp only [bind_tc_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, spec_ok]
        show Spec.passM step a0 V = .error (absArithError e)
        have hsplit : V = V.take i.val ++ (V[i.val] :: V.drop (i.val + 1)) := by
          rw [← List.drop_eq_getElem_cons hil, List.take_append_drop]
        rw [hsplit, passM_append, hps, except_ok_bind, Spec.passM_cons, hst, except_error_bind,
          except_error_bind]
    · rename_i hge
      have hiv : i.val = V.length := by scalar_tac
      simp only [spec_ok]
      show Spec.passM step a0 V = .ok (absChurn chj, view s)
      have h1 : V.take i.val = V := by rw [hiv, List.take_length]
      have h2 : (view s).take i.val = view s := by rw [hiv, ← hls, List.take_length]
      rw [← h1, hps, h2]
  · exact ⟨hj, hl, hd, hp⟩

theorem single_pass_rows_spec {R E : Type} (inst : LhRegistryRows R E)
    (view : R → List Spec.Row)
    (step : Spec.Epoch × Spec.Gwei → Spec.Row → Spec.SpecM ((Spec.Epoch × Spec.Gwei) × Spec.Row))
    (c : StepContext) (k : per_epoch_processing.registry_update.RegistryConstants)
    (hcount : ∀ s, ∃ n : Usize, inst.row_count s = ok n ∧ n.val = (view s).length)
    (hstep : StepSpec inst view step c k) (rows : R) (ch : ExitChurn) :
    per_epoch_processing.registry_rows.single_pass_rows inst rows ch c k
      ⦃ res => LoopPost view (Spec.passM step (absChurn ch) (view rows)) res ⦄ := by
  unfold per_epoch_processing.registry_rows.single_pass_rows
  obtain ⟨n, hn, hnv⟩ := hcount rows
  rw [hn, bind_tc_ok]
  exact single_pass_rows_loop_spec inst view step c k hstep (view rows) (absChurn ch) n hnv rows
    ch 0#usize (by simp) rfl rfl (by simp [Spec.passM, pure, Except.pure])

/-- `lhRowStepFull` reads the base reward only for an eligible validator. -/
theorem lhRowStepFull_base_reward (p : Spec.Preset) (ctx : Spec.LhStepContext)
    (downward upward : Spec.Uint64) (inputs : Spec.LhRowInputs) (b : Spec.Gwei)
    (churn : Spec.Epoch × Spec.Gwei) (r : Spec.Row)
    (h : Spec.validatorEligible ctx.previous_epoch r.validator ≠ .ok true) :
    Spec.lhRowStepFull p ctx downward upward { inputs with base_reward := b } churn r =
      Spec.lhRowStepFull p ctx downward upward inputs churn r := by
  unfold Spec.lhRowStepFull Spec.lhRowStep
  cases he : Spec.validatorEligible ctx.previous_epoch r.validator with
  | error e => rfl
  | ok v =>
    cases v with
    | true => exact absurd he h
    | false =>
      simp only [except_ok_bind, Bool.false_eq_true, ↓reduceIte]

theorem rowsContract_stepSpec {R E : Type} (inst : LhRegistryRows R E) (p : Spec.Preset)
    (view : R → List Spec.Row) (inputsOf : Spec.Row → Spec.LhRowInputs)
    (hc : RowsContract inst p view inputsOf) (c : StepContext) (ctx : Spec.LhStepContext)
    (hcm : ContextMatches p c ctx) (downward upward : Spec.Uint64)
    (hdownward : c.downward_threshold.val = downward) (hupward : c.upward_threshold.val = upward)
    (k : per_epoch_processing.registry_update.RegistryConstants) (hk : ConstantsMatch p k) :
    StepSpec inst view (fun churn r => Spec.lhRowStepFull p ctx downward upward (inputsOf r) churn r)
      c k := by
  intro s i ch r hr
  obtain ⟨lr, ri, hm, hi, hrun⟩ := hc.apply_step s i ch c k r hr
  have hi' : InputsMatches p ri { inputsOf r with base_reward := ri.base_reward.val } r :=
    ⟨rfl, hi.deposit, hi.in_consolidation, hi.effective_balance_limit⟩
  obtain ⟨res, hres, habs⟩ := spec_imp_exists (single_pass_step_equiv p lr r hm ri _ hi' ch c ctx
    hcm downward upward hdownward hupward k hk)
  have hirr : Spec.lhRowStepFull p ctx downward upward
      { inputsOf r with base_reward := ri.base_reward.val }
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r =
      Spec.lhRowStepFull p ctx downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r := by
    rcases hi.base_reward with h | h
    · rw [h]
    · rw [hcm.previous_epoch] at h
      exact lhRowStepFull_base_reward p ctx downward upward _ _ _ r h
  obtain ⟨s', happ, hview⟩ := hrun res hres
  cases res with
  | Ok v =>
    obtain ⟨lr', ch'⟩ := v
    left
    refine ⟨ch', rowAfter r lr', s', happ, ?_, hview lr' ch' rfl⟩
    show Spec.lhRowStepFull p ctx downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl
  | Err e =>
    right
    refine ⟨e, s', happ, ?_⟩
    show Spec.lhRowStepFull p ctx downward upward (inputsOf r)
      (ch.earliest_exit_epoch.val, ch.exit_balance_to_consume.val) r = _
    rw [← hirr, ← habs]
    rfl

/-- The Lighthouse single-pass loop equals one `passM` of `lhRowStepFull` over the rows, under
the trusted `RowsContract`. -/
theorem single_pass_rows_eq_passM {R E : Type} (inst : LhRegistryRows R E) (p : Spec.Preset)
    (view : R → List Spec.Row) (inputsOf : Spec.Row → Spec.LhRowInputs)
    (hc : RowsContract inst p view inputsOf) (c : StepContext) (ctx : Spec.LhStepContext)
    (hcm : ContextMatches p c ctx) (downward upward : Spec.Uint64)
    (hdownward : c.downward_threshold.val = downward) (hupward : c.upward_threshold.val = upward)
    (k : per_epoch_processing.registry_update.RegistryConstants) (hk : ConstantsMatch p k)
    (rows : R) (ch : ExitChurn) :
    per_epoch_processing.registry_rows.single_pass_rows inst rows ch c k ⦃ res =>
      LoopPost view (Spec.passM (fun churn r =>
        Spec.lhRowStepFull p ctx downward upward (inputsOf r) churn r) (absChurn ch) (view rows))
        res ⦄ :=
  single_pass_rows_spec inst view _ c k hc.row_count
    (rowsContract_stepSpec inst p view inputsOf hc c ctx hcm downward upward hdownward hupward k
      hk) rows ch

end EpochProofs
