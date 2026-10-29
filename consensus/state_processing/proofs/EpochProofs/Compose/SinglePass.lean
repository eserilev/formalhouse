import EpochProofs.Equiv.StepContext
import EpochProofs.Equiv.DepositWrites
import EpochProofs.Equiv.ListWrites
import EpochProofs.Equiv.ConsolidationTable
import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Sanity.Invariants.LighthouseTailSpecNF

/-!
# The single pass, composed from the translated functions

`singlePass` is `process_epoch_single_pass` of `single_pass.rs` up to the builder payments, as one
Lean function: the translated `step_context`, `single_pass_rows`, `apply_deposit_writes`,
`process_on_table`, `update_effective_balances_at` and `apply_builder_pending_payments`, joined by
the untranslated glue (`SinglePassGlue`, `PaymentsGlue`): the trait implementations over the
milhouse lists, the borrows of the state by each wrapper, and the values read from the state and
the spec. `singlePass_spec` shows that, under the trusted facts about the glue
(`SinglePassLinks`, `PaymentsLinks`), it returns the state of the model `lhSinglePass`, the
single pass of `process_epoch_lh_order`. `singlePassCore` stops before the builder payments; the
Fulu epoch uses it (`Compose/Fulu.lean`).

The first part of the file proves the frame facts of the model steps that the composition needs:
which fields each step after the loop keeps.
-/

namespace EpochProofs.Spec

/-- The Lighthouse model from the start of the single pass to the builder payments. -/
def lhSinglePass [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState :=
  lhFullTailWith (fun s tab plan x => lhMid o s tab plan (s.withRowsChurn x.1 x.2)) s

theorem lhFullTailWith_order_eq [PresetCfg] (o : Oracle) (s : BeaconState) :
    lhFullTailWith (lhAfterPassOrder o) s = lhSinglePass o s >>= lhRestOrder o := by
  unfold lhSinglePass lhFullTailWith lhAfterPassOrder
  simp only [bind, Except.bind]
  repeat' split
  all_goals rfl

/-! ## Frame facts of the model steps -/

/-- A `for` loop in `SpecM` keeps every property that each successful pass keeps. -/
theorem forIn_keep {α β : Type} (P : β → Prop)
    (f : α → β → SpecM (ForInStep β)) (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b b' : β), P b → forIn l b f = .ok b' → P b' := by
  intro l
  induction l with
  | nil => intro b b' hb h; cases h; exact hb
  | cons a l ih =>
    intro b b' hb h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := specM_bind_ok h
    have := hf a b r hb hr
    cases r with
    | done c => cases h; exact this
    | yield c => exact ih c b' this h

/-- A fold keeps a property that each step keeps. -/
theorem foldlM_keep {α : Type} (P : BeaconState → Prop) (f : BeaconState → α → SpecM BeaconState)
    (hf : ∀ t x t', P t → f t x = .ok t' → P t') :
    ∀ (l : List α) (t t' : BeaconState), P t → l.foldlM f t = .ok t' → P t'
  | [], t, t', ht, h => by cases h; exact ht
  | x :: l, t, t', ht, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t1, h1, h⟩ := specM_bind_ok h
    exact foldlM_keep P f hf l t1 t' (hf t x t1 ht h1) h

/-- The balances and the validators have the same length. -/
def BalLen (t : BeaconState) : Prop := t.balances.length = t.validators.length

theorem add_validator_balLen (p : Preset) (t t' : BeaconState) (pubkey : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) (h : add_validator_to_registry p t pubkey wc amount = .ok t')
    (ht : BalLen t) : BalLen t' := by
  unfold add_validator_to_registry get_index_for_new_validator at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨l1, h1, h⟩ := specM_bind_ok h
  obtain ⟨l2, h2, h⟩ := specM_bind_ok h
  obtain ⟨l3, -, h⟩ := specM_bind_ok h
  obtain ⟨l4, -, h⟩ := specM_bind_ok h
  obtain ⟨l5, -, h⟩ := specM_bind_ok h
  cases h
  simp only at h2
  unfold BalLen at ht
  rw [← ht] at h2
  have e1 := set_or_append_list_len_eq h1
  have e2 := set_or_append_list_len_eq h2
  show l2.length = l1.length
  omega

theorem apply_balLen [PresetCfg] (o : Oracle) (t t' : BeaconState) (d : PendingDeposit)
    (h : apply_pending_deposit P o t d = .ok t') (ht : BalLen t) : BalLen t' := by
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact add_validator_balLen P t t' _ _ _ h ht
    · cases h; exact ht
  · split at h
    · contradiction
    · rename_i bs hbs
      cases h
      unfold increase_balance at hbs
      simp only [bind, Except.bind, pure, Except.pure] at hbs
      repeat' split at hbs
      all_goals first
        | contradiction
        | (unfold listSet at hbs
           split at hbs
           · cases hbs
             show (List.set _ _ _).length = _
             rw [List.length_set]; exact ht
           · contradiction)

theorem ebUpdateAt_balLen [PresetCfg] (t t' : BeaconState) (i : Nat)
    (h : ebUpdateAt t i = .ok t') (ht : BalLen t) : BalLen t' := by
  obtain ⟨v, b, e, -, -, -, rfl⟩ := (ebUpdateAt_ok t t' i).mp h
  unfold setEB BalLen at *
  split
  · simp only [List.length_set]; exact ht
  · exact ht

/-- The fields that the steps of the single pass after the loop do not write, other than the
builder payments step: the builder pending payments, the proposer lookahead and the PTC window. -/
def KeepB (t t' : BeaconState) : Prop :=
  t'.builder_pending_payments = t.builder_pending_payments ∧
    t'.proposer_lookahead = t.proposer_lookahead ∧ t'.ptc_window = t.ptc_window

theorem KeepB.trans {t1 t2 t3 : BeaconState} (h12 : KeepB t1 t2) (h23 : KeepB t2 t3) :
    KeepB t1 t3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.trans h12.2.2⟩

/-- `KeepB`, and the pending consolidations (before the consolidations step). -/
def MidKeep (t t' : BeaconState) : Prop :=
  t'.pending_consolidations = t.pending_consolidations ∧ KeepB t t'

theorem MidKeep.trans {t1 t2 t3 : BeaconState} (h12 : MidKeep t1 t2) (h23 : MidKeep t2 t3) :
    MidKeep t1 t3 :=
  ⟨h23.1.trans h12.1, h12.2.trans h23.2⟩

theorem add_validator_midKeep (p : Preset) (t t' : BeaconState) (pubkey : BLSPubkey)
    (wc : Bytes32) (amount : Gwei)
    (h : add_validator_to_registry p t pubkey wc amount = .ok t') : MidKeep t t' := by
  unfold add_validator_to_registry at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem apply_midKeep [PresetCfg] (o : Oracle) (t t' : BeaconState) (d : PendingDeposit)
    (h : apply_pending_deposit P o t d = .ok t') : MidKeep t t' := by
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact add_validator_midKeep P t t' _ _ _ h
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · split at h
    · contradiction
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem ebUpdateAt_midKeep [PresetCfg] (t t' : BeaconState) (i : Nat)
    (h : ebUpdateAt t i = .ok t') : MidKeep t t' := by
  obtain ⟨v, b, e, -, -, -, rfl⟩ := (ebUpdateAt_ok t t' i).mp h
  unfold setEB
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem consolidations_keepB (p : Preset) (t t' : BeaconState)
    (h : process_pending_consolidations p t = .ok t') : KeepB t t' := by
  unfold process_pending_consolidations at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_keep (fun r : MProd Nat BeaconState => KeepB t r.snd) _ ?_ _ _ _
    ⟨rfl, rfl, rfl⟩ hr
  · cases h
    exact hP
  · intro _ ⟨_, _⟩ r hst hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hst)

theorem lhNewValidators_keep [PresetCfg] (o : Oracle) (plan : LhDepositPlan) (t t' : BeaconState)
    (h : lhNewValidators o plan t = .ok t') (ht : BalLen t) : MidKeep t t' ∧ BalLen t' := by
  unfold lhNewValidators at h
  rw [lhApplyPendingDeposit_mainnet] at h
  obtain ⟨t3, h3, h⟩ := specM_bind_ok h
  have k3 := foldlM_keep (fun u => MidKeep t u ∧ BalLen u) (apply_pending_deposit P o)
    (fun u d u' hu hd => ⟨hu.1.trans (apply_midKeep o u u' d hd), apply_balLen o u u' d hd hu.2⟩)
    _ t t3 ⟨⟨rfl, rfl, rfl, rfl⟩, ht⟩ h3
  exact foldlM_keep (fun u => MidKeep t u ∧ BalLen u) ebUpdateAt
    (fun u i u' hu hd => ⟨hu.1.trans (ebUpdateAt_midKeep u u' i hd), ebUpdateAt_balLen u u' i hd hu.2⟩)
    _ t3 t' k3 h

theorem ebFold_keepB [PresetCfg] (l : List Nat) (t t' : BeaconState)
    (h : l.foldlM ebUpdateAt t = .ok t') : KeepB t t' :=
  foldlM_keep (fun u => KeepB t u) ebUpdateAt
    (fun u i u' hu hd => hu.trans (ebUpdateAt_midKeep u u' i hd).2) l t t' ⟨rfl, rfl, rfl⟩ h

/-- `process_builder_pending_payments` reads and writes only the two builder lists. -/
theorem process_builder_pending_payments_frame (p : Preset) (tab : Gwei) (t t0 t0' : BeaconState)
    (hp : t0.builder_pending_payments = t.builder_pending_payments)
    (hw : t0.builder_pending_withdrawals = t.builder_pending_withdrawals)
    (h : process_builder_pending_payments p tab t0 = .ok t0') :
    process_builder_pending_payments p tab t = .ok { t with
      builder_pending_withdrawals := t0'.builder_pending_withdrawals
      builder_pending_payments := t0'.builder_pending_payments } := by
  unfold process_builder_pending_payments at h ⊢
  rw [hp, hw] at h
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; simp only [*])

/-- The steps of `lhMid` before the builder payments: the deposit writes, the pending
consolidations and the effective balance updates of the validators that consolidations name. -/
def lhMidCore [PresetCfg] (o : Oracle) (s : BeaconState) (plan : LhDepositPlan)
    (s1 : BeaconState) : SpecM BeaconState := do
  let s4 ← lhNewValidators o plan (lhQueueWrite s plan s1)
  let s5 ← process_pending_consolidations P s4
  (consolidationIndices s).foldlM ebUpdateAt s5

theorem lhMid_eq [PresetCfg] (o : Oracle) (s : BeaconState) (tab : Gwei) (plan : LhDepositPlan)
    (s1 : BeaconState) :
    lhMid o s tab plan s1 = lhMidCore o s plan s1 >>= process_builder_pending_payments P tab := by
  simp only [lhMid, lhMidCore, bind_assoc]

/-- `lhMidCore` does not write the builder pending payments, the proposer lookahead or the PTC
window. -/
theorem lhMidCore_keep [PresetCfg] (o : Oracle) (s : BeaconState) (plan : LhDepositPlan)
    (x : (Epoch × Gwei) × List Row) (s6 : BeaconState)
    (h : lhMidCore o s plan (s.withRowsChurn x.1 x.2) = .ok s6) : KeepB s s6 := by
  unfold lhMidCore at h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h6⟩ := specM_bind_ok h
  have hW : BalLen (lhQueueWrite s plan (s.withRowsChurn x.1 x.2)) := by
    simp [BalLen, lhQueueWrite, BeaconState.withRowsChurn, BeaconState.withRows]
  exact ((lhNewValidators_keep o plan _ s4 h4 hW).1.2.trans
    (consolidations_keepB _ s4 s5 h5)).trans (ebFold_keepB _ s5 s6 h6)

/-- The single pass does not write the proposer lookahead or the PTC window. -/
theorem lhSinglePass_keep [PresetCfg] (o : Oracle) (s T : BeaconState)
    (h : lhSinglePass o s = .ok T) :
    T.proposer_lookahead = s.proposer_lookahead ∧ T.ptc_window = s.ptc_window := by
  unfold lhSinglePass lhFullTailWith at h
  obtain ⟨cur, -, h⟩ := specM_bind_ok h
  obtain ⟨tab, -, h⟩ := specM_bind_ok h
  obtain ⟨rctx, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨adj, per⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨plan, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨dn, up⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨x, -, h⟩ := specM_bind_ok h
  simp only [lhMid_eq] at h
  obtain ⟨s6, h6, h7⟩ := specM_bind_ok h
  have k := lhMidCore_keep o s plan x s6 h6
  have h8 := process_builder_pending_payments_frame P tab s6 s6 T rfl rfl h7
  rw [h7] at h8
  have hT := Except.ok.inj h8
  rw [hT]
  exact ⟨k.2.1, k.2.2⟩

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open state_processing.per_epoch_processing.single_pass_step (ExitChurn StepContext ContextInputs)

/-- What `PendingDepositsContext::new` hands to `apply_deposit_writes`. -/
structure DepositPlan (D : Type) where
  next : Usize
  dbtc : U64
  postponed : List D
  news : Slice D

/-- The untranslated Rust around the translated calls of `process_epoch_single_pass`, from the
step context to the effective balance updates after the consolidations. `σ` is the Rust
`BeaconState` with its caches. Each trait of the translated code has its implementation
(`StateRows`, `StateDeposits`, ...), and each borrow of the state by a wrapper has its start and
its end. The other fields are the values that `single_pass.rs` reads and passes to the
translated code. -/
structure SinglePassGlue (σ E : Type) where
  /-- `StateRows`: the per-validator lists, borrowed for the loop. -/
  R : Type
  rows : LhRegistryRows R E
  rowsView : R → List Spec.Row
  rowsBorrow : σ → R
  /-- The end of the borrow, and the write of the exit churn that the loop returns. -/
  rowsReturn : σ → R → ExitChurn → σ
  /-- `ContextInputs`, `registry_constants` and the exit churn of the state. -/
  contextInputs : σ → ContextInputs
  registryConstants : per_epoch_processing.registry_update.RegistryConstants
  churn : σ → ExitChurn
  /-- `StateDeposits` and the plan of `PendingDepositsContext::new`. -/
  SD : Type
  D : Type
  deposits : LhDepositWrites SD D E
  absDep : D → Spec.PendingDeposit
  postOf : SD → List Spec.PendingDeposit
  depositPlan : σ → DepositPlan D
  depositBorrow : σ → List D → SD
  depositReturn : SD → σ
  /-- `StateConsolidations`, `StateEffectiveBalances` and `get_validators_in_consolidations`. -/
  consolidations : LhConsolidationState σ E
  effectiveBalances : LhEffectiveBalanceWrites σ E
  consolidationIndices : σ → Slice Usize

variable {σ E : Type}

/-- The steps of `process_epoch_single_pass` after the loop and before the builder payments:
`apply_deposit_writes`, `process_on_table` and `update_effective_balances_at`. `st` is the input
of the single pass, where `single_pass.rs` computed the plan and the indices, and `st1` the
state after the loop. `none`: the Rust returns an error. -/
def afterLoop (G : SinglePassGlue σ E) (st st1 : σ) : Result (Option σ) := do
  let (r, sd) ← per_epoch_processing.deposit_writes.apply_deposit_writes G.deposits
    (G.depositBorrow st1 (G.depositPlan st).postponed) (G.depositPlan st).next
    (G.depositPlan st).dbtc (G.depositPlan st).news true
  match r with
  | .Err _ => ok none
  | .Ok _ =>
  let (r, st3) ← per_epoch_processing.pending_consolidations.process_on_table G.consolidations
    (G.depositReturn sd) (G.consolidationIndices st)
  match r with
  | .Err _ => ok none
  | .Ok _ =>
  let (r, st4) ← per_epoch_processing.list_writes.update_effective_balances_at G.effectiveBalances
    st3 (G.consolidationIndices st)
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some st4)

/-- `process_epoch_single_pass` from the step context to the effective balance updates after the
consolidations: `step_context`, `single_pass_rows` and `afterLoop`. -/
def singlePassCore (G : SinglePassGlue σ E) (st : σ) : Result (Option σ) := do
  let c ← per_epoch_processing.single_pass_step.step_context (G.contextInputs st)
  match c with
  | .Err _ => ok none
  | .Ok c =>
  let (r, rows) ← per_epoch_processing.registry_rows.single_pass_rows G.rows (G.rowsBorrow st)
    (G.churn st) c G.registryConstants
  match r with
  | .Err _ => ok none
  | .Ok ch => afterLoop G st (G.rowsReturn st rows ch)

/-- The untranslated Rust of `process_builder_pending_payments` in `single_pass.rs`:
`StateBuilderPayments` and the arguments of `apply_builder_pending_payments`. -/
structure PaymentsGlue (σ E : Type) where
  SP : Type
  payments : LhPaymentWrites SP E
  wview : SP → List LhWithdrawal
  pview : SP → List LhPayment
  paymentsBorrow : σ → SP
  paymentsReturn : σ → SP → σ
  /-- `state_ctxt.total_active_balance`, read at the input of the single pass. -/
  totalActiveBalance : σ → U64
  slotsPerEpoch : U64
  slotsPerEpochUsize : Usize
  thresholdNumerator : U64
  thresholdDenominator : U64

/-- `process_builder_pending_payments`. `st` is the input of the single pass. -/
def payments (P : PaymentsGlue σ E) (st st4 : σ) : Result (Option σ) := do
  let (r, sp) ← per_epoch_processing.list_writes.apply_builder_pending_payments P.payments
    (P.paymentsBorrow st4) (P.totalActiveBalance st) P.slotsPerEpoch P.slotsPerEpochUsize
    P.thresholdNumerator P.thresholdDenominator
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some (P.paymentsReturn st4 sp))

/-- The Gloas `process_epoch_single_pass` up to the builder payments, as the calls of the
translated functions in `Generated.lean` joined by the glue. `none`: the Rust returns an
error. -/
def singlePass (G : SinglePassGlue σ E) (P : PaymentsGlue σ E) (st : σ) : Result (Option σ) := do
  let r ← singlePassCore G st
  match r with
  | none => ok none
  | some st4 => payments P st st4

variable [Spec.PresetCfg]

/-- The trusted facts about the glue `G` at the input `st` of the single pass, with `view` the
spec state that a Rust state holds. The contracts are those of `Trusted/`. The borrow facts say
which fields of the state each wrapper holds. The read facts say that the values passed to the
translated code are the spec values. `planTab` is the total that the deposit plan uses: the
total active balance in Gloas, `fuluTab` in Fulu. -/
structure SinglePassLinks (G : SinglePassGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (planTab : Spec.Gwei → Spec.Gwei) : Prop where
  /-- `RowsContract`, with the row inputs of the model. -/
  rowsContract : ∀ tab cur plan, Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    Spec.get_current_epoch Spec.P (view st) = .ok cur →
    Spec.lhDepositPlan (view st) (planTab tab) cur = .ok plan →
    RowsContract G.rows Spec.P G.rowsView
      (modelRowInputs tab plan.topups (Spec.consolidationIndices (view st)))
  depositContract : DepositWritesContract G.deposits o (fun sd => view (G.depositReturn sd))
    G.absDep G.postOf
  consolidationContract : ConsolidationStateContract G.consolidations Spec.P view
  /-- `BTreeSetIter` of `get_validators_in_consolidations`. -/
  btree : BTreeSetIter ((view st).pending_consolidations.flatMap
    fun c => [c.source_index, c.target_index]) ((G.consolidationIndices st).val.map (·.val))
  effectiveBalanceContract : EffectiveBalanceContract G.effectiveBalances view
  /-- `StateRows` holds the rows of the state. Ending its borrow and writing the churn gives
  the state with the new rows and churn. -/
  rowsBorrow : G.rowsView (G.rowsBorrow st) = Spec.rowsOf (view st)
  rowsReturn : ∀ r ch, view (G.rowsReturn st r ch) =
    (view st).withRowsChurn (absChurn ch) (G.rowsView r)
  /-- `StateDeposits` holds the state and the postponed deposits. -/
  depositBorrow : ∀ t post, view (G.depositReturn (G.depositBorrow t post)) = view t ∧
    G.postOf (G.depositBorrow t post) = post.map G.absDep
  /-- `ContextInputs`. -/
  contextInputs : ∀ cur tab, Spec.get_current_epoch Spec.P (view st) = .ok cur →
    Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    ContextInputsMatch (view st) cur tab (G.contextInputs st)
  churn : absChurn (G.churn st) =
    ((view st).earliest_exit_epoch, (view st).exit_balance_to_consume)
  /-- `PendingDepositsContext::new` hands over the plan of the model. -/
  depositPlan : ∀ tab cur plan, Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    Spec.get_current_epoch Spec.P (view st) = .ok cur →
    Spec.lhDepositPlan (view st) (planTab tab) cur = .ok plan →
    (G.depositPlan st).next.val = plan.next_deposit_index ∧
    (G.depositPlan st).dbtc.val = plan.deposit_balance_to_consume ∧
    (G.depositPlan st).postponed.map G.absDep = plan.postponed ∧
    (G.depositPlan st).news.val.map G.absDep = plan.new_validator_deposits
  /-- A state fact, not a glue fact: the new validators of the epoch fit under
  `VALIDATOR_REGISTRY_LIMIT = 2^40`, where the milhouse validator list fails and the spec does
  not. It holds on every real chain (the registry is far below `2^40`). -/
  depositRoom : ∀ tab cur plan, Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    Spec.get_current_epoch Spec.P (view st) = .ok cur →
    Spec.lhDepositPlan (view st) (planTab tab) cur = .ok plan →
    (view st).validators.length + plan.new_validator_deposits.length ≤ 2 ^ 40
  /-- `usize` has 64 bits. -/
  usize64 : Usize.max = U64.max

/-- The trusted facts about the payments glue `P`, with `st` the input of the single pass. -/
structure PaymentsLinks (P : PaymentsGlue σ E) (view : σ → Spec.BeaconState) (st : σ) : Prop where
  paymentContract : PaymentWritesContract P.payments P.wview P.pview
  /-- `StateBuilderPayments` holds the two builder lists of the state, and writes only them. -/
  paymentsBorrow : ∀ t, (P.pview (P.paymentsBorrow t)).map absPayment =
      (view t).builder_pending_payments ∧
    (P.wview (P.paymentsBorrow t)).map absWithdrawal = (view t).builder_pending_withdrawals
  paymentsReturn : ∀ t sp, view (P.paymentsReturn t sp) = { view t with
    builder_pending_withdrawals := (P.wview sp).map absWithdrawal
    builder_pending_payments := (P.pview sp).map absPayment }
  totalActiveBalance : ∀ tab, Spec.get_total_active_balance Spec.P (view st) = .ok tab →
    (P.totalActiveBalance st).val = tab
  slotsPerEpoch : P.slotsPerEpoch.val = Spec.P.SLOTS_PER_EPOCH
  slotsPerEpochUsize : P.slotsPerEpochUsize.val = Spec.P.SLOTS_PER_EPOCH
  /-- The builder payment threshold, 6/10. -/
  threshold : P.thresholdNumerator = 6#u64 ∧ P.thresholdDenominator = 10#u64

/-- The steps after the loop return the state of the model `lhMidCore`. -/
theorem afterLoop_spec (G : SinglePassGlue σ E) (o : Spec.Oracle) (view : σ → Spec.BeaconState)
    (st : σ) (planTab : Spec.Gwei → Spec.Gwei) (hL : SinglePassLinks G o view st planTab)
    (tab cur : Nat) (htab : Spec.get_total_active_balance Spec.P (view st) = .ok tab)
    (hcur : Spec.get_current_epoch Spec.P (view st) = .ok cur) (plan : Spec.LhDepositPlan)
    (hplan : Spec.lhDepositPlan (view st) (planTab tab) cur = .ok plan) (st1 : σ)
    (x : (Spec.Epoch × Spec.Gwei) × List Spec.Row)
    (hv1 : view st1 = (view st).withRowsChurn x.1 x.2)
    (hxlen : x.2.length = (view st).validators.length) (s6 : Spec.BeaconState)
    (h : Spec.lhMidCore o (view st) plan ((view st).withRowsChurn x.1 x.2) = .ok s6) :
    ∃ st4, afterLoop G st st1 = ok (some st4) ∧ view st4 = s6 := by
  unfold Spec.lhMidCore at h
  obtain ⟨s4, h4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s5, h5, h6⟩ := Spec.specM_bind_ok h
  unfold afterLoop
  -- The deposit writes.
  obtain ⟨hnext, hdbtc, hpostp, hnews⟩ := hL.depositPlan tab cur plan htab hcur hplan
  obtain ⟨hdv, hdp⟩ := hL.depositBorrow st1 (G.depositPlan st).postponed
  have hdep := apply_deposit_writes_model G.deposits o (fun sd => view (G.depositReturn sd))
    G.absDep G.postOf hL.depositContract (view st) (planTab tab) cur plan hplan
    (G.depositBorrow st1 (G.depositPlan st).postponed)
    (by simp only [hdv, hv1]; rfl) (G.depositPlan st).next (G.depositPlan st).dbtc
    (G.depositPlan st).news hnext hdbtc (by rw [hdp, hpostp]) hnews
    (by
      simp only [hdv, hv1, Spec.BeaconState.withRowsChurn, Spec.BeaconState.withRows,
        List.length_map, hxlen]
      exact hL.depositRoom tab cur plan htab hcur hplan)
  obtain ⟨⟨rd, sd⟩, hrd, hdpost⟩ := spec_imp_exists hdep
  rw [hrd]
  simp only [bind_tc_ok, uncurry_apply_pair]
  simp only [hdv, hv1] at hdpost
  obtain ⟨u, rfl⟩ : ∃ u, rd = .Ok u := by
    cases rd with
    | Ok u => exact ⟨u, rfl⟩
    | Err e =>
      obtain ⟨e', he'⟩ := hdpost
      rw [h4] at he'
      cases he'
  have hv2 : view (G.depositReturn sd) = s4 := by
    have := h4.symm.trans hdpost
    cases this; rfl
  simp only
  -- The pending consolidations.
  have hW : Spec.BalLen (Spec.lhQueueWrite (view st) plan
      ((view st).withRowsChurn x.1 x.2)) := by
    simp [Spec.BalLen, Spec.lhQueueWrite, Spec.BeaconState.withRowsChurn,
      Spec.BeaconState.withRows]
  obtain ⟨⟨hpc4, -⟩, hlen4⟩ := Spec.lhNewValidators_keep o plan _ s4 h4 hW
  have hbtree4 : BTreeSetIter (s4.pending_consolidations.flatMap
      fun c => [c.source_index, c.target_index])
      ((G.consolidationIndices st).val.map (·.val)) := by
    rw [hpc4]; exact hL.btree
  have hcons := process_on_table_spec G.consolidations Spec.P view hL.consolidationContract
    hL.usize64 (G.depositReturn sd) (G.consolidationIndices st) (by rw [hv2]; exact hbtree4)
    (by rw [hv2]; exact hlen4)
  obtain ⟨⟨rc, st3⟩, hrc, hcpost, -⟩ := spec_imp_exists hcons
  rw [hrc]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [hv2] at hcpost
  obtain ⟨hrc1, hv3⟩ := hcpost s5 h5
  simp only at hrc1 hv3
  subst hrc1
  simp only
  -- The effective balance updates of the validators that consolidations name.
  have hidx := btreeSetIter_consolidationIndices (view st) _ hL.btree
  have heb := update_effective_balances_at_spec G.effectiveBalances view
    hL.effectiveBalanceContract st3 (G.consolidationIndices st) _ hidx
  obtain ⟨⟨re, st4⟩, hre, hepost⟩ := spec_imp_exists heb
  rw [hre]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [hv3] at hepost
  obtain ⟨u, rfl⟩ : ∃ u, re = .Ok u := by
    cases re with
    | Ok u => exact ⟨u, rfl⟩
    | Err e =>
      obtain ⟨e', he'⟩ := hepost
      rw [h6] at he'
      cases he'
  refine ⟨st4, rfl, ?_⟩
  have := h6.symm.trans hepost
  cases this; rfl

/-- The builder payments return the state of the spec `process_builder_pending_payments`. -/
theorem payments_spec (P : PaymentsGlue σ E) (view : σ → Spec.BeaconState) (st : σ)
    (hL : PaymentsLinks P view st) (tab : Nat)
    (htab : Spec.get_total_active_balance Spec.P (view st) = .ok tab) (st4 : σ)
    (hlen : (view st4).builder_pending_payments.length = 2 * Spec.P.SLOTS_PER_EPOCH)
    (T : Spec.BeaconState)
    (h : Spec.process_builder_pending_payments Spec.P tab (view st4) = .ok T) :
    ∃ st', payments P st st4 = ok (some st') ∧ view st' = T := by
  obtain ⟨hpb, hwb⟩ := hL.paymentsBorrow st4
  have hplen : (P.pview (P.paymentsBorrow st4)).length = 2 * Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := absPayment), hpb, hlen]
  obtain ⟨v, -, hvv⟩ := hL.paymentContract.payments (P.paymentsBorrow st4)
  obtain ⟨hnum, hden⟩ := hL.threshold
  have hpay := apply_builder_pending_payments_equiv Spec.P P.payments P.wview P.pview
    hL.paymentContract (P.paymentsBorrow st4) (P.totalActiveBalance st) P.slotsPerEpoch
    P.slotsPerEpochUsize hL.slotsPerEpoch hL.slotsPerEpochUsize hplen ⟨v.val, v.property⟩ hvv
  rw [← hnum, ← hden] at hpay
  obtain ⟨⟨rp, sp⟩, hrp, hppost⟩ := spec_imp_exists hpay
  unfold payments
  rw [hrp]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [hL.totalActiveBalance tab htab] at hppost
  have hp0 : (view st4).builder_pending_payments =
      (absState (P.wview (P.paymentsBorrow st4),
        P.pview (P.paymentsBorrow st4))).builder_pending_payments := by
    rw [← hpb]; rfl
  have hw0 : (view st4).builder_pending_withdrawals =
      (absState (P.wview (P.paymentsBorrow st4),
        P.pview (P.paymentsBorrow st4))).builder_pending_withdrawals := by
    rw [← hwb]; rfl
  cases rp with
  | Err e =>
    exfalso
    obtain ⟨e', he'⟩ := hppost
    have := Spec.process_builder_pending_payments_frame Spec.P tab _ (view st4) T hp0 hw0 h
    rw [he'] at this
    cases this
  | Ok u =>
    refine ⟨_, rfl, ?_⟩
    have := Spec.process_builder_pending_payments_frame Spec.P tab (view st4) _ _ hp0.symm
      hw0.symm hppost
    rw [h] at this
    cases this
    rw [hL.paymentsReturn]
    rfl

/-- The composed Gloas single pass returns the state of the model `lhSinglePass`: when the model
returns `ok`, the Rust returns `Ok` with a state whose view is the model's. -/
theorem singlePass_spec [Spec.PresetCfg.Ok] (G : SinglePassGlue σ E) (P : PaymentsGlue σ E)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (st : σ) (hL : SinglePassLinks G o view st id)
    (hPL : PaymentsLinks P view st) (hk : ConstantsMatch Spec.P G.registryConstants)
    (hslot : (view st).slot < 2 ^ 64)
    (hbpp : (view st).builder_pending_payments.length = 2 * Spec.P.SLOTS_PER_EPOCH)
    (T : Spec.BeaconState) (hT : Spec.lhSinglePass o (view st) = .ok T) :
    ∃ st', singlePass G P st = ok (some st') ∧ view st' = T := by
  unfold Spec.lhSinglePass Spec.lhFullTailWith at hT
  obtain ⟨cur, hcur, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨tab, htab, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨rctx, hr, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨adj, per⟩, hpre, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨plan, hplan, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨dn, up⟩, hh, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨x, hx, hT⟩ := Spec.specM_bind_ok hT
  have hxlen : x.2.length = (view st).validators.length := by
    rw [(Spec.passM_rows _ _ _ _ hx).1, Spec.rowsOf_length]
  simp only [Spec.lhMid_eq] at hT
  obtain ⟨s6, h6, h7⟩ := Spec.specM_bind_ok hT
  have htarget : cur + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE := by
    rw [Spec.get_current_epoch_ok_eq hcur]; exact Spec.P_slot_target_lt hslot
  -- The step context and the loop.
  have hloop := single_pass_rows_model_inputs G.rows (view st) tab plan.topups
    (Spec.consolidationIndices (view st)) G.rowsView (G.rowsBorrow st) hL.rowsBorrow
    (hL.rowsContract tab cur plan htab hcur hplan) cur hcur rctx hr adj per hpre dn up hh htarget
    (G.contextInputs st) (hL.contextInputs cur tab hcur htab) G.registryConstants hk
    (G.churn st) hL.churn
  obtain ⟨r0, hr0, c, rfl, hc⟩ := spec_imp_exists hloop
  obtain ⟨⟨res, rows'⟩, hres, hpost⟩ := spec_imp_exists hc
  obtain ⟨ch, rfl⟩ : ∃ ch, res = .Ok ch := by
    cases res with
    | Ok ch => exact ⟨ch, rfl⟩
    | Err e =>
      cases e with
      | Step e =>
        have := hx.symm.trans hpost
        cases this
      | Rows e => exact absurd hpost id
  have hxv : x = (absChurn ch, G.rowsView rows') := by
    have := hx.symm.trans hpost
    cases this; rfl
  subst hxv
  -- The steps after the loop.
  obtain ⟨st4, ha, hv4⟩ := afterLoop_spec G o view st id hL tab cur htab hcur plan hplan
    (G.rowsReturn st rows' ch) _ (hL.rowsReturn rows' ch) (by rw [← hxlen]) s6 h6
  -- The builder payments.
  have hk6 := Spec.lhMidCore_keep o (view st) plan _ s6 h6
  obtain ⟨st', hp, hv'⟩ := payments_spec P view st hPL tab htab st4
    (by rw [hv4, hk6.1, hbpp]) T (by rw [hv4]; exact h7)
  refine ⟨st', ?_, hv'⟩
  unfold singlePass singlePassCore
  rw [hr0]
  simp only [bind_tc_ok]
  rw [hres]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [ha]
  simp only [bind_tc_ok]
  exact hp

end EpochProofs.Compose
