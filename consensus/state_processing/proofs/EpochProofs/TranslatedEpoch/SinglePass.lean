import EpochProofs.AeneasCompat
import EpochProofs.TranslatedSteps.StepContext
import EpochProofs.TranslatedSteps.DepositWrites
import EpochProofs.TranslatedSteps.ListWrites
import EpochProofs.TranslatedSteps.ConsolidationTable
import EpochProofs.LighthouseModel.Order
import EpochProofs.LighthouseModel.SpecToCommonStepOrder

/-!
# The single pass, composed from the translated functions

`singlePass` is `process_epoch_single_pass` of `single_pass.rs` up to the builder payments, as one
Lean function: the translated `step_context`, `single_pass_rows`, `apply_deposit_writes`,
`process_on_table`, `update_effective_balances_at` and `apply_builder_pending_payments`, joined by
the untranslated code (`UntranslatedSinglePass`, `UntranslatedBuilderPayments`): the trait
implementations over the milhouse lists, the borrows of the state by each wrapper, and the values
read from the state and the spec. `translatedSinglePass_matches_model` shows that, under the
trusted facts about the untranslated code (`UntranslatedSinglePassFacts`,
`UntranslatedBuilderPaymentsFacts`), it returns the state of the model `lighthouseSinglePass`, the
single pass of `process_epoch_lighthouse`. `translatedSinglePassBeforePayments` stops before the
builder payments; the Fulu epoch uses it (`TranslatedEpoch/Fulu.lean`).

The first part of the file proves the frame facts of the model steps that the composition needs:
which fields each step after the loop keeps.
-/

namespace EpochProofs.Spec

/-- The Lighthouse model from the start of the single pass to the builder payments. -/
def lighthouseSinglePass [CurrentPreset] (oracle : Oracle) (s : BeaconState) : SpecM BeaconState :=
  lighthouseSinglePassThen (fun s tab plan x =>
    lighthouseDepositsConsolidationsPayments oracle s tab plan (s.withRowsChurn x.1 x.2)) s

theorem lighthouseSinglePassThen_order_eq [CurrentPreset] (oracle : Oracle) (s : BeaconState) :
    lighthouseSinglePassThen (lighthouseStepsAfterSinglePass oracle) s =
      lighthouseSinglePass oracle s >>= lighthouseStepsAfterPayments oracle := by
  unfold lighthouseSinglePass lighthouseSinglePassThen lighthouseStepsAfterSinglePass
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

theorem apply_balLen [CurrentPreset] (oracle : Oracle) (t t' : BeaconState) (d : PendingDeposit)
    (h : apply_pending_deposit P oracle t d = .ok t') (ht : BalLen t) : BalLen t' := by
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

theorem updateEffectiveBalanceAt_balLen [CurrentPreset] (t t' : BeaconState) (i : Nat)
    (h : updateEffectiveBalanceAt t i = .ok t') (ht : BalLen t) : BalLen t' := by
  obtain ⟨v, b, e, -, -, -, rfl⟩ := (updateEffectiveBalanceAt_ok t t' i).mp h
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

theorem apply_midKeep [CurrentPreset] (oracle : Oracle) (t t' : BeaconState) (d : PendingDeposit)
    (h : apply_pending_deposit P oracle t d = .ok t') : MidKeep t t' := by
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact add_validator_midKeep P t t' _ _ _ h
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · split at h
    · contradiction
    · cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem updateEffectiveBalanceAt_midKeep [CurrentPreset] (t t' : BeaconState) (i : Nat)
    (h : updateEffectiveBalanceAt t i = .ok t') : MidKeep t t' := by
  obtain ⟨v, b, e, -, -, -, rfl⟩ := (updateEffectiveBalanceAt_ok t t' i).mp h
  unfold setEB
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem consolidations_keepB (p : Preset) (t t' : BeaconState)
    (h : process_pending_consolidations p t = .ok t') : KeepB t t' := by
  unfold process_pending_consolidations at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_keep (fun r : Prod Nat BeaconState => KeepB t r.snd) _ ?_ _ _ _
    ⟨rfl, rfl, rfl⟩ hr
  · cases h
    exact hP
  · intro _ ⟨_, _⟩ r hst hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hst)

theorem lighthouseNewValidators_keep [CurrentPreset] (oracle : Oracle)
    (plan : LighthouseDepositPlan) (t t' : BeaconState)
    (h : lighthouseNewValidators oracle plan t = .ok t') (ht : BalLen t) : MidKeep t t' ∧
    BalLen t' := by
  unfold lighthouseNewValidators at h
  rw [lighthouseApplyPendingDeposit_mainnet] at h
  obtain ⟨t3, h3, h⟩ := specM_bind_ok h
  have k3 := foldlM_keep (fun u => MidKeep t u ∧ BalLen u) (apply_pending_deposit P oracle)
    (fun u d u' hu hd => ⟨hu.1.trans (apply_midKeep oracle u u' d hd),
      apply_balLen oracle u u' d hd hu.2⟩)
    _ t t3 ⟨⟨rfl, rfl, rfl, rfl⟩, ht⟩ h3
  exact foldlM_keep (fun u => MidKeep t u ∧ BalLen u) updateEffectiveBalanceAt
    (fun u i u' hu hd => ⟨hu.1.trans (updateEffectiveBalanceAt_midKeep u u' i hd),
      updateEffectiveBalanceAt_balLen u u' i hd hu.2⟩)
    _ t3 t' k3 h

theorem ebFold_keepB [CurrentPreset] (l : List Nat) (t t' : BeaconState)
    (h : l.foldlM updateEffectiveBalanceAt t = .ok t') : KeepB t t' :=
  foldlM_keep (fun u => KeepB t u) updateEffectiveBalanceAt
    (fun u i u' hu hd => hu.trans (updateEffectiveBalanceAt_midKeep u u' i hd).2) l t t' ⟨rfl, rfl,
      rfl⟩ h

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

/-- The steps of `lighthouseDepositsConsolidationsPayments` before the builder payments: the
deposit writes, the pending consolidations and the effective balance updates of the validators that
consolidations name. -/
def lighthouseDepositsConsolidations [CurrentPreset] (oracle : Oracle) (s : BeaconState)
    (plan : LighthouseDepositPlan)
    (s1 : BeaconState) : SpecM BeaconState := do
  let s4 ← lighthouseNewValidators oracle plan (lighthouseDepositQueueWrite s plan s1)
  let s5 ← process_pending_consolidations P s4
  (validatorsInConsolidations s).foldlM updateEffectiveBalanceAt s5

theorem lighthouseDepositsConsolidationsPayments_eq [CurrentPreset] (oracle : Oracle)
    (s : BeaconState) (tab : Gwei)
    (plan : LighthouseDepositPlan)
    (s1 : BeaconState) :
    lighthouseDepositsConsolidationsPayments oracle s tab plan s1 =
      lighthouseDepositsConsolidations oracle s plan s1 >>=
      process_builder_pending_payments P tab := by
  simp only [lighthouseDepositsConsolidationsPayments, lighthouseDepositsConsolidations, bind_assoc]

/-- `lighthouseDepositsConsolidations` does not write the builder pending payments, the proposer
lookahead or the PTC window. -/
theorem lighthouseDepositsConsolidations_keep [CurrentPreset] (oracle : Oracle) (s : BeaconState)
    (plan : LighthouseDepositPlan)
    (x : (Epoch × Gwei) × List Row) (s6 : BeaconState)
    (h : lighthouseDepositsConsolidations oracle s plan (s.withRowsChurn x.1 x.2) = .ok s6) : KeepB
    s s6 := by
  unfold lighthouseDepositsConsolidations at h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h6⟩ := specM_bind_ok h
  have hW : BalLen (lighthouseDepositQueueWrite s plan (s.withRowsChurn x.1 x.2)) := by
    simp [BalLen, lighthouseDepositQueueWrite, BeaconState.withRowsChurn, BeaconState.withRows]
  exact ((lighthouseNewValidators_keep oracle plan _ s4 h4 hW).1.2.trans
    (consolidations_keepB _ s4 s5 h5)).trans (ebFold_keepB _ s5 s6 h6)

/-- The single pass does not write the proposer lookahead or the PTC window. -/
theorem lighthouseSinglePass_keep [CurrentPreset] (oracle : Oracle) (s T : BeaconState)
    (h : lighthouseSinglePass oracle s = .ok T) :
    T.proposer_lookahead = s.proposer_lookahead ∧ T.ptc_window = s.ptc_window := by
  unfold lighthouseSinglePass lighthouseSinglePassThen at h
  obtain ⟨cur, -, h⟩ := specM_bind_ok h
  obtain ⟨tab, -, h⟩ := specM_bind_ok h
  obtain ⟨rctx, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨adj, per⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨plan, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨dn, up⟩, -, h⟩ := specM_bind_ok h
  obtain ⟨x, -, h⟩ := specM_bind_ok h
  simp only [lighthouseDepositsConsolidationsPayments_eq] at h
  obtain ⟨s6, h6, h7⟩ := specM_bind_ok h
  have k := lighthouseDepositsConsolidations_keep oracle s plan x s6 h6
  have h8 := process_builder_pending_payments_frame P tab s6 s6 T rfl rfl h7
  rw [h7] at h8
  have hT := Except.ok.inj h8
  rw [hT]
  exact ⟨k.2.1, k.2.2⟩

end EpochProofs.Spec

namespace EpochProofs.TranslatedEpoch

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing
open state_processing.per_epoch_processing.single_pass_step (ExitChurn StepContext ContextInputs)

/-- What `PendingDepositsContext::new` hands to `apply_deposit_writes`. -/
structure TranslatedDepositPlan (D : Type) where
  nextDepositIndex : Usize
  depositBalanceToConsume : U64
  postponed : List D
  newValidators : Slice D

/-- The untranslated Rust around the translated calls of `process_epoch_single_pass`, from the
step context to the effective balance updates after the consolidations. `RustState` is the Rust
`BeaconState` with its caches. Each trait of the translated code has its implementation
(`StateRows`, `StateDeposits`, ...), and each borrow of the state by a wrapper has its start and
its end. The other fields are the values that `single_pass.rs` reads and passes to the
translated code. -/
structure UntranslatedSinglePass (RustState RustError : Type) where
  /-- `StateRows`: the per-validator lists, borrowed for the loop. -/
  Rows : Type
  rowOperations : LighthouseRegistryRows Rows RustError
  rowsToSpec : Rows → List Spec.Row
  rowsBorrow : RustState → Rows
  /-- The end of the borrow, and the write of the exit churn that the loop returns. -/
  rowsReturn : RustState → Rows → ExitChurn → RustState
  /-- `ContextInputs`, `registry_constants` and the exit churn of the state. -/
  contextInputs : RustState → ContextInputs
  registryConstants : per_epoch_processing.registry_update.RegistryConstants
  exitChurn : RustState → ExitChurn
  /-- `StateDeposits` and the plan of `PendingDepositsContext::new`. -/
  DepositState : Type
  Deposit : Type
  depositOperations : LighthouseDepositWrites DepositState Deposit RustError
  depositToSpec : Deposit → Spec.PendingDeposit
  postponedDeposits : DepositState → List Spec.PendingDeposit
  depositPlan : RustState → TranslatedDepositPlan Deposit
  depositBorrow : RustState → List Deposit → DepositState
  depositReturn : DepositState → RustState
  /-- `StateConsolidations`, `StateEffectiveBalances` and `get_validators_in_consolidations`. -/
  consolidationOperations : LighthouseConsolidationState RustState RustError
  effectiveBalanceOperations : LighthouseEffectiveBalanceWrites RustState RustError
  validatorsInConsolidations : RustState → Slice Usize

variable {RustState RustError : Type}

/-- The steps of `process_epoch_single_pass` after the loop and before the builder payments:
`apply_deposit_writes`, `process_on_table` and `update_effective_balances_at`. `rustState` is the
input of the single pass, where `single_pass.rs` computed the plan and the indices, and
`rustState1` the state after the loop. `none`: the Rust returns an error. -/
def translatedStepsAfterLoop (code : UntranslatedSinglePass RustState RustError)
    (rustState rustState1 : RustState) : Result (Option RustState) := do
  let (r, sd) ← per_epoch_processing.deposit_writes.apply_deposit_writes code.depositOperations
    (code.depositBorrow rustState1 (code.depositPlan rustState).postponed)
      (code.depositPlan rustState).nextDepositIndex
    (code.depositPlan rustState).depositBalanceToConsume (code.depositPlan rustState).newValidators
      true
  match r with
  | .Err _ => ok none
  | .Ok _ =>
  let (r, rustState3) ← per_epoch_processing.pending_consolidations.process_on_table
    code.consolidationOperations
    (code.depositReturn sd) (code.validatorsInConsolidations rustState)
  match r with
  | .Err _ => ok none
  | .Ok _ =>
  let (r, rustState4) ← per_epoch_processing.list_writes.update_effective_balances_at
    code.effectiveBalanceOperations
    rustState3 (code.validatorsInConsolidations rustState)
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some rustState4)

/-- `process_epoch_single_pass` from the step context to the effective balance updates after the
consolidations: `step_context`, `single_pass_rows` and `translatedStepsAfterLoop`. -/
def translatedSinglePassBeforePayments (code : UntranslatedSinglePass RustState RustError)
    (rustState : RustState) : Result (Option RustState) := do
  let c ← per_epoch_processing.single_pass_step.step_context (code.contextInputs rustState)
  match c with
  | .Err _ => ok none
  | .Ok c =>
  let (r, rows) ← per_epoch_processing.registry_rows.single_pass_rows code.rowOperations
    (code.rowsBorrow rustState)
    (code.exitChurn rustState) c code.registryConstants
  match r with
  | .Err _ => ok none
  | .Ok ch => translatedStepsAfterLoop code rustState (code.rowsReturn rustState rows ch)

/-- The untranslated Rust of `process_builder_pending_payments` in `single_pass.rs`:
`StateBuilderPayments` and the arguments of `apply_builder_pending_payments`. -/
structure UntranslatedBuilderPayments (RustState RustError : Type) where
  PaymentState : Type
  paymentOperations : LighthousePaymentWrites PaymentState RustError
  pendingWithdrawals : PaymentState → List LighthouseWithdrawal
  pendingPayments : PaymentState → List LighthousePayment
  paymentsBorrow : RustState → PaymentState
  paymentsReturn : RustState → PaymentState → RustState
  /-- `state_ctxt.total_active_balance`, read at the input of the single pass. -/
  totalActiveBalance : RustState → U64
  slotsPerEpoch : U64
  slotsPerEpochUsize : Usize
  thresholdNumerator : U64
  thresholdDenominator : U64

/-- `process_builder_pending_payments`. `rustState` is the input of the single pass. -/
def translatedBuilderPayments (paymentsCode : UntranslatedBuilderPayments RustState RustError)
    (rustState rustState4 : RustState) : Result (Option RustState) := do
  let (r, sp) ← per_epoch_processing.list_writes.apply_builder_pending_payments
    paymentsCode.paymentOperations
    (paymentsCode.paymentsBorrow rustState4) (paymentsCode.totalActiveBalance rustState)
      paymentsCode.slotsPerEpoch paymentsCode.slotsPerEpochUsize
    paymentsCode.thresholdNumerator paymentsCode.thresholdDenominator
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some (paymentsCode.paymentsReturn rustState4 sp))

/-- The Gloas `process_epoch_single_pass` up to the builder payments, as the calls of the
translated functions in `Generated.lean` joined by the untranslated code. `none`: the Rust
returns an error. -/
def translatedSinglePass (code : UntranslatedSinglePass RustState RustError)
    (paymentsCode : UntranslatedBuilderPayments RustState RustError)
    (rustState : RustState) : Result (Option RustState) := do
  let r ← translatedSinglePassBeforePayments code rustState
  match r with
  | none => ok none
  | some rustState4 => translatedBuilderPayments paymentsCode rustState rustState4

variable [Spec.CurrentPreset]

/-- The trusted facts about the untranslated code at the input `rustState` of the single pass, with
`rustStateToSpec` the spec state that a Rust state holds. The contracts are those of `Trusted/`.
The borrow
facts say which fields of the state each wrapper holds. The read facts say that the values passed
to the translated code are the spec values. `planTotal` is the total that the deposit plan uses: the
total active balance in Gloas, `fuluTotalActiveBalance` in Fulu. -/
structure UntranslatedSinglePassFacts (code : UntranslatedSinglePass RustState RustError)
    (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (planTotal : Spec.Gwei → Spec.Gwei) : Prop where
  /-- `ValidatorRowsMatchSpec`, with the row inputs of the model. -/
  rowsContract : ∀ total current plan,
    Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) = .ok total →
    Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current →
    Spec.lighthouseDepositPlan (rustStateToSpec rustState) (planTotal total) current = .ok plan →
    ValidatorRowsMatchSpec code.rowOperations Spec.P code.rowsToSpec
      (modelRowInputs total plan.topups
        (Spec.validatorsInConsolidations (rustStateToSpec rustState)))
  depositContract : DepositWritesMatchSpec code.depositOperations oracle (fun sd =>
    rustStateToSpec (code.depositReturn sd))
    code.depositToSpec code.postponedDeposits
  consolidationContract : ConsolidationAccessMatchesSpec code.consolidationOperations Spec.P
    rustStateToSpec
  /-- `IteratesLikeBTreeSet` of `get_validators_in_consolidations`. -/
  validatorsInConsolidations : IteratesLikeBTreeSet
    ((rustStateToSpec rustState).pending_consolidations.flatMap
    fun c => [c.source_index, c.target_index])
      ((code.validatorsInConsolidations rustState).val.map (·.val))
  effectiveBalanceContract : EffectiveBalanceWritesMatchSpec code.effectiveBalanceOperations
    rustStateToSpec
  /-- `StateRows` holds the rows of the state. Ending its borrow and writing the churn gives
  the state with the new rows and churn. -/
  rowsBorrow : code.rowsToSpec (code.rowsBorrow rustState) = Spec.rowsOf (rustStateToSpec rustState)
  rowsReturn : ∀ r ch, rustStateToSpec (code.rowsReturn rustState r ch) =
    (rustStateToSpec rustState).withRowsChurn (exitChurnToSpec ch) (code.rowsToSpec r)
  /-- `StateDeposits` holds the state and the postponed deposits. -/
  depositBorrow : ∀ t post, rustStateToSpec (code.depositReturn (code.depositBorrow t post)) =
    rustStateToSpec t ∧
    code.postponedDeposits (code.depositBorrow t post) = post.map code.depositToSpec
  /-- `ContextInputs`. -/
  contextInputs : ∀ current total, Spec.get_current_epoch Spec.P (rustStateToSpec rustState) =
    .ok current →
    Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) = .ok total →
    ContextInputsMatch (rustStateToSpec rustState) current total (code.contextInputs rustState)
  exitChurn : exitChurnToSpec (code.exitChurn rustState) =
    ((rustStateToSpec rustState).earliest_exit_epoch,
      (rustStateToSpec rustState).exit_balance_to_consume)
  /-- `PendingDepositsContext::new` hands over the plan of the model. -/
  depositPlan : ∀ total current plan,
    Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) = .ok total →
    Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current →
    Spec.lighthouseDepositPlan (rustStateToSpec rustState) (planTotal total) current = .ok plan →
    (code.depositPlan rustState).nextDepositIndex.val = plan.next_deposit_index ∧
    (code.depositPlan rustState).depositBalanceToConsume.val = plan.deposit_balance_to_consume ∧
    (code.depositPlan rustState).postponed.map code.depositToSpec = plan.postponed ∧
    (code.depositPlan rustState).newValidators.val.map code.depositToSpec =
      plan.new_validator_deposits
  /-- A state fact, not a fact about the Rust: the new validators of the epoch fit under
  `VALIDATOR_REGISTRY_LIMIT = 2^40`, where the milhouse validator list fails and the spec does
  not. It holds on every real chain (the registry is far below `2^40`). -/
  depositRoom : ∀ total current plan,
    Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) = .ok total →
    Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current →
    Spec.lighthouseDepositPlan (rustStateToSpec rustState) (planTotal total) current = .ok plan →
    (rustStateToSpec rustState).validators.length + plan.new_validator_deposits.length ≤ 2 ^ 40
  /-- `usize` has 64 bits. -/
  usize64 : Usize.max = U64.max

/-- The trusted facts about the untranslated payments code, with `rustState` the input of the single
pass. -/
structure UntranslatedBuilderPaymentsFacts
    (paymentsCode : UntranslatedBuilderPayments RustState RustError)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState) : Prop where
  paymentContract : BuilderPaymentWritesMatchSpec paymentsCode.paymentOperations
    paymentsCode.pendingWithdrawals paymentsCode.pendingPayments
  /-- `StateBuilderPayments` holds the two builder lists of the state, and writes only them. -/
  paymentsBorrow : ∀ t, (paymentsCode.pendingPayments (paymentsCode.paymentsBorrow t)).map
    paymentToSpec =
      (rustStateToSpec t).builder_pending_payments ∧
    (paymentsCode.pendingWithdrawals (paymentsCode.paymentsBorrow t)).map withdrawalToSpec =
      (rustStateToSpec t).builder_pending_withdrawals
  paymentsReturn : ∀ t sp, rustStateToSpec (paymentsCode.paymentsReturn t sp) =
    { rustStateToSpec t with
    builder_pending_withdrawals := (paymentsCode.pendingWithdrawals sp).map withdrawalToSpec
    builder_pending_payments := (paymentsCode.pendingPayments sp).map paymentToSpec }
  totalActiveBalance : ∀ total, Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) =
    .ok total →
    (paymentsCode.totalActiveBalance rustState).val = total
  slotsPerEpoch : paymentsCode.slotsPerEpoch.val = Spec.P.SLOTS_PER_EPOCH
  slotsPerEpochUsize : paymentsCode.slotsPerEpochUsize.val = Spec.P.SLOTS_PER_EPOCH
  /-- The builder payment threshold, 6/10. -/
  threshold : paymentsCode.thresholdNumerator = 6#u64 ∧ paymentsCode.thresholdDenominator = 10#u64

/-- The steps after the loop return the state of the model `lighthouseDepositsConsolidations`. -/
theorem translatedStepsAfterLoop_spec (code : UntranslatedSinglePass RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (rustState : RustState) (planTotal : Spec.Gwei → Spec.Gwei)
    (hL : UntranslatedSinglePassFacts code oracle rustStateToSpec rustState planTotal)
    (total current : Nat) (htab : Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) =
    .ok total)
    (hcur : Spec.get_current_epoch Spec.P (rustStateToSpec rustState) = .ok current)
    (plan : Spec.LighthouseDepositPlan)
    (hplan : Spec.lighthouseDepositPlan (rustStateToSpec rustState) (planTotal total) current =
    .ok plan)
    (rustState1 : RustState)
    (x : (Spec.Epoch × Spec.Gwei) × List Spec.Row)
    (hv1 : rustStateToSpec rustState1 = (rustStateToSpec rustState).withRowsChurn x.1 x.2)
    (hxlen : x.2.length = (rustStateToSpec rustState).validators.length) (s6 : Spec.BeaconState)
    (h : Spec.lighthouseDepositsConsolidations oracle (rustStateToSpec rustState) plan
    ((rustStateToSpec rustState).withRowsChurn x.1 x.2) = .ok s6) :
    ∃ rustState4, translatedStepsAfterLoop code rustState rustState1 = ok (some rustState4) ∧
      rustStateToSpec rustState4 = s6 := by
  unfold Spec.lighthouseDepositsConsolidations at h
  obtain ⟨s4, h4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s5, h5, h6⟩ := Spec.specM_bind_ok h
  unfold translatedStepsAfterLoop
  -- The deposit writes.
  obtain ⟨hnext, hdbtc, hpostp, hnews⟩ := hL.depositPlan total current plan htab hcur hplan
  obtain ⟨hdv, hdp⟩ := hL.depositBorrow rustState1 (code.depositPlan rustState).postponed
  have hdep := apply_deposit_writes_model code.depositOperations oracle (fun sd =>
    rustStateToSpec (code.depositReturn sd))
    code.depositToSpec code.postponedDeposits hL.depositContract (rustStateToSpec rustState)
      (planTotal total) current plan hplan
    (code.depositBorrow rustState1 (code.depositPlan rustState).postponed)
    (by simp only [hdv, hv1]; rfl) (code.depositPlan rustState).nextDepositIndex
      (code.depositPlan rustState).depositBalanceToConsume
    (code.depositPlan rustState).newValidators hnext hdbtc (by rw [hdp, hpostp]) hnews
    (by
      simp only [hdv, hv1, Spec.BeaconState.withRowsChurn, Spec.BeaconState.withRows,
        List.length_map, hxlen]
      exact hL.depositRoom total current plan htab hcur hplan)
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
  have hv2 : rustStateToSpec (code.depositReturn sd) = s4 := by
    have := h4.symm.trans hdpost
    cases this; rfl
  simp only
  -- The pending consolidations.
  have hW : Spec.BalLen (Spec.lighthouseDepositQueueWrite (rustStateToSpec rustState) plan
      ((rustStateToSpec rustState).withRowsChurn x.1 x.2)) := by
    simp [Spec.BalLen, Spec.lighthouseDepositQueueWrite, Spec.BeaconState.withRowsChurn,
      Spec.BeaconState.withRows]
  obtain ⟨⟨hpc4, -⟩, hlen4⟩ := Spec.lighthouseNewValidators_keep oracle plan _ s4 h4 hW
  have hbtree4 : IteratesLikeBTreeSet (s4.pending_consolidations.flatMap
      fun c => [c.source_index, c.target_index])
      ((code.validatorsInConsolidations rustState).val.map (·.val)) := by
    rw [hpc4]; exact hL.validatorsInConsolidations
  have hcons := process_on_table_spec code.consolidationOperations Spec.P rustStateToSpec
    hL.consolidationContract
    hL.usize64 (code.depositReturn sd) (code.validatorsInConsolidations rustState)
      (by rw [hv2]; exact hbtree4)
    (by rw [hv2]; exact hlen4)
  obtain ⟨⟨rc, rustState3⟩, hrc, hcpost, -⟩ := spec_imp_exists hcons
  rw [hrc]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [hv2] at hcpost
  obtain ⟨hrc1, hv3⟩ := hcpost s5 h5
  simp only at hrc1 hv3
  subst hrc1
  simp only
  -- The effective balance updates of the validators that consolidations name.
  have hidx := btreeSetIter_consolidationIndices (rustStateToSpec rustState) _
    hL.validatorsInConsolidations
  have heb := update_effective_balances_at_spec code.effectiveBalanceOperations rustStateToSpec
    hL.effectiveBalanceContract rustState3 (code.validatorsInConsolidations rustState) _ hidx
  obtain ⟨⟨re, rustState4⟩, hre, hepost⟩ := spec_imp_exists heb
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
  refine ⟨rustState4, rfl, ?_⟩
  have := h6.symm.trans hepost
  cases this; rfl

/-- The builder payments return the state of the spec `process_builder_pending_payments`. -/
theorem translatedBuilderPayments_matches_model
    (paymentsCode : UntranslatedBuilderPayments RustState RustError)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedBuilderPaymentsFacts paymentsCode rustStateToSpec rustState) (total : Nat)
    (htab : Spec.get_total_active_balance Spec.P (rustStateToSpec rustState) = .ok total)
    (rustState4 : RustState)
    (hlen : (rustStateToSpec rustState4).builder_pending_payments.length = 2 *
    Spec.P.SLOTS_PER_EPOCH)
    (T : Spec.BeaconState)
    (h : Spec.process_builder_pending_payments Spec.P total (rustStateToSpec rustState4) = .ok T) :
    ∃ rustState', translatedBuilderPayments paymentsCode rustState rustState4 = ok (some rustState')
      ∧ rustStateToSpec rustState' = T := by
  obtain ⟨hpb, hwb⟩ := hL.paymentsBorrow rustState4
  have hplen : (paymentsCode.pendingPayments (paymentsCode.paymentsBorrow rustState4)).length = 2 *
    Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := paymentToSpec), hpb, hlen]
  obtain ⟨v, -, hvv⟩ := hL.paymentContract.payments (paymentsCode.paymentsBorrow rustState4)
  obtain ⟨hnum, hden⟩ := hL.threshold
  have hpay := apply_builder_pending_payments_equiv Spec.P paymentsCode.paymentOperations
    paymentsCode.pendingWithdrawals paymentsCode.pendingPayments
    hL.paymentContract (paymentsCode.paymentsBorrow rustState4)
      (paymentsCode.totalActiveBalance rustState) paymentsCode.slotsPerEpoch
    paymentsCode.slotsPerEpochUsize hL.slotsPerEpoch hL.slotsPerEpochUsize hplen
    (Slice.from v.val v.property) (by rw [Slice.from_val]; exact hvv)
  rw [← hnum, ← hden] at hpay
  obtain ⟨⟨rp, sp⟩, hrp, hppost⟩ := spec_imp_exists hpay
  unfold translatedBuilderPayments
  rw [hrp]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [hL.totalActiveBalance total htab] at hppost
  have hp0 : (rustStateToSpec rustState4).builder_pending_payments =
      (builderStateToSpec (paymentsCode.pendingWithdrawals (paymentsCode.paymentsBorrow rustState4),
        paymentsCode.pendingPayments
          (paymentsCode.paymentsBorrow rustState4))).builder_pending_payments := by
    rw [← hpb]; rfl
  have hw0 : (rustStateToSpec rustState4).builder_pending_withdrawals =
      (builderStateToSpec (paymentsCode.pendingWithdrawals (paymentsCode.paymentsBorrow rustState4),
        paymentsCode.pendingPayments
          (paymentsCode.paymentsBorrow rustState4))).builder_pending_withdrawals := by
    rw [← hwb]; rfl
  cases rp with
  | Err e =>
    exfalso
    obtain ⟨e', he'⟩ := hppost
    have := Spec.process_builder_pending_payments_frame Spec.P total _ (rustStateToSpec rustState4)
      T hp0 hw0 h
    rw [he'] at this
    cases this
  | Ok u =>
    refine ⟨_, rfl, ?_⟩
    have := Spec.process_builder_pending_payments_frame Spec.P total (rustStateToSpec rustState4) _
      _ hp0.symm
      hw0.symm hppost
    rw [h] at this
    cases this
    rw [hL.paymentsReturn]
    rfl

/-- The composed Gloas single pass returns the state of the model `lighthouseSinglePass`: when the
model returns `ok`, the Rust returns `Ok` with a state whose spec state is the model's. -/
theorem translatedSinglePass_matches_model [Spec.CurrentPreset.Valid]
    (code : UntranslatedSinglePass RustState RustError)
    (paymentsCode : UntranslatedBuilderPayments RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (hL : UntranslatedSinglePassFacts code oracle rustStateToSpec rustState id)
    (hPL : UntranslatedBuilderPaymentsFacts paymentsCode rustStateToSpec rustState)
    (hk : RegistryConstantsMatchGloas Spec.P code.registryConstants)
    (hslot : (rustStateToSpec rustState).slot < 2 ^ 64)
    (hbpp : (rustStateToSpec rustState).builder_pending_payments.length = 2 *
    Spec.P.SLOTS_PER_EPOCH)
    (T : Spec.BeaconState) (hT : Spec.lighthouseSinglePass oracle (rustStateToSpec rustState) =
    .ok T) :
    ∃ rustState', translatedSinglePass code paymentsCode rustState = ok (some rustState') ∧
      rustStateToSpec rustState' = T := by
  unfold Spec.lighthouseSinglePass Spec.lighthouseSinglePassThen at hT
  obtain ⟨current, hcur, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨total, htab, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨rctx, hr, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨adj, per⟩, hpre, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨plan, hplan, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨⟨dn, up⟩, hh, hT⟩ := Spec.specM_bind_ok hT
  obtain ⟨x, hx, hT⟩ := Spec.specM_bind_ok hT
  have hxlen : x.2.length = (rustStateToSpec rustState).validators.length := by
    rw [(Spec.passM_rows _ _ _ _ hx).1, Spec.rowsOf_length]
  simp only [Spec.lighthouseDepositsConsolidationsPayments_eq] at hT
  obtain ⟨s6, h6, h7⟩ := Spec.specM_bind_ok hT
  have htarget : current + Spec.P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < Spec.UINT64_SIZE := by
    rw [Spec.get_current_epoch_ok_eq hcur]; exact Spec.P_slot_target_lt hslot
  -- The step context and the loop.
  have hloop := single_pass_rows_model_inputs code.rowOperations (rustStateToSpec rustState) total
    plan.topups
    (Spec.validatorsInConsolidations (rustStateToSpec rustState)) code.rowsToSpec
      (code.rowsBorrow rustState) hL.rowsBorrow
    (hL.rowsContract total current plan htab hcur hplan) current hcur rctx hr adj per hpre dn up hh
      htarget
    (code.contextInputs rustState) (hL.contextInputs current total hcur htab) code.registryConstants
      hk
    (code.exitChurn rustState) hL.exitChurn
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
  have hxv : x = (exitChurnToSpec ch, code.rowsToSpec rows') := by
    have := hx.symm.trans hpost
    cases this; rfl
  subst hxv
  -- The steps after the loop.
  obtain ⟨rustState4, ha, hv4⟩ :=
    translatedStepsAfterLoop_spec code oracle rustStateToSpec rustState id hL total current htab
    hcur plan hplan
    (code.rowsReturn rustState rows' ch) _ (hL.rowsReturn rows' ch) (by rw [← hxlen]) s6 h6
  -- The builder payments.
  have hk6 := Spec.lighthouseDepositsConsolidations_keep oracle (rustStateToSpec rustState) plan _
    s6 h6
  obtain ⟨rustState', hp, hv'⟩ :=
    translatedBuilderPayments_matches_model paymentsCode rustStateToSpec rustState hPL total htab
    rustState4
    (by rw [hv4, hk6.1, hbpp]) T (by rw [hv4]; exact h7)
  refine ⟨rustState', ?_, hv'⟩
  unfold translatedSinglePass translatedSinglePassBeforePayments
  rw [hr0]
  simp only [bind_tc_ok]
  rw [hres]
  simp only [bind_tc_ok, uncurry_apply_pair]
  rw [ha]
  simp only [bind_tc_ok]
  exact hp

end EpochProofs.TranslatedEpoch
