import EpochProofs.LighthouseModel.OrderEth1
import EpochProofs.Spec.CurrentPreset
import EpochProofs.LighthouseModel.StateTransition
import EpochProofs.LighthouseModel.NewValidator

/-!
# The Lighthouse epoch in the Lighthouse order

`processEpochWithSinglePassAndDeposits` runs the steps after the single pass in the spec order and
calls the spec functions for the resets and the historical summaries update.
`process_epoch_lighthouse` runs them
as `altair.rs` and `single_pass.rs` do:

1. the single pass, the deposits, the consolidations and the builder payments,
2. the proposer lookahead and the PTC window (inside `process_epoch_single_pass`),
3. the eth1, slashings and randao resets and the historical summaries update, with the checks of
   `tail_updates.rs` (`LighthouseModel/Resets.lean`),
4. the participation rotation and the sync committee update.

`process_epoch_lighthouse_sameResultOrBothFail` shows that the two give the same `ok` results, at
the last slot of an epoch, when the next slot fits in a `u64` and `historical_summaries` is below
the Lighthouse limit.
-/

namespace EpochProofs.Spec

/-! ## The steps between the single pass and the committee steps -/

/-- The deposit queue write after the single pass. -/
def lighthouseDepositQueueWrite (s : BeaconState) (plan : LighthouseDepositPlan)
    (s1 : BeaconState) : BeaconState :=
  { s1 with
    pending_deposits := s.pending_deposits.drop plan.next_deposit_index ++ plan.postponed
    deposit_balance_to_consume := plan.deposit_balance_to_consume }

/-- The new validators and their effective balance updates. A new validator gets the effective
balance of `deposit_balance.rs` (`lighthouseApplyPendingDeposit`). -/
def lighthouseNewValidators [CurrentPreset] (o : Oracle) (plan : LighthouseDepositPlan)
    (s2 : BeaconState) :
    SpecM BeaconState := do
  let s3 ← plan.new_validator_deposits.foldlM (lighthouseApplyPendingDeposit P o) s2
  (List.range' s2.validators.length (s3.validators.length - s2.validators.length)).foldlM
    updateEffectiveBalanceAt s3

/-- The steps of `lighthouseFullTail` from the deposit queue write to the builder payments. -/
def lighthouseDepositsConsolidationsPayments [CurrentPreset] (o : Oracle) (s : BeaconState)
    (total_active_balance : Gwei) (plan : LighthouseDepositPlan)
    (s1 : BeaconState) : SpecM BeaconState := do
  let s4 ← lighthouseNewValidators o plan (lighthouseDepositQueueWrite s plan s1)
  let s5 ← process_pending_consolidations P s4
  let s6 ← (validatorsInConsolidations s).foldlM updateEffectiveBalanceAt s5
  process_builder_pending_payments P total_active_balance s6

theorem lighthouseAfterPass_eq [CurrentPreset] (o : Oracle) (s : BeaconState)
    (total_active_balance : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) :
    lighthouseAfterPass o s total_active_balance plan x =
      (process_eth1_data_reset P (s.withRowsChurn x.1 x.2) >>= fun s1 =>
        lighthouseDepositsConsolidationsPayments o s total_active_balance plan s1 >>=
          epochRest2 o) := by
  simp only [lighthouseAfterPass, lighthouseAfterPassG, gloasFin,
    lighthouseDepositsConsolidationsPayments, lighthouseNewValidators, lighthouseDepositQueueWrite,
    bind_assoc, lighthouseApplyPendingDeposit_mainnet]

theorem lighthouseNewValidators_votesBlind [CurrentPreset] (o : Oracle)
    (plan : LighthouseDepositPlan) :
    VotesBlind (lighthouseNewValidators o plan) := by
  intro t
  unfold lighthouseNewValidators
  rw [lighthouseApplyPendingDeposit_mainnet]
  have h3 := votesBlind_foldlM (fun t x => apply_pending_deposit P o t x)
    (apply_votesBlind o) plan.new_validator_deposits t
  simp only at h3
  rw [h3]
  cases plan.new_validator_deposits.foldlM (apply_pending_deposit P o) t with
  | error e => rfl
  | ok s3 =>
    have h4 := votesBlind_foldlM (fun t i => updateEffectiveBalanceAt t i)
      updateEffectiveBalanceAt_votesBlind
      (List.range' t.validators.length (s3.validators.length - t.validators.length)) s3
    simp only at h4
    exact h4

theorem lighthouseNewValidators_slotKeep [CurrentPreset] (o : Oracle)
    (plan : LighthouseDepositPlan) :
    KeepsSlot (lighthouseNewValidators o plan) := by
  intro t t' h
  unfold lighthouseNewValidators at h
  rw [lighthouseApplyPendingDeposit_mainnet] at h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨a1, a2⟩ := slotKeep_foldlM (fun t x => apply_pending_deposit P o t x)
    (apply_slotKeep o) plan.new_validator_deposits t s3 h3
  obtain ⟨b1, b2⟩ := slotKeep_foldlM (fun t i => updateEffectiveBalanceAt t i)
    updateEffectiveBalanceAt_slotKeep _ s3 t' h
  exact ⟨b1.trans a1, b2.trans a2⟩

theorem lighthouseDepositsConsolidationsPayments_votesBlind [CurrentPreset] (o : Oracle)
    (s : BeaconState) (tab : Gwei) (plan : LighthouseDepositPlan) :
    VotesBlind (lighthouseDepositsConsolidationsPayments o s tab plan) := by
  intro t
  have hq : lighthouseDepositQueueWrite s plan (clearVotes t) =
    clearVotes (lighthouseDepositQueueWrite s plan t) := rfl
  have h := votesBlind_bind (lighthouseNewValidators_votesBlind o plan)
    (votesBlind_bind consolidations_votesBlind
      (votesBlind_bind (votesBlind_foldlM (fun t i => updateEffectiveBalanceAt t i)
        updateEffectiveBalanceAt_votesBlind
        (validatorsInConsolidations s)) (payments_votesBlind tab)))
          (lighthouseDepositQueueWrite s plan t)
  simp only [bind_assoc] at h
  simp only [lighthouseDepositsConsolidationsPayments, hq, bind_assoc]
  exact h

theorem lighthouseDepositsConsolidationsPayments_slotKeep [CurrentPreset] (o : Oracle)
    (s : BeaconState) (tab : Gwei) (plan : LighthouseDepositPlan) :
    KeepsSlot (lighthouseDepositsConsolidationsPayments o s tab plan) := by
  intro t t' h
  have k := slotKeep_bind (lighthouseNewValidators_slotKeep o plan)
    (slotKeep_bind consolidations_slotKeep
      (slotKeep_bind (slotKeep_foldlM (fun t i => updateEffectiveBalanceAt t i)
        updateEffectiveBalanceAt_slotKeep
        (validatorsInConsolidations s)) (payments_slotKeep tab)))
          (lighthouseDepositQueueWrite s plan t) t'
  simp only [bind_assoc] at k
  simp only [lighthouseDepositsConsolidationsPayments, bind_assoc] at h
  exact k h

/-! ## The steps after the builder payments in the Lighthouse order -/

/-- The steps after the builder payments, as Lighthouse runs them. -/
def lighthouseStepsAfterPayments [CurrentPreset] (o : Oracle)
    (t : BeaconState) : SpecM BeaconState := do
  let t ← process_proposer_lookahead P o t
  let t ← process_ptc_window P o t
  let t ← lighthouseEth1DataReset t
  let t ← lighthouseSlashingsReset t
  let t ← lighthouseRandaoMixesReset t
  let t ← lighthouseHistoricalSummariesUpdate o t
  let t := process_participation_flag_updates t
  process_sync_committee_updates P o t

/-- The conditions of the Lighthouse order at a state: the last slot of an epoch, the next slot
fits in a `u64`, and `historical_summaries` is below the Lighthouse limit. -/
def AtLastSlotOfEpoch [CurrentPreset] (s : BeaconState) : Prop :=
  (s.slot + 1) % P.SLOTS_PER_EPOCH = 0 ∧ s.slot + 1 < 2 ^ 64 ∧
    s.historical_summaries.length < LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT

/-- A bind whose continuations agree on the results with `Q`. -/
theorem bind_congr_of {α : Type} {x : SpecM α} {k1 k2 : α → SpecM BeaconState} (Q : α → Prop)
    (hx : ∀ v, x = .ok v → Q v) (hk : ∀ v, Q v → k1 v = k2 v) : (x >>= k1) = (x >>= k2) := by
  cases h : x with
  | error e => rfl
  | ok v => exact hk v (hx v h)

/-- The fields that the conditions read: the slot and `historical_summaries`. -/
def SameSH (T t : BeaconState) : Prop :=
  t.slot = T.slot ∧ t.historical_summaries = T.historical_summaries

theorem runSteps_lighthouseOrder_eq [CurrentPreset] [CurrentPreset.Valid] (o : Oracle)
    (T : BeaconState) (hT : AtLastSlotOfEpoch T) :
    runSteps (lighthouseOrder o) T = lighthouseStepsAfterPayments o T := by
  obtain ⟨halign, hslot, hroom⟩ := hT
  have kpl : StepKeeps (SameSH T) (process_proposer_lookahead P o) :=
    keeps_of_shape _ _ _ _ (process_proposer_lookahead_eq o) (fun _ _ h => h)
  have kptc : StepKeeps (SameSH T) (process_ptc_window P o) :=
    keeps_of_shape _ _ _ _ (process_ptc_window_eq o) (fun _ _ h => h)
  have ke1 : StepKeeps (SameSH T) (process_eth1_data_reset P) :=
    keeps_of_shape _ _ _ _ eth1_eq (fun b _ h => by cases b <;> exact h)
  have ksr : StepKeeps (SameSH T) (process_slashings_reset P) :=
    keeps_of_shape _ _ _ _ process_slashings_reset_eq (fun _ _ h => h)
  have krr : StepKeeps (SameSH T) (process_randao_mixes_reset P) :=
    keeps_of_shape _ _ _ _ process_randao_mixes_reset_eq (fun _ _ h => h)
  have hfit : ∀ t, SameSH T t → t.slot / P.SLOTS_PER_EPOCH + 1 +
      P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 := by
    intro t ht
    rw [ht.1]
    exact P_slot_hist_fit hslot
  have hfit' : ∀ t, SameSH T t → t.slot / P.SLOTS_PER_EPOCH + 1 +
      P.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64 := by
    intro t ht
    rw [ht.1]
    exact P_slot_slash_fit hslot
  simp only [runSteps, lighthouseOrder, lighthouseStepsAfterPayments, pfStep, bind_pure]
  refine bind_congr_of (SameSH T) (fun v h => kpl T v ⟨rfl, rfl⟩ h) (fun t1 h1 => ?_)
  refine bind_congr_of (SameSH T) (fun v h => kptc t1 v h1 h) (fun t2 h2 => ?_)
  rw [lighthouseEth1DataReset_eq t2 (by rw [h2.1]; exact hslot) (by rw [h2.1]; exact halign)]
  refine bind_congr_of (SameSH T) (fun v h => ke1 t2 v h2 h) (fun t3 h3 => ?_)
  rw [lighthouseSlashingsReset_eq t3 (hfit' t3 h3)]
  refine bind_congr_of (SameSH T) (fun v h => ksr t3 v h3 h) (fun t4 h4 => ?_)
  rw [lighthouseRandaoMixesReset_eq t4 (hfit t4 h4)]
  refine bind_congr_of (SameSH T) (fun v h => krr t4 v h4 h) (fun t5 h5 => ?_)
  rw [lighthouseHistoricalSummariesUpdate_eq o t5 (by rw [h5.2]; exact hroom)]
  rfl

theorem runSteps_specOrder_eq [CurrentPreset] (o : Oracle) (T : BeaconState) :
    runSteps (specOrder o) T = (process_eth1_data_reset P T >>= epochRest2 o) := by
  simp only [runSteps, specOrder, pfStep, bind_pure, pure_bind]
  rfl

/-- The steps after the builder payments: the Lighthouse order with the Lighthouse resets gives
the same `ok` results as the eth1 reset followed by the spec order. -/
theorem lighthouseStepsAfterPayments_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid]
    (o : Oracle) (T : BeaconState) (hT : AtLastSlotOfEpoch T) :
    SameResultOrBothFail (lighthouseStepsAfterPayments o T) (process_eth1_data_reset P T >>=
      epochRest2 o) := by
  have hroom : SlotRoom T := P_slot_room hT.2.1
  rw [← runSteps_lighthouseOrder_eq o T hT, ← runSteps_specOrder_eq o T]
  exact SameResultOrBothFail.flip (specOrder_lighthouseOrder o T hroom)

/-- `lighthouseAfterPass` in the Lighthouse order. -/
def lighthouseStepsAfterSinglePass [CurrentPreset] (o : Oracle) (s : BeaconState)
    (total_active_balance : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState :=
  lighthouseDepositsConsolidationsPayments o s total_active_balance plan (s.withRowsChurn x.1 x.2)
    >>= lighthouseStepsAfterPayments o

theorem lighthouseStepsAfterSinglePass_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid]
    (o : Oracle) (s : BeaconState) (tab : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) (hs : AtLastSlotOfEpoch s) :
    SameResultOrBothFail (lighthouseStepsAfterSinglePass o s tab plan x)
      (lighthouseAfterPass o s tab plan x) := by
  rw [lighthouseAfterPass_eq]
  let W := s.withRowsChurn x.1 x.2
  have hW : AtLastSlotOfEpoch W := hs
  -- Move the eth1 reset after the middle steps.
  have hcomm := eth1_comm (lighthouseDepositsConsolidationsPayments o s tab plan) W (fun t h =>
    (lighthouseDepositsConsolidationsPayments_slotKeep o s tab plan W t h).1)
    (lighthouseDepositsConsolidationsPayments_votesBlind o s tab plan W)
  have hspec : SameResultOrBothFail
      (process_eth1_data_reset P W >>= fun s1 =>
        lighthouseDepositsConsolidationsPayments o s tab plan s1 >>= epochRest2 o)
      (lighthouseDepositsConsolidationsPayments o s tab plan W >>= fun t =>
        process_eth1_data_reset P t >>=
        epochRest2 o) := by
    rw [← bind_assoc, ← bind_assoc]
    exact sameResultOrBothFail_cont hcomm (epochRest2 o)
  refine SameResultOrBothFail.trans ?_ (SameResultOrBothFail.flip hspec)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun t ht => ?_)
  obtain ⟨h1, h2⟩ := lighthouseDepositsConsolidationsPayments_slotKeep o s tab plan W t ht
  exact lighthouseStepsAfterPayments_sameResultOrBothFail o t
    ⟨by rw [h1]; exact hW.1, by rw [h1]; exact hW.2.1,
    by rw [h2]; exact hW.2.2⟩

/-! ## The whole Lighthouse epoch in the Lighthouse order -/

/-- `lighthouseFullTail` with the steps after the single pass given as `after`. -/
def lighthouseSinglePassThen [CurrentPreset]
    (after : BeaconState → Gwei → LighthouseDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState)
    (s : BeaconState) : SpecM BeaconState := do
  let current_epoch ← get_current_epoch P s
  let total_active_balance ← get_total_active_balance P s
  let rctx ← rewardsContextOf P total_active_balance s
  let (_, per) ← slashingsPreamble P total_active_balance s.slashings
  let plan ← lighthouseDepositPlan s total_active_balance current_epoch
  let (downward, upward) ← hysteresisThresholds P
  let named := validatorsInConsolidations s
  let ctx := lighthouseContextOf s total_active_balance current_epoch rctx per
  let x ← passOverRows (fun churn r => lighthouseValidatorStep P ctx downward upward
      ⟨lighthouseBaseReward total_active_balance r, plan.topups.getD r.index 0,
        decide (r.index ∈ named)⟩
      churn r)
    (s.earliest_exit_epoch, s.exit_balance_to_consume) (rowsOf s)
  after s total_active_balance plan x

theorem lighthouseFullTail_eq_with [CurrentPreset] (o : Oracle) (s : BeaconState) :
    lighthouseFullTail o s = lighthouseSinglePassThen (lighthouseAfterPass o) s := by
  unfold lighthouseFullTail lighthouseFullTailG lighthouseSinglePassThen lighthouseAfterPass
    lighthouseAfterPassG gloasFin
  rfl

theorem lighthouseSinglePassThen_sameResultOrBothFail [CurrentPreset]
    (a1 a2 : BeaconState → Gwei → LighthouseDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState) (s : BeaconState)
    (h : ∀ tab plan x, SameResultOrBothFail (a1 s tab plan x) (a2 s tab plan x)) :
    SameResultOrBothFail (lighthouseSinglePassThen a1 s) (lighthouseSinglePassThen a2 s) := by
  unfold lighthouseSinglePassThen
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun _ _ => ?_
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun _ _ => ?_
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun _ _ => ?_
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun ap _ => ?_
  obtain ⟨_, _⟩ := ap
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun _ _ => ?_
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun du _ => ?_
  obtain ⟨_, _⟩ := du
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun _ _ => ?_
  exact h _ _ _

/-- The Gloas `process_epoch` as Lighthouse runs it, in the Lighthouse order and with the
Lighthouse resets, for any preset (`CurrentPreset`). The genesis epoch takes the same path. -/
def process_epoch_lighthouse [CurrentPreset] (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let s1 ← lighthouseJustificationAndFinalization P s
  lighthouseSinglePassThen (lighthouseStepsAfterSinglePass o) s1

/-- At the last slot of an epoch, when the next slot fits in a `u64` and `historical_summaries`
is below the Lighthouse limit, the Lighthouse order gives the same `ok` results as
`processEpochWithSinglePassAndDeposits`. -/
theorem process_epoch_lighthouse_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid] (o : Oracle) (s : BeaconState) (hs : AtLastSlotOfEpoch s) :
    SameResultOrBothFail (process_epoch_lighthouse o s)
      (processEpochWithSinglePassAndDeposits o s) := by
  unfold process_epoch_lighthouse processEpochWithSinglePassAndDeposits
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun s1 h1 => ?_
  obtain ⟨_, _, _, _, rfl⟩ := process_justification_and_finalization_shape _ _ _
    ((lighthouseJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1)
  rw [lighthouseFullTail_eq_with]
  exact lighthouseSinglePassThen_sameResultOrBothFail _ _ _ fun tab plan x =>
    lighthouseStepsAfterSinglePass_sameResultOrBothFail o _ tab plan x hs

/-! ## Every reachable state -/

/-- `reachable_state_transition_sameResultOrBothFail'` for an epoch function `f` that also needs the
last-slot and next-slot facts. `process_slots` runs `process_epoch` only at the last slot of an
epoch, before the slot of the block, so the next slot fits. -/
theorem reachable_state_transition_sameResultOrBothFail_last [CurrentPreset] [CurrentPreset.Valid] (o : Oracle) (max_blobs_per_block : Epoch → Uint64)
    (GLOAS_FORK_EPOCH : Epoch) (init : BeaconState)
    (hffg : CheckpointsInOrder P init) (hrows : ListLengthsMatch init)
    (hd : ExitToWithdrawableDelay P init) (hx : ExitEpochsAreUint64 init)
    (h0 : AfterEffectiveBalanceUpdates P init)
    (hsupply : ActiveBalanceBounded o max_blobs_per_block GLOAS_FORK_EPOCH init)
    (InputCondition : BeaconState → Prop)
    (hinputCondition : AtEveryEpochInput o max_blobs_per_block GLOAS_FORK_EPOCH init InputCondition)
    (f : BeaconState → SpecM BeaconState)
    (hf : ∀ t, BasicEpochInputInvariants InputCondition t → (t.slot + 1) % P.SLOTS_PER_EPOCH = 0 →
      t.slot + 1 < 2 ^ 64 → SameResultOrBothFail (f t) (process_epoch P o t))
    (s : BeaconState) (hr : ReachableByBlocks o max_blobs_per_block GLOAS_FORK_EPOCH init s)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (hslot64 : signed_block.message.slot < 2 ^ 64) :
    SameResultOrBothFail (state_transition_with o max_blobs_per_block GLOAS_FORK_EPOCH f s signed_block
        validate_result)
      (state_transition P o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
        validate_result) := by
  have hs := reachable_inv o _ _ init hffg hrows hd hx h0 hsupply s hr
  have hslots : SameResultOrBothFail (process_slots P o f s signed_block.message.slot)
      (process_slots P o (process_epoch P o) s
        signed_block.message.slot) := by
    unfold process_slots
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · exact SameResultOrBothFail.refl _
    · have h := loopInv_steps o signed_block.message.slot s.slot hslot64
      refine process_slots_loop_sameResultOrBothFail' _ o _
        (fun t => SlotLoopInvariants s.slot t ∧ ReachableBySlots o s t)
        (fun t => SlotLoopInvariants s.slot t ∧ ∃ t0, ReachableBySlots o s t0 ∧
          process_slot P o t0 = .ok t)
        (fun t => PostEpoch s.slot t ∧ ∃ t0 t1, ReachableBySlots o s t0 ∧
          process_slot P o t0 = .ok t1 ∧
          (t1.slot + 1) % P.SLOTS_PER_EPOCH = 0 ∧
          process_epoch P o t1 = .ok t)
        (fun t => BasicEpochInputInvariants InputCondition t ∧ (t.slot + 1) % P.SLOTS_PER_EPOCH = 0 ∧
          t.slot + 1 < 2 ^ 64) ?_ ?_ ?_ ?_ ?_ f (fun t ⟨hin, hz, hn⟩ => hf t hin hz hn) _ s
        ⟨hs, .refl⟩
      · intro t t' ht hlt hP
        exact ⟨h.1 t t' ht hlt hP.1, t, hP.2, ht⟩
      · intro t t' hlt hz he hM
        obtain ⟨t0, h0', ht0⟩ := hM.2
        exact ⟨h.2.1 t t' hlt hz he hM.1, t0, t, h0', ht0, hz, he⟩
      · intro t hlt hz hM
        obtain ⟨hinv, t0, h0', ht0⟩ := hM
        have hok := h.2.2.1 t hlt hz hinv
        obtain ⟨-, -, -, hx', -, s0, n, hA, hb, -⟩ := hinv
        exact ⟨⟨hok, by simp only [Slot] at *; omega, hb.ebOk hA, hx',
          hinputCondition s t0 t hr h0' ht0 hz⟩, hz, by simp only [Slot] at *; omega⟩
      · intro t hz hQ
        obtain ⟨hpost, t0, t1, h0', ht0, hz1, he⟩ := hQ
        exact ⟨h.2.2.2.1 t hz hpost, .epoch h0' ht0 hz1 he⟩
      · intro t hlt hz hM
        obtain ⟨hinv, t0, h0', ht0⟩ := hM
        exact ⟨h.2.2.2.2 t hlt hz hinv, .skip h0' ht0 hz⟩
  unfold state_transition_with state_transition
  dsimp only
  exact sameResultOrBothFail_bind hslots fun _ _ => SameResultOrBothFail.refl _

/-- The whole Lighthouse epoch in the Lighthouse order: on mainnet, from every reachable state,
`state_transition` with `process_epoch_lighthouse` has the same `ok` results as the spec
`state_transition`. Beyond the hypotheses of `lighthouse_full_epoch_state_transition_sameResultOrBothFail`,
`historical_summaries` is below the Lighthouse limit at each epoch boundary. -/
theorem lighthouse_order_epoch_state_transition_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid] (o : Oracle)
    (max_blobs_per_block : Epoch → Uint64) (GLOAS_FORK_EPOCH : Epoch) (init : BeaconState)
    (hffg : CheckpointsInOrder P init) (hrows : ListLengthsMatch init)
    (hd : ExitToWithdrawableDelay P init) (hx : ExitEpochsAreUint64 init)
    (h0 : AfterEffectiveBalanceUpdates P init) (hpk : PubkeysUnique init)
    (hcr : ConsolidationsInRange init) (hw : WithdrawableEpochsFitUint64 init)
    (hsupply : ActiveBalanceBounded o max_blobs_per_block GLOAS_FORK_EPOCH init)
    (hinputCondition : AtEveryEpochInput o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => BalancesFarFromOverflow t ∧ t.historical_summaries.length <
        LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT))
    (s : BeaconState) (hr : ReachableByBlocks o max_blobs_per_block GLOAS_FORK_EPOCH init s)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (hslot64 : signed_block.message.slot < 2 ^ 64) :
    SameResultOrBothFail (state_transition_with o max_blobs_per_block GLOAS_FORK_EPOCH
        (process_epoch_lighthouse o) s signed_block validate_result)
      (state_transition P o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
        validate_result) := by
  have hecon1 : AtEveryEpochInput o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => (BalancesFarFromOverflow t ∧ t.historical_summaries.length <
        LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT) ∧ PubkeysUnique t ∧ ConsolidationsInRange t) := by
    intro s' t t1 hr' hreach ht hz
    have htail := hreach.tail (reachable_tail o _ _ init hpk hcr s' hr')
    exact ⟨hinputCondition s' t t1 hr' hreach ht hz,
      (SamePubkeys.of_eq (process_slot_frame _ o _ _ ht).1.1).pubkeysUnique htail.1,
      (process_slot_cstep _ o _ _ ht).inRange htail.2⟩
  have hecon2 : AtEveryEpochInput o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => ((BalancesFarFromOverflow t ∧ t.historical_summaries.length <
        LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT) ∧ PubkeysUnique t ∧ ConsolidationsInRange t) ∧
        WithdrawableEpochsFitUint64 t ∧ NoWithdrawableEpochWithoutExit t) := by
    intro s' t t1 hr' hreach ht hz
    have hstart : ExitToWithdrawableDelay P s' ∧ WithdrawableEpochsFitUint64 s' :=
      ⟨(reachable_inv o _ _ init hffg hrows hd hx h0 hsupply s' hr').2.2.1,
        reachable_withdrawableU64 o _ _ init hw s' hr'⟩
    have hwd := hreach.withdrawable hstart
    have hv := (process_slot_frame _ o _ _ ht).1.1
    have h1 := ExitToWithdrawableDelay.of_validators_eq hv hwd.1
    have h2 := WithdrawableEpochsFitUint64.of_validators_eq hv hwd.2
    exact ⟨hecon1 s' t t1 hr' hreach ht hz, h2, withdrawableValid_of h1 h2⟩
  refine reachable_state_transition_sameResultOrBothFail_last o _ _ init hffg hrows hd hx h0 hsupply _ hecon2
    (process_epoch_lighthouse o) ?_ s hr signed_block validate_result hslot64
  intro t ⟨hb, hslot, heb, hexit, ⟨⟨hsup, hroom⟩, _, hcons⟩, _, hvalid⟩ hz hn
  exact SameResultOrBothFail.trans (process_epoch_lighthouse_sameResultOrBothFail o t ⟨hz, hn, hroom⟩)
    (processEpochWithSinglePassAndDeposits_sameResultOrBothFail' o t hb hslot heb hexit hsup hvalid
      hcons)

end EpochProofs.Spec
