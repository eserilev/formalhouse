import EpochProofs.Sanity.Invariants.LighthouseOrderEth1
import EpochProofs.Sanity.Invariants.Capstone
import EpochProofs.Sanity.LighthouseNewValidator

/-!
# The Lighthouse epoch in the Lighthouse order

`process_epoch_lh_full` runs the steps after the single pass in the spec order and calls the spec
functions for the resets and the historical summaries update. `process_epoch_lh_order` runs them
as `altair.rs` and `single_pass.rs` do:

1. the single pass, the deposits, the consolidations and the builder payments,
2. the proposer lookahead and the PTC window (inside `process_epoch_single_pass`),
3. the eth1, slashings and randao resets and the historical summaries update, with the checks of
   `tail_updates.rs` (`LighthouseResets.lean`),
4. the participation rotation and the sync committee update.

`process_epoch_lh_order_sameOk` shows that the two give the same `ok` results, at the last slot
of an epoch, when the next slot fits in a `u64` and `historical_summaries` is below the
Lighthouse limit.
-/

namespace EpochProofs.Spec

/-! ## The steps between the single pass and the committee steps -/

/-- The deposit queue write after the single pass. -/
def lhQueueWrite (s : BeaconState) (plan : LhDepositPlan) (s1 : BeaconState) : BeaconState :=
  { s1 with
    pending_deposits := s.pending_deposits.drop plan.next_deposit_index ++ plan.postponed
    deposit_balance_to_consume := plan.deposit_balance_to_consume }

/-- The new validators and their effective balance updates. A new validator gets the effective
balance of `deposit_balance.rs` (`lhApplyPendingDeposit`). -/
def lhNewValidators (o : Oracle) (plan : LhDepositPlan) (s2 : BeaconState) :
    SpecM BeaconState := do
  let s3 ← plan.new_validator_deposits.foldlM (lhApplyPendingDeposit Preset.mainnet o) s2
  (List.range' s2.validators.length (s3.validators.length - s2.validators.length)).foldlM
    ebUpdateAt s3

/-- The steps of `lhFullTail` from the deposit queue write to the builder payments. -/
def lhMid (o : Oracle) (s : BeaconState) (total_active_balance : Gwei) (plan : LhDepositPlan)
    (s1 : BeaconState) : SpecM BeaconState := do
  let s4 ← lhNewValidators o plan (lhQueueWrite s plan s1)
  let s5 ← process_pending_consolidations Preset.mainnet s4
  let s6 ← (consolidationIndices s).foldlM ebUpdateAt s5
  process_builder_pending_payments Preset.mainnet total_active_balance s6

theorem lhAfterPass_eq (o : Oracle) (s : BeaconState) (total_active_balance : Gwei)
    (plan : LhDepositPlan) (x : (Epoch × Gwei) × List Row) :
    lhAfterPass o s total_active_balance plan x =
      (process_eth1_data_reset Preset.mainnet (s.withRowsChurn x.1 x.2) >>= fun s1 =>
        lhMid o s total_active_balance plan s1 >>= epochRest2 o) := by
  simp only [lhAfterPass, lhMid, lhNewValidators, lhQueueWrite, bind_assoc,
    lhApplyPendingDeposit_mainnet]

theorem lhNewValidators_votesBlind (o : Oracle) (plan : LhDepositPlan) :
    VotesBlind (lhNewValidators o plan) := by
  intro t
  unfold lhNewValidators
  rw [lhApplyPendingDeposit_mainnet]
  have h3 := votesBlind_foldlM (fun t x => apply_pending_deposit Preset.mainnet o t x)
    (apply_votesBlind o) plan.new_validator_deposits t
  simp only at h3
  rw [h3]
  cases plan.new_validator_deposits.foldlM (apply_pending_deposit Preset.mainnet o) t with
  | error e => rfl
  | ok s3 =>
    have h4 := votesBlind_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_votesBlind
      (List.range' t.validators.length (s3.validators.length - t.validators.length)) s3
    simp only at h4
    exact h4

theorem lhNewValidators_slotKeep (o : Oracle) (plan : LhDepositPlan) :
    SlotKeep (lhNewValidators o plan) := by
  intro t t' h
  unfold lhNewValidators at h
  rw [lhApplyPendingDeposit_mainnet] at h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨a1, a2⟩ := slotKeep_foldlM (fun t x => apply_pending_deposit Preset.mainnet o t x)
    (apply_slotKeep o) plan.new_validator_deposits t s3 h3
  obtain ⟨b1, b2⟩ := slotKeep_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_slotKeep _ s3 t' h
  exact ⟨b1.trans a1, b2.trans a2⟩

theorem lhMid_votesBlind (o : Oracle) (s : BeaconState) (tab : Gwei) (plan : LhDepositPlan) :
    VotesBlind (lhMid o s tab plan) := by
  intro t
  have hq : lhQueueWrite s plan (clearVotes t) = clearVotes (lhQueueWrite s plan t) := rfl
  have h := votesBlind_bind (lhNewValidators_votesBlind o plan)
    (votesBlind_bind consolidations_votesBlind
      (votesBlind_bind (votesBlind_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_votesBlind
        (consolidationIndices s)) (payments_votesBlind tab))) (lhQueueWrite s plan t)
  simp only [bind_assoc] at h
  simp only [lhMid, hq, bind_assoc]
  exact h

theorem lhMid_slotKeep (o : Oracle) (s : BeaconState) (tab : Gwei) (plan : LhDepositPlan) :
    SlotKeep (lhMid o s tab plan) := by
  intro t t' h
  have k := slotKeep_bind (lhNewValidators_slotKeep o plan)
    (slotKeep_bind consolidations_slotKeep
      (slotKeep_bind (slotKeep_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_slotKeep
        (consolidationIndices s)) (payments_slotKeep tab))) (lhQueueWrite s plan t) t'
  simp only [bind_assoc] at k
  simp only [lhMid, bind_assoc] at h
  exact k h

/-! ## The steps after the builder payments in the Lighthouse order -/

/-- The steps after the builder payments, as Lighthouse runs them. -/
def lhRestOrder (o : Oracle) (t : BeaconState) : SpecM BeaconState := do
  let t ← process_proposer_lookahead Preset.mainnet o t
  let t ← process_ptc_window Preset.mainnet o t
  let t ← lhEth1DataReset t
  let t ← lhSlashingsReset t
  let t ← lhRandaoMixesReset t
  let t ← lhHistoricalSummariesUpdate o t
  let t := process_participation_flag_updates t
  process_sync_committee_updates Preset.mainnet o t

/-- The conditions of the Lighthouse order at a state: the last slot of an epoch, the next slot
fits in a `u64`, and `historical_summaries` is below the Lighthouse limit. -/
def TailPre (s : BeaconState) : Prop :=
  (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 ∧ s.slot + 1 < 2 ^ 64 ∧
    s.historical_summaries.length < LH_HISTORICAL_ROOTS_LIMIT

/-- A bind whose continuations agree on the results with `Q`. -/
theorem bind_congr_of {α : Type} {x : SpecM α} {k1 k2 : α → SpecM BeaconState} (Q : α → Prop)
    (hx : ∀ v, x = .ok v → Q v) (hk : ∀ v, Q v → k1 v = k2 v) : (x >>= k1) = (x >>= k2) := by
  cases h : x with
  | error e => rfl
  | ok v => exact hk v (hx v h)

/-- The fields that the conditions read: the slot and `historical_summaries`. -/
def SameSH (T t : BeaconState) : Prop :=
  t.slot = T.slot ∧ t.historical_summaries = T.historical_summaries

theorem runSteps_lhOrder_eq (o : Oracle) (T : BeaconState) (hT : TailPre T) :
    runSteps (lhOrder o) T = lhRestOrder o T := by
  obtain ⟨halign, hslot, hroom⟩ := hT
  have kpl : StepKeeps (SameSH T) (process_proposer_lookahead Preset.mainnet o) :=
    keeps_of_shape _ _ _ _ (process_proposer_lookahead_eq o) (fun _ _ h => h)
  have kptc : StepKeeps (SameSH T) (process_ptc_window Preset.mainnet o) :=
    keeps_of_shape _ _ _ _ (process_ptc_window_eq o) (fun _ _ h => h)
  have ke1 : StepKeeps (SameSH T) (process_eth1_data_reset Preset.mainnet) :=
    keeps_of_shape _ _ _ _ eth1_eq (fun b _ h => by cases b <;> exact h)
  have ksr : StepKeeps (SameSH T) (process_slashings_reset Preset.mainnet) :=
    keeps_of_shape _ _ _ _ process_slashings_reset_eq (fun _ _ h => h)
  have krr : StepKeeps (SameSH T) (process_randao_mixes_reset Preset.mainnet) :=
    keeps_of_shape _ _ _ _ process_randao_mixes_reset_eq (fun _ _ h => h)
  have hfit : ∀ t, SameSH T t → t.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 +
      Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 := by
    intro t ht
    rw [ht.1]
    show @LT.lt Nat _ (T.slot / 32 + 1 + 65536) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hslot
    omega
  have hfit' : ∀ t, SameSH T t → t.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 +
      Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64 := by
    intro t ht
    rw [ht.1]
    show @LT.lt Nat _ (T.slot / 32 + 1 + 8192) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hslot
    omega
  simp only [runSteps, lhOrder, lhRestOrder, pfStep, bind_pure]
  refine bind_congr_of (SameSH T) (fun v h => kpl T v ⟨rfl, rfl⟩ h) (fun t1 h1 => ?_)
  refine bind_congr_of (SameSH T) (fun v h => kptc t1 v h1 h) (fun t2 h2 => ?_)
  rw [lhEth1DataReset_eq t2 (by rw [h2.1]; exact hslot) (by rw [h2.1]; exact halign)]
  refine bind_congr_of (SameSH T) (fun v h => ke1 t2 v h2 h) (fun t3 h3 => ?_)
  rw [lhSlashingsReset_eq t3 (hfit' t3 h3)]
  refine bind_congr_of (SameSH T) (fun v h => ksr t3 v h3 h) (fun t4 h4 => ?_)
  rw [lhRandaoMixesReset_eq t4 (hfit t4 h4)]
  refine bind_congr_of (SameSH T) (fun v h => krr t4 v h4 h) (fun t5 h5 => ?_)
  rw [lhHistoricalSummariesUpdate_eq o t5 (by rw [h5.2]; exact hroom)]
  rfl

theorem runSteps_specOrder_eq (o : Oracle) (T : BeaconState) :
    runSteps (specOrder o) T = (process_eth1_data_reset Preset.mainnet T >>= epochRest2 o) := by
  simp only [runSteps, specOrder, pfStep, bind_pure, pure_bind]
  rfl

/-- The steps after the builder payments: the Lighthouse order with the Lighthouse resets gives
the same `ok` results as the eth1 reset followed by the spec order. -/
theorem lhRestOrder_sameOk (o : Oracle) (T : BeaconState) (hT : TailPre T) :
    SameOk (lhRestOrder o T) (process_eth1_data_reset Preset.mainnet T >>= epochRest2 o) := by
  have hroom : SlotRoom T := by
    show @LT.lt Nat _ (T.slot / 32 + 65538) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hT.2.1
    omega
  rw [← runSteps_lhOrder_eq o T hT, ← runSteps_specOrder_eq o T]
  exact SameOk.flip (specOrder_lhOrder o T hroom)

/-- `lhAfterPass` in the Lighthouse order. -/
def lhAfterPassOrder (o : Oracle) (s : BeaconState) (total_active_balance : Gwei)
    (plan : LhDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState :=
  lhMid o s total_active_balance plan (s.withRowsChurn x.1 x.2) >>= lhRestOrder o

theorem lhAfterPassOrder_sameOk (o : Oracle) (s : BeaconState) (tab : Gwei)
    (plan : LhDepositPlan) (x : (Epoch × Gwei) × List Row) (hs : TailPre s) :
    SameOk (lhAfterPassOrder o s tab plan x) (lhAfterPass o s tab plan x) := by
  rw [lhAfterPass_eq]
  let W := s.withRowsChurn x.1 x.2
  have hW : TailPre W := hs
  -- Move the eth1 reset after the middle steps.
  have hcomm := eth1_comm (lhMid o s tab plan) W (fun t h => (lhMid_slotKeep o s tab plan W t h).1)
    (lhMid_votesBlind o s tab plan W)
  have hspec : SameOk
      (process_eth1_data_reset Preset.mainnet W >>= fun s1 =>
        lhMid o s tab plan s1 >>= epochRest2 o)
      (lhMid o s tab plan W >>= fun t => process_eth1_data_reset Preset.mainnet t >>=
        epochRest2 o) := by
    rw [← bind_assoc, ← bind_assoc]
    exact sameOk_cont hcomm (epochRest2 o)
  refine SameOk.trans ?_ (SameOk.flip hspec)
  refine SameOk.bind (SameOk.refl _) (fun t ht => ?_)
  obtain ⟨h1, h2⟩ := lhMid_slotKeep o s tab plan W t ht
  exact lhRestOrder_sameOk o t ⟨by rw [h1]; exact hW.1, by rw [h1]; exact hW.2.1,
    by rw [h2]; exact hW.2.2⟩

/-! ## The whole Lighthouse epoch in the Lighthouse order -/

/-- `lhFullTail` with the steps after the single pass given as `after`. -/
def lhFullTailWith
    (after : BeaconState → Gwei → LhDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState)
    (s : BeaconState) : SpecM BeaconState := do
  let current_epoch ← get_current_epoch Preset.mainnet s
  let total_active_balance ← get_total_active_balance Preset.mainnet s
  let rctx ← rewardsContextOf Preset.mainnet total_active_balance s
  let (_, per) ← slashingsPreamble Preset.mainnet total_active_balance s.slashings
  let plan ← lhDepositPlan s total_active_balance current_epoch
  let (downward, upward) ← hysteresisThresholds Preset.mainnet
  let named := consolidationIndices s
  let ctx := lhContextOf s total_active_balance current_epoch rctx per
  let x ← passM (fun churn r => lhRowStepFull Preset.mainnet ctx downward upward
      ⟨lhBaseReward total_active_balance r, plan.topups.getD r.index 0, decide (r.index ∈ named)⟩
      churn r)
    (s.earliest_exit_epoch, s.exit_balance_to_consume) (rowsOf s)
  after s total_active_balance plan x

theorem lhFullTail_eq_with (o : Oracle) (s : BeaconState) :
    lhFullTail o s = lhFullTailWith (lhAfterPass o) s := by
  unfold lhFullTail lhFullTailWith lhAfterPass
  rfl

theorem lhFullTailWith_sameOk
    (a1 a2 : BeaconState → Gwei → LhDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState) (s : BeaconState)
    (h : ∀ tab plan x, SameOk (a1 s tab plan x) (a2 s tab plan x)) :
    SameOk (lhFullTailWith a1 s) (lhFullTailWith a2 s) := by
  unfold lhFullTailWith
  refine SameOk.bind (SameOk.refl _) fun _ _ => ?_
  refine SameOk.bind (SameOk.refl _) fun _ _ => ?_
  refine SameOk.bind (SameOk.refl _) fun _ _ => ?_
  refine SameOk.bind (SameOk.refl _) fun ap _ => ?_
  obtain ⟨_, _⟩ := ap
  refine SameOk.bind (SameOk.refl _) fun _ _ => ?_
  refine SameOk.bind (SameOk.refl _) fun du _ => ?_
  obtain ⟨_, _⟩ := du
  refine SameOk.bind (SameOk.refl _) fun _ _ => ?_
  exact h _ _ _

/-- The Gloas `process_epoch` on mainnet as Lighthouse runs it, in the Lighthouse order and with
the Lighthouse resets. The genesis epoch takes the same path. -/
def process_epoch_lh_order (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let s1 ← lhJustificationAndFinalization Preset.mainnet s
  lhFullTailWith (lhAfterPassOrder o) s1

/-- At the last slot of an epoch, when the next slot fits in a `u64` and `historical_summaries`
is below the Lighthouse limit, the Lighthouse order gives the same `ok` results as
`process_epoch_lh_full`. -/
theorem process_epoch_lh_order_sameOk (o : Oracle) (s : BeaconState) (hs : TailPre s) :
    SameOk (process_epoch_lh_order o s) (process_epoch_lh_full o s) := by
  unfold process_epoch_lh_order process_epoch_lh_full
  refine SameOk.bind (SameOk.refl _) fun s1 h1 => ?_
  obtain ⟨_, _, _, _, rfl⟩ := process_justification_and_finalization_shape _ _ _
    ((lhJustificationAndFinalization_sameOk _ _ s1).mp h1)
  rw [lhFullTail_eq_with]
  exact lhFullTailWith_sameOk _ _ _ fun tab plan x =>
    lhAfterPassOrder_sameOk o _ tab plan x hs

/-! ## Every reachable state -/

/-- `reachable_state_transition_sameOk'` for an epoch function `f` that also needs the
last-slot and next-slot facts. `process_slots` runs `process_epoch` only at the last slot of an
epoch, before the slot of the block, so the next slot fits. -/
theorem reachable_state_transition_sameOk_last (o : Oracle) (max_blobs_per_block : Epoch → Uint64)
    (GLOAS_FORK_EPOCH : Epoch) (init : BeaconState)
    (hffg : FfgInvariant Preset.mainnet init) (hrows : RowsOk init)
    (hd : ExitDelay Preset.mainnet init) (hx : ExitEpochsU64 init)
    (h0 : AfterEB Preset.mainnet init)
    (hsupply : SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH init)
    (Econ : BeaconState → Prop)
    (hecon : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH init Econ)
    (f : BeaconState → SpecM BeaconState)
    (hf : ∀ t, EpochInputOk Econ t → (t.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 →
      t.slot + 1 < 2 ^ 64 → SameOk (f t) (process_epoch Preset.mainnet o t))
    (s : BeaconState) (hr : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH init s)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (hslot64 : signed_block.message.slot < 2 ^ 64) :
    SameOk (state_transition_with o max_blobs_per_block GLOAS_FORK_EPOCH f s signed_block
        validate_result)
      (state_transition Preset.mainnet o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
        validate_result) := by
  have hs := reachable_inv o _ _ init hffg hrows hd hx h0 hsupply s hr
  have hslots : SameOk (process_slots Preset.mainnet o f s signed_block.message.slot)
      (process_slots Preset.mainnet o (process_epoch Preset.mainnet o) s
        signed_block.message.slot) := by
    unfold process_slots
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · exact SameOk.refl _
    · have h := loopInv_steps o signed_block.message.slot s.slot hslot64
      refine process_slots_loop_sameOk' _ o _
        (fun t => LoopInv s.slot t ∧ SlotReach o s t)
        (fun t => LoopInv s.slot t ∧ ∃ t0, SlotReach o s t0 ∧
          process_slot Preset.mainnet o t0 = .ok t)
        (fun t => PostEpoch s.slot t ∧ ∃ t0 t1, SlotReach o s t0 ∧
          process_slot Preset.mainnet o t0 = .ok t1 ∧
          (t1.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 ∧
          process_epoch Preset.mainnet o t1 = .ok t)
        (fun t => EpochInputOk Econ t ∧ (t.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 ∧
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
          hecon s t0 t hr h0' ht0 hz⟩, hz, by simp only [Slot] at *; omega⟩
      · intro t hz hQ
        obtain ⟨hpost, t0, t1, h0', ht0, hz1, he⟩ := hQ
        exact ⟨h.2.2.2.1 t hz hpost, .epoch h0' ht0 hz1 he⟩
      · intro t hlt hz hM
        obtain ⟨hinv, t0, h0', ht0⟩ := hM
        exact ⟨h.2.2.2.2 t hlt hz hinv, .skip h0' ht0 hz⟩
  unfold state_transition_with state_transition
  dsimp only
  exact sameOk_bind hslots fun _ _ => SameOk.refl _

/-- `historical_summaries` is below the Lighthouse limit. -/
def HistRoom (t : BeaconState) : Prop :=
  t.historical_summaries.length < LH_HISTORICAL_ROOTS_LIMIT

/-- The whole Lighthouse epoch in the Lighthouse order: on mainnet, from every reachable state,
`state_transition` with `process_epoch_lh_order` has the same `ok` results as the spec
`state_transition`. Beyond the hypotheses of `lighthouse_full_epoch_state_transition_sameOk`,
`historical_summaries` is below the Lighthouse limit at each epoch boundary (`HistRoom` in the
economic facts). -/
theorem lighthouse_order_epoch_state_transition_sameOk (o : Oracle)
    (max_blobs_per_block : Epoch → Uint64) (GLOAS_FORK_EPOCH : Epoch) (init : BeaconState)
    (hffg : FfgInvariant Preset.mainnet init) (hrows : RowsOk init)
    (hd : ExitDelay Preset.mainnet init) (hx : ExitEpochsU64 init)
    (h0 : AfterEB Preset.mainnet init) (hpk : PubkeysUnique init)
    (hcr : ConsolidationsInRange init) (hw : WithdrawableU64 init)
    (hsupply : SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH init)
    (hecon : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => EpochSupply t ∧ HistRoom t))
    (s : BeaconState) (hr : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH init s)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (hslot64 : signed_block.message.slot < 2 ^ 64) :
    SameOk (state_transition_with o max_blobs_per_block GLOAS_FORK_EPOCH
        (process_epoch_lh_order o) s signed_block validate_result)
      (state_transition Preset.mainnet o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
        validate_result) := by
  have hecon1 : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => (EpochSupply t ∧ HistRoom t) ∧ PubkeysUnique t ∧ ConsolidationsInRange t) := by
    intro s' t t1 hr' hreach ht hz
    have htail := hreach.tail (reachable_tail o _ _ init hpk hcr s' hr')
    exact ⟨hecon s' t t1 hr' hreach ht hz,
      (PkSame.of_eq (process_slot_frame _ o _ _ ht).1.1).pubkeysUnique htail.1,
      (process_slot_cstep _ o _ _ ht).inRange htail.2⟩
  have hecon2 : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH init
      (fun t => ((EpochSupply t ∧ HistRoom t) ∧ PubkeysUnique t ∧ ConsolidationsInRange t) ∧
        WithdrawableU64 t ∧ WithdrawableValid t) := by
    intro s' t t1 hr' hreach ht hz
    have hstart : ExitDelay Preset.mainnet s' ∧ WithdrawableU64 s' :=
      ⟨(reachable_inv o _ _ init hffg hrows hd hx h0 hsupply s' hr').2.2.1,
        reachable_withdrawableU64 o _ _ init hw s' hr'⟩
    have hwd := hreach.withdrawable hstart
    have hv := (process_slot_frame _ o _ _ ht).1.1
    have h1 := ExitDelay.of_validators_eq hv hwd.1
    have h2 := WithdrawableU64.of_validators_eq hv hwd.2
    exact ⟨hecon1 s' t t1 hr' hreach ht hz, h2, withdrawableValid_of h1 h2⟩
  refine reachable_state_transition_sameOk_last o _ _ init hffg hrows hd hx h0 hsupply _ hecon2
    (process_epoch_lh_order o) ?_ s hr signed_block validate_result hslot64
  intro t ⟨hb, hslot, heb, hexit, ⟨⟨hsup, hroom⟩, _, hcons⟩, _, hvalid⟩ hz hn
  exact SameOk.trans (process_epoch_lh_order_sameOk o t ⟨hz, hn, hroom⟩)
    (process_epoch_lh_full_sameOk' o t hb hslot heb hexit hsup hvalid hcons)

end EpochProofs.Spec
