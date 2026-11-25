import EpochProofs.LighthouseModel.Fulu
import EpochProofs.Spec.CurrentPreset
import EpochProofs.Spec.CurrentFuluConfig
import EpochProofs.LighthouseModel.Order
import EpochProofs.Invariants.FuluOrder

/-!
# The Lighthouse Fulu epoch in the Lighthouse order

`process_epoch_lighthouse_fulu` runs the Fulu steps as `altair.rs` and `single_pass.rs` do:

1. the single pass, the deposits and the consolidations,
2. the Fulu proposer lookahead (inside `process_epoch_single_pass`),
3. the eth1, slashings and randao resets and the historical summaries update, with the checks of
   `tail_updates.rs`,
4. the participation rotation and the sync committee update.

`process_epoch_lighthouse_fulu_sameResultOrBothFail` shows that it gives the same `ok` results as
`processEpochWithSinglePassAndDeposits_fulu`, at the last slot of an epoch, when the next slot fits
in a `u64` and `historical_summaries` is below the Lighthouse limit (`AtLastSlotOfEpoch`). It is
the Gloas proof without the builder payments and the PTC window, with the Fulu swaps of
`FuluOrder.lean`.
-/

namespace EpochProofs.Spec

/-! ## The steps between the single pass and the committee steps -/

/-- The steps of `lighthouseFullTailFulu` from the deposit queue write to the effective balance
updates of the validators that consolidations name. -/
def lighthouseDepositsConsolidationsFulu [CurrentPreset] (o : Oracle) (s : BeaconState)
    (plan : LighthouseDepositPlan) (s1 : BeaconState) :
    SpecM BeaconState := do
  let s4 ← lighthouseNewValidators o plan (lighthouseDepositQueueWrite s plan s1)
  let s5 ← process_pending_consolidations P s4
  (validatorsInConsolidations s).foldlM updateEffectiveBalanceAt s5

theorem lighthouseAfterPassFulu_eq [CurrentPreset] (o : Oracle) (s : BeaconState)
    (plan : LighthouseDepositPlan)
    (x : (Epoch × Gwei) × List Row) :
    lighthouseAfterPassG o (epochRest2Fulu o) s plan x =
      (process_eth1_data_reset P (s.withRowsChurn x.1 x.2) >>= fun s1 =>
        lighthouseDepositsConsolidationsFulu o s plan s1 >>= epochRest2Fulu o) := by
  simp only [lighthouseAfterPassG, lighthouseDepositsConsolidationsFulu, lighthouseNewValidators,
    lighthouseDepositQueueWrite, bind_assoc,
    lighthouseApplyPendingDeposit_mainnet]

theorem lighthouseDepositsConsolidationsFulu_votesBlind [CurrentPreset] (o : Oracle)
    (s : BeaconState) (plan : LighthouseDepositPlan) :
    VotesBlind (lighthouseDepositsConsolidationsFulu o s plan) := by
  intro t
  have hq : lighthouseDepositQueueWrite s plan (clearVotes t) =
    clearVotes (lighthouseDepositQueueWrite s plan t) := rfl
  have h := votesBlind_bind (lighthouseNewValidators_votesBlind o plan)
    (votesBlind_bind consolidations_votesBlind
      (votesBlind_foldlM (fun t i => updateEffectiveBalanceAt t i)
        updateEffectiveBalanceAt_votesBlind
        (validatorsInConsolidations s))) (lighthouseDepositQueueWrite s plan t)
  simp only [bind_assoc] at h
  simp only [lighthouseDepositsConsolidationsFulu, hq, bind_assoc]
  exact h

theorem lighthouseDepositsConsolidationsFulu_slotKeep [CurrentPreset] (o : Oracle) (s : BeaconState)
    (plan : LighthouseDepositPlan) :
    KeepsSlot (lighthouseDepositsConsolidationsFulu o s plan) := by
  intro t t' h
  have k := slotKeep_bind (lighthouseNewValidators_slotKeep o plan)
    (slotKeep_bind consolidations_slotKeep
      (slotKeep_foldlM (fun t i => updateEffectiveBalanceAt t i) updateEffectiveBalanceAt_slotKeep
        (validatorsInConsolidations s))) (lighthouseDepositQueueWrite s plan t) t'
  simp only [bind_assoc] at k
  simp only [lighthouseDepositsConsolidationsFulu, bind_assoc] at h
  exact k h

/-! ## The steps after the consolidations in the Lighthouse order -/

/-- The Fulu steps after the consolidations, as Lighthouse runs them. -/
def lighthouseStepsAfterPaymentsFulu [CurrentPreset] (o : Oracle)
    (t : BeaconState) : SpecM BeaconState := do
  let t ← process_proposer_lookahead_fulu P o t
  let t ← lighthouseEth1DataReset t
  let t ← lighthouseSlashingsReset t
  let t ← lighthouseRandaoMixesReset t
  let t ← lighthouseHistoricalSummariesUpdate o t
  let t := process_participation_flag_updates t
  process_sync_committee_updates P o t

theorem runSteps_lighthouseOrderFulu_eq [CurrentPreset] [CurrentPreset.Valid] (o : Oracle)
    (T : BeaconState) (hT : AtLastSlotOfEpoch T) :
    runSteps (lighthouseOrderFulu o) T = lighthouseStepsAfterPaymentsFulu o T := by
  obtain ⟨halign, hslot, hroom⟩ := hT
  have kpl : StepKeeps (SameSH T) (process_proposer_lookahead_fulu P o) :=
    keeps_of_shape _ _ _ _ (process_proposer_lookahead_fulu_eq o) (fun _ _ h => h)
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
  simp only [runSteps, lighthouseOrderFulu, lighthouseStepsAfterPaymentsFulu, pfStep, bind_pure]
  refine bind_congr_of (SameSH T) (fun v h => kpl T v ⟨rfl, rfl⟩ h) (fun t2 h2 => ?_)
  rw [lighthouseEth1DataReset_eq t2 (by rw [h2.1]; exact hslot) (by rw [h2.1]; exact halign)]
  refine bind_congr_of (SameSH T) (fun v h => ke1 t2 v h2 h) (fun t3 h3 => ?_)
  rw [lighthouseSlashingsReset_eq t3 (hfit' t3 h3)]
  refine bind_congr_of (SameSH T) (fun v h => ksr t3 v h3 h) (fun t4 h4 => ?_)
  rw [lighthouseRandaoMixesReset_eq t4 (hfit t4 h4)]
  refine bind_congr_of (SameSH T) (fun v h => krr t4 v h4 h) (fun t5 h5 => ?_)
  rw [lighthouseHistoricalSummariesUpdate_eq o t5 (by rw [h5.2]; exact hroom)]
  rfl

theorem runSteps_specOrderFulu_eq [CurrentPreset] (o : Oracle) (T : BeaconState) :
    runSteps (specOrderFulu o) T =
      (process_eth1_data_reset P T >>= epochRest2Fulu o) := by
  simp only [runSteps, specOrderFulu, pfStep, bind_pure, pure_bind]
  rfl

/-- The Fulu steps after the consolidations: the Lighthouse order with the Lighthouse resets
gives the same `ok` results as the eth1 reset followed by the spec order. -/
theorem lighthouseStepsAfterPaymentsFulu_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid]
    (o : Oracle) (T : BeaconState) (hT : AtLastSlotOfEpoch T) :
    SameResultOrBothFail (lighthouseStepsAfterPaymentsFulu o T) (process_eth1_data_reset P T >>=
      epochRest2Fulu o) := by
  have hroom : SlotRoom T := P_slot_room hT.2.1
  rw [← runSteps_lighthouseOrderFulu_eq o T hT, ← runSteps_specOrderFulu_eq o T]
  exact SameResultOrBothFail.flip (specOrderFulu_lighthouseOrderFulu o T hroom)

/-- The steps after the single pass in the Lighthouse Fulu order. -/
def lighthouseStepsAfterSinglePassFulu [CurrentPreset] (o : Oracle) (s : BeaconState)
    (_total_active_balance : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState :=
  lighthouseDepositsConsolidationsFulu o s plan (s.withRowsChurn x.1 x.2) >>=
    lighthouseStepsAfterPaymentsFulu o

theorem lighthouseStepsAfterSinglePassFulu_sameResultOrBothFail [CurrentPreset]
    [CurrentPreset.Valid] (o : Oracle) (s : BeaconState) (tab : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) (hs : AtLastSlotOfEpoch s) :
    SameResultOrBothFail (lighthouseStepsAfterSinglePassFulu o s tab plan x)
      (lighthouseAfterPassG o (epochRest2Fulu o) s plan x) := by
  rw [lighthouseAfterPassFulu_eq]
  let W := s.withRowsChurn x.1 x.2
  have hW : AtLastSlotOfEpoch W := hs
  have hcomm := eth1_comm (lighthouseDepositsConsolidationsFulu o s plan) W
    (fun t h => (lighthouseDepositsConsolidationsFulu_slotKeep o s plan W t h).1)
      (lighthouseDepositsConsolidationsFulu_votesBlind o s plan W)
  have hspec : SameResultOrBothFail
      (process_eth1_data_reset P W >>= fun s1 =>
        lighthouseDepositsConsolidationsFulu o s plan s1 >>= epochRest2Fulu o)
      (lighthouseDepositsConsolidationsFulu o s plan W >>= fun t => process_eth1_data_reset P t >>=
        epochRest2Fulu o) := by
    rw [← bind_assoc, ← bind_assoc]
    exact sameResultOrBothFail_cont hcomm (epochRest2Fulu o)
  refine SameResultOrBothFail.trans ?_ (SameResultOrBothFail.flip hspec)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun t ht => ?_)
  obtain ⟨h1, h2⟩ := lighthouseDepositsConsolidationsFulu_slotKeep o s plan W t ht
  exact lighthouseStepsAfterPaymentsFulu_sameResultOrBothFail o t
    ⟨by rw [h1]; exact hW.1, by rw [h1]; exact hW.2.1,
    by rw [h2]; exact hW.2.2⟩

/-! ## The whole Lighthouse Fulu epoch in the Lighthouse order -/

/-- `lighthouseFullTailFulu` with the steps after the single pass given as `after`. -/
def lighthouseSinglePassThenFulu [CurrentPreset] [CurrentFuluConfig]
    (after : BeaconState → Gwei → LighthouseDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState)
    (s : BeaconState) : SpecM BeaconState := do
  let current_epoch ← get_current_epoch P s
  let total_active_balance ← get_total_active_balance P s
  let rctx ← rewardsContextOf P total_active_balance s
  let (_, per) ← slashingsPreamble P total_active_balance s.slashings
  let plan ← lighthouseDepositPlan s (fuluChurnTotal total_active_balance) current_epoch
  let (downward, upward) ← hysteresisThresholds P
  let named := validatorsInConsolidations s
  let ctx := lighthouseContextOf s (fuluChurnTotal total_active_balance) current_epoch rctx per
  let x ← passM (fun churn r => lighthouseValidatorStep P ctx downward upward
      ⟨lighthouseBaseReward total_active_balance r, plan.topups.getD r.index 0,
        decide (r.index ∈ named)⟩
      churn r)
    (s.earliest_exit_epoch, s.exit_balance_to_consume) (rowsOf s)
  after s total_active_balance plan x

theorem lighthouseFullTailFulu_eq_with [CurrentPreset] [CurrentFuluConfig] (o : Oracle)
    (s : BeaconState) :
    lighthouseFullTailFulu o s =
      lighthouseSinglePassThenFulu (fun s _ plan x =>
        lighthouseAfterPassG o (epochRest2Fulu o) s plan x) s := by
  unfold lighthouseFullTailFulu lighthouseFullTailG lighthouseSinglePassThenFulu
    lighthouseAfterPassG
  rfl

theorem lighthouseSinglePassThenFulu_sameResultOrBothFail [CurrentPreset] [CurrentFuluConfig]
    (a1 a2 : BeaconState → Gwei → LighthouseDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState) (s : BeaconState)
    (h : ∀ tab plan x, SameResultOrBothFail (a1 s tab plan x) (a2 s tab plan x)) :
    SameResultOrBothFail (lighthouseSinglePassThenFulu a1 s)
      (lighthouseSinglePassThenFulu a2 s) := by
  unfold lighthouseSinglePassThenFulu
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

/-- The Fulu `process_epoch` as Lighthouse runs it, in the Lighthouse order and with the
Lighthouse resets, for any preset (`CurrentPreset`). The genesis epoch takes the same path. -/
def process_epoch_lighthouse_fulu [CurrentPreset] [CurrentFuluConfig] (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let s1 ← lighthouseJustificationAndFinalization P s
  lighthouseSinglePassThenFulu (lighthouseStepsAfterSinglePassFulu o) s1

/-- Under `AtLastSlotOfEpoch`, the Lighthouse Fulu order gives the same `ok` results as
`processEpochWithSinglePassAndDeposits_fulu`. -/
theorem process_epoch_lighthouse_fulu_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid] [CurrentFuluConfig] (o : Oracle) (s : BeaconState) (hs : AtLastSlotOfEpoch s) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu o s)
      (processEpochWithSinglePassAndDeposits_fulu o s) := by
  unfold process_epoch_lighthouse_fulu processEpochWithSinglePassAndDeposits_fulu
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) fun s1 h1 => ?_
  obtain ⟨_, _, _, _, rfl⟩ := process_justification_and_finalization_shape _ _ _
    ((lighthouseJustificationAndFinalization_sameResultOrBothFail _ _ s1).mp h1)
  rw [lighthouseFullTailFulu_eq_with]
  exact lighthouseSinglePassThenFulu_sameResultOrBothFail _ _ _ fun tab plan x =>
    lighthouseStepsAfterSinglePassFulu_sameResultOrBothFail o _ tab plan x hs

/-- The Lighthouse Fulu epoch in the Lighthouse order gives the same `ok` results as the Fulu
`process_epoch` on mainnet, at an epoch boundary state with the invariants that reachable Gloas
states have (`EpochInputInvariantsFor`) and `AtLastSlotOfEpoch`. -/
theorem lighthouse_fulu_epoch_sameResultOrBothFail [CurrentPreset] [CurrentPreset.Valid] [CurrentFuluConfig] [CurrentFuluConfig.Valid] (o : Oracle) (t : BeaconState)
    (hin : EpochInputInvariants t) (hpre : AtLastSlotOfEpoch t) :
    SameResultOrBothFail (process_epoch_lighthouse_fulu o t)
      (process_epoch_fulu P FC o t) := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsupply⟩, _, hcons⟩, _, hvalid⟩ := hin
  exact SameResultOrBothFail.trans (process_epoch_lighthouse_fulu_sameResultOrBothFail o t hpre)
    (processEpochWithSinglePassAndDeposits_fulu_sameResultOrBothFail' o t hb hslot heb hexit hsupply
      hvalid hcons)

end EpochProofs.Spec
