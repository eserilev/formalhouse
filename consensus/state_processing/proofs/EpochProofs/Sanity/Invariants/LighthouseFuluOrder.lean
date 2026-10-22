import EpochProofs.Sanity.Invariants.LighthouseFulu
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluCfg
import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Sanity.Invariants.FuluOrder

/-!
# The Lighthouse Fulu epoch in the Lighthouse order

`process_epoch_lh_order_fulu` runs the Fulu steps as `altair.rs` and `single_pass.rs` do:

1. the single pass, the deposits and the consolidations,
2. the Fulu proposer lookahead (inside `process_epoch_single_pass`),
3. the eth1, slashings and randao resets and the historical summaries update, with the checks of
   `tail_updates.rs`,
4. the participation rotation and the sync committee update.

`process_epoch_lh_order_fulu_sameOk` shows that it gives the same `ok` results as
`process_epoch_lh_full_fulu`, at the last slot of an epoch, when the next slot fits in a `u64`
and `historical_summaries` is below the Lighthouse limit (`TailPre`). It is the Gloas proof
without the builder payments and the PTC window, with the Fulu swaps of `FuluOrder.lean`.
-/

namespace EpochProofs.Spec

/-! ## The steps between the single pass and the committee steps -/

/-- The steps of `lhFullTailFulu` from the deposit queue write to the effective balance updates
of the validators that consolidations name. -/
def lhMidFulu [PresetCfg] (o : Oracle) (s : BeaconState) (plan : LhDepositPlan) (s1 : BeaconState) :
    SpecM BeaconState := do
  let s4 ← lhNewValidators o plan (lhQueueWrite s plan s1)
  let s5 ← process_pending_consolidations P s4
  (consolidationIndices s).foldlM ebUpdateAt s5

theorem lhAfterPassFulu_eq [PresetCfg] (o : Oracle) (s : BeaconState) (plan : LhDepositPlan)
    (x : (Epoch × Gwei) × List Row) :
    lhAfterPassG o (epochRest2Fulu o) s plan x =
      (process_eth1_data_reset P (s.withRowsChurn x.1 x.2) >>= fun s1 =>
        lhMidFulu o s plan s1 >>= epochRest2Fulu o) := by
  simp only [lhAfterPassG, lhMidFulu, lhNewValidators, lhQueueWrite, bind_assoc,
    lhApplyPendingDeposit_mainnet]

theorem lhMidFulu_votesBlind (o : Oracle) (s : BeaconState) (plan : LhDepositPlan) :
    VotesBlind (lhMidFulu o s plan) := by
  intro t
  have hq : lhQueueWrite s plan (clearVotes t) = clearVotes (lhQueueWrite s plan t) := rfl
  have h := votesBlind_bind (lhNewValidators_votesBlind o plan)
    (votesBlind_bind consolidations_votesBlind
      (votesBlind_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_votesBlind
        (consolidationIndices s))) (lhQueueWrite s plan t)
  simp only [bind_assoc] at h
  simp only [lhMidFulu, hq, bind_assoc]
  exact h

theorem lhMidFulu_slotKeep (o : Oracle) (s : BeaconState) (plan : LhDepositPlan) :
    SlotKeep (lhMidFulu o s plan) := by
  intro t t' h
  have k := slotKeep_bind (lhNewValidators_slotKeep o plan)
    (slotKeep_bind consolidations_slotKeep
      (slotKeep_foldlM (fun t i => ebUpdateAt t i) ebUpdateAt_slotKeep
        (consolidationIndices s))) (lhQueueWrite s plan t) t'
  simp only [bind_assoc] at k
  simp only [lhMidFulu, bind_assoc] at h
  exact k h

/-! ## The steps after the consolidations in the Lighthouse order -/

/-- The Fulu steps after the consolidations, as Lighthouse runs them. -/
def lhRestOrderFulu [PresetCfg] (o : Oracle) (t : BeaconState) : SpecM BeaconState := do
  let t ← process_proposer_lookahead_fulu P o t
  let t ← lhEth1DataReset t
  let t ← lhSlashingsReset t
  let t ← lhRandaoMixesReset t
  let t ← lhHistoricalSummariesUpdate o t
  let t := process_participation_flag_updates t
  process_sync_committee_updates P o t

theorem runSteps_lhOrderFulu_eq [PresetCfg] [PresetCfg.Ok] (o : Oracle) (T : BeaconState) (hT : TailPre T) :
    runSteps (lhOrderFulu o) T = lhRestOrderFulu o T := by
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
    show @LT.lt Nat _ (T.slot / 32 + 1 + 65536) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hslot
    omega
  have hfit' : ∀ t, SameSH T t → t.slot / P.SLOTS_PER_EPOCH + 1 +
      P.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64 := by
    intro t ht
    rw [ht.1]
    show @LT.lt Nat _ (T.slot / 32 + 1 + 8192) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hslot
    omega
  simp only [runSteps, lhOrderFulu, lhRestOrderFulu, pfStep, bind_pure]
  refine bind_congr_of (SameSH T) (fun v h => kpl T v ⟨rfl, rfl⟩ h) (fun t2 h2 => ?_)
  rw [lhEth1DataReset_eq t2 (by rw [h2.1]; exact hslot) (by rw [h2.1]; exact halign)]
  refine bind_congr_of (SameSH T) (fun v h => ke1 t2 v h2 h) (fun t3 h3 => ?_)
  rw [lhSlashingsReset_eq t3 (hfit' t3 h3)]
  refine bind_congr_of (SameSH T) (fun v h => ksr t3 v h3 h) (fun t4 h4 => ?_)
  rw [lhRandaoMixesReset_eq t4 (hfit t4 h4)]
  refine bind_congr_of (SameSH T) (fun v h => krr t4 v h4 h) (fun t5 h5 => ?_)
  rw [lhHistoricalSummariesUpdate_eq o t5 (by rw [h5.2]; exact hroom)]
  rfl

theorem runSteps_specOrderFulu_eq [PresetCfg] (o : Oracle) (T : BeaconState) :
    runSteps (specOrderFulu o) T =
      (process_eth1_data_reset P T >>= epochRest2Fulu o) := by
  simp only [runSteps, specOrderFulu, pfStep, bind_pure, pure_bind]
  rfl

/-- The Fulu steps after the consolidations: the Lighthouse order with the Lighthouse resets
gives the same `ok` results as the eth1 reset followed by the spec order. -/
theorem lhRestOrderFulu_sameOk [PresetCfg] [PresetCfg.Ok] (o : Oracle) (T : BeaconState) (hT : TailPre T) :
    SameOk (lhRestOrderFulu o T) (process_eth1_data_reset P T >>= epochRest2Fulu o) := by
  have hroom : SlotRoom T := by
    show @LT.lt Nat _ (T.slot / 32 + 65538) (2 ^ 64)
    have : @LT.lt Nat _ (T.slot + 1) (2 ^ 64) := hT.2.1
    omega
  rw [← runSteps_lhOrderFulu_eq o T hT, ← runSteps_specOrderFulu_eq o T]
  exact SameOk.flip (specOrderFulu_lhOrderFulu o T hroom)

/-- The steps after the single pass in the Lighthouse Fulu order. -/
def lhAfterPassOrderFulu (o : Oracle) (s : BeaconState) (_total_active_balance : Gwei)
    (plan : LhDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState :=
  lhMidFulu o s plan (s.withRowsChurn x.1 x.2) >>= lhRestOrderFulu o

theorem lhAfterPassOrderFulu_sameOk [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) (tab : Gwei)
    (plan : LhDepositPlan) (x : (Epoch × Gwei) × List Row) (hs : TailPre s) :
    SameOk (lhAfterPassOrderFulu o s tab plan x) (lhAfterPassG o (epochRest2Fulu o) s plan x) := by
  rw [lhAfterPassFulu_eq]
  let W := s.withRowsChurn x.1 x.2
  have hW : TailPre W := hs
  have hcomm := eth1_comm (lhMidFulu o s plan) W
    (fun t h => (lhMidFulu_slotKeep o s plan W t h).1) (lhMidFulu_votesBlind o s plan W)
  have hspec : SameOk
      (process_eth1_data_reset P W >>= fun s1 =>
        lhMidFulu o s plan s1 >>= epochRest2Fulu o)
      (lhMidFulu o s plan W >>= fun t => process_eth1_data_reset P t >>=
        epochRest2Fulu o) := by
    rw [← bind_assoc, ← bind_assoc]
    exact sameOk_cont hcomm (epochRest2Fulu o)
  refine SameOk.trans ?_ (SameOk.flip hspec)
  refine SameOk.bind (SameOk.refl _) (fun t ht => ?_)
  obtain ⟨h1, h2⟩ := lhMidFulu_slotKeep o s plan W t ht
  exact lhRestOrderFulu_sameOk o t ⟨by rw [h1]; exact hW.1, by rw [h1]; exact hW.2.1,
    by rw [h2]; exact hW.2.2⟩

/-! ## The whole Lighthouse Fulu epoch in the Lighthouse order -/

/-- `lhFullTailFulu` with the steps after the single pass given as `after`. -/
def lhFullTailWithFulu [PresetCfg]
    (after : BeaconState → Gwei → LhDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState)
    (s : BeaconState) : SpecM BeaconState := do
  let current_epoch ← get_current_epoch P s
  let total_active_balance ← get_total_active_balance P s
  let rctx ← rewardsContextOf P total_active_balance s
  let (_, per) ← slashingsPreamble P total_active_balance s.slashings
  let plan ← lhDepositPlan s (fuluTabM total_active_balance) current_epoch
  let (downward, upward) ← hysteresisThresholds P
  let named := consolidationIndices s
  let ctx := lhContextOf s (fuluTabM total_active_balance) current_epoch rctx per
  let x ← passM (fun churn r => lhRowStepFull P ctx downward upward
      ⟨lhBaseReward total_active_balance r, plan.topups.getD r.index 0, decide (r.index ∈ named)⟩
      churn r)
    (s.earliest_exit_epoch, s.exit_balance_to_consume) (rowsOf s)
  after s total_active_balance plan x

theorem lhFullTailFulu_eq_with (o : Oracle) (s : BeaconState) :
    lhFullTailFulu o s =
      lhFullTailWithFulu (fun s _ plan x => lhAfterPassG o (epochRest2Fulu o) s plan x) s := by
  unfold lhFullTailFulu lhFullTailG lhFullTailWithFulu lhAfterPassG
  rfl

theorem lhFullTailWithFulu_sameOk
    (a1 a2 : BeaconState → Gwei → LhDepositPlan → (Epoch × Gwei) × List Row →
      SpecM BeaconState) (s : BeaconState)
    (h : ∀ tab plan x, SameOk (a1 s tab plan x) (a2 s tab plan x)) :
    SameOk (lhFullTailWithFulu a1 s) (lhFullTailWithFulu a2 s) := by
  unfold lhFullTailWithFulu
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

/-- The Fulu `process_epoch` on mainnet as Lighthouse runs it, in the Lighthouse order and with
the Lighthouse resets. The genesis epoch takes the same path. -/
def process_epoch_lh_order_fulu [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let s1 ← lhJustificationAndFinalization P s
  lhFullTailWithFulu (lhAfterPassOrderFulu o) s1

/-- Under `TailPre`, the Lighthouse Fulu order gives the same `ok` results as
`process_epoch_lh_full_fulu`. -/
theorem process_epoch_lh_order_fulu_sameOk (o : Oracle) (s : BeaconState) (hs : TailPre s) :
    SameOk (process_epoch_lh_order_fulu o s) (process_epoch_lh_full_fulu o s) := by
  unfold process_epoch_lh_order_fulu process_epoch_lh_full_fulu
  refine SameOk.bind (SameOk.refl _) fun s1 h1 => ?_
  obtain ⟨_, _, _, _, rfl⟩ := process_justification_and_finalization_shape _ _ _
    ((lhJustificationAndFinalization_sameOk _ _ s1).mp h1)
  rw [lhFullTailFulu_eq_with]
  exact lhFullTailWithFulu_sameOk _ _ _ fun tab plan x =>
    lhAfterPassOrderFulu_sameOk o _ tab plan x hs

/-- The Lighthouse Fulu epoch in the Lighthouse order gives the same `ok` results as the Fulu
`process_epoch` on mainnet, at an epoch boundary state with the invariants that reachable Gloas
states have (`EpochInputOk''`) and `TailPre`. -/
theorem lighthouse_fulu_epoch_sameOk [PresetCfg] [PresetCfg.Ok] [FuluCfg] (o : Oracle) (t : BeaconState)
    (hin : EpochInputOk'' EpochSupply t) (hpre : TailPre t) :
    SameOk (process_epoch_lh_order_fulu o t)
      (process_epoch_fulu P FC o t) := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsupply⟩, _, hcons⟩, _, hvalid⟩ := hin
  exact SameOk.trans (process_epoch_lh_order_fulu_sameOk o t hpre)
    (process_epoch_lh_full_fulu_sameOk' o t hb hslot heb hexit hsupply hvalid hcons)

end EpochProofs.Spec
