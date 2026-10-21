import EpochProofs.Etheorem.BuilderPendingPayments
import EpochProofs.Etheorem.Resets
import EpochProofs.Etheorem.EffectiveBalance
import EpochProofs.Etheorem.HistoricalSummaries
import EpochProofs.Etheorem.Committees
import EpochProofs.Etheorem.Justification
import EpochProofs.Etheorem.Inactivity
import EpochProofs.Etheorem.Rewards
import EpochProofs.Etheorem.Slashings
import EpochProofs.Etheorem.Registry
import EpochProofs.Etheorem.Deposits
import EpochProofs.Etheorem.Consolidations
import EthCLSpecs.Gloas.Transition
import EpochProofs.Sanity.Invariants.Capstone

/-!
# The whole epoch equals Etheorem

`process_epoch_etheorem`: if the reference `process_epoch` returns `s'`, Etheorem's Gloas
`processEpoch` succeeds and `absEState` of its result is `s'`.

Both specs run the same 17 steps in the same order. `epochSteps` lists Etheorem's steps, and
`processEpoch_eq` shows that `processEpoch` runs them in sequence. The proof runs one step
theorem after the other.

Each step theorem has its own conditions. `EtheoremEpochConds e` collects them. A condition
on a later step reads the Etheorem state right before that step: `Before k e e'` says that
Etheorem runs the first `k` steps from `e` and reaches `e'`. Most conditions are facts about
the state. Three are facts about Etheorem's own output: its balance weighted selections
return `size` items (F3).
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Preset

/-- All the preset facts the 17 steps read. -/
structure EpochPresetAgrees [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]
    (p : Spec.Preset) : Prop where
  base : PresetAgrees p
  tail : TailPresetAgrees p
  passes : PassesPresetAgrees p
  queues : QueuesPresetAgrees p
  committee : CommitteePresetAgrees p
  slotsPerEpochSix : 6 ≤ p.SLOTS_PER_EPOCH
  epochsPerSyncCommitteePeriodLt : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
theorem epochPresetAgrees_mainnet : EpochPresetAgrees Spec.Preset.mainnet :=
  ⟨presetAgrees_mainnet, tailPresetAgrees_mainnet, passesPresetAgrees_mainnet,
    queuesPresetAgrees_mainnet, committeePresetAgrees_mainnet, by decide, by decide⟩
end

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
theorem epochPresetAgrees_minimal : EpochPresetAgrees Spec.Preset.minimal :=
  ⟨presetAgrees_minimal, tailPresetAgrees_minimal, passesPresetAgrees_minimal,
    queuesPresetAgrees_minimal, committeePresetAgrees_minimal, by decide, by decide⟩
end

end Preset

section Main

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

/-! ## Running steps in sequence -/

/-- Etheorem runs the steps `l` in order from `e` and reaches `e'`. Each step starts and ends on
the uncached box. -/
inductive StepsOk : List (GloasRun Unit) → EState → EState → Prop
  | nil (e : EState) : StepsOk [] e e
  | cons {a : GloasRun Unit} {l : List (GloasRun Unit)} {e e1 e2 : EState} :
      a.run (pureState e) = .ok ((), pureState e1) → StepsOk l e1 e2 → StepsOk (a :: l) e e2

theorem StepsOk.snoc {l : List (GloasRun Unit)} {a : GloasRun Unit} {e e1 e2 : EState}
    (h : StepsOk l e e1) (ha : a.run (pureState e1) = .ok ((), pureState e2)) :
    StepsOk (l ++ [a]) e e2 := by
  induction h with
  | nil e => exact .cons ha (.nil _)
  | cons hr _ ih => exact .cons hr (ih ha)

/-- The steps `l` in sequence. -/
def seqSteps : List (GloasRun Unit) → GloasRun Unit
  | [] => pure ()
  | [a] => a
  | a :: b :: l => a >>= fun _ => seqSteps (b :: l)

theorem StepsOk.run_seq {l : List (GloasRun Unit)} {e e' : EState} (h : StepsOk l e e') :
    (seqSteps l).run (pureState e) = .ok ((), pureState e') := by
  induction h with
  | nil e => rfl
  | @cons a l e e1 e2 hr hl ih =>
    cases l with
    | nil => cases hl; exact hr
    | cons b l => rw [seqSteps, run_bind, hr, except_bind_ok]; exact ih

variable [EthCLSpecs.Gloas.Config] [CryptoBackend]

/-- Etheorem's 17 epoch steps, in `processEpoch` order. -/
def epochSteps : List (GloasRun Unit) :=
  [EthCLSpecs.Gloas.processJustificationAndFinalization,
   EthCLSpecs.Gloas.processInactivityUpdates,
   EthCLSpecs.Gloas.processRewardsAndPenalties,
   EthCLSpecs.Gloas.processRegistryUpdates,
   EthCLSpecs.Gloas.processSlashings,
   EthCLSpecs.Gloas.processEth1DataReset,
   EthCLSpecs.Gloas.processPendingDeposits,
   EthCLSpecs.Gloas.processPendingConsolidations,
   EthCLSpecs.Gloas.processBuilderPendingPayments,
   EthCLSpecs.Gloas.processEffectiveBalanceUpdates,
   EthCLSpecs.Gloas.processSlashingsReset,
   EthCLSpecs.Gloas.processRandaoMixesReset,
   EthCLSpecs.Gloas.processHistoricalSummariesUpdate,
   EthCLSpecs.Gloas.processParticipationFlagUpdates,
   EthCLSpecs.Gloas.processSyncCommitteeUpdates,
   EthCLSpecs.Gloas.processProposerLookahead,
   EthCLSpecs.Gloas.processPtcWindow]

theorem processEpoch_eq :
    (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)) = seqSteps epochSteps := rfl

/-- Etheorem runs the first `k` epoch steps from `e` and reaches `e'`. -/
def Before (k : Nat) (e e' : EState) : Prop := StepsOk (epochSteps.take k) e e'

/-! ## The conditions -/

/-- The conditions of the 17 step theorems, for an epoch that starts at `e`.

State facts:
- `finalized`: the finalized epoch is below `FAR_FUTURE_EPOCH` before the registry update.
- `depositLens`, `depositRoom`, `depositBridge`: before the pending deposits, the registry
  lists have the same length, each pending deposit has room for a new validator, and every
  pending deposit is at slot 0 or `deposit_requests_start_index ≤ eth1_deposit_index` (F2).
- `consolidationLens`: one balance for each validator before the pending consolidations.
- `builderRoom`: the new builder withdrawals fit under Etheorem's list limit (F6).
- `summariesRoom`: the historical summaries list has room for one more item (F6).

Facts about Etheorem's output (F3):
- `syncFull`, `proposersFull`, `ptcFull`: each balance weighted selection returns `size`
  items. -/
structure EtheoremEpochConds (e : EState) : Prop where
  finalized : ∀ e', Before 3 e e' →
    (absEState e').finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH
  depositLens : ∀ e', Before 6 e e' → LensEq e'
  depositRoom : ∀ e', Before 6 e e' → e'.validators.val.size + e'.pendingDeposits.val.size ≤
    EthCLSpecs.Gloas.Const.validatorRegistryLimit
  depositBridge : ∀ e', Before 6 e e' → ∀ d ∈ e'.pendingDeposits.val.toList,
    d.slot = 0 ∨ e'.depositRequestsStartIndex ≤ e'.eth1DepositIndex
  consolidationLens : ∀ e', Before 7 e e' → e'.balances.val.size = e'.validators.val.size
  builderRoom : ∀ e', Before 8 e e' →
    e'.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e').length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit
  summariesRoom : ∀ e', Before 12 e e' →
    e'.historicalSummaries.val.size < EthCLSpecs.Gloas.Const.historicalRootsLimit
  syncFull : ∀ e', Before 14 e e' → SyncSelectionFull e'
  proposersFull : ∀ e', Before 15 e e' → ProposerSelectionsFull e'
    (EthCLSpecs.Gloas.currentEpochOf (pureState e') + EthCLSpecs.Gloas.Const.minSeedLookahead + 1)
  ptcFull : ∀ e', Before 16 e e' → PtcSelectionsFull e'

/-! ## The builder payment step in the form of the other steps -/

omit [CryptoBackend] in
theorem builder_pending_payments_etheorem' {p : Spec.Preset} (hp : PresetAgrees p)
    (hslots6 : 6 ≤ p.SLOTS_PER_EPOCH) (e : EState)
    (hfits : e.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e).length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit)
    {s' : Spec.BeaconState}
    (h : Spec.process_builder_pending_payments p (etheoremTotalActiveBalance e) (absEState e) =
      .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processBuilderPendingPayments (StateTransition := GloasRun)).run
        (pureState e) = .ok ((), pureState e') ∧ absEState e' = s' := by
  obtain ⟨e', s'', hrun, hspec, ⟨hpay, hwd⟩, he', hs''⟩ :=
    builder_pending_payments_etheorem p hp.slotsPerEpoch hslots6 e (absEState e) ⟨rfl, rfl⟩ hfits
  have hbox := processBuilderPendingPayments_run e
  have hX := runPure_of_run_ok hbox
  rw [hX] at hrun
  cases hrun
  refine ⟨_, hbox, ?_⟩
  have : s' = s'' := by
    have h2 : Spec.process_builder_pending_payments p (totalActiveBalance e) (absEState e) =
      .ok s' := h
    rw [h2] at hspec; cases hspec; rfl
  subst this
  rw [hs'', absEState_set_builderPayments, ← hpay, ← hwd]

/-! ## The whole epoch -/

variable {p : Spec.Preset} (hp : EpochPresetAgrees p)
include hp

/-- The reference `process_epoch` equals Etheorem's Gloas `processEpoch`.

If the reference returns `s'`, Etheorem's run succeeds and `absEState` of its result is `s'`.
`ho`: the oracle fields equal Etheorem's functions. `hsha`: `sha` returns 32 bytes
(`sha_size_pure` proves it for the pure SHA-256). `hc`: the step conditions. -/
theorem process_epoch_etheorem (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (hc : EtheoremEpochConds e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  have hpp := hp.passes
  have hb := hp.base
  unfold Spec.process_epoch at h
  -- 1. justification and finalization
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e1, r1, rfl⟩ := justification_etheorem hpp e h1
  have b1 : StepsOk (epochSteps.take 1) e e1 := .cons r1 (.nil _)
  -- 2. inactivity
  obtain ⟨s2, h2, h⟩ := Spec.specM_bind_ok h
  obtain ⟨r2, rfl⟩ := inactivity_updates_etheorem hpp e1 h2
  have b2 : StepsOk (epochSteps.take 2) e (inactivityUpdatesE e1) := b1.snoc r2
  generalize inactivityUpdatesE e1 = e2 at *
  -- 3. rewards and penalties
  obtain ⟨t3, ht3, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e2 ht3
  subst this
  obtain ⟨s3, h3, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e3, r3, rfl⟩ := rewards_etheorem hpp e2 h3
  have b3 : StepsOk (epochSteps.take 3) e e3 := b2.snoc r3
  -- 4. registry updates
  obtain ⟨t4, ht4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e4, r4, rfl⟩ :=
    process_registry_updates_etheorem hb hp.queues e3 ht4 (hc.finalized e3 b3) h4
  have b4 : StepsOk (epochSteps.take 4) e e4 := b3.snoc r4
  -- 5. slashings
  obtain ⟨t5, ht5, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e4 ht5
  subst this
  obtain ⟨s5, h5, h⟩ := Spec.specM_bind_ok h
  obtain ⟨r5, rfl⟩ := slashings_etheorem hpp e4 h5
  have b5 : StepsOk (epochSteps.take 5) e (slashingsE e4) := b4.snoc r5
  generalize slashingsE e4 = e5 at *
  -- 6. eth1 data reset
  obtain ⟨s6, h6, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e6, r6, rfl⟩ := eth1_data_reset_etheorem hb hp.tail e5 h6
  have b6 : StepsOk (epochSteps.take 6) e e6 := b5.snoc r6
  -- 7. pending deposits
  obtain ⟨t7, ht7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e7, r7, rfl⟩ := process_pending_deposits_etheorem hb hp.queues o ho e6 ht7
    (hc.depositLens e6 b6) (hc.depositRoom e6 b6) (hc.depositBridge e6 b6) h7
  have b7 : StepsOk (epochSteps.take 7) e e7 := b6.snoc r7
  -- 8. pending consolidations
  obtain ⟨s8, h8, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e8, r8, rfl⟩ :=
    process_pending_consolidations_etheorem hb e7 (hc.consolidationLens e7 b7) h8
  have b8 : StepsOk (epochSteps.take 8) e e8 := b7.snoc r8
  -- 9. builder pending payments
  obtain ⟨t9, ht9, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e8 ht9
  subst this
  obtain ⟨s9, h9, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e9, r9, rfl⟩ :=
    builder_pending_payments_etheorem' hb hp.slotsPerEpochSix e8 (hc.builderRoom e8 b8) h9
  have b9 : StepsOk (epochSteps.take 9) e e9 := b8.snoc r9
  -- 10. effective balance updates
  obtain ⟨s10, h10, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e10, r10, rfl⟩ := effective_balance_updates_etheorem hb hp.tail e9 h10
  have b10 : StepsOk (epochSteps.take 10) e e10 := b9.snoc r10
  -- 11. slashings reset
  obtain ⟨s11, h11, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e11, r11, rfl⟩ := slashings_reset_etheorem hb hp.tail e10 h11
  have b11 : StepsOk (epochSteps.take 11) e e11 := b10.snoc r11
  -- 12. randao mixes reset
  obtain ⟨s12, h12, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e12, r12, rfl⟩ := randao_mixes_reset_etheorem hb e11 h12
  have b12 : StepsOk (epochSteps.take 12) e e12 := b11.snoc r12
  -- 13. historical summaries
  obtain ⟨s13, h13, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e13, r13, rfl⟩ :=
    historical_summaries_update_etheorem hb hp.tail ho e12 (hc.summariesRoom e12 b12) h13
  have b13 : StepsOk (epochSteps.take 13) e e13 := b12.snoc r13
  -- 14. participation flags
  obtain ⟨e14, r14, h14⟩ := participation_flag_updates_etheorem e13
  have b14 : StepsOk (epochSteps.take 14) e e14 := b13.snoc r14
  rw [← h14] at h
  -- 15. sync committees
  obtain ⟨s15, h15, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e15, r15, rfl⟩ := process_sync_committee_updates_etheorem hb hp.committee o ho
    hp.epochsPerSyncCommitteePeriodLt e14 (hc.syncFull e14 b14) h15
  have b15 : StepsOk (epochSteps.take 15) e e15 := b14.snoc r15
  -- 16. proposer lookahead
  obtain ⟨s16, h16, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e16, r16, rfl⟩ := process_proposer_lookahead_etheorem hb hp.committee o ho.hash hsha
    e15 (hc.proposersFull e15 b15) h16
  have b16 : StepsOk (epochSteps.take 16) e e16 := b15.snoc r16
  -- 17. PTC window
  obtain ⟨e17, r17, rfl⟩ := process_ptc_window_etheorem hb hp.committee o ho.hash hsha e16
    (hc.ptcFull e16 b16) h
  have b17 : StepsOk epochSteps e e17 := b16.snoc r17
  exact ⟨e17, by rw [processEpoch_eq]; exact b17.run_seq, rfl⟩

end Main

/-! ## Lighthouse equals Etheorem -/

section Lighthouse

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- Lighthouse's epoch processing equals Etheorem's Gloas `processEpoch` on mainnet.

`process_epoch_lh_full` is the model of the whole Lighthouse epoch: the single pass from the
Aeneas translation, then the Lighthouse order of deposits, consolidations and effective
balances. If it returns `s'`, Etheorem's run succeeds and `absEState` of its result is `s'`.

`hin` is the condition that `reachable_state_transition_sameOk'''` proves at each epoch
boundary of a reachable state. `hc` holds the conditions of the Etheorem steps. -/
theorem lighthouse_epoch_etheorem (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e)) (hc : EtheoremEpochConds e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_full o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, _, hcons⟩, _, hvalid⟩ := hin
  have hsame := Spec.process_epoch_lh_full_sameOk' o (absEState e) hb hslot heb hexit hsup hvalid
    hcons
  exact process_epoch_etheorem epochPresetAgrees_mainnet o ho hsha e hc ((hsame s').mp h)

end Lighthouse

end EpochProofs.Etheorem
