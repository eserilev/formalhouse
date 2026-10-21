import EpochProofs.Etheorem.Fulu.Resets
import EpochProofs.Etheorem.Fulu.EffectiveBalance
import EpochProofs.Etheorem.Fulu.HistoricalSummaries
import EpochProofs.Etheorem.Fulu.Committees
import EpochProofs.Etheorem.Fulu.Justification
import EpochProofs.Etheorem.Fulu.Inactivity
import EpochProofs.Etheorem.Fulu.Rewards
import EpochProofs.Etheorem.Fulu.Slashings
import EpochProofs.Etheorem.Fulu.Registry
import EpochProofs.Etheorem.Fulu.Deposits
import EpochProofs.Etheorem.Fulu.Consolidations
import EthCLSpecs.Fulu.Transition

/-!
# The whole Fulu epoch equals Etheorem

`process_epoch_fulu_etheorem`: if the reference Fulu `process_epoch` returns `s'`, Etheorem's
Fulu `processEpoch` succeeds and `absEState` of its result is `s'`.

Both specs run the same 15 steps in the same order. `epochSteps` lists Etheorem's steps, and
`processEpoch_eq` shows that `processEpoch` runs them in sequence. The reference registry update
and pending deposits are the Gloas functions at `fuluTab` (`process_epoch_fulu_eq_tab`), so the
proof runs the Fulu copies of the Gloas step theorems, one after the other.

Each step theorem has its own conditions. `FuluEpochConds p o e` collects them. A condition on a
later step reads the Etheorem state right before that step: `Before k e e'` says that Etheorem
runs the first `k` steps from `e` and reaches `e'`.
-/

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu

section Preset

/-- All the preset and config facts the 15 Fulu steps read. -/
structure EpochPresetAgrees [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config]
    (p : Spec.Preset) (f : Spec.FuluConfig) : Prop where
  base : PresetAgrees p
  churn : FuluChurnAgrees p f
  tail : TailPresetAgrees p
  passes : PassesPresetAgrees p
  queues : QueuesPresetAgrees p
  committee : CommitteePresetAgrees p
  epochsPerSyncCommitteePeriodLt : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64
  syncCommitteeSizePos : 0 < p.SYNC_COMMITTEE_SIZE

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
theorem epochPresetAgrees_mainnet :
    EpochPresetAgrees Spec.Preset.mainnet Spec.FuluConfig.mainnet :=
  ⟨presetAgrees_mainnet, fuluChurnAgrees_mainnet, tailPresetAgrees_mainnet,
    passesPresetAgrees_mainnet, queuesPresetAgrees_mainnet, committeePresetAgrees_mainnet,
    by decide, by decide⟩
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
theorem epochPresetAgrees_minimal :
    EpochPresetAgrees Spec.Preset.minimal Spec.FuluConfig.minimal :=
  ⟨presetAgrees_minimal, fuluChurnAgrees_minimal, tailPresetAgrees_minimal,
    passesPresetAgrees_minimal, queuesPresetAgrees_minimal, committeePresetAgrees_minimal,
    by decide, by decide⟩
end

end Preset

section Main

variable [EthCLSpecs.Fulu.Preset] [HasherTag]

/-! ## Running steps in sequence -/

/-- Etheorem runs the steps `l` in order from `e` and reaches `e'`. Each step starts and ends on
the uncached box. -/
inductive StepsOk : List (FuluRun Unit) → EState → EState → Prop
  | nil (e : EState) : StepsOk [] e e
  | cons {a : FuluRun Unit} {l : List (FuluRun Unit)} {e e1 e2 : EState} :
      a.run (pureState e) = .ok ((), pureState e1) → StepsOk l e1 e2 → StepsOk (a :: l) e e2

theorem StepsOk.snoc {l : List (FuluRun Unit)} {a : FuluRun Unit} {e e1 e2 : EState}
    (h : StepsOk l e e1) (ha : a.run (pureState e1) = .ok ((), pureState e2)) :
    StepsOk (l ++ [a]) e e2 := by
  induction h with
  | nil e => exact .cons ha (.nil _)
  | cons hr _ ih => exact .cons hr (ih ha)

/-- The steps `l` in sequence. -/
def seqSteps : List (FuluRun Unit) → FuluRun Unit
  | [] => pure ()
  | [a] => a
  | a :: b :: l => a >>= fun _ => seqSteps (b :: l)

theorem StepsOk.run_seq {l : List (FuluRun Unit)} {e e' : EState} (h : StepsOk l e e') :
    (seqSteps l).run (pureState e) = .ok ((), pureState e') := by
  induction h with
  | nil e => rfl
  | @cons a l e e1 e2 hr hl ih =>
    cases l with
    | nil => cases hl; exact hr
    | cons b l => rw [seqSteps, run_bind, hr, except_bind_ok]; exact ih

variable [EthCLSpecs.Fulu.Config] [CryptoBackend]

/-- Etheorem's 15 Fulu epoch steps, in `processEpoch` order. -/
def epochSteps : List (FuluRun Unit) :=
  [EthCLSpecs.Fulu.processJustificationAndFinalization,
   EthCLSpecs.Fulu.processInactivityUpdates,
   EthCLSpecs.Fulu.processRewardsAndPenalties,
   EthCLSpecs.Fulu.processRegistryUpdates,
   EthCLSpecs.Fulu.processSlashings,
   EthCLSpecs.Fulu.processEth1DataReset,
   EthCLSpecs.Fulu.processPendingDeposits,
   EthCLSpecs.Fulu.processPendingConsolidations,
   EthCLSpecs.Fulu.processEffectiveBalanceUpdates,
   EthCLSpecs.Fulu.processSlashingsReset,
   EthCLSpecs.Fulu.processRandaoMixesReset,
   EthCLSpecs.Fulu.processHistoricalSummariesUpdate,
   EthCLSpecs.Fulu.processParticipationFlagUpdates,
   EthCLSpecs.Fulu.processSyncCommitteeUpdates,
   EthCLSpecs.Fulu.processProposerLookahead]

theorem processEpoch_eq :
    (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)) = seqSteps epochSteps := rfl

/-- Etheorem runs the first `k` epoch steps from `e` and reaches `e'`. -/
def Before (k : Nat) (e e' : EState) : Prop := StepsOk (epochSteps.take k) e e'

/-! ## The conditions -/

/-- The conditions of the 15 Fulu step theorems, for an epoch that starts at `e`.

State facts:
- `finalized`: the finalized epoch is below `FAR_FUTURE_EPOCH` before the registry update.
- `depositLens`, `depositRoom`, `depositBridge`: before the pending deposits, the registry
  lists have the same length, each pending deposit has room for a new validator, and every
  pending deposit is at slot 0 or `deposit_requests_start_index ≤ eth1_deposit_index` (F2).
- `consolidationLens`: one balance for each validator before the pending consolidations.
- `summariesRoom`: the historical summaries list has room for one more item.

Facts about the hash values:
- `proposerFin`: each Electra proposer loop of the lookahead ends before its last pass
  (`Spec.ProposerFin`). The last pass needs `2**64 - 1` rejected candidates before it.

Facts about Etheorem's output (F3):
- `syncFull`, `proposersFull`: each balance weighted selection returns `size` items. -/
structure FuluEpochConds (p : Spec.Preset) (o : Spec.Oracle) (e : EState) : Prop where
  finalized : ∀ e', Before 3 e e' →
    (absEState e').finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH
  depositLens : ∀ e', Before 6 e e' → LensEq e'
  depositRoom : ∀ e', Before 6 e e' → e'.validators.val.size + e'.pendingDeposits.val.size ≤
    EthCLSpecs.Fulu.Const.validatorRegistryLimit
  depositBridge : ∀ e', Before 6 e e' → ∀ d ∈ e'.pendingDeposits.val.toList,
    d.slot = 0 ∨ e'.depositRequestsStartIndex ≤ e'.eth1DepositIndex
  consolidationLens : ∀ e', Before 7 e e' → e'.balances.val.size = e'.validators.val.size
  summariesRoom : ∀ e', Before 11 e e' →
    e'.historicalSummaries.val.size < EthCLSpecs.Fulu.Const.historicalRootsLimit
  syncFull : ∀ e', Before 13 e e' → SyncSelectionFull e'
  proposersFull : ∀ e', Before 14 e e' → ProposerSelectionsFull e'
    (EthCLSpecs.Fulu.currentEpochOf (pureState e') + EthCLSpecs.Fulu.Const.minSeedLookahead + 1)
  proposerFin : ∀ e', Before 14 e e' → ∀ s, Spec.ProposerFin p o (absEState e')
    (Spec.get_active_validator_indices (absEState e')
      (EthCLSpecs.Fulu.currentEpochOf (pureState e') + EthCLSpecs.Fulu.Const.minSeedLookahead +
        1).toNat) s

/-! ## The whole epoch -/

variable {p : Spec.Preset} {f : Spec.FuluConfig} (hp : EpochPresetAgrees p f)
include hp

/-- The reference Fulu `process_epoch` equals Etheorem's Fulu `processEpoch`.

If the reference returns `s'`, Etheorem's run succeeds and `absEState` of its result is `s'`.
`ho`: the oracle fields equal Etheorem's functions. `hsha`: `sha` returns 32 bytes
(`sha_size_pure` proves it for the pure SHA-256). `hc`: the step conditions. -/
theorem process_epoch_fulu_etheorem (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (hc : FuluEpochConds p o e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_fulu p f o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  have hpp := hp.passes
  have hb := hp.base
  rw [Spec.process_epoch_fulu_eq_tab p f hp.churn.compat] at h
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
  -- 4. registry updates, at `fuluTab`
  obtain ⟨t4, ht4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e4, r4, rfl⟩ :=
    process_registry_updates_etheorem hb hp.queues hp.churn e3 ht4 (hc.finalized e3 b3) h4
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
  -- 7. pending deposits, at `fuluTab`
  obtain ⟨t7, ht7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e7, r7, rfl⟩ := process_pending_deposits_etheorem hb hp.queues hp.churn o ho e6 ht7
    (hc.depositLens e6 b6) (hc.depositRoom e6 b6) (hc.depositBridge e6 b6) h7
  have b7 : StepsOk (epochSteps.take 7) e e7 := b6.snoc r7
  -- 8. pending consolidations
  obtain ⟨s8, h8, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e8, r8, rfl⟩ :=
    process_pending_consolidations_etheorem hb e7 (hc.consolidationLens e7 b7) h8
  have b8 : StepsOk (epochSteps.take 8) e e8 := b7.snoc r8
  -- 9. effective balance updates
  obtain ⟨s9, h9, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e9, r9, rfl⟩ := effective_balance_updates_etheorem hb hp.tail e8 h9
  have b9 : StepsOk (epochSteps.take 9) e e9 := b8.snoc r9
  -- 10. slashings reset
  obtain ⟨s10, h10, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e10, r10, rfl⟩ := slashings_reset_etheorem hb hp.tail e9 h10
  have b10 : StepsOk (epochSteps.take 10) e e10 := b9.snoc r10
  -- 11. randao mixes reset
  obtain ⟨s11, h11, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e11, r11, rfl⟩ := randao_mixes_reset_etheorem hb e10 h11
  have b11 : StepsOk (epochSteps.take 11) e e11 := b10.snoc r11
  -- 12. historical summaries
  obtain ⟨s12, h12, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e12, r12, rfl⟩ :=
    historical_summaries_update_etheorem hb hp.tail ho e11 (hc.summariesRoom e11 b11) h12
  have b12 : StepsOk (epochSteps.take 12) e e12 := b11.snoc r12
  -- 13. participation flags
  obtain ⟨e13, r13, h13⟩ := participation_flag_updates_etheorem e12
  have b13 : StepsOk (epochSteps.take 13) e e13 := b12.snoc r13
  rw [← h13] at h
  -- 14. sync committees, with the Electra loop
  obtain ⟨s14, h14, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e14, r14, rfl⟩ := process_sync_committee_updates_fulu_etheorem hb hp.committee o ho
    hp.epochsPerSyncCommitteePeriodLt hp.syncCommitteeSizePos e13 (hc.syncFull e13 b13) h14
  have b14 : StepsOk (epochSteps.take 14) e e14 := b13.snoc r14
  -- 15. proposer lookahead, with the Electra loop
  obtain ⟨e15, r15, rfl⟩ := process_proposer_lookahead_etheorem hb hp.committee o ho.hash hsha
    e14 (hc.proposersFull e14 b14) (hc.proposerFin e14 b14) h
  have b15 : StepsOk epochSteps e e15 := b14.snoc r15
  exact ⟨e15, by rw [processEpoch_eq]; exact b15.run_seq, rfl⟩

end Main

end EpochProofs.Etheorem.Fulu
