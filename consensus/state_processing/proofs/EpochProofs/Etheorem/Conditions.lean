import EpochProofs.Etheorem.Epoch
import EpochProofs.Spec.PresetBounds
import EpochProofs.Sanity.EpochStepFrames

/-!
# The Etheorem step conditions from the state at the epoch start

`process_epoch_etheorem` takes `EtheoremEpochConds e`: facts about the Etheorem state right
before some steps. This file proves most of them from facts about the reference state at the
start of the epoch, on mainnet.

- Proved from the reachable-state invariants (`EpochInputOk''`): the finalized epoch is below
  `FAR_FUTURE_EPOCH` before the registry update, and the registry lists have equal lengths
  before the pending deposits and the pending consolidations.
- Moved to the epoch start by frame lemmas (`GloasEtheoremDivergenceAssumptions`): room in the
  registry for the pending deposits, and room in the historical summaries. The steps before each
  of these reads do not write the fields it reads. The registry bound `RegBound` of each step
  comes from the same registry room and the length frames.

F2 is fixed on the Etheorem fork that this project requires (`eserilev/etheorem`, branch
`formalhouse-pin-beta4`). That fork has no eth1 bridge check in `process_pending_deposits`, as in the
pyspec since v1.7.0-alpha.9, so no bridge condition is needed.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Generic

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]

/-! ## Facts about the map -/

/-- `RowsOk` of the mapped state gives `LensEq`. -/
theorem lensEq_of_rowsOk {e : EtheoremState} (h : Spec.RowsOk (toSpecState e)) : LensEq e := by
  obtain ⟨r1, r2, r3, r4⟩ := h
  simp only [toSpecState_balances, toSpecState_validators, toSpecState_inactivity_scores,
    toSpecState_previous_epoch_participation, toSpecState_current_epoch_participation,
    length_map_regList] at r1 r2 r3 r4
  exact ⟨r1, by simpa using r3, by simpa using r4, r2⟩

/-! ## The conditions at the epoch start -/


variable [HasherTag] [CryptoBackend]

theorem qualifyingBuilderWithdrawals_length (e : EtheoremState) :
    (qualifyingBuilderWithdrawals e).length ≤ EthCLSpecs.Gloas.Const.slotsPerEpoch := by
  unfold qualifyingBuilderWithdrawals
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The reference `process_epoch` equals Etheorem's Gloas `processEpoch` on mainnet, from facts
about the state at the epoch start.

`hb0` and `hslot` hold at each epoch boundary of a reachable run (`EpochInputOk''`). They give
the finalized epoch condition and the equal list lengths. `hin` holds the facts that frame
lemmas carry to the step that reads them. `hhist`: the historical summaries are below
`HISTORICAL_ROOTS_LIMIT`, a cap that beta.4 keeps. -/
theorem process_epoch_etheorem_in [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hb0 : Spec.BoundaryOk (toSpecState e)) (hslot : (toSpecState e).slot < 2 ^ 64)
    (hin : GloasEtheoremDivergenceAssumptions e)
    (hhist : (toSpecState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {s' : Spec.BeaconState} (h : Spec.process_epoch Spec.P o (toSpecState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s' := by
  have hp := hpa
  have hpp := hp.passes
  have hb := hp.base
  -- The registry bound at each step (`RegBound`): `depositRoom` at the input, the length frames
  -- of the steps, and the bound that the deposit step keeps.
  haveI : RegBound e := ⟨by
    have hr := hin.depositRoom
    simp only [toSpecState_validators, length_map_regList] at hr
    omega⟩
  unfold Spec.process_epoch at h
  -- 1. justification and finalization
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  have j1 := Spec.BoundaryOk.of_justification hb0 h1
  have sl1 := (Spec.process_justification_and_finalization_frame _ _ _ h1).2
  have f1 := Spec.process_justification_and_finalization_pframe _ _ _ h1
  have l1 := Spec.process_justification_and_finalization_len _ _ _ h1
  obtain ⟨e1, r1, rfl⟩ := justification_etheorem hpp e h1
  have b1 : StepsOk (epochSteps.take 1) e e1 := .cons r1 (.nil _)
  haveI : RegBound e1 := RegBound.of_length (e := e) l1.1
  -- 2. inactivity
  obtain ⟨s2, h2, h⟩ := Spec.specM_bind_ok h
  have c2 := Spec.process_inactivity_updates_checkpointsStable _ _ _ h2
  have f2 := Spec.process_inactivity_updates_pframe _ _ _ h2
  have l2 := Spec.process_inactivity_updates_len _ _ _ h2
  obtain ⟨r2, rfl⟩ := inactivity_updates_etheorem hpp e1 h2
  have b2 : StepsOk (epochSteps.take 2) e (inactivityUpdatesE e1) := b1.snoc r2
  generalize inactivityUpdatesE e1 = e2 at *
  haveI : RegBound e2 := RegBound.of_length (e := e1) l2.1
  -- 3. rewards and penalties
  obtain ⟨t3, ht3, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e2 ht3
  subst this
  obtain ⟨s3, h3, h⟩ := Spec.specM_bind_ok h
  have c3 := Spec.process_rewards_and_penalties_checkpointsStable _ _ _ _ h3
  have f3 := Spec.process_rewards_and_penalties_pframe _ _ _ _ h3
  have l3 := Spec.process_rewards_and_penalties_len _ _ _ _ h3
  obtain ⟨e3, r3, rfl⟩ := rewards_etheorem hpp e2 h3
  have b3 : StepsOk (epochSteps.take 3) e e3 := b2.snoc r3
  haveI : RegBound e3 := RegBound.of_length (e := e2) l3.1
  -- 4. registry updates
  have hfin : (toSpecState e3).finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH := by
    have hf := j1.2.1
    rw [← c2.2.1, ← c3.2.1, ← c2.1, ← c3.1] at hf
    have hs : (toSpecState e3).slot = (toSpecState e).slot := by rw [c3.1, c2.1, sl1]
    rw [hs] at hf
    have h6 := Spec.P_epoch_le_div6 (toSpecState e).slot
    have hslot' : @LT.lt Nat _ (toSpecState e).slot (2 ^ 64) := hslot
    have hlt : @LT.lt Nat _ ((toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH) (2 ^ 64 - 1) := by omega
    unfold Spec.FAR_FUTURE_EPOCH
    exact Nat.lt_of_le_of_lt hf hlt
  obtain ⟨t4, ht4, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := Spec.specM_bind_ok h
  have f4 := Spec.process_registry_updates_pframe _ _ _ _ h4
  have l4 := Spec.process_registry_updates_len _ _ _ _ h4
  obtain ⟨e4, r4, rfl⟩ := process_registry_updates_etheorem hb hp.queues e3 ht4 hfin h4
  have b4 : StepsOk (epochSteps.take 4) e e4 := b3.snoc r4
  haveI : RegBound e4 := RegBound.of_length (e := e3) l4.1
  -- 5. slashings
  obtain ⟨t5, ht5, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e4 ht5
  subst this
  obtain ⟨s5, h5, h⟩ := Spec.specM_bind_ok h
  have f5 := Spec.process_slashings_pframe _ _ _ _ h5
  have l5 := Spec.process_slashings_len _ _ _ _ h5
  obtain ⟨r5, rfl⟩ := slashings_etheorem hpp e4 h5
  have b5 : StepsOk (epochSteps.take 5) e (slashingsE e4) := b4.snoc r5
  generalize slashingsE e4 = e5 at *
  haveI : RegBound e5 := RegBound.of_length (e := e4) l5.1
  -- 6. eth1 data reset
  obtain ⟨s6, h6, h⟩ := Spec.specM_bind_ok h
  have f6 := Spec.process_eth1_data_reset_pframe _ _ _ h6
  have l6 := Spec.process_eth1_data_reset_len _ _ _ h6
  obtain ⟨e6, r6, rfl⟩ := eth1_data_reset_etheorem hb hp.tail e5 h6
  have b6 : StepsOk (epochSteps.take 6) e e6 := b5.snoc r6
  haveI : RegBound e6 := RegBound.of_length (e := e5) l6.1
  -- 7. pending deposits
  have F6 : Spec.PFrame (toSpecState e) (toSpecState e6) :=
    f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6))))
  have L6 : Spec.LenStep (toSpecState e) (toSpecState e6) :=
    l1.trans (l2.trans (l3.trans (l4.trans (l5.trans l6))))
  have rows6 : Spec.RowsOk (toSpecState e6) := L6.rowsOk hb0.2.1
  have hroom : e6.validators.val.size + EthCLSpecs.Gloas.Const.maxPendingDepositsPerEpoch ≤
      EthCLSpecs.Gloas.Const.validatorRegistryLimit := by
    have hv := L6.1
    have hr := hin.depositRoom
    simp only [toSpecState_validators, length_map_regList] at hv hr
    omega
  obtain ⟨t7, ht7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := Spec.specM_bind_ok h
  have q7 := Spec.process_pending_deposits_qframe _ _ _ _ _ h7
  have rows7 := Spec.process_pending_deposits_rowsOk _ _ _ _ _ h7 rows6
  obtain ⟨e7, r7, rfl, hreg7⟩ := process_pending_deposits_etheorem hb hp.queues o ho e6 ht7
    (lensEq_of_rowsOk rows6) hroom h7
  have b7 : StepsOk (epochSteps.take 7) e e7 := b6.snoc r7
  -- 8. pending consolidations
  have hlens7 : e7.balances.val.size = e7.validators.val.size := by
    have := rows7.1
    simp only [toSpecState_balances, toSpecState_validators, length_map_regList] at this
    exact this
  obtain ⟨s8, h8, h⟩ := Spec.specM_bind_ok h
  have f8 := Spec.process_pending_consolidations_pframe _ _ _ h8
  have l8 := Spec.process_pending_consolidations_len _ _ _ h8
  obtain ⟨e8, r8, rfl⟩ := process_pending_consolidations_etheorem hb e7 hlens7 h8
  have b8 : StepsOk (epochSteps.take 8) e e8 := b7.snoc r8
  haveI : RegBound e8 := RegBound.of_length (e := e7) l8.1
  -- 9. builder pending payments
  have Q8 : Spec.QFrame (toSpecState e) (toSpecState e8) := F6.1.trans (q7.trans f8.1)
  obtain ⟨t9, ht9, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e8 ht9
  subst this
  obtain ⟨s9, h9, h⟩ := Spec.specM_bind_ok h
  have hs9 := Spec.process_builder_pending_payments_summaries _ _ _ _ h9
  have l9 := Spec.process_builder_pending_payments_len _ _ _ _ h9
  obtain ⟨e9, r9, rfl⟩ :=
    builder_pending_payments_etheorem' hb hp.slotsPerEpochSix e8 h9
  have b9 : StepsOk (epochSteps.take 9) e e9 := b8.snoc r9
  haveI : RegBound e9 := RegBound.of_length (e := e8) l9.1
  -- 10. effective balance updates
  obtain ⟨s10, h10, h⟩ := Spec.specM_bind_ok h
  have f10 := Spec.process_effective_balance_updates_pframe _ _ _ h10
  have l10 := Spec.process_effective_balance_updates_len _ _ _ h10
  obtain ⟨e10, r10, rfl⟩ := effective_balance_updates_etheorem hb hp.tail e9 h10
  have b10 : StepsOk (epochSteps.take 10) e e10 := b9.snoc r10
  haveI : RegBound e10 := RegBound.of_length (e := e9) l10.1
  -- 11. slashings reset
  obtain ⟨s11, h11, h⟩ := Spec.specM_bind_ok h
  have f11 := Spec.process_slashings_reset_pframe _ _ _ h11
  have l11 := Spec.process_slashings_reset_len _ _ _ h11
  obtain ⟨e11, r11, rfl⟩ := slashings_reset_etheorem hb hp.tail e10 h11
  have b11 : StepsOk (epochSteps.take 11) e e11 := b10.snoc r11
  haveI : RegBound e11 := RegBound.of_length (e := e10) l11.1
  -- 12. randao mixes reset
  obtain ⟨s12, h12, h⟩ := Spec.specM_bind_ok h
  have f12 := Spec.process_randao_mixes_reset_pframe _ _ _ h12
  have l12 := Spec.process_randao_mixes_reset_len _ _ _ h12
  obtain ⟨e12, r12, rfl⟩ := randao_mixes_reset_etheorem hb e11 h12
  have b12 : StepsOk (epochSteps.take 12) e e12 := b11.snoc r12
  haveI : RegBound e12 := RegBound.of_length (e := e11) l12.1
  -- 13. historical summaries
  have hsroom : e12.historicalSummaries.val.size < EthCLSpecs.Gloas.Const.historicalRootsLimit := by
    have heq : (toSpecState e12).historical_summaries = (toSpecState e).historical_summaries := by
      rw [f12.1.2.2.2, f11.1.2.2.2, f10.1.2.2.2, hs9, Q8.2.2.2]
    have hw := congrArg List.length heq
    have hr := hhist
    simp only [toSpecState_historical_summaries, length_map_regList, length_map_toList] at hw hr
    omega
  obtain ⟨s13, h13, h⟩ := Spec.specM_bind_ok h
  have l13 := Spec.process_historical_summaries_update_len _ _ _ _ h13
  obtain ⟨e13, r13, rfl⟩ :=
    historical_summaries_update_etheorem hb hp.tail ho e12 hsroom h13
  have b13 : StepsOk (epochSteps.take 13) e e13 := b12.snoc r13
  haveI : RegBound e13 := RegBound.of_length (e := e12) l13.1
  -- 14. participation flags
  obtain ⟨e14, r14, h14⟩ := participation_flag_updates_etheorem e13
  have b14 : StepsOk (epochSteps.take 14) e e14 := b13.snoc r14
  haveI : RegBound e14 := RegBound.of_length (e := e13) (by rw [h14]; rfl)
  rw [← h14] at h
  -- 15. sync committees
  obtain ⟨s15, h15, h⟩ := Spec.specM_bind_ok h
  have l15 : s15.validators.length = (toSpecState e14).validators.length := by
    obtain ⟨_, _, hs⟩ := Spec.process_sync_committee_updates_shape _ _ _ _ h15
    rw [hs]
  obtain ⟨e15, r15, rfl⟩ := process_sync_committee_updates_etheorem hb hp.committee o ho
    hp.epochsPerSyncCommitteePeriodLt e14 h15
  have b15 : StepsOk (epochSteps.take 15) e e15 := b14.snoc r15
  haveI : RegBound e15 := RegBound.of_length (e := e14) l15
  -- 16. proposer lookahead
  obtain ⟨s16, h16, h⟩ := Spec.specM_bind_ok h
  have l16 : s16.validators.length = (toSpecState e15).validators.length := by
    obtain ⟨_, hs⟩ := Spec.process_proposer_lookahead_shape _ _ _ _ h16
    rw [hs]
  obtain ⟨e16, r16, rfl⟩ := process_proposer_lookahead_etheorem hb hp.committee o ho.hash hsha
    e15 h16
  have b16 : StepsOk (epochSteps.take 16) e e16 := b15.snoc r16
  haveI : RegBound e16 := RegBound.of_length (e := e15) l16
  -- 17. PTC window
  obtain ⟨e17, r17, rfl⟩ := process_ptc_window_etheorem hb hp.committee o ho.hash hsha e16 h
  have b17 : StepsOk epochSteps e e17 := b16.snoc r17
  exact ⟨e17, by rw [processEpoch_eq]; exact b17.run_seq, rfl⟩

/-- Lighthouse's epoch processing equals Etheorem's Gloas `processEpoch` at each epoch boundary
of a reachable run, on mainnet.

`hin` is the fact that `reachable_state_transition_sameResultOrBothFail'''` proves at each epoch boundary.
The conditions that remain:
- `hcond`: room in the registry for the new validators of one epoch (F10), a fact about the
  epoch start state.
- `hhist`: the historical summaries are below `HISTORICAL_ROOTS_LIMIT`. Beta.4 keeps this cap.
- `ho`, `hsha`: the oracle is Etheorem's hash and BLS functions, and SHA-256 returns 32 bytes. -/
theorem lighthouse_epoch_etheorem_reachable [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hin : Spec.ReachableInvariants (toSpecState e)) (hcond : GloasEtheoremDivergenceAssumptions e)
    (hhist : (toSpecState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_full o (toSpecState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s' := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, _, hcons⟩, _, hvalid⟩ := hin
  have hsame := Spec.process_epoch_lh_full_sameResultOrBothFail' o (toSpecState e) hb hslot heb hexit hsup hvalid
    hcons
  exact process_epoch_etheorem_in hpa o ho hsha e hb hslot hcond hhist ((hsame s').mp h)

end Generic

end EpochProofs.Etheorem
