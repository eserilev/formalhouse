import EpochProofs.AgreesEtheorem.Committees
import EpochProofs.Etheorem.Total
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder

/-!
# The Lighthouse epoch and Etheorem's give the same state, or both fail

`Etheorem/Final.lean` proves one direction: when the Lighthouse epoch model returns `s'`,
Etheorem's `processEpoch` returns a state that maps to `s'`. This file adds the other: when
Etheorem's `processEpoch` succeeds, the Lighthouse model succeeds. Together they give `SameResultOrBothFail`
of the Lighthouse model and Etheorem's epoch (`lighthouse_epoch_agrees_etheorem`, and
`lighthouse_fulu_epoch_agrees_etheorem` for Fulu), with no pyspec precondition.

The proof of the new direction:

1. The reference epoch is the steps before the committee steps (`epochToCommittees`), then the
   committee steps. The steps before succeed under the time and supply bounds
   (`epochToCommittees_total`).
2. Etheorem runs the same steps first and reaches a state that maps to the reference's
   (`epochToCommittees_etheorem`, the first steps of `process_epoch_etheorem_in`).
3. Etheorem's committee steps succeed, so the reference committee steps succeed
   (`AgreesEtheorem/Committees.lean`).
4. So the reference epoch succeeds, and the Lighthouse model with it (`SameResultOrBothFail` of the model and
   the reference).

`etheoremProcessEpoch` reads Etheorem's run as a reference result, so that `SameResultOrBothFail` applies.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

/-- Etheorem runs the steps `l1` and reaches `e1`, so its run of `l1 ++ l2` is its run of `l2`
from `e1`. -/
theorem StepsOk.run_seq_append {l1 l2 : List (GloasRun Unit)} {e e1 : EtheoremState}
    (h : StepsOk l1 e e1) (hl2 : l2 ≠ []) :
    (seqSteps (l1 ++ l2)).run (pureState e) = (seqSteps l2).run (pureState e1) := by
  induction h with
  | nil e => rfl
  | @cons a l e e1 e2 hr _ ih =>
    have hne : l ++ l2 ≠ [] := by simp [hl2]
    obtain ⟨b, l', hbl⟩ := List.exists_cons_of_ne_nil hne
    rw [List.cons_append, hbl, seqSteps, run_bind, hr, except_bind_ok, ← hbl]
    exact ih

variable [EthCLSpecs.Gloas.Config] [CryptoBackend]

/-- Etheorem's Gloas `processEpoch` on `e`, read as a result of the reference: `ok` with the
mapped state when Etheorem succeeds, an error when it fails. The error kind is not kept, as
`SameResultOrBothFail` does not compare errors. -/
def etheoremProcessEpoch (e : EtheoremState) : Spec.SpecM Spec.BeaconState :=
  match runPure (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)) e with
  | .ok (_, e') => .ok (toSpecState e')
  | .error _ => .error .assertionFailed

/-- A successful run, read through `etheoremProcessEpoch`. -/
theorem etheoremProcessEpoch_of_run {e e' : EtheoremState}
    (h : (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e')) :
    etheoremProcessEpoch e = .ok (toSpecState e') := by
  unfold etheoremProcessEpoch
  rw [runPure_of_run_ok h]

/-- `etheoremProcessEpoch` returns `ok` only on a successful run. -/
theorem run_of_etheoremProcessEpoch {e : EtheoremState} {s : Spec.BeaconState}
    (h : etheoremProcessEpoch e = .ok s) :
    ∃ r, (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok r ∧ s = toSpecState r.2.view := by
  unfold etheoremProcessEpoch runPure at h
  cases hr : (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) with
  | error err => rw [hr] at h; cases h
  | ok r =>
    rw [hr] at h
    exact ⟨r, rfl, (Except.ok.inj h).symm⟩

end forkproof

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]

omit [HasherTag] [CryptoBackend] in
/-- The SSZ vector fields of a mapped Etheorem state have their lengths: Etheorem holds them as
fixed-size vectors. -/
theorem vectorLengths_toSpecState [Spec.PresetCfg] (hpa : PresetMatchesEtheorem Spec.P) (e : EtheoremState) :
    (toSpecState e).VectorLengths Spec.P := by
  have hm : Spec.P.MIN_SEED_LOOKAHEAD = 1 := Spec.P_min_seed
  unfold Spec.BeaconState.VectorLengths
  simp [toSpecState, absBits, absSyncCommittee, ← hpa.tail.slotsPerHistoricalRoot,
    ← hpa.tail.epochsPerSlashingsVector, ← hpa.base.epochsPerHistoricalVector,
    ← hpa.base.slotsPerEpoch, ← hpa.committee.syncCommitteeSize, ← hpa.committee.ptcSize, hm,
    Spec.JUSTIFICATION_BITS_LENGTH]

/-- The first 14 steps of the reference epoch (`epochToCommittees`) equal Etheorem's: if the
reference returns `s`, Etheorem runs its first 14 steps and reaches a state that maps to `s`.
The steps of `process_epoch_etheorem_in`, up to the committee steps. -/
theorem epochToCommittees_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o) (e : EtheoremState)
    (hb0 : Spec.BoundaryOk (toSpecState e)) (hslot : (toSpecState e).slot < 2 ^ 64)
    (hin : GloasEtheoremDivergenceAssumptions e)
    (hhist : (toSpecState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {s : Spec.BeaconState} (h : Spec.epochToCommittees Spec.P o (toSpecState e) = .ok s) :
    ∃ e14, StepsOk (epochSteps.take 14) e e14 ∧ toSpecState e14 = s := by
  have hp := hpa
  have hpp := hp.passes
  have hb := hp.base
  unfold Spec.epochToCommittees at h
  -- 1. justification and finalization
  obtain ⟨s1, h1, h⟩ := Spec.specM_bind_ok h
  have j1 := Spec.BoundaryOk.of_justification hb0 h1
  have sl1 := (Spec.process_justification_and_finalization_frame _ _ _ h1).2
  have f1 := Spec.process_justification_and_finalization_pframe _ _ _ h1
  have l1 := Spec.process_justification_and_finalization_len _ _ _ h1
  obtain ⟨e1, r1, rfl⟩ := justification_etheorem hpp e h1
  have b1 : StepsOk (epochSteps.take 1) e e1 := .cons r1 (.nil _)
  -- 2. inactivity
  obtain ⟨s2, h2, h⟩ := Spec.specM_bind_ok h
  have c2 := Spec.process_inactivity_updates_checkpointsStable _ _ _ h2
  have f2 := Spec.process_inactivity_updates_pframe _ _ _ h2
  have l2 := Spec.process_inactivity_updates_len _ _ _ h2
  obtain ⟨r2, rfl⟩ := inactivity_updates_etheorem hpp e1 h2
  have b2 : StepsOk (epochSteps.take 2) e (inactivityUpdatesE e1) := b1.snoc r2
  generalize inactivityUpdatesE e1 = e2 at *
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
  -- 6. eth1 data reset
  obtain ⟨s6, h6, h⟩ := Spec.specM_bind_ok h
  have f6 := Spec.process_eth1_data_reset_pframe _ _ _ h6
  have l6 := Spec.process_eth1_data_reset_len _ _ _ h6
  obtain ⟨e6, r6, rfl⟩ := eth1_data_reset_etheorem hb hp.tail e5 h6
  have b6 : StepsOk (epochSteps.take 6) e e6 := b5.snoc r6
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
    simp only [toSpecState_validators, length_map_toList] at hv hr
    omega
  obtain ⟨t7, ht7, h⟩ := Spec.specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := Spec.specM_bind_ok h
  have q7 := Spec.process_pending_deposits_qframe _ _ _ _ _ h7
  have rows7 := Spec.process_pending_deposits_rowsOk _ _ _ _ _ h7 rows6
  obtain ⟨e7, r7, rfl⟩ := process_pending_deposits_etheorem hb hp.queues o ho e6 ht7
    (lensEq_of_rowsOk rows6) hroom h7
  have b7 : StepsOk (epochSteps.take 7) e e7 := b6.snoc r7
  -- 8. pending consolidations
  have hlens7 : e7.balances.val.size = e7.validators.val.size := by
    have := rows7.1
    simp only [toSpecState_balances, toSpecState_validators, length_map_toList] at this
    exact this
  obtain ⟨s8, h8, h⟩ := Spec.specM_bind_ok h
  have f8 := Spec.process_pending_consolidations_pframe _ _ _ h8
  obtain ⟨e8, r8, rfl⟩ := process_pending_consolidations_etheorem hb e7 hlens7 h8
  have b8 : StepsOk (epochSteps.take 8) e e8 := b7.snoc r8
  -- 9. builder pending payments
  have Q8 : Spec.QFrame (toSpecState e) (toSpecState e8) := F6.1.trans (q7.trans f8.1)
  have hbroom : e8.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e8).length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit := by
    have hw := congrArg List.length Q8.2.2.1
    have hr := hin.builderRoom
    have hq := qualifyingBuilderWithdrawals_length e8
    simp only [toSpecState_builder_pending_withdrawals, length_map_toList] at hw hr
    omega
  obtain ⟨t9, ht9, h⟩ := Spec.specM_bind_ok h
  have := get_total_active_balance_ok hb e8 ht9
  subst this
  obtain ⟨s9, h9, h⟩ := Spec.specM_bind_ok h
  have hs9 := Spec.process_builder_pending_payments_summaries _ _ _ _ h9
  obtain ⟨e9, r9, rfl⟩ :=
    builder_pending_payments_etheorem' hb hp.slotsPerEpochSix e8 hbroom h9
  have b9 : StepsOk (epochSteps.take 9) e e9 := b8.snoc r9
  -- 10. effective balance updates
  obtain ⟨s10, h10, h⟩ := Spec.specM_bind_ok h
  have f10 := Spec.process_effective_balance_updates_pframe _ _ _ h10
  obtain ⟨e10, r10, rfl⟩ := effective_balance_updates_etheorem hb hp.tail e9 h10
  have b10 : StepsOk (epochSteps.take 10) e e10 := b9.snoc r10
  -- 11. slashings reset
  obtain ⟨s11, h11, h⟩ := Spec.specM_bind_ok h
  have f11 := Spec.process_slashings_reset_pframe _ _ _ h11
  obtain ⟨e11, r11, rfl⟩ := slashings_reset_etheorem hb hp.tail e10 h11
  have b11 : StepsOk (epochSteps.take 11) e e11 := b10.snoc r11
  -- 12. randao mixes reset
  obtain ⟨s12, h12, h⟩ := Spec.specM_bind_ok h
  have f12 := Spec.process_randao_mixes_reset_pframe _ _ _ h12
  obtain ⟨e12, r12, rfl⟩ := randao_mixes_reset_etheorem hb e11 h12
  have b12 : StepsOk (epochSteps.take 12) e e12 := b11.snoc r12
  -- 13. historical summaries
  have hsroom : e12.historicalSummaries.val.size < EthCLSpecs.Gloas.Const.historicalRootsLimit := by
    have heq : (toSpecState e12).historical_summaries = (toSpecState e).historical_summaries := by
      rw [f12.1.2.2.2, f11.1.2.2.2, f10.1.2.2.2, hs9, Q8.2.2.2]
    have hw := congrArg List.length heq
    have hr := hhist
    simp only [toSpecState_historical_summaries, length_map_toList] at hw hr
    omega
  obtain ⟨s13, h13, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e13, r13, rfl⟩ :=
    historical_summaries_update_etheorem hb hp.tail ho e12 hsroom h13
  have b13 : StepsOk (epochSteps.take 13) e e13 := b12.snoc r13
  -- 14. participation flags
  obtain ⟨e14, r14, h14⟩ := participation_flag_updates_etheorem e13
  have b14 : StepsOk (epochSteps.take 14) e e14 := b13.snoc r14
  rw [← h14] at h
  exact ⟨e14, b14, (Except.ok.inj h)⟩

/-- When Etheorem's Gloas `processEpoch` succeeds, the reference `process_epoch` succeeds.

The steps before the committee steps succeed under the time and supply bounds (`hslot`, `hrb`,
and the invariants `hin`). Etheorem reaches the same state after them. Its committee
steps succeed, so the reference committee steps succeed with the state facts `hsel`
(`SelectionStateFacts`) at the state that the epoch passes to them. No pyspec precondition. -/
theorem process_epoch_of_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds]
    (hpa : PresetMatchesEtheorem Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hin : Spec.ReachableInvariants (toSpecState e)) (hpre : Spec.AtEpochBoundary (toSpecState e))
    (hcond : GloasEtheoremDivergenceAssumptions e)
    (hhist : (toSpecState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hslot : (toSpecState e).slot + 8192 < 2 ^ 64) (hrb : Spec.PhysicalLimits (toSpecState e))
    (hsel : ∀ t, Spec.epochToCommittees Spec.P o (toSpecState e) = .ok t →
      Spec.SelectionStateFacts o t)
    {r : Unit × EthCLSpecs.Gloas.State}
    (h : (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) = .ok r) :
    ∃ s', Spec.process_epoch Spec.P o (toSpecState e) = .ok s' := by
  have hb := hpa.base
  have hc := hpa.committee
  have hvec := vectorLengths_toSpecState hpa e
  obtain ⟨⟨⟨hb0, hslot64, heb, -, hsup⟩, -, hcons⟩, -, -⟩ := hin
  -- The steps before the committee steps, in the reference and in Etheorem.
  obtain ⟨s, hs, hfr⟩ := Spec.epochToCommittees_total o (toSpecState e) hb0.2.1 hslot hpre.1 hvec
    hb0.1 (Nat.lt_trans hrb.supply (by decide))
    (Spec.midOk_of_physicalLimits _ hb0.2.1 hslot heb hvec hcons hsup.2.2 hrb)
    (Spec.depOk_of_physicalLimits o _ hslot hrb)
  obtain ⟨e14, b14, rfl⟩ := epochToCommittees_etheorem hpa o ho e hb0 hslot64 hcond hhist hs
  have hf14 : Spec.SelFacts o (toSpecState e14) := Spec.SelFacts.of_frame hfr hslot (hsel _ hs)
  rw [processEpoch_eq, ← List.take_append_drop 14 epochSteps,
    b14.run_seq_append (by simp [epochSteps])] at h
  change ((EthCLSpecs.Gloas.processSyncCommitteeUpdates >>= fun _ =>
      (EthCLSpecs.Gloas.processProposerLookahead >>= fun _ =>
        EthCLSpecs.Gloas.processPtcWindow) : GloasRun Unit).run (pureState e14) = .ok r) at h
  -- 15. sync committees
  rw [run_bind] at h
  cases h15 : (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run
      (pureState e14) with
  | error err => rw [h15, except_bind_error] at h; cases h
  | ok p15 =>
  obtain ⟨s15, hs15, f15s, f15v, f15r, -, -⟩ := sync_committee_updates_of_etheorem hb hc o ho
    hpa.epochsPerSyncCommitteePeriodLt e14 hf14 h15
  obtain ⟨e15, r15, rfl⟩ := process_sync_committee_updates_etheorem hb hc o ho
    hpa.epochsPerSyncCommitteePeriodLt e14 hs15
  rw [h15] at r15
  cases r15
  rw [h15, except_bind_ok] at h
  have hf15 : Spec.SelFacts o (toSpecState e15) := hf14.congr f15s f15v f15r
  -- 16. proposer lookahead
  rw [run_bind] at h
  cases h16 : (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run
      (pureState e15) with
  | error err => rw [h16, except_bind_error] at h; cases h
  | ok p16 =>
  obtain ⟨s16, hs16, f16s, f16v, f16r, -⟩ := proposer_lookahead_of_etheorem hb hc o ho.hash hsha
    e15 hf15 h16
  obtain ⟨e16, r16, rfl⟩ := process_proposer_lookahead_etheorem hb hc o ho.hash hsha e15 hs16
  rw [h16] at r16
  cases r16
  rw [h16, except_bind_ok] at h
  have hf16 : Spec.SelFacts o (toSpecState e16) := hf15.congr f16s f16v f16r
  -- 17. PTC window
  obtain ⟨s17, hs17, -⟩ := ptc_window_of_etheorem hb hc o ho.hash hsha e16 hf16 h
  refine ⟨s17, ?_⟩
  rw [Spec.process_epoch_committees, hs, Spec.tot_bind_ok]
  unfold Spec.committeeSteps
  rw [hs15, Spec.tot_bind_ok, hs16, Spec.tot_bind_ok, hs17]

/-- The Lean model of Lighthouse's Gloas epoch and Etheorem's Gloas `processEpoch` give the same
state, or both fail.

- `hin`, `hpre`: the reachable-state invariants at the epoch boundary and the boundary facts.
- `hcond`: Etheorem's alpha.11 list limits have room (F6, F10). Etheorem diverges from the pyspec
  there.
- `hslot`, `hrb`: the time and supply bounds. The proof gets the success of the steps before
  the committee steps from them. The SSZ vector lengths hold on every Etheorem state
  (`vectorLengths_toSpecState`).
- `hsel`: the state facts that the committee steps read and Etheorem does not check.
- `hpa`, `hhr`, `ho`, `hsha`: the preset, the historical roots limit and the oracle agree with
  Etheorem's. -/
theorem lighthouse_epoch_agrees_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    [Spec.PresetCfg.Bounds] (hpa : PresetMatchesEtheorem Spec.P)
    (hhr : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle) (ho : OracleAgrees o) (hsha : ∀ b : ByteArray, (sha b).size = 32)
    (e : EtheoremState) (hin : Spec.ReachableInvariants (toSpecState e))
    (hpre : Spec.AtEpochBoundary (toSpecState e)) (hcond : GloasEtheoremDivergenceAssumptions e)
    (hslot : (toSpecState e).slot + 8192 < 2 ^ 64) (hrb : Spec.PhysicalLimits (toSpecState e))
    (hsel : ∀ t, Spec.epochToCommittees Spec.P o (toSpecState e) = .ok t →
      Spec.SelectionStateFacts o t) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse o (toSpecState e)) (etheoremProcessEpoch e) := by
  have hin' := hin
  obtain ⟨⟨⟨hb, hslot64, heb, hexit, hsup⟩, _, hcons⟩, _, hvalid⟩ := hin'
  have hlh : Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse o (toSpecState e))
      (Spec.process_epoch Spec.P o (toSpecState e)) :=
    Spec.SameResultOrBothFail.trans (Spec.process_epoch_lighthouse_sameResultOrBothFail o (toSpecState e) hpre)
      (Spec.process_epoch_lh_full_sameResultOrBothFail' o (toSpecState e) hb hslot64 heb hexit hsup hvalid hcons)
  intro v
  constructor
  · intro h
    obtain ⟨e', he', rfl⟩ := lighthouse_order_epoch_etheorem_reachable hpa hhr o ho hsha e hin
      hpre hcond h
    exact etheoremProcessEpoch_of_run he'
  · intro h
    obtain ⟨r, hr, rfl⟩ := run_of_etheoremProcessEpoch h
    obtain ⟨s', hs'⟩ := process_epoch_of_etheorem hpa o ho hsha e hin hpre hcond
      (Nat.lt_of_lt_of_le hpre.2.2 hhr) hslot hrb hsel hr
    have hl := (hlh s').mpr hs'
    obtain ⟨e', he', rfl⟩ := lighthouse_order_epoch_etheorem_reachable hpa hhr o ho hsha e hin
      hpre hcond hl
    rw [hr] at he'
    cases he'
    exact hl

end Gloas

end EpochProofs.Etheorem

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu

section Fulu

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]

omit [HasherTag] [CryptoBackend] in
/-- The Fulu SSZ vector fields of a mapped Etheorem Fulu state have their lengths. -/
theorem fuluVectorLengths_toSpecState [Spec.PresetCfg] [Spec.FuluCfg]
    (hpa : PresetMatchesEtheorem Spec.P Spec.FC) (e : EtheoremState) :
    (toSpecState e).FuluVectorLengths Spec.P := by
  have hm : Spec.P.MIN_SEED_LOOKAHEAD = 1 := Spec.P_min_seed
  unfold Spec.BeaconState.FuluVectorLengths
  simp [toSpecState, absBits, absSyncCommittee, ← hpa.tail.slotsPerHistoricalRoot,
    ← hpa.tail.epochsPerSlashingsVector, ← hpa.base.epochsPerHistoricalVector,
    ← hpa.base.slotsPerEpoch, ← hpa.committee.syncCommitteeSize, hm,
    Spec.JUSTIFICATION_BITS_LENGTH]

/-- The first 13 steps of the reference Fulu epoch (`epochToCommitteesFulu`) equal Etheorem's:
if the reference returns `s`, Etheorem runs its first 13 steps and reaches a state that maps to
`s`. The steps of `process_epoch_fulu_etheorem`, up to the committee steps. -/
theorem epochToCommitteesFulu_etheorem [Spec.PresetCfg] [Spec.FuluCfg]
    (hpa : PresetMatchesEtheorem Spec.P Spec.FC) (o : Spec.Oracle) (ho : OracleAgrees o) (e : EtheoremState)
    (hc : FuluEtheoremBridgeConditions Spec.P o e) {s : Spec.BeaconState}
    (h : Spec.epochToCommitteesFulu Spec.P Spec.FC o (toSpecState e) = .ok s) :
    ∃ e13, StepsOk (epochSteps.take 13) e e13 ∧ toSpecState e13 = s := by
  have hp := hpa
  have hpp := hp.passes
  have hb := hp.base
  unfold Spec.epochToCommitteesFulu at h
  simp only [Spec.process_registry_updates_fulu_eq Spec.P Spec.FC hp.churn.compat,
    Spec.process_pending_deposits_fulu_tab_eq Spec.P Spec.FC hp.churn.compat] at h
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
    (hc.depositLens e6 b6) (hc.depositRoom e6 b6) h7
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
  exact ⟨e13, b13, (Except.ok.inj h)⟩

/-- When Etheorem's Fulu `processEpoch` succeeds, the reference Fulu `process_epoch` succeeds.
As `process_epoch_of_etheorem`, with the two Fulu committee steps. -/
theorem process_epoch_fulu_of_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    [Spec.PresetCfg.Bounds] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P Spec.FC) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState) (hc : FuluEtheoremBridgeConditions Spec.P o e)
    (hin : Spec.ReachableInvariants (toSpecState e)) (hpre : Spec.AtEpochBoundary (toSpecState e))
    (hslot : (toSpecState e).slot + 8192 < 2 ^ 64) (hrb : Spec.PhysicalLimits (toSpecState e))
    (hsel : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o (toSpecState e) = .ok t →
      Spec.SelectionStateFacts o t)
    {r : Unit × EthCLSpecs.Fulu.State}
    (h : (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) = .ok r) :
    ∃ s', Spec.process_epoch_fulu Spec.P Spec.FC o (toSpecState e) = .ok s' := by
  have hb := hpa.base
  have hcm := hpa.committee
  have hvec := fuluVectorLengths_toSpecState hpa e
  obtain ⟨⟨⟨hb0, -, heb, -, hsup⟩, -, hcons⟩, -, -⟩ := hin
  -- The steps before the committee steps, in the reference and in Etheorem.
  obtain ⟨s, hs, hfr⟩ := Spec.epochToCommitteesFulu_total o (toSpecState e) hb0.2.1 hslot hpre.1
    hvec hb0.1 heb hcons hsup.2.2 hrb
  obtain ⟨e13, b13, rfl⟩ := epochToCommitteesFulu_etheorem hpa o ho e hc hs
  have hf13 : Spec.SelFacts o (toSpecState e13) := Spec.SelFacts.of_frame hfr hslot (hsel _ hs)
  rw [processEpoch_eq, ← List.take_append_drop 13 epochSteps,
    b13.run_seq_append (by simp [epochSteps])] at h
  change ((EthCLSpecs.Fulu.processSyncCommitteeUpdates >>= fun _ =>
      EthCLSpecs.Fulu.processProposerLookahead : FuluRun Unit).run (pureState e13) = .ok r) at h
  -- 14. sync committees
  rw [run_bind] at h
  cases h14 : (EthCLSpecs.Fulu.processSyncCommitteeUpdates (StateTransition := FuluRun)).run
      (pureState e13) with
  | error err => rw [h14, except_bind_error] at h; cases h
  | ok p14 =>
  obtain ⟨s14, hs14, f14s, f14v, f14r, -, -⟩ := sync_committee_updates_of_etheorem hb hcm o ho
    hpa.epochsPerSyncCommitteePeriodLt e13 hf13 h14
  obtain ⟨e14, r14, rfl⟩ := process_sync_committee_updates_etheorem hb hcm o ho
    hpa.epochsPerSyncCommitteePeriodLt e13 hs14
  rw [h14] at r14
  cases r14
  rw [h14, except_bind_ok] at h
  have hf14 : Spec.SelFacts o (toSpecState e14) := hf13.congr f14s f14v f14r
  -- 15. proposer lookahead
  obtain ⟨s15, hs15⟩ := proposer_lookahead_of_etheorem hb hcm o ho.hash hsha e14 hf14 h
  refine ⟨s15, ?_⟩
  rw [Spec.process_epoch_fulu_committees, hs, Spec.tot_bind_ok]
  unfold Spec.committeeStepsFulu
  rw [(Spec.process_sync_committee_updates_fulu_sameResultOrBothFail Spec.P o _ Spec.P_sync_pos _).mpr hs14,
    Spec.tot_bind_ok, hs15]

/-- The Lean model of Lighthouse's Fulu epoch and Etheorem's Fulu `processEpoch` give the same
state, or both fail. As `lighthouse_epoch_agrees_etheorem`. `hc` holds the conditions of the
Etheorem Fulu bridge (`FuluEtheoremBridgeConditions`); one of them, `proposerFin`, is an Etheorem divergence:
Etheorem's Fulu selects proposers with the Gloas selection, which fails one pass before the
Electra loop of the pyspec. -/
theorem lighthouse_fulu_epoch_agrees_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    [Spec.PresetCfg.Bounds] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P Spec.FC) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState) (hc : FuluEtheoremBridgeConditions Spec.P o e)
    (hin : Spec.ReachableInvariants (toSpecState e)) (hpre : Spec.AtEpochBoundary (toSpecState e))
    (hslot : (toSpecState e).slot + 8192 < 2 ^ 64) (hrb : Spec.PhysicalLimits (toSpecState e))
    (hsel : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o (toSpecState e) = .ok t →
      Spec.SelectionStateFacts o t) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu o (toSpecState e)) (etheoremProcessEpoch e) := by
  have hlh := Spec.lighthouse_fulu_epoch_sameResultOrBothFail o (toSpecState e) hin hpre
  have hf1 : ∀ s', Spec.process_epoch_lighthouse_fulu o (toSpecState e) = .ok s' →
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ toSpecState e' = s' :=
    fun s' hs' => process_epoch_fulu_etheorem hpa o ho hsha e hc ((hlh s').mp hs')
  intro v
  constructor
  · intro h
    obtain ⟨e', he', rfl⟩ := hf1 v h
    exact etheoremProcessEpoch_of_run he'
  · intro h
    obtain ⟨r, hr, rfl⟩ := run_of_etheoremProcessEpoch h
    obtain ⟨s', hs'⟩ := process_epoch_fulu_of_etheorem hpa o ho hsha e hc hin hpre hslot hrb hsel hr
    have hl := (hlh s').mpr hs'
    obtain ⟨e', he', rfl⟩ := hf1 _ hl
    rw [hr] at he'
    cases he'
    exact hl

end Fulu

end EpochProofs.Etheorem.Fulu
