import EpochProofs.Etheorem.Epoch
import EpochProofs.Spec.PresetBounds

/-!
# The Etheorem step conditions from the state at the epoch start

`process_epoch_etheorem` takes `EtheoremEpochConds e`: facts about the Etheorem state right
before some steps. This file proves most of them from facts about the reference state at the
start of the epoch, on mainnet.

- Proved from the reachable-state invariants (`EpochInputOk''`): the finalized epoch is below
  `FAR_FUTURE_EPOCH` before the registry update, and the registry lists have equal lengths
  before the pending deposits and the pending consolidations.
- Moved to the epoch start by frame lemmas (`EpochCondsIn`): room for the pending deposits,
  room in the builder withdrawals and in the historical summaries (F6). The steps before each of these reads do not write the fields it reads.
- Kept as they are (`SelectionsFull`): Etheorem's balance weighted selections return all their
  items (F3). These are facts about Etheorem's own output.

F2 is fixed on the Etheorem fork that this project requires (`eserilev/etheorem`, branch
`formalhouse-pin`). That fork has no eth1 bridge check in `process_pending_deposits`, as in the
pyspec since v1.7.0-alpha.9, so no bridge condition is needed.
-/

namespace EpochProofs.Spec

/-! ## Frame lemmas for the epoch steps -/

/-- The eth1 deposit index, the deposit request start index, the builder pending withdrawals
and the historical summaries do not change. -/
def QFrame (s s' : BeaconState) : Prop :=
  s'.eth1_deposit_index = s.eth1_deposit_index ∧
    s'.deposit_requests_start_index = s.deposit_requests_start_index ∧
    s'.builder_pending_withdrawals = s.builder_pending_withdrawals ∧
    s'.historical_summaries = s.historical_summaries

/-- `QFrame`, and the pending deposits do not change. -/
def PFrame (s s' : BeaconState) : Prop :=
  QFrame s s' ∧ s'.pending_deposits = s.pending_deposits

theorem QFrame.refl (s : BeaconState) : QFrame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem QFrame.trans {s1 s2 s3 : BeaconState} (h12 : QFrame s1 s2) (h23 : QFrame s2 s3) :
    QFrame s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
    h23.2.2.2.trans h12.2.2.2⟩

theorem PFrame.refl (s : BeaconState) : PFrame s s := ⟨QFrame.refl s, rfl⟩

theorem PFrame.trans {s1 s2 s3 : BeaconState} (h12 : PFrame s1 s2) (h23 : PFrame s2 s3) :
    PFrame s1 s3 :=
  ⟨h12.1.trans h23.1, h23.2.trans h12.2⟩

/-- Splits the binds, `if`s and `match`es of a step that does not write the frame fields, and
closes each success branch by `rfl`. -/
local macro "pf_tac" h:ident : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure] at $h:ident
  repeat' split at $h:ident
  all_goals first
    | contradiction
    | (cases $h:ident; first | exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | assumption)))

/-- A `for` loop in `SpecM` keeps every property that each successful pass keeps. -/
private theorem forIn_ok_invariant {α β : Type} (P : β → Prop)
    (f : α → β → SpecM (ForInStep β)) (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b b' : β), P b → forIn l b f = .ok b' → P b' := by
  intro l
  induction l with
  | nil => intro b b' hb h; cases h; exact hb
  | cons a rest ih =>
    intro b b' hb h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := specM_bind_ok h
    have := hf a b r hb hr
    cases r with
    | done c => cases h; exact this
    | yield c => exact ih c b' this h

theorem weigh_justification_and_finalization_pframe (p : Preset) (s s' : BeaconState)
    (total_active_balance previous_epoch_target_balance current_epoch_target_balance : Gwei)
    (h : weigh_justification_and_finalization p s total_active_balance
      previous_epoch_target_balance current_epoch_target_balance = .ok s') : PFrame s s' := by
  unfold weigh_justification_and_finalization at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨t1, ht1, h⟩ := specM_bind_ok h
  have q1 : PFrame s t1 := by pf_tac ht1
  obtain ⟨t2, ht2, h⟩ := specM_bind_ok h
  have q2 : PFrame s t2 := by pf_tac ht2
  obtain ⟨t3, ht3, h⟩ := specM_bind_ok h
  have q3 : PFrame s t3 := by pf_tac ht3
  obtain ⟨t4, ht4, h⟩ := specM_bind_ok h
  have q4 : PFrame s t4 := by pf_tac ht4
  obtain ⟨t5, ht5, h⟩ := specM_bind_ok h
  have q5 : PFrame s t5 := by pf_tac ht5
  pf_tac h

theorem process_justification_and_finalization_pframe (p : Preset) (s s' : BeaconState)
    (h : process_justification_and_finalization p s = .ok s') : PFrame s s' := by
  unfold process_justification_and_finalization at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact PFrame.refl _)
    | exact weigh_justification_and_finalization_pframe p _ _ _ _ _ h

theorem process_inactivity_updates_pframe (p : Preset) (s s' : BeaconState)
    (h : process_inactivity_updates p s = .ok s') : PFrame s s' := by
  unfold process_inactivity_updates at h
  pf_tac h

theorem process_rewards_and_penalties_pframe (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_rewards_and_penalties p total_active_balance s = .ok s') :
    PFrame s s' := by
  unfold process_rewards_and_penalties at h
  pf_tac h

theorem compute_exit_epoch_and_update_churn_pframe (p : Preset) (total_active_balance : Gwei)
    (s : BeaconState) (exit_balance : Gwei) (r : Epoch × BeaconState)
    (h : compute_exit_epoch_and_update_churn p total_active_balance s exit_balance = .ok r) :
    PFrame s r.2 := by
  unfold compute_exit_epoch_and_update_churn at h
  pf_tac h

theorem initiate_validator_exit_pframe (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit p total_active_balance s index = .ok s') : PFrame s s' := by
  unfold initiate_validator_exit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩)
    | (cases h
       exact compute_exit_epoch_and_update_churn_pframe p total_active_balance s _ _
         ‹_ = Except.ok _›)

theorem process_registry_updates_pframe (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_registry_updates p total_active_balance s = .ok s') :
    PFrame s s' := by
  unfold process_registry_updates at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨r, hr, h⟩ := specM_bind_ok h
  cases h
  refine forIn_ok_invariant (PFrame s) _ ?_ _ s _ (PFrame.refl s) hr
  intro index st r hst hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | contradiction
    | (cases hb; exact hst)
    | (cases hb
       exact hst.trans (initiate_validator_exit_pframe p total_active_balance _ _ _
         ‹initiate_validator_exit _ _ _ _ = _›))

theorem process_slashings_pframe (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_slashings p total_active_balance s = .ok s') :
    PFrame s s' := by
  unfold process_slashings at h
  pf_tac h

theorem process_eth1_data_reset_pframe (p : Preset) (s s' : BeaconState)
    (h : process_eth1_data_reset p s = .ok s') : PFrame s s' := by
  unfold process_eth1_data_reset at h
  pf_tac h

theorem add_validator_to_registry_pframe (p : Preset) (s s' : BeaconState)
    (pubkey : BLSPubkey) (withdrawal_credentials : Bytes32) (amount : Gwei)
    (h : add_validator_to_registry p s pubkey withdrawal_credentials amount = .ok s') :
    PFrame s s' := by
  unfold add_validator_to_registry at h
  pf_tac h

theorem apply_pending_deposit_pframe (p : Preset) (o : Oracle) (s s' : BeaconState)
    (deposit : PendingDeposit) (h : apply_pending_deposit p o s deposit = .ok s') :
    PFrame s s' := by
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩)
    | exact add_validator_to_registry_pframe p s s' _ _ _ h

/-- `process_pending_deposits` writes the pending deposits, but keeps `QFrame`. -/
theorem process_pending_deposits_qframe (p : Preset) (o : Oracle)
    (total_active_balance : Gwei) (s s' : BeaconState)
    (h : process_pending_deposits p total_active_balance (apply_pending_deposit p o) s = .ok s') :
    QFrame s s' := by
  unfold process_pending_deposits at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, _, _, _, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_invariant
    (fun r : MProd (List PendingDeposit) (MProd Bool (MProd Uint64 (MProd Uint64 BeaconState))) =>
      QFrame s r.2.2.2.2) _ ?_ _ _ _ (QFrame.refl s) hr
  · simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | contradiction
      | (cases h; exact hP)
  · intro _ ⟨_, _, _, _, _⟩ r hst hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hst)
      | (cases hb
         exact hst.trans (apply_pending_deposit_pframe p o _ _ _
           ‹apply_pending_deposit _ _ _ _ = _›).1)

theorem process_pending_consolidations_pframe (p : Preset) (s s' : BeaconState)
    (h : process_pending_consolidations p s = .ok s') : PFrame s s' := by
  unfold process_pending_consolidations at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_invariant (fun r : MProd Nat BeaconState => PFrame s r.snd) _ ?_
    _ _ _ (PFrame.refl s) hr
  · cases h
    exact hP
  · intro _ ⟨_, _⟩ r hst hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hst)

/-- `process_builder_pending_payments` writes the builder withdrawals, but keeps the
historical summaries. -/
theorem process_builder_pending_payments_summaries (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_builder_pending_payments p total_active_balance s = .ok s') :
    s'.historical_summaries = s.historical_summaries := by
  unfold process_builder_pending_payments at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; rfl)

theorem process_effective_balance_updates_pframe (p : Preset) (s s' : BeaconState)
    (h : process_effective_balance_updates p s = .ok s') : PFrame s s' := by
  unfold process_effective_balance_updates at h
  pf_tac h

theorem process_slashings_reset_pframe (p : Preset) (s s' : BeaconState)
    (h : process_slashings_reset p s = .ok s') : PFrame s s' := by
  unfold process_slashings_reset at h
  pf_tac h

theorem process_randao_mixes_reset_pframe (p : Preset) (s s' : BeaconState)
    (h : process_randao_mixes_reset p s = .ok s') : PFrame s s' := by
  unfold process_randao_mixes_reset at h
  pf_tac h

end EpochProofs.Spec

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Generic

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]

/-! ## Facts about the map -/

/-- `RowsOk` of the mapped state gives `LensEq`. -/
theorem lensEq_of_rowsOk {e : EState} (h : Spec.RowsOk (absEState e)) : LensEq e := by
  obtain ⟨r1, r2, r3, r4⟩ := h
  simp only [absEState_balances, absEState_validators, absEState_inactivity_scores,
    absEState_previous_epoch_participation, absEState_current_epoch_participation,
    length_map_toList] at r1 r2 r3 r4
  exact ⟨r1, by simpa using r3, by simpa using r4, r2⟩

/-! ## The conditions at the epoch start -/

/-- Facts about the state at the epoch start. The steps before each read do not write these
fields, so each fact still holds when its step reads it.

- `depositRoom`: Etheorem's registry limit `2^40` has room for `MAX_PENDING_DEPOSITS_PER_EPOCH`
  new validators, the most that one epoch adds. Etheorem drops a new validator past this limit
  (F10). Beta.4 has no registry limit. Lighthouse keeps the `2^40` limit.
- `builderRoom`: the builder withdrawals have room for `SLOTS_PER_EPOCH` more items under
  Etheorem's alpha.11 limit (F6). Beta.4 has no limit.

The historical summaries room is not here: beta.4 keeps the `HISTORICAL_ROOTS_LIMIT` cap, so it
is a spec condition. `process_epoch_etheorem_in` takes it as `hhist`. -/
structure EpochCondsIn (e : EState) : Prop where
  depositRoom : (absEState e).validators.length +
    EthCLSpecs.Gloas.Const.maxPendingDepositsPerEpoch ≤ EthCLSpecs.Gloas.Const.validatorRegistryLimit
  builderRoom : (absEState e).builder_pending_withdrawals.length +
      EthCLSpecs.Gloas.Const.slotsPerEpoch ≤ EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit

variable [HasherTag] [CryptoBackend]

/-- Etheorem's balance weighted selections return all their items (F3). Etheorem stops each
selection after `10^7` passes. The pyspec has no such bound. -/
structure SelectionsFull (e : EState) : Prop where
  syncFull : ∀ e', Before 14 e e' → SyncSelectionFull e'
  proposersFull : ∀ e', Before 15 e e' → ProposerSelectionsFull e'
    (EthCLSpecs.Gloas.currentEpochOf (pureState e') + EthCLSpecs.Gloas.Const.minSeedLookahead + 1)
  ptcFull : ∀ e', Before 16 e e' → PtcSelectionsFull e'

theorem qualifyingBuilderWithdrawals_length (e : EState) :
    (qualifyingBuilderWithdrawals e).length ≤ EthCLSpecs.Gloas.Const.slotsPerEpoch := by
  unfold qualifyingBuilderWithdrawals
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The reference `process_epoch` equals Etheorem's Gloas `processEpoch` on mainnet, from facts
about the state at the epoch start.

`hb0` and `hslot` hold at each epoch boundary of a reachable run (`EpochInputOk''`). They give
the finalized epoch condition and the equal list lengths. `hin` holds the facts that frame
lemmas carry to the step that reads them. `hhist`: the historical summaries are below
`HISTORICAL_ROOTS_LIMIT`, a cap that beta.4 keeps. `hsel` holds the facts about Etheorem's
output. -/
theorem process_epoch_etheorem_in [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : EpochPresetAgrees Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hb0 : Spec.BoundaryOk (absEState e)) (hslot : (absEState e).slot < 2 ^ 64)
    (hin : EpochCondsIn e)
    (hhist : (absEState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hsel : SelectionsFull e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch Spec.P o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  have hp := hpa
  have hpp := hp.passes
  have hb := hp.base
  unfold Spec.process_epoch at h
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
  have hfin : (absEState e3).finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH := by
    have hf := j1.2.1
    rw [← c2.2.1, ← c3.2.1, ← c2.1, ← c3.1] at hf
    have hs : (absEState e3).slot = (absEState e).slot := by rw [c3.1, c2.1, sl1]
    rw [hs] at hf
    have h6 := Spec.P_epoch_le_div6 (absEState e).slot
    have hslot' : @LT.lt Nat _ (absEState e).slot (2 ^ 64) := hslot
    have hlt : @LT.lt Nat _ ((absEState e).slot / Spec.P.SLOTS_PER_EPOCH) (2 ^ 64 - 1) := by omega
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
  have F6 : Spec.PFrame (absEState e) (absEState e6) :=
    f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6))))
  have L6 : Spec.LenStep (absEState e) (absEState e6) :=
    l1.trans (l2.trans (l3.trans (l4.trans (l5.trans l6))))
  have rows6 : Spec.RowsOk (absEState e6) := L6.rowsOk hb0.2.1
  have hroom : e6.validators.val.size + EthCLSpecs.Gloas.Const.maxPendingDepositsPerEpoch ≤
      EthCLSpecs.Gloas.Const.validatorRegistryLimit := by
    have hv := L6.1
    have hr := hin.depositRoom
    simp only [absEState_validators, length_map_toList] at hv hr
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
    simp only [absEState_balances, absEState_validators, length_map_toList] at this
    exact this
  obtain ⟨s8, h8, h⟩ := Spec.specM_bind_ok h
  have f8 := Spec.process_pending_consolidations_pframe _ _ _ h8
  obtain ⟨e8, r8, rfl⟩ := process_pending_consolidations_etheorem hb e7 hlens7 h8
  have b8 : StepsOk (epochSteps.take 8) e e8 := b7.snoc r8
  -- 9. builder pending payments
  have Q8 : Spec.QFrame (absEState e) (absEState e8) := F6.1.trans (q7.trans f8.1)
  have hbroom : e8.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e8).length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit := by
    have hw := congrArg List.length Q8.2.2.1
    have hr := hin.builderRoom
    have hq := qualifyingBuilderWithdrawals_length e8
    simp only [absEState_builder_pending_withdrawals, length_map_toList] at hw hr
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
    have heq : (absEState e12).historical_summaries = (absEState e).historical_summaries := by
      rw [f12.1.2.2.2, f11.1.2.2.2, f10.1.2.2.2, hs9, Q8.2.2.2]
    have hw := congrArg List.length heq
    have hr := hhist
    simp only [absEState_historical_summaries, length_map_toList] at hw hr
    omega
  obtain ⟨s13, h13, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e13, r13, rfl⟩ :=
    historical_summaries_update_etheorem hb hp.tail ho e12 hsroom h13
  have b13 : StepsOk (epochSteps.take 13) e e13 := b12.snoc r13
  -- 14. participation flags
  obtain ⟨e14, r14, h14⟩ := participation_flag_updates_etheorem e13
  have b14 : StepsOk (epochSteps.take 14) e e14 := b13.snoc r14
  rw [← h14] at h
  -- 15. sync committees
  obtain ⟨s15, h15, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e15, r15, rfl⟩ := process_sync_committee_updates_etheorem hb hp.committee o ho
    hp.epochsPerSyncCommitteePeriodLt e14 (hsel.syncFull e14 b14) h15
  have b15 : StepsOk (epochSteps.take 15) e e15 := b14.snoc r15
  -- 16. proposer lookahead
  obtain ⟨s16, h16, h⟩ := Spec.specM_bind_ok h
  obtain ⟨e16, r16, rfl⟩ := process_proposer_lookahead_etheorem hb hp.committee o ho.hash hsha
    e15 (hsel.proposersFull e15 b15) h16
  have b16 : StepsOk (epochSteps.take 16) e e16 := b15.snoc r16
  -- 17. PTC window
  obtain ⟨e17, r17, rfl⟩ := process_ptc_window_etheorem hb hp.committee o ho.hash hsha e16
    (hsel.ptcFull e16 b16) h
  have b17 : StepsOk epochSteps e e17 := b16.snoc r17
  exact ⟨e17, by rw [processEpoch_eq]; exact b17.run_seq, rfl⟩

/-- Lighthouse's epoch processing equals Etheorem's Gloas `processEpoch` at each epoch boundary
of a reachable run, on mainnet.

`hin` is the fact that `reachable_state_transition_sameOk'''` proves at each epoch boundary.
The conditions that remain:
- `hcond`: room in the registry for the new validators of one epoch (F10), and room in the
  builder withdrawals (F6). Each is a fact about the epoch start state.
- `hhist`: the historical summaries are below `HISTORICAL_ROOTS_LIMIT`. Beta.4 keeps this cap.
- `hsel`: Etheorem's balance weighted selections return all their items (F3).
- `ho`, `hsha`: the oracle is Etheorem's hash and BLS functions, and SHA-256 returns 32 bytes. -/
theorem lighthouse_epoch_etheorem_reachable [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : EpochPresetAgrees Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e)) (hcond : EpochCondsIn e)
    (hhist : (absEState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hsel : SelectionsFull e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_full o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  obtain ⟨⟨⟨hb, hslot, heb, hexit, hsup⟩, _, hcons⟩, _, hvalid⟩ := hin
  have hsame := Spec.process_epoch_lh_full_sameOk' o (absEState e) hb hslot heb hexit hsup hvalid
    hcons
  exact process_epoch_etheorem_in hpa o ho hsha e hb hslot hcond hhist hsel ((hsame s').mp h)

end Generic

end EpochProofs.Etheorem
