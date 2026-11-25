import EpochProofs.Sanity.Invariants.FuluSteps
import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Spec.PresetBounds

/-!
# Frame lemmas for the epoch steps

The steps of the epoch do not write the deposit indices, the builder pending withdrawals, the
historical summaries (`QFrame`) and the pending deposits (`PFrame`). `Etheorem/Conditions.lean`
uses these lemmas. They do not use Etheorem.
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
    (fun r : Prod Uint64 (Prod Uint64 (Prod (List PendingDeposit) (Prod Bool BeaconState))) =>
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
  have hP := forIn_ok_invariant (fun r : Prod Nat BeaconState => PFrame s r.snd) _ ?_
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
