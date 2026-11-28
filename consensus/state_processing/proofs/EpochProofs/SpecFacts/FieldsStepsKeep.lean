import EpochProofs.Invariants.FuluSteps
import EpochProofs.Invariants.TotalityFulu
import EpochProofs.Spec.PresetBounds

/-!
# The steps before the committee steps keep the committee windows

The steps of `process_epoch` before the committee steps do not write the proposer lookahead and the
PTC window (`SameCommitteeWindows`).
-/

namespace EpochProofs.Spec

/-- The two states have the same proposer lookahead and the same PTC window. -/
def SameCommitteeWindows (s s' : BeaconState) : Prop :=
  s'.proposer_lookahead = s.proposer_lookahead ∧ s'.ptc_window = s.ptc_window

theorem SameCommitteeWindows.refl (s : BeaconState) : SameCommitteeWindows s s := ⟨rfl, rfl⟩

theorem SameCommitteeWindows.trans {s1 s2 s3 : BeaconState} (h12 : SameCommitteeWindows s1 s2)
    (h23 : SameCommitteeWindows s2 s3) : SameCommitteeWindows s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

/-- Splits the binds, `if`s and `match`es of a step that does not write the two fields, and
closes each success branch by `rfl`. -/
local macro "windows_tac" h:ident : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure] at $h:ident
  repeat' split at $h:ident
  all_goals first
    | contradiction
    | (cases $h:ident; first | exact ⟨rfl, rfl⟩ | assumption)))

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

theorem weigh_justification_and_finalization_windows (p : Preset) (s s' : BeaconState)
    (total_active_balance previous_epoch_target_balance current_epoch_target_balance : Gwei)
    (h : weigh_justification_and_finalization p s total_active_balance
      previous_epoch_target_balance current_epoch_target_balance = .ok s') :
    SameCommitteeWindows s s' := by
  unfold weigh_justification_and_finalization at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨t1, ht1, h⟩ := specM_bind_ok h
  have q1 : SameCommitteeWindows s t1 := by windows_tac ht1
  obtain ⟨t2, ht2, h⟩ := specM_bind_ok h
  have q2 : SameCommitteeWindows s t2 := by windows_tac ht2
  obtain ⟨t3, ht3, h⟩ := specM_bind_ok h
  have q3 : SameCommitteeWindows s t3 := by windows_tac ht3
  obtain ⟨t4, ht4, h⟩ := specM_bind_ok h
  have q4 : SameCommitteeWindows s t4 := by windows_tac ht4
  obtain ⟨t5, ht5, h⟩ := specM_bind_ok h
  have q5 : SameCommitteeWindows s t5 := by windows_tac ht5
  windows_tac h

theorem process_justification_and_finalization_windows (p : Preset) (s s' : BeaconState)
    (h : process_justification_and_finalization p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_justification_and_finalization at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact SameCommitteeWindows.refl _)
    | exact weigh_justification_and_finalization_windows p _ _ _ _ _ h

theorem process_inactivity_updates_windows (p : Preset) (s s' : BeaconState)
    (h : process_inactivity_updates p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_inactivity_updates at h
  windows_tac h

theorem process_rewards_and_penalties_windows (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_rewards_and_penalties p total_active_balance s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_rewards_and_penalties at h
  windows_tac h

theorem compute_exit_epoch_and_update_churn_windows (p : Preset) (total_active_balance : Gwei)
    (s : BeaconState) (exit_balance : Gwei) (r : Epoch × BeaconState)
    (h : compute_exit_epoch_and_update_churn p total_active_balance s exit_balance = .ok r) :
    SameCommitteeWindows s r.2 := by
  unfold compute_exit_epoch_and_update_churn at h
  windows_tac h

theorem initiate_validator_exit_windows (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit p total_active_balance s index = .ok s') :
    SameCommitteeWindows s s' := by
  unfold initiate_validator_exit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl⟩)
    | (cases h
       exact compute_exit_epoch_and_update_churn_windows p total_active_balance s _ _
         ‹_ = Except.ok _›)

theorem process_registry_updates_windows (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_registry_updates p total_active_balance s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_registry_updates at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨r, hr, h⟩ := specM_bind_ok h
  cases h
  refine forIn_ok_invariant (SameCommitteeWindows s) _ ?_ _ s _ (SameCommitteeWindows.refl s) hr
  intro index st r hst hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | contradiction
    | (cases hb; exact hst)
    | (cases hb
       exact hst.trans (initiate_validator_exit_windows p total_active_balance _ _ _
         ‹initiate_validator_exit _ _ _ _ = _›))

theorem process_slashings_windows (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_slashings p total_active_balance s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_slashings at h
  windows_tac h

theorem process_eth1_data_reset_windows (p : Preset) (s s' : BeaconState)
    (h : process_eth1_data_reset p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_eth1_data_reset at h
  windows_tac h

theorem add_validator_to_registry_windows (p : Preset) (s s' : BeaconState)
    (pubkey : BLSPubkey) (withdrawal_credentials : Bytes32) (amount : Gwei)
    (h : add_validator_to_registry p s pubkey withdrawal_credentials amount = .ok s') :
    SameCommitteeWindows s s' := by
  unfold add_validator_to_registry at h
  windows_tac h

theorem apply_pending_deposit_windows (p : Preset) (o : Oracle) (s s' : BeaconState)
    (deposit : PendingDeposit) (h : apply_pending_deposit p o s deposit = .ok s') :
    SameCommitteeWindows s s' := by
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl⟩)
    | exact add_validator_to_registry_windows p s s' _ _ _ h

theorem process_pending_deposits_windows (p : Preset) (o : Oracle)
    (total_active_balance : Gwei) (s s' : BeaconState)
    (h : process_pending_deposits p total_active_balance (apply_pending_deposit p o) s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_pending_deposits at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, _, _, _, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_invariant
    (fun r : Prod Uint64 (Prod Uint64 (Prod (List PendingDeposit) (Prod Bool BeaconState))) =>
      SameCommitteeWindows s r.2.2.2.2) _ ?_ _ _ _ (SameCommitteeWindows.refl s) hr
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
         exact hst.trans (apply_pending_deposit_windows p o _ _ _
           ‹apply_pending_deposit _ _ _ _ = _›))

theorem process_pending_consolidations_windows (p : Preset) (s s' : BeaconState)
    (h : process_pending_consolidations p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_pending_consolidations at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_invariant (fun r : Prod Nat BeaconState => SameCommitteeWindows s r.snd) _ ?_
    _ _ _ (SameCommitteeWindows.refl s) hr
  · cases h
    exact hP
  · intro _ ⟨_, _⟩ r hst hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hst)

theorem process_builder_pending_payments_windows (p : Preset) (total_active_balance : Gwei)
    (s s' : BeaconState) (h : process_builder_pending_payments p total_active_balance s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_builder_pending_payments at h
  windows_tac h

theorem process_effective_balance_updates_windows (p : Preset) (s s' : BeaconState)
    (h : process_effective_balance_updates p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_effective_balance_updates at h
  windows_tac h

theorem process_slashings_reset_windows (p : Preset) (s s' : BeaconState)
    (h : process_slashings_reset p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_slashings_reset at h
  windows_tac h

theorem process_randao_mixes_reset_windows (p : Preset) (s s' : BeaconState)
    (h : process_randao_mixes_reset p s = .ok s') : SameCommitteeWindows s s' := by
  unfold process_randao_mixes_reset at h
  windows_tac h

theorem process_historical_summaries_update_windows (p : Preset) (o : Oracle)
    (s s' : BeaconState) (h : process_historical_summaries_update p o s = .ok s') :
    SameCommitteeWindows s s' := by
  unfold process_historical_summaries_update at h
  windows_tac h

/-- The Gloas steps before the committee steps keep the committee windows. -/
theorem epochBeforeCommitteeSteps_windows (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : epochBeforeCommitteeSteps p o s = .ok s') : SameCommitteeWindows s s' := by
  unfold epochBeforeCommitteeSteps at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  obtain ⟨s8, h8, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  obtain ⟨s13, h13, h⟩ := specM_bind_ok h
  cases h
  exact (process_justification_and_finalization_windows _ _ _ h1).trans <|
    (process_inactivity_updates_windows _ _ _ h2).trans <|
    (process_rewards_and_penalties_windows _ _ _ _ h3).trans <|
    (process_registry_updates_windows _ _ _ _ h4).trans <|
    (process_slashings_windows _ _ _ _ h5).trans <|
    (process_eth1_data_reset_windows _ _ _ h6).trans <|
    (process_pending_deposits_windows _ _ _ _ _ h7).trans <|
    (process_pending_consolidations_windows _ _ _ h8).trans <|
    (process_builder_pending_payments_windows _ _ _ _ h9).trans <|
    (process_effective_balance_updates_windows _ _ _ h10).trans <|
    (process_slashings_reset_windows _ _ _ h11).trans <|
    (process_randao_mixes_reset_windows _ _ _ h12).trans <|
    (process_historical_summaries_update_windows _ _ _ _ h13).trans ⟨rfl, rfl⟩

/-- The Fulu steps before the committee steps keep the committee windows. -/
theorem epochBeforeCommitteeStepsFulu_windows [CurrentPreset] [CurrentFuluConfig] [CurrentFuluConfig.Valid] (o : Oracle)
    (s s' : BeaconState) (h : epochBeforeCommitteeStepsFulu P FC o s = .ok s') :
    SameCommitteeWindows s s' := by
  rw [epochBeforeCommitteeStepsFulu_parts] at h
  unfold specFourStepsFulu epochRestToCommitteesFulu at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s5, hfour, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, hfour⟩ := specM_bind_ok hfour
  obtain ⟨_, -, hfour⟩ := specM_bind_ok hfour
  obtain ⟨s3, h3, hfour⟩ := specM_bind_ok hfour
  obtain ⟨_, -, hfour⟩ := specM_bind_ok hfour
  obtain ⟨s4, h4, hfour⟩ := specM_bind_ok hfour
  obtain ⟨_, -, h5⟩ := specM_bind_ok hfour
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  obtain ⟨s8, h8, h⟩ := specM_bind_ok h
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  cases h
  exact (process_justification_and_finalization_windows _ _ _ h1).trans <|
    (process_inactivity_updates_windows _ _ _ h2).trans <|
    (process_rewards_and_penalties_windows _ _ _ _ h3).trans <|
    (process_registry_updates_windows _ _ _ _ h4).trans <|
    (process_slashings_windows _ _ _ _ h5).trans <|
    (process_eth1_data_reset_windows _ _ _ h6).trans <|
    (process_pending_deposits_windows _ _ _ _ _ h7).trans <|
    (process_pending_consolidations_windows _ _ _ h8).trans <|
    (process_effective_balance_updates_windows _ _ _ h9).trans <|
    (process_slashings_reset_windows _ _ _ h10).trans <|
    (process_randao_mixes_reset_windows _ _ _ h11).trans <|
    (process_historical_summaries_update_windows _ _ _ _ h12).trans ⟨rfl, rfl⟩

end EpochProofs.Spec
