import EpochProofs.Sanity.Invariants.FuluSteps
import EpochProofs.Sanity.Invariants.Lengths

/-!
# The row lengths invariant for Fulu

`RowsOk` says that `balances`, `inactivity_scores` and both participation lists have one entry
per validator. This file is `Lengths.lean` for the Fulu functions: each Fulu block function
keeps the five row lengths (`LenStep`), and the Fulu `process_epoch` keeps `RowsOk` with the
Gloas epoch lemmas. So `state_transition_fulu` keeps `RowsOk`.
-/

namespace EpochProofs.Spec

namespace FuluLengthsSanity

/-- A successful `if` ran one of its branches. -/
theorem ite_ok {α : Type} {c : Prop} [Decidable c] {t e : SpecM α} {x : α}
    (h : (if c then t else e) = .ok x) : (c ∧ t = .ok x) ∨ (¬ c ∧ e = .ok x) := by
  by_cases hc : c
  · exact .inl ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · exact .inr ⟨hc, by rw [if_neg hc] at h; exact h⟩

/-- A `for` loop in `SpecM` keeps every property that each successful pass keeps. -/
theorem forIn_ok_invariant {α β : Type} (P : β → Prop)
    (f : α → β → SpecM (ForInStep β)) (hf : ∀ a b r, P b → f a b = .ok r → P r.value) :
    ∀ (l : List α) (b b' : β), P b → forIn l b f = .ok b' → P b' := by
  intro l
  induction l with
  | nil => intro b b' hb h; cases h; exact hb
  | cons a as ih =>
    intro b b' hb h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := specM_bind_ok h
    have := hf a b r hb hr
    cases r with
    | done c => cases h; exact this
    | yield c => exact ih c b' this h

/-- A successful `listSet` keeps the length of the list. -/
theorem listSet_ok_length {α : Type} {l l' : List α} {i : Nat} {a : α}
    (h : listSet l i a = .ok l') : l'.length = l.length := by
  unfold listSet at h
  split at h
  · cases h; exact List.length_set
  · cases h

end FuluLengthsSanity

open FuluLengthsSanity

/-- Unfolds the list helpers of a step, then splits its binds, `if`s and `match`es. Each error
branch closes. -/
local macro "len_split" h:ident : tactic => `(tactic| (
  try simp only [increase_balance, decrease_balance, bind_assoc, listSet_bind] at $h:ident
  try simp only [throw, throwThe, MonadExceptOf.throw] at $h:ident
  try simp only [bind, Except.bind, pure, Except.pure] at $h:ident
  repeat' first
    | split at $h:ident
    | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
       rcases ite_ok $h:ident with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩)
  all_goals try contradiction))

/-- Closes `LenStep s s'` from the length facts in the context. -/
local macro "len_close" : tactic => `(tactic| (
  simp only [LenStep, List.length_set, ForInStep.value] at *
  repeat' apply And.intro
  all_goals first | trivial | omega))

/-! ## Block operations -/

/-- The state from the Fulu `compute_exit_epoch_and_update_churn` keeps the row lengths. -/
theorem compute_exit_epoch_and_update_churn_fulu_len (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s : BeaconState) (exit_balance : Gwei) (r : Epoch × BeaconState)
    (h : compute_exit_epoch_and_update_churn_fulu p f total_active_balance s exit_balance = .ok r) :
    LenStep s r.2 := by
  unfold compute_exit_epoch_and_update_churn_fulu at h
  len_split h
  all_goals (cases h; exact LenStep.refl _)

/-- The Fulu `initiate_validator_exit` keeps the row lengths. -/
theorem initiate_validator_exit_fulu_len (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit_fulu p f total_active_balance s index = .ok s') :
    LenStep s s' := by
  unfold initiate_validator_exit_fulu at h
  len_split h
  all_goals
    cases h
    try (have := compute_exit_epoch_and_update_churn_fulu_len p f total_active_balance s _ _
                    ‹compute_exit_epoch_and_update_churn_fulu _ _ _ _ _ = _›)
    len_close

/-- The Fulu `slash_validator` keeps the row lengths. -/
theorem slash_validator_fulu_len (p : Preset) (f : FuluConfig) (s s' : BeaconState)
    (index : ValidatorIndex) (whistleblower_index : Option ValidatorIndex)
    (h : slash_validator_fulu p f s index whistleblower_index = .ok s') : LenStep s s' := by
  unfold slash_validator_fulu at h
  len_split h
  all_goals
    cases h
    try (have := initiate_validator_exit_fulu_len p f _ s _ _
            ‹initiate_validator_exit_fulu _ _ _ _ _ = _›)
    len_close

/-- The Fulu `process_proposer_slashing` keeps the row lengths. -/
theorem process_proposer_slashing_fulu_len (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (proposer_slashing : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s proposer_slashing = .ok s') : LenStep s s' := by
  unfold process_proposer_slashing_fulu at h
  len_split h
  all_goals
    try (have := slash_validator_fulu_len p f _ _ _ _ ‹slash_validator_fulu _ _ _ _ _ = _›)
    len_close

/-- The Fulu `process_attester_slashing` keeps the row lengths. -/
theorem process_attester_slashing_fulu_len (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (attester_slashing : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s attester_slashing = .ok s') : LenStep s s' := by
  unfold process_attester_slashing_fulu at h
  len_split h
  all_goals
    cases h
    refine forIn_ok_invariant (fun r : MProd Bool BeaconState => LenStep s r.snd) _ ?_ _ _ _
      (LenStep.refl s) ‹forIn _ _ _ = _›
    intro _ ⟨_, st⟩ _ hst hb
    len_split hb
    all_goals
      cases hb
      try (have := slash_validator_fulu_len p f _ _ _ _ ‹slash_validator_fulu _ _ _ _ _ = _›)
      try simp only at hst
      len_close

/-- The Fulu `process_voluntary_exit` keeps the row lengths. -/
theorem process_voluntary_exit_fulu_len (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (signed_voluntary_exit : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s signed_voluntary_exit = .ok s') : LenStep s s' := by
  unfold process_voluntary_exit_fulu at h
  len_split h
  all_goals
    try (have := initiate_validator_exit_fulu_len p f _ _ _ _
            ‹initiate_validator_exit_fulu _ _ _ _ _ = _›)
    len_close

/-- The Fulu attestation loop keeps the length of the participation list. -/
theorem process_attestation_loop_fulu_length (p : Preset) (state : BeaconState)
    (participation_flag_indices : List Nat) (attesting_indices : List ValidatorIndex)
    (epoch_participation epoch_participation' : List ParticipationFlags)
    (proposer_reward_numerator : Gwei)
    (h : process_attestation_loop_fulu p state participation_flag_indices attesting_indices
      epoch_participation = .ok (epoch_participation', proposer_reward_numerator)) :
    epoch_participation'.length = epoch_participation.length := by
  unfold process_attestation_loop_fulu at h
  obtain ⟨⟨e, n⟩, hr, h⟩ := specM_bind_ok h
  cases h
  refine forIn_ok_invariant
    (fun r : MProd (List ParticipationFlags) Uint64 => r.fst.length = epoch_participation.length)
    _ ?_ attesting_indices ⟨epoch_participation, 0⟩ _ rfl hr
  intro index ⟨b1, b2⟩ r hb hr
  obtain ⟨⟨e2, n2⟩, hin, hr⟩ := specM_bind_ok hr
  have hlen := forIn_ok_invariant
    (fun x : MProd (List ParticipationFlags) Uint64 => x.fst.length = b1.length)
    _ ?_ _ _ _ rfl hin
  · simp only [bind, Except.bind, pure, Except.pure] at hr
    cases hr
    exact hlen.trans hb
  · intro ⟨_, flag_index⟩ ⟨c1, c2⟩ r hc hr
    simp only [bind, Except.bind, pure, Except.pure] at hr
    repeat' split at hr
    all_goals first
      | contradiction
      | (cases hr; exact hc)
      | (cases hr; exact (listSet_ok_length ‹listSet _ _ _ = _›).trans hc)

/-- The Fulu `process_attestation` keeps the row lengths. -/
theorem process_attestation_fulu_len (p : Preset) (o : Oracle) (s s' : BeaconState)
    (attestation : Attestation) (h : process_attestation_fulu p o s attestation = .ok s') :
    LenStep s s' := by
  unfold process_attestation_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       have hl := process_attestation_loop_fulu_length _ _ _ _ _ _ _
         ‹process_attestation_loop_fulu _ _ _ _ _ = _›
       obtain ⟨hlen, -⟩ := increase_balance_up ‹increase_balance _ _ _ = _›
       first
         | exact ⟨rfl, hlen, rfl, rfl, hl.trans (by simp_all)⟩
         | exact ⟨rfl, hlen, rfl, hl.trans (by simp_all), rfl⟩)

/-- The Fulu `process_withdrawal_request` keeps the row lengths. -/
theorem process_withdrawal_request_fulu_len (p : Preset) (f : FuluConfig) (s s' : BeaconState)
    (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') : LenStep s s' := by
  unfold process_withdrawal_request_fulu at h
  len_split h
  all_goals
    try (cases h)
    try (have := initiate_validator_exit_fulu_len p f _ _ _ _
            ‹initiate_validator_exit_fulu _ _ _ _ _ = _›)
    try (have := compute_exit_epoch_and_update_churn_fulu_len p f _ _ _ _
                   ‹compute_exit_epoch_and_update_churn_fulu _ _ _ _ _ = _›)
    len_close

/-- The state from the Fulu `compute_consolidation_epoch_and_update_churn` keeps the row
lengths. -/
theorem compute_consolidation_epoch_and_update_churn_fulu_len (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s : BeaconState) (consolidation_balance : Gwei)
    (r : Epoch × BeaconState)
    (h : compute_consolidation_epoch_and_update_churn_fulu p f total_active_balance s
      consolidation_balance = .ok r) : LenStep s r.2 := by
  unfold compute_consolidation_epoch_and_update_churn_fulu at h
  len_split h
  all_goals (cases h; exact LenStep.refl _)

set_option maxHeartbeats 1000000 in
/-- The Fulu `process_consolidation_request` keeps the row lengths. -/
theorem process_consolidation_request_fulu_len (p : Preset) (f : FuluConfig) (s s' : BeaconState)
    (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    LenStep s s' := by
  unfold process_consolidation_request_fulu at h
  len_split h
  all_goals
    try (cases h)
    try (have := switch_to_compounding_validator_len p _ _ _
                   ‹switch_to_compounding_validator _ _ _ = _›)
    try (have := compute_consolidation_epoch_and_update_churn_fulu_len p f _ _ _ _
                   ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = _›)
    len_close

/-- The Fulu `process_operations` keeps the row lengths. -/
theorem process_operations_fulu_len (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') : LenStep s s' :=
  process_operations_fulu_inv p o f (LenStep s)
    (fun _ _ _ h' hs => hs.trans (process_proposer_slashing_fulu_len p o f _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_attester_slashing_fulu_len p o f _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_attestation_fulu_len p o _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_voluntary_exit_fulu_len p o f _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_bls_to_execution_change_len p o _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_deposit_request_len _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_withdrawal_request_fulu_len p f _ _ _ h'))
    (fun _ _ _ h' hs => hs.trans (process_consolidation_request_fulu_len p f _ _ _ h'))
    s s' body h (LenStep.refl s)

/-- The Fulu `process_block_header` keeps the row lengths. -/
theorem process_block_header_fulu_len (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') : LenStep s s' := by
  unfold process_block_header_fulu at h
  len_split h
  all_goals (cases h; len_close)

/-- The Fulu `apply_withdrawals` keeps the row lengths. -/
theorem apply_withdrawals_fulu_len :
    ∀ (withdrawals : List Withdrawal) (s s' : BeaconState),
      apply_withdrawals_fulu s withdrawals = .ok s' → LenStep s s'
  | [], s, s', h => by
    cases h
    exact LenStep.refl s
  | w :: rest, s, s', h => by
    unfold apply_withdrawals_fulu at h
    len_split h
    all_goals
      have := apply_withdrawals_fulu_len rest _ _ h
      len_close

/-- The Fulu `process_withdrawals` keeps the row lengths. -/
theorem process_withdrawals_fulu_len (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    LenStep s s' := by
  unfold process_withdrawals_fulu at h
  len_split h
  all_goals
    try (cases h)
    try (have := apply_withdrawals_fulu_len _ _ _ ‹apply_withdrawals_fulu _ _ = _›)
    try (have := update_next_withdrawal_index_len _ _ _ ‹update_next_withdrawal_index _ _ = _›)
    try (have := update_next_withdrawal_validator_index_len p _ _ _
                   ‹update_next_withdrawal_validator_index _ _ _ = _›)
    try simp only [update_pending_partial_withdrawals] at *
    len_close

/-- The Fulu `process_block` keeps `RowsOk`. -/
theorem process_block_fulu_rowsOk (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fs block = .ok fs') (hs : RowsOk fs.state) :
    RowsOk fs'.state :=
  process_block_fulu_inv p o fo f c RowsOk
    (fun _ _ _ h' hs => (process_block_header_fulu_len p o fo _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_withdrawals_fulu_len p _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_randao_len p o _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_eth1_data_len p _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_operations_fulu_len p o f _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_sync_aggregate_len p o _ _ _ h').rowsOk hs)
    fs fs' block h hs

/-! ## Slots and the epoch -/

/-- `process_slot_fulu` keeps the row lengths of the inner state. -/
theorem process_slot_fulu_len (p : Preset) (o : Oracle) (fo : FuluOracle) (fs fs' : FuluState)
    (h : process_slot_fulu p o fo fs = .ok fs') : LenStep fs.state fs'.state := by
  unfold process_slot_fulu at h
  len_split h
  all_goals (cases h; len_close)

/-- The Fulu `process_epoch` keeps `RowsOk`. -/
theorem process_epoch_fulu_rowsOk (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (s s' : BeaconState) (h : process_epoch_fulu p f o s = .ok s') (hs : RowsOk s) :
    RowsOk s' :=
  process_epoch_fulu_inv p f hc o RowsOk
    (fun _ _ h' hs => (process_justification_and_finalization_len p _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_inactivity_updates_len p _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_rewards_and_penalties_len p _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_registry_updates_len p _ _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => (process_slashings_len p _ _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_eth1_data_reset_len p _ _ h').rowsOk hs)
    (fun _ _ _ h' hs => process_pending_deposits_rowsOk p o _ _ _ h' hs)
    (fun _ _ h' hs => (process_pending_consolidations_len p _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_effective_balance_updates_len p _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_slashings_reset_len p _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_randao_mixes_reset_len p _ _ h').rowsOk hs)
    (fun _ _ h' hs => (process_historical_summaries_update_len p o _ _ h').rowsOk hs)
    (fun _ hs => process_participation_flag_updates_rowsOk _ hs)
    (fun _ _ h' hs => by
      obtain ⟨_, _, rfl⟩ := process_sync_committee_updates_fulu_shape p o _ _ h'
      exact hs)
    (fun _ _ h' hs => by
      obtain ⟨_, rfl⟩ := process_proposer_lookahead_fulu_shape p o _ _ h'
      exact hs)
    s s' h hs

/-- `process_slots_fulu` with the Fulu `process_epoch` keeps `RowsOk`. -/
theorem process_slots_fulu_rowsOk (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (fo : FuluOracle) (fs fs' : FuluState) (slot : Slot)
    (h : process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot = .ok fs')
    (hs : RowsOk fs.state) : RowsOk fs'.state :=
  process_slots_fulu_inv p o fo (process_epoch_fulu p f o) RowsOk
    (fun _ _ h' hs => (process_slot_fulu_len p o fo _ _ h').rowsOk hs)
    (fun _ _ h' hs => process_epoch_fulu_rowsOk p f hc o _ _ h' hs)
    (fun _ _ hs => hs) fs fs' slot hs h

/-- `state_transition_fulu` keeps `RowsOk`. -/
theorem state_transition_fulu_rowsOk (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool) (hs : RowsOk fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    RowsOk fs'.state :=
  state_transition_fulu_inv p o fo f c RowsOk
    (fun _ _ _ h' hs => process_slots_fulu_rowsOk p f hc o fo _ _ _ h' hs)
    (fun _ _ _ h' hs => process_block_fulu_rowsOk p o fo f c _ _ _ h' hs)
    fs fs' signed_block validate_result hs h

end EpochProofs.Spec
