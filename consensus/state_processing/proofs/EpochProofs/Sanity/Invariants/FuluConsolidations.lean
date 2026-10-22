import EpochProofs.Sanity.Invariants.FuluPubkeys
import EpochProofs.Sanity.Invariants.ConsolidationIndices

/-!
# Pending consolidations point at existing validators, for Fulu

This file is `ConsolidationIndices.lean` for the Fulu functions. Most Fulu steps keep the
queue of pending consolidations and the number of validators (`CStep`). A Fulu consolidation
request appends a consolidation whose indices come from the pubkey list (`RStep`). The Fulu
`process_epoch` keeps `ConsolidationsInRange` with the Gloas epoch lemmas. So
`state_transition_fulu` keeps `ConsolidationsInRange`.
-/

namespace EpochProofs.Spec

open FuluLengthsSanity

/-- Unfolds the list helpers of a step, then splits its binds, `if`s and `match`es. Each error
branch closes. -/
local macro "c_split" h:ident : tactic => `(tactic| (
  try simp only [increase_balance, decrease_balance, bind_assoc, listSet_bind] at $h:ident
  try simp only [throw, throwThe, MonadExceptOf.throw] at $h:ident
  try simp only [bind, Except.bind, pure, Except.pure] at $h:ident
  repeat' first
    | split at $h:ident
    | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
       rcases ite_ok $h:ident with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩)
  all_goals try contradiction))

/-- Splits the binds and `if`s of a successful run without `simp`. -/
local macro "peel_ok" h:ident : tactic => `(tactic| repeat' first
  | (guard_hyp $h:ident : ((_ : SpecM _) >>= _) = _
     obtain ⟨_, hx, $h:ident⟩ := specM_bind_ok $h
     try (guard_hyp hx : (throw _ : SpecM _) = _; cases hx))
  | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _;
     rcases ite_ok $h with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩))

/-- Closes `CStep s s'` from the `CStep` facts in the context. -/
local macro "c_close" : tactic => `(tactic| (
  first
    | exact ⟨rfl, rfl⟩
    | exact ⟨rfl, List.length_set⟩
    | exact ‹CStep _ _›
    | exact ⟨(‹CStep _ _›).1, (‹CStep _ _›).2⟩
    | exact ⟨(‹CStep _ _›).1, List.length_set.trans (‹CStep _ _›).2⟩))

/-! ## Block operations -/

/-- The Fulu `initiate_validator_exit` keeps the queue and the registry size. -/
theorem initiate_validator_exit_fulu_cstep (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (tab : Gwei) (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit_fulu p f tab s index = .ok s') : CStep s s' := by
  rw [initiate_validator_exit_fulu_eq p f hc] at h
  exact initiate_validator_exit_cstep p _ s s' index h

/-- The Fulu `slash_validator` keeps the queue and the registry size. -/
theorem slash_validator_fulu_cstep (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (index : ValidatorIndex) (whistleblower_index : Option ValidatorIndex)
    (h : slash_validator_fulu p f s index whistleblower_index = .ok s') : CStep s s' := by
  have hlen := (slash_validator_fulu_ok p f hc s s' index whistleblower_index h).2.1
  unfold slash_validator_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc] at h
  obtain ⟨epoch, -, h⟩ := specM_bind_ok h
  obtain ⟨v0, hv0, h⟩ := specM_bind_ok h
  obtain ⟨s1, hs1, h⟩ := SlashingsSanity.bind_if_ok h
  obtain ⟨tab, hs1⟩ := slash_validator_fulu_initiate_ok p f s s1 index v0 hv0 hs1
  have c1 := initiate_validator_exit_cstep p tab s s1 index hs1
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨c1.1, hlen⟩)

/-- The Fulu `process_proposer_slashing` keeps the queue and the registry size. -/
theorem process_proposer_slashing_fulu_cstep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') : CStep s s' := by
  obtain ⟨_, _, -, -, -, hsl⟩ := process_proposer_slashing_fulu_ok p o f s s' ps h
  exact slash_validator_fulu_cstep p f hc s s' _ none hsl

/-- The Fulu `process_attester_slashing` keeps the queue and the registry size. -/
theorem process_attester_slashing_fulu_cstep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') : CStep s s' := by
  unfold process_attester_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine forIn_ok_invariant (fun r : MProd Bool BeaconState => CStep s r.snd) _ ?_ _
    (⟨false, s⟩ : MProd Bool BeaconState) _ (CStep.refl s) ‹forIn _ _ _ = _›
  intro index r step hr hstep
  obtain ⟨_, -, hstep⟩ := specM_bind_ok hstep
  obtain ⟨_, -, hstep⟩ := specM_bind_ok hstep
  split at hstep
  · obtain ⟨r', hr', hstep⟩ := specM_bind_ok hstep
    cases hstep
    exact hr.trans (slash_validator_fulu_cstep p f hc _ _ index none hr')
  · cases hstep
    exact hr

/-- The Fulu `process_attestation` keeps the queue and the registry. -/
theorem process_attestation_fulu_cstep (p : Preset) (o : Oracle) (s s' : BeaconState)
    (attestation : Attestation) (h : process_attestation_fulu p o s attestation = .ok s') :
    CStep s s' := by
  obtain ⟨_, _, -, hs | hs⟩ := process_attestation_fulu_shape p o s s' attestation h
  all_goals (subst hs; exact ⟨rfl, rfl⟩)

/-- The Fulu `process_voluntary_exit` keeps the queue and the registry size. -/
theorem process_voluntary_exit_fulu_cstep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') : CStep s s' := by
  obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc s s' e h
  exact initiate_validator_exit_cstep p tab s s' _ hi

/-- The Fulu `process_withdrawal_request` keeps the queue and the registry size. -/
theorem process_withdrawal_request_fulu_cstep (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') : CStep s s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  c_split h
  all_goals
    try (cases h)
    try (have := initiate_validator_exit_cstep p _ _ _ _ ‹initiate_validator_exit _ _ _ _ = _›)
    try (have := compute_exit_epoch_and_update_churn_cstep p _ _ _ _
                   ‹compute_exit_epoch_and_update_churn _ _ _ _ = _›)
    c_close

/-- The state from the Fulu `compute_consolidation_epoch_and_update_churn` keeps the queue and
the registry. -/
theorem compute_consolidation_epoch_and_update_churn_fulu_cstep (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s : BeaconState) (consolidation_balance : Gwei)
    (r : Epoch × BeaconState)
    (h : compute_consolidation_epoch_and_update_churn_fulu p f total_active_balance s
      consolidation_balance = .ok r) : CStep s r.2 := by
  unfold compute_consolidation_epoch_and_update_churn_fulu at h
  c_split h
  all_goals (cases h; exact CStep.refl _)

/-- The last step of a Fulu consolidation appends a consolidation whose indices point at
existing validators. -/
theorem consolidation_append_fulu_inRange {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v' : Validator} {r : Epoch × BeaconState}
    {l : List Validator} {src tgt : BLSPubkey}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hl : listSet r.2.validators i v' = .ok l)
    (hsrc : src ∈ s.validators.map (·.pubkey)) (htgt : tgt ∈ s.validators.map (·.pubkey)) :
    RStep s { r.2 with
      validators := l
      pending_consolidations := r.2.pending_consolidations ++
        [{ source_index := (s.validators.map (·.pubkey)).idxOf src
           target_index := (s.validators.map (·.pubkey)).idxOf tgt }] } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  have hc := (compute_consolidation_epoch_and_update_churn_fulu_cstep p f tab s x _ hr).1
  rw [hvs] at hl
  have hlen : l.length = s.validators.length := by
    rw [(ExitsSanity.listSet_ok hl).2, List.length_set]
  refine ⟨fun hs c hc' => ?_, hlen⟩
  change c ∈ s1.pending_consolidations ++ _ at hc'
  change c.source_index < l.length ∧ c.target_index < l.length
  rw [hlen]
  rw [hc] at hc'
  rcases List.mem_append.mp hc' with hc' | hc'
  · exact hs c hc'
  · rw [List.mem_singleton.mp hc']
    have h1 := List.idxOf_lt_length_of_mem hsrc
    have h2 := List.idxOf_lt_length_of_mem htgt
    simp only [List.length_map] at h1 h2
    exact ⟨h1, h2⟩

/-- The Fulu `process_consolidation_request` keeps `ConsolidationsInRange` and the registry
size. -/
theorem process_consolidation_request_fulu_rstep (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    RStep s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact RStep.refl _)
    | exact (switch_to_compounding_validator_cstep h).rstep
    | (cases h
       refine consolidation_append_fulu_inRange
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹listSet _ _ _ = .ok _› ?_ ?_ <;>
       exact Decidable.of_not_not ‹_›)

/-- The Fulu `process_operations` keeps `ConsolidationsInRange`. -/
theorem process_operations_fulu_inRange (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : ConsolidationsInRange s) :
    ConsolidationsInRange s' :=
  process_operations_fulu_inv p o f ConsolidationsInRange
    (fun _ _ _ h' hs => (process_proposer_slashing_fulu_cstep p o f hc _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_attester_slashing_fulu_cstep p o f hc _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_attestation_fulu_cstep p o _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_voluntary_exit_fulu_cstep p o f hc _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_bls_to_execution_change_cstep p o _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_deposit_request_cstep _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_withdrawal_request_fulu_cstep p f hc _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_consolidation_request_fulu_rstep p f _ _ _ h').1 hs)
    s s' body h hs

/-- The Fulu `process_block_header` keeps the queue and the registry. -/
theorem process_block_header_fulu_cstep (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') : CStep s s' := by
  unfold process_block_header_fulu at h
  c_split h
  all_goals (cases h; c_close)

/-- The Fulu `apply_withdrawals` keeps the queue and the registry. -/
theorem apply_withdrawals_fulu_cstep :
    ∀ (withdrawals : List Withdrawal) (s s' : BeaconState),
      apply_withdrawals_fulu s withdrawals = .ok s' → CStep s s'
  | [], s, s', h => by
    cases h
    exact CStep.refl s
  | w :: rest, s, s', h => by
    unfold apply_withdrawals_fulu at h
    c_split h
    all_goals
      have := apply_withdrawals_fulu_cstep rest _ _ h
      c_close

/-- The Fulu `process_withdrawals` keeps the queue and the registry. -/
theorem process_withdrawals_fulu_cstep (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    CStep s s' := by
  unfold process_withdrawals_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try contradiction
  have c1 := apply_withdrawals_fulu_cstep _ _ _ ‹apply_withdrawals_fulu _ _ = _›
  have c2 := update_next_withdrawal_index_cstep _ _ _ ‹update_next_withdrawal_index _ _ = _›
  have c3 := update_next_withdrawal_validator_index_cstep p _ _ _ h
  exact c1.trans (c2.trans (CStep.trans ⟨rfl, rfl⟩ c3))

/-- The Fulu `process_block` keeps `ConsolidationsInRange`. -/
theorem process_block_fulu_inRange (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fs block = .ok fs')
    (hs : ConsolidationsInRange fs.state) : ConsolidationsInRange fs'.state :=
  process_block_fulu_inv p o fo f c ConsolidationsInRange
    (fun _ _ _ h' hs => (process_block_header_fulu_cstep p o fo _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_withdrawals_fulu_cstep p _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_randao_cstep p o _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_eth1_data_cstep p _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => process_operations_fulu_inRange p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => (process_sync_aggregate_cstep p o _ _ _ h').inRange hs)
    fs fs' block h hs

/-! ## Slots and the epoch -/

/-- `process_slot_fulu` keeps the queue and the registry of the inner state. -/
theorem process_slot_fulu_cstep (p : Preset) (o : Oracle) (fo : FuluOracle) (fs fs' : FuluState)
    (h : process_slot_fulu p o fo fs = .ok fs') : CStep fs.state fs'.state := by
  unfold process_slot_fulu at h
  c_split h
  all_goals (cases h; c_close)

/-- `process_eth1_data_reset` keeps the queue and the registry. -/
theorem process_eth1_data_reset_cstep (p : Preset) (s s' : BeaconState)
    (h : process_eth1_data_reset p s = .ok s') : CStep s s' := by
  unfold process_eth1_data_reset at h
  c_split h
  all_goals (cases h; exact CStep.refl _)

/-- `process_slashings_reset` keeps the queue and the registry. -/
theorem process_slashings_reset_cstep (p : Preset) (s s' : BeaconState)
    (h : process_slashings_reset p s = .ok s') : CStep s s' := by
  unfold process_slashings_reset at h
  c_split h
  all_goals (cases h; exact CStep.refl _)

/-- `process_randao_mixes_reset` keeps the queue and the registry. -/
theorem process_randao_mixes_reset_cstep (p : Preset) (s s' : BeaconState)
    (h : process_randao_mixes_reset p s = .ok s') : CStep s s' := by
  unfold process_randao_mixes_reset at h
  c_split h
  all_goals (cases h; exact CStep.refl _)

/-- `process_historical_summaries_update` keeps the queue and the registry. -/
theorem process_historical_summaries_update_cstep (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_historical_summaries_update p o s = .ok s') : CStep s s' := by
  unfold process_historical_summaries_update at h
  c_split h
  all_goals (cases h; exact CStep.refl _)

/-- The Fulu `process_epoch` keeps `ConsolidationsInRange`. -/
theorem process_epoch_fulu_inRange (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (s s' : BeaconState) (h : process_epoch_fulu p f o s = .ok s')
    (hs : ConsolidationsInRange s) : ConsolidationsInRange s' :=
  process_epoch_fulu_inv p f hc o ConsolidationsInRange
    (fun _ _ h' hs => (process_justification_and_finalization_cstep p _ _ h').inRange hs)
    (fun _ _ h' hs => (process_inactivity_updates_cstep p _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_rewards_and_penalties_cstep p _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_registry_updates_cstep p _ _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_slashings_cstep p _ _ _ h').inRange hs)
    (fun _ _ h' hs => (process_eth1_data_reset_cstep p _ _ h').inRange hs)
    (fun _ _ _ h' hs => (process_pending_deposits_dstep p o _ _ _ h').inRange hs)
    (fun _ _ h' hs => process_pending_consolidations_inRange p _ _ h' hs)
    (fun _ _ h' hs => (process_effective_balance_updates_cstep p _ _ h').inRange hs)
    (fun _ _ h' hs => (process_slashings_reset_cstep p _ _ h').inRange hs)
    (fun _ _ h' hs => (process_randao_mixes_reset_cstep p _ _ h').inRange hs)
    (fun _ _ h' hs => (process_historical_summaries_update_cstep p o _ _ h').inRange hs)
    (fun _ hs => hs)
    (fun _ _ h' hs => by
      obtain ⟨_, _, rfl⟩ := process_sync_committee_updates_fulu_shape p o _ _ h'
      exact hs)
    (fun _ _ h' hs => by
      obtain ⟨_, rfl⟩ := process_proposer_lookahead_fulu_shape p o _ _ h'
      exact hs)
    s s' h hs

/-- `process_slots_fulu` with the Fulu `process_epoch` keeps `ConsolidationsInRange`. -/
theorem process_slots_fulu_inRange (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (fo : FuluOracle) (fs fs' : FuluState) (slot : Slot)
    (h : process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot = .ok fs')
    (hs : ConsolidationsInRange fs.state) : ConsolidationsInRange fs'.state :=
  process_slots_fulu_inv p o fo (process_epoch_fulu p f o) ConsolidationsInRange
    (fun _ _ h' hs => (process_slot_fulu_cstep p o fo _ _ h').inRange hs)
    (fun _ _ h' hs => process_epoch_fulu_inRange p f hc o _ _ h' hs)
    (fun _ _ hs => hs) fs fs' slot hs h

/-- `state_transition_fulu` keeps `ConsolidationsInRange`. -/
theorem state_transition_fulu_inRange (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : ConsolidationsInRange fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    ConsolidationsInRange fs'.state :=
  state_transition_fulu_inv p o fo f c ConsolidationsInRange
    (fun _ _ _ h' hs => process_slots_fulu_inRange p f hc o fo _ _ _ h' hs)
    (fun _ _ _ h' hs => process_block_fulu_inRange p o fo f hc c _ _ _ h' hs)
    fs fs' signed_block validate_result hs h

end EpochProofs.Spec
