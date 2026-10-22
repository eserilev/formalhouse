import EpochProofs.Sanity.FuluEpoch
import EpochProofs.Sanity.Block.FuluEffects
import EpochProofs.Sanity.EpochCommittees

/-!
# Invariants of the Fulu state transition, step by step

The Fulu invariant files (`Fulu*.lean` in this directory) prove each invariant for each Fulu
function. This file joins those facts. A property of the inner `BeaconState` that each step
keeps is kept by:

- the Fulu `process_epoch` (`process_epoch_fulu_inv`). By `process_epoch_fulu_eq_tab`, its
  steps are the Gloas steps at `fuluTab`, without builder payments and the PTC window, and with
  the Fulu sync committee and proposer lookahead.
- the Fulu `process_operations` and `process_block` (`process_operations_fulu_inv`,
  `process_block_fulu_inv`).
- `process_slots_fulu` and `state_transition_fulu` (`process_slots_fulu_inv`,
  `state_transition_fulu_inv`).
-/

namespace EpochProofs.Spec

/-- The Fulu sync committee update writes only the two sync committees. -/
theorem process_sync_committee_updates_fulu_shape (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_sync_committee_updates_fulu p o s = .ok s') :
    ∃ current next : SyncCommittee,
      s' = { s with current_sync_committee := current, next_sync_committee := next } := by
  unfold process_sync_committee_updates_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨_, _, rfl⟩)
    | (cases h; exact ⟨s.current_sync_committee, s.next_sync_committee, rfl⟩)

/-- The Fulu proposer lookahead writes only `proposer_lookahead`. -/
theorem process_proposer_lookahead_fulu_shape (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead_fulu p o s = .ok s') :
    ∃ proposer_lookahead : List ValidatorIndex, s' = { s with proposer_lookahead } := by
  unfold process_proposer_lookahead_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨_, rfl⟩)

/-- The Fulu `process_epoch` keeps every property that each of its steps keeps. -/
theorem process_epoch_fulu_inv (p : Preset) (f : FuluConfig) (hc : FuluCompat p f) (o : Oracle)
    (P : BeaconState → Prop)
    (hJ : ∀ a b, process_justification_and_finalization p a = .ok b → P a → P b)
    (hI : ∀ a b, process_inactivity_updates p a = .ok b → P a → P b)
    (hR : ∀ tab a b, process_rewards_and_penalties p tab a = .ok b → P a → P b)
    (hReg : ∀ tab a b, process_registry_updates p tab a = .ok b → P a → P b)
    (hS : ∀ tab a b, process_slashings p tab a = .ok b → P a → P b)
    (hE1 : ∀ a b, process_eth1_data_reset p a = .ok b → P a → P b)
    (hD : ∀ tab a b, process_pending_deposits p tab (apply_pending_deposit p o) a = .ok b →
      P a → P b)
    (hC : ∀ a b, process_pending_consolidations p a = .ok b → P a → P b)
    (hEB : ∀ a b, process_effective_balance_updates p a = .ok b → P a → P b)
    (hSR : ∀ a b, process_slashings_reset p a = .ok b → P a → P b)
    (hRM : ∀ a b, process_randao_mixes_reset p a = .ok b → P a → P b)
    (hHS : ∀ a b, process_historical_summaries_update p o a = .ok b → P a → P b)
    (hPF : ∀ a, P a → P (process_participation_flag_updates a))
    (hSC : ∀ a b, process_sync_committee_updates_fulu p o a = .ok b → P a → P b)
    (hPL : ∀ a b, process_proposer_lookahead_fulu p o a = .ok b → P a → P b)
    (s s' : BeaconState) (h : process_epoch_fulu p f o s = .ok s') (hs : P s) : P s' := by
  rw [process_epoch_fulu_eq_tab p f hc] at h
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
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  obtain ⟨s13, h13, h⟩ := specM_bind_ok h
  exact hPL _ _ h (hSC _ _ h13 (hPF _ (hHS _ _ h12 (hRM _ _ h11 (hSR _ _ h10 (hEB _ _ h9
    (hC _ _ h8 (hD _ _ _ h7 (hE1 _ _ h6 (hS _ _ _ h5 (hReg _ _ _ h4 (hR _ _ _ h3
    (hI _ _ h2 (hJ _ _ h1 hs))))))))))))))

/-- A `List.foldlM` over the state keeps every property that each step keeps. -/
theorem foldlM_inv {α : Type} (P : BeaconState → Prop) (f : BeaconState → α → SpecM BeaconState)
    (hf : ∀ s a s', f s a = .ok s' → P s → P s') :
    ∀ (l : List α) (s s' : BeaconState), l.foldlM f s = .ok s' → P s → P s' := by
  intro l
  induction l with
  | nil => intro s s' h hs; cases h; exact hs
  | cons a as ih =>
    intro s s' h hs
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := specM_bind_ok h
    exact ih s1 s' h (hf s a s1 h1 hs)

/-- The Fulu `process_operations` keeps every property that each operation keeps. -/
theorem process_operations_fulu_inv (p : Preset) (o : Oracle) (f : FuluConfig)
    (P : BeaconState → Prop)
    (hPS : ∀ a x b, process_proposer_slashing_fulu p o f a x = .ok b → P a → P b)
    (hAS : ∀ a x b, process_attester_slashing_fulu p o f a x = .ok b → P a → P b)
    (hAt : ∀ a x b, process_attestation_fulu p o a x = .ok b → P a → P b)
    (hVE : ∀ a x b, process_voluntary_exit_fulu p o f a x = .ok b → P a → P b)
    (hBLS : ∀ a x b, process_bls_to_execution_change p o a x = .ok b → P a → P b)
    (hDR : ∀ a x b, process_deposit_request a x = .ok b → P a → P b)
    (hWR : ∀ a x b, process_withdrawal_request_fulu p f a x = .ok b → P a → P b)
    (hCR : ∀ a x b, process_consolidation_request_fulu p f a x = .ok b → P a → P b)
    (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : P s) : P s' := by
  unfold process_operations_fulu at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals try contradiction
  have e1 := foldlM_inv P _ hPS _ _ _ ‹List.foldlM (process_proposer_slashing_fulu p o f) _ _ = _› hs
  have e2 := foldlM_inv P _ hAS _ _ _ ‹List.foldlM (process_attester_slashing_fulu p o f) _ _ = _› e1
  have e3 := foldlM_inv P _ hAt _ _ _ ‹List.foldlM (process_attestation_fulu p o) _ _ = _› e2
  have e4 := foldlM_inv P _ hVE _ _ _ ‹List.foldlM (process_voluntary_exit_fulu p o f) _ _ = _› e3
  have e5 := foldlM_inv P _ hBLS _ _ _
    ‹List.foldlM (process_bls_to_execution_change p o) _ _ = _› e4
  have e6 := foldlM_inv P _ hDR _ _ _ ‹List.foldlM process_deposit_request _ _ = _› e5
  have e7 := foldlM_inv P _ hWR _ _ _
    ‹List.foldlM (process_withdrawal_request_fulu p f) _ _ = _› e6
  exact foldlM_inv P _ hCR _ _ _ h e7

/-- `process_execution_payload_fulu` writes only the payload header. -/
theorem process_execution_payload_fulu_state (p : Preset) (o : Oracle) (fo : FuluOracle)
    (c : FuluBlockConfig) (fs fs' : FuluState) (body : FuluBeaconBlockBody)
    (h : process_execution_payload_fulu p o fo c fs body = .ok fs') : fs'.state = fs.state := by
  unfold process_execution_payload_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; rfl)

/-- The Fulu `process_block` keeps every property of the inner state that each step keeps. -/
theorem process_block_fulu_inv (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (P : BeaconState → Prop)
    (hH : ∀ a b block, process_block_header_fulu p o fo a block = .ok b → P a → P b)
    (hW : ∀ a b payload, process_withdrawals_fulu p a payload = .ok b → P a → P b)
    (hR : ∀ a b body, process_randao p o a body = .ok b → P a → P b)
    (hE : ∀ a b body, process_eth1_data p a body = .ok b → P a → P b)
    (hO : ∀ a b body, process_operations_fulu p o f a body = .ok b → P a → P b)
    (hSA : ∀ a b sa, process_sync_aggregate p o a sa = .ok b → P a → P b)
    (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fs block = .ok fs') (hs : P fs.state) : P fs'.state := by
  unfold process_block_fulu at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨fs3, h3, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  cases h
  have e3 : P fs3.state := by
    rw [process_execution_payload_fulu_state p o fo c _ _ _ h3]
    exact hW _ _ _ h2 (hH _ _ _ h1 hs)
  exact hSA _ _ _ h7 (hO _ _ _ h6 (hE _ _ _ h5 (hR _ _ _ h4 e3)))

/-- The Fulu slot loop keeps every property of the inner state that `process_slot_fulu`,
`processEpoch` and any slot write keep. -/
theorem process_slots_loop_fulu_inv (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (P : BeaconState → Prop)
    (hslot : ∀ fs fs', process_slot_fulu p o fo fs = .ok fs' → P fs.state → P fs'.state)
    (hepoch : ∀ s s', processEpoch s = .ok s' → P s → P s')
    (hbump : ∀ s n, P s → P { s with slot := n }) (slot : Slot) :
    ∀ fuel (fs fs' : FuluState), P fs.state →
      process_slots_loop_fulu p o fo processEpoch slot fuel fs = .ok fs' → P fs'.state := by
  intro fuel
  induction fuel with
  | zero => intro fs fs' hP h; cases h; exact hP
  | succ n ih =>
    intro fs fs' hP h
    simp only [process_slots_loop_fulu] at h
    split at h
    · obtain ⟨fs1, h1, h⟩ := specM_bind_ok h
      have hP1 := hslot _ _ h1 hP
      obtain ⟨a, -, h⟩ := specM_bind_ok h
      obtain ⟨m, -, h⟩ := specM_bind_ok h
      split at h
      · obtain ⟨s2, he, h⟩ := specM_bind_ok h
        obtain ⟨_, hp, h⟩ := specM_bind_ok h
        cases hp
        obtain ⟨c, -, h⟩ := specM_bind_ok h
        exact ih _ _ (hbump _ c (hepoch _ _ he hP1)) h
      · obtain ⟨_, h2, h⟩ := specM_bind_ok h
        cases h2
        obtain ⟨c, -, h⟩ := specM_bind_ok h
        exact ih _ _ (hbump _ c hP1) h
    · cases h
      exact hP

/-- `process_slots_fulu` keeps every property of the inner state that `process_slot_fulu`,
`processEpoch` and any slot write keep. -/
theorem process_slots_fulu_inv (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (P : BeaconState → Prop)
    (hslot : ∀ fs fs', process_slot_fulu p o fo fs = .ok fs' → P fs.state → P fs'.state)
    (hepoch : ∀ s s', processEpoch s = .ok s' → P s → P s')
    (hbump : ∀ s n, P s → P { s with slot := n })
    (fs fs' : FuluState) (slot : Slot) (hP : P fs.state)
    (h : process_slots_fulu p o fo processEpoch fs slot = .ok fs') : P fs'.state := by
  unfold process_slots_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · exact process_slots_loop_fulu_inv p o fo processEpoch P hslot hepoch hbump slot _ _ _ hP h

/-- `state_transition_fulu` keeps every property of the inner state that the slot loop and
the block keep. -/
theorem state_transition_fulu_inv (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (P : BeaconState → Prop)
    (hslots : ∀ fs fs' slot, process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot =
      .ok fs' → P fs.state → P fs'.state)
    (hblock : ∀ fs fs' block, process_block_fulu p o fo f c fs block = .ok fs' → P fs.state →
      P fs'.state)
    (fs fs' : FuluState) (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : P fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    P fs'.state := by
  unfold state_transition_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact hblock _ _ _ ‹process_block_fulu _ _ _ _ _ _ _ = _›
         (hslots _ _ _ ‹process_slots_fulu _ _ _ _ _ _ = _› hs))

end EpochProofs.Spec
