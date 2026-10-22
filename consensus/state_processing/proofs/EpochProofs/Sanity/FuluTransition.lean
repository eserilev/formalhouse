import EpochProofs.Spec.Block.FuluTransition
import EpochProofs.Sanity.Driver
import EpochProofs.Sanity.Block.FuluBlock

/-!
# The Fulu state transition keeps the FFG invariant

This file mirrors `Sanity/Driver` for Fulu.

- `process_slots_fulu` keeps every property of the inner `BeaconState` that `process_slot_fulu`,
  `process_epoch` and the slot increment keep, and it ends at the target slot.
- Each step of the Fulu `process_epoch` after `process_justification_and_finalization` keeps
  the slot and the checkpoints. So the Fulu `process_epoch` turns `FfgInvariant` into
  `FfgInvariantAfter`.
- Each step of the Fulu `process_block` keeps the slot and the checkpoints.
- So `state_transition_fulu` keeps `FfgInvariant`.
-/

namespace EpochProofs.Spec

/-- Splits the binds, `if`s and `match`es of a step that does not write the slot or the
checkpoints, and closes each success branch by `rfl`. -/
local macro "cs_tac" h:ident : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    at $h:ident
  repeat' split at $h:ident
  all_goals first
    | contradiction
    | (cases $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩)))

namespace FuluTransitionSanity

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

/-- A `List.foldlM` in `SpecM` keeps the slot and the checkpoints when each step keeps them. -/
theorem foldlM_checkpointsStable {α : Type} (f : BeaconState → α → SpecM BeaconState)
    (hf : ∀ s a s', f s a = .ok s' → CheckpointsStable s s') :
    ∀ (l : List α) (s s' : BeaconState), l.foldlM f s = .ok s' → CheckpointsStable s s' := by
  intro l
  induction l with
  | nil => intro s s' h; cases h; exact CheckpointsStable.refl s
  | cons a as ih =>
    intro s s' h
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := specM_bind_ok h
    exact (hf s a s1 h1).trans (ih s1 s' h)

theorem uint64Add_ok_eq {a b c : Uint64} (h : uint64Add a b = .ok c) : c = a + b := by
  unfold uint64Add at h
  split at h
  · cases h; rfl
  · cases h

theorem uint64Mod_ok_eq {a b c : Uint64} (h : uint64Mod a b = .ok c) : c = a % b := by
  unfold uint64Mod at h
  split at h
  · cases h
  · cases h; rfl

/-- A successful `if` ran one of its branches. -/
theorem ite_ok {α : Type} {c : Prop} [Decidable c] {t e : SpecM α} {x : α}
    (h : (if c then t else e) = .ok x) : (c ∧ t = .ok x) ∨ (¬ c ∧ e = .ok x) := by
  by_cases hc : c
  · exact .inl ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · exact .inr ⟨hc, by rw [if_neg hc] at h; exact h⟩

end FuluTransitionSanity

open FuluTransitionSanity

/-! ## Slots -/

/-- `process_slot_fulu` keeps the registry, the slot and the checkpoints of the inner state. -/
theorem process_slot_fulu_frame (p : Preset) (o : Oracle) (fo : FuluOracle)
    (fs fs' : FuluState) (h : process_slot_fulu p o fo fs = .ok fs') :
    RegistryFrame fs.state fs'.state ∧ CheckpointsStable fs.state fs'.state := by
  unfold process_slot_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩)

/-- The Fulu `process_slots` loop keeps `P` of the inner state when the slot only grows by one.
`processEpoch` runs on the last slot of an epoch. Its result satisfies a weaker `Q`, and the
step to the next slot turns `Q` back into `P`. This is `process_slots_loop_invariant_mono` for
Fulu. -/
theorem process_slots_loop_fulu_invariant_mono (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (slot : Slot) (P Q : BeaconState → Prop)
    (hslot : ∀ fs fs', process_slot_fulu p o fo fs = .ok fs' → P fs.state → P fs'.state)
    (hepoch : ∀ s s', (s.slot + 1) % p.SLOTS_PER_EPOCH = 0 → processEpoch s = .ok s' → P s →
      Q s' ∧ s'.slot = s.slot)
    (hbump_epoch : ∀ s, (s.slot + 1) % p.SLOTS_PER_EPOCH = 0 → Q s →
      P { s with slot := s.slot + 1 })
    (hbump : ∀ s, P s → P { s with slot := s.slot + 1 }) :
    ∀ fuel fs fs', P fs.state →
      process_slots_loop_fulu p o fo processEpoch slot fuel fs = .ok fs' → P fs'.state := by
  intro fuel
  induction fuel with
  | zero =>
    intro fs fs' hP h
    cases h
    exact hP
  | succ n ih =>
    intro fs fs' hP h
    simp only [process_slots_loop_fulu] at h
    split at h
    · obtain ⟨fs1, h1, h⟩ := specM_bind_ok h
      have hP1 := hslot _ _ h1 hP
      obtain ⟨a, ha, h⟩ := specM_bind_ok h
      obtain ⟨m, hm, h⟩ := specM_bind_ok h
      rw [uint64Add_ok_eq ha] at hm
      have hm' := uint64Mod_ok_eq hm
      split at h
      · rename_i hz
        have hz' : (fs1.state.slot + 1) % p.SLOTS_PER_EPOCH = 0 := by
          rw [← hm']; simpa using hz
        obtain ⟨s2, he, h⟩ := specM_bind_ok h
        obtain ⟨_, hp, h⟩ := specM_bind_ok h
        cases hp
        obtain ⟨hQ, hs2⟩ := hepoch _ _ hz' he hP1
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        rw [uint64Add_ok_eq hc] at h
        rw [← hs2] at hz'
        exact ih _ _ (hbump_epoch _ hz' hQ) h
      · obtain ⟨_, h2, h⟩ := specM_bind_ok h
        cases h2
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        rw [uint64Add_ok_eq hc] at h
        exact ih _ _ (hbump _ hP1) h
    · cases h
      exact hP

/-- The Fulu `process_slots` keeps every property that the loop keeps by
`process_slots_loop_fulu_invariant_mono`. -/
theorem process_slots_fulu_invariant_mono (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (P Q : BeaconState → Prop)
    (hslot : ∀ fs fs', process_slot_fulu p o fo fs = .ok fs' → P fs.state → P fs'.state)
    (hepoch : ∀ s s', (s.slot + 1) % p.SLOTS_PER_EPOCH = 0 → processEpoch s = .ok s' → P s →
      Q s' ∧ s'.slot = s.slot)
    (hbump_epoch : ∀ s, (s.slot + 1) % p.SLOTS_PER_EPOCH = 0 → Q s →
      P { s with slot := s.slot + 1 })
    (hbump : ∀ s, P s → P { s with slot := s.slot + 1 })
    (fs fs' : FuluState) (slot : Slot) (hP : P fs.state)
    (h : process_slots_fulu p o fo processEpoch fs slot = .ok fs') : P fs'.state := by
  unfold process_slots_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · exact process_slots_loop_fulu_invariant_mono p o fo processEpoch slot P Q hslot hepoch
      hbump_epoch hbump _ _ _ hP h

private theorem slot_step {a b c fuel : Nat} (hlt : a < b) (hfuel : b - a ≤ fuel + 1)
    (hc : c = a + 1) : c ≤ b ∧ b - c ≤ fuel := by
  omega

private theorem slot_done {a b : Nat} (hle : a ≤ b) (h : ¬ a < b ∨ b - a ≤ 0) :
    a = b := by
  omega

theorem process_slots_loop_fulu_slot (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState) (slot : Slot)
    (hepoch : ∀ s s', processEpoch s = .ok s' → s'.slot = s.slot) :
    ∀ fuel (fs fs' : FuluState), fs.state.slot ≤ slot → slot - fs.state.slot ≤ fuel →
      process_slots_loop_fulu p o fo processEpoch slot fuel fs = .ok fs' →
        fs'.state.slot = slot := by
  intro fuel
  induction fuel with
  | zero =>
    intro fs fs' hle hfuel h
    cases h
    exact slot_done hle (.inr hfuel)
  | succ n ih =>
    intro fs fs' hle hfuel h
    simp only [process_slots_loop_fulu] at h
    split at h
    · obtain ⟨fs1, h1, h⟩ := specM_bind_ok h
      have hs1 := (process_slot_fulu_frame p o fo _ _ h1).2.1
      obtain ⟨_, -, h⟩ := specM_bind_ok h
      obtain ⟨_, -, h⟩ := specM_bind_ok h
      split at h
      · obtain ⟨s2, he, h⟩ := specM_bind_ok h
        obtain ⟨_, hp, h⟩ := specM_bind_ok h
        cases hp
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        have hstep := slot_step (fuel := n) ‹fs.state.slot < slot› hfuel
          ((uint64Add_ok_eq hc).trans (by rw [hepoch _ _ he, hs1]))
        exact ih _ _ hstep.1 hstep.2 h
      · obtain ⟨_, h2, h⟩ := specM_bind_ok h
        cases h2
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        have hstep := slot_step (fuel := n) ‹fs.state.slot < slot› hfuel
          ((uint64Add_ok_eq hc).trans (by rw [hs1]))
        exact ih _ _ hstep.1 hstep.2 h
    · cases h
      exact slot_done hle (.inl ‹¬ fs.state.slot < slot›)

/-- If each `processEpoch` call keeps `slot`, then the Fulu `process_slots` ends at the target
slot. -/
theorem process_slots_fulu_slot (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState)
    (hepoch : ∀ s s', processEpoch s = .ok s' → s'.slot = s.slot)
    (fs fs' : FuluState) (slot : Slot)
    (h : process_slots_fulu p o fo processEpoch fs slot = .ok fs') : fs'.state.slot = slot := by
  unfold process_slots_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · exact process_slots_loop_fulu_slot p o fo processEpoch slot hepoch _ _ _
      (Nat.le_of_lt (Decidable.of_not_not ‹¬ ¬ fs.state.slot < slot›)) (Nat.le_refl _) h

/-- One more slot does not lower the epoch. -/
private theorem epochOf_succ_le (p : Preset) (s : BeaconState) :
    epochOf p s ≤ epochOf p { s with slot := s.slot + 1 } :=
  Nat.div_le_div_right (Nat.le_succ _)

/-- From the last slot of an epoch, one more slot raises the epoch. -/
private theorem epochOf_succ_of_mod (p : Preset) (s : BeaconState)
    (hz : (s.slot + 1) % p.SLOTS_PER_EPOCH = 0) :
    epochOf p s < epochOf p { s with slot := s.slot + 1 } := by
  simp only [epochOf]
  by_cases h0 : p.SLOTS_PER_EPOCH = 0
  · rw [h0, Nat.mod_zero] at hz
    simp only [Slot] at *
    omega
  · have hpos : 0 < p.SLOTS_PER_EPOCH := Nat.pos_of_ne_zero h0
    have h1 := Nat.div_add_mod (s.slot + 1) p.SLOTS_PER_EPOCH
    have h2 := Nat.div_add_mod s.slot p.SLOTS_PER_EPOCH
    have h3 := Nat.mod_lt s.slot hpos
    rw [hz, Nat.add_zero] at h1
    refine Nat.lt_of_not_le fun hle => ?_
    have := Nat.mul_le_mul_left p.SLOTS_PER_EPOCH hle
    simp only [Slot] at *
    omega

/-- The Fulu `process_slots` keeps `FfgInvariant`. Each `processEpoch` call starts from a state
with `FfgInvariant` and must end in a state with `FfgInvariantAfter` at the same slot. -/
theorem process_slots_fulu_ffg (p : Preset) (o : Oracle) (fo : FuluOracle)
    (processEpoch : BeaconState → SpecM BeaconState)
    (hepoch : ∀ s s', processEpoch s = .ok s' → FfgInvariant p s →
      FfgInvariantAfter p s' ∧ s'.slot = s.slot)
    (fs fs' : FuluState) (slot : Slot) (hinv : FfgInvariant p fs.state)
    (h : process_slots_fulu p o fo processEpoch fs slot = .ok fs') :
    FfgInvariant p fs'.state := by
  refine process_slots_fulu_invariant_mono p o fo processEpoch (FfgInvariant p)
    (FfgInvariantAfter p)
    (fun fs fs' hs hP => hP.of_checkpointsStable (process_slot_fulu_frame p o fo fs fs' hs).2)
    (fun s s' _ hs hP => hepoch s s' hs hP) ?_ ?_ fs fs' slot hinv h
  · intro s hz ⟨hord, hc⟩
    exact ⟨hord, .inl (Nat.lt_of_le_of_lt hc (epochOf_succ_of_mod p s hz))⟩
  · intro s ⟨hord, hc⟩
    refine ⟨hord, ?_⟩
    rcases hc with hc | hc
    · exact .inl (Nat.lt_of_lt_of_le hc (epochOf_succ_le p s))
    · exact .inr hc

/-! ## Fulu epoch steps -/

/-- The Fulu `compute_exit_epoch_and_update_churn` keeps the slot and the checkpoints. -/
theorem compute_exit_epoch_and_update_churn_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s : BeaconState) (exit_balance : Gwei)
    (r : Epoch × BeaconState)
    (h : compute_exit_epoch_and_update_churn_fulu p f total_active_balance s exit_balance =
      .ok r) :
    CheckpointsStable s r.2 := by
  unfold compute_exit_epoch_and_update_churn_fulu at h
  cs_tac h

/-- The Fulu `initiate_validator_exit` keeps the slot and the checkpoints. -/
theorem initiate_validator_exit_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit_fulu p f total_active_balance s index = .ok s') :
    CheckpointsStable s s' := by
  unfold initiate_validator_exit_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (cases h
       exact compute_exit_epoch_and_update_churn_fulu_checkpointsStable p f
         total_active_balance s _ _ ‹_ = Except.ok _›)

/-- The Fulu `process_registry_updates` keeps the slot and the checkpoints. -/
theorem process_registry_updates_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (total_active_balance : Gwei) (s s' : BeaconState)
    (h : process_registry_updates_fulu p f total_active_balance s = .ok s') :
    CheckpointsStable s s' := by
  unfold process_registry_updates_fulu at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨r, hr, h⟩ := specM_bind_ok h
  cases h
  refine forIn_ok_invariant (CheckpointsStable s) _ ?_ _ s _ (CheckpointsStable.refl s) hr
  intro index st r hst hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first
    | contradiction
    | (cases hb; exact hst)
    | (cases hb
       exact hst.trans (initiate_validator_exit_fulu_checkpointsStable p f total_active_balance
         _ _ _ ‹initiate_validator_exit_fulu _ _ _ _ _ = _›))

/-- The Fulu `process_pending_deposits` with `apply_pending_deposit` keeps the slot and the
checkpoints. -/
theorem process_pending_deposits_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (o : Oracle) (total_active_balance : Gwei) (s s' : BeaconState)
    (h : process_pending_deposits_fulu p f total_active_balance (apply_pending_deposit p o) s =
      .ok s') :
    CheckpointsStable s s' := by
  unfold process_pending_deposits_fulu at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, _, _, _, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_invariant
    (fun r : MProd (List PendingDeposit) (MProd Bool (MProd Uint64 (MProd Uint64 BeaconState))) =>
      CheckpointsStable s r.2.2.2.2) _ ?_ _ _ _ (CheckpointsStable.refl s) hr
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
         exact hst.trans (apply_pending_deposit_checkpointsStable p o _ _ _
           ‹apply_pending_deposit _ _ _ _ = _›))

/-- The Fulu `process_sync_committee_updates` keeps the slot and the checkpoints. -/
theorem process_sync_committee_updates_fulu_checkpointsStable (p : Preset) (o : Oracle)
    (s s' : BeaconState) (h : process_sync_committee_updates_fulu p o s = .ok s') :
    CheckpointsStable s s' := by
  unfold process_sync_committee_updates_fulu at h
  cs_tac h

/-- The Fulu `process_proposer_lookahead` keeps the slot and the checkpoints. -/
theorem process_proposer_lookahead_fulu_checkpointsStable (p : Preset) (o : Oracle)
    (s s' : BeaconState) (h : process_proposer_lookahead_fulu p o s = .ok s') :
    CheckpointsStable s s' := by
  unfold process_proposer_lookahead_fulu at h
  cs_tac h

/-- After `process_justification_and_finalization`, the other steps of the Fulu `process_epoch`
keep the slot and the checkpoints. -/
theorem process_epoch_fulu_split (p : Preset) (f : FuluConfig) (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu p f o s = .ok s') :
    ∃ s1, process_justification_and_finalization p s = .ok s1 ∧ CheckpointsStable s1 s' := by
  unfold process_epoch_fulu at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  refine ⟨s1, h1, ?_⟩
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
  exact (process_inactivity_updates_checkpointsStable p _ _ h2).trans
    ((process_rewards_and_penalties_checkpointsStable p _ _ _ h3).trans
    ((process_registry_updates_fulu_checkpointsStable p f _ _ _ h4).trans
    ((process_slashings_checkpointsStable p _ _ _ h5).trans
    ((process_eth1_data_reset_checkpointsStable p _ _ h6).trans
    ((process_pending_deposits_fulu_checkpointsStable p f o _ _ _ h7).trans
    ((process_pending_consolidations_checkpointsStable p _ _ h8).trans
    ((process_effective_balance_updates_checkpointsStable p _ _ h9).trans
    ((process_slashings_reset_checkpointsStable p _ _ h10).trans
    ((process_randao_mixes_reset_checkpointsStable p _ _ h11).trans
    ((process_historical_summaries_update_checkpointsStable p o _ _ h12).trans
    ((process_participation_flag_updates_checkpointsStable _).trans
    ((process_sync_committee_updates_fulu_checkpointsStable p o _ _ h13).trans
    (process_proposer_lookahead_fulu_checkpointsStable p o _ _ h)))))))))))))

/-- The Fulu `process_epoch` keeps the slot. -/
theorem process_epoch_fulu_slot (p : Preset) (f : FuluConfig) (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu p f o s = .ok s') : s'.slot = s.slot := by
  obtain ⟨s1, h1, hs⟩ := process_epoch_fulu_split p f o s s' h
  exact hs.1.trans (process_justification_and_finalization_frame p s s1 h1).2

/-- The Fulu `process_epoch` turns `FfgInvariant` into `FfgInvariantAfter` and keeps the
slot. -/
theorem process_epoch_fulu_ffg (p : Preset) (f : FuluConfig) (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu p f o s = .ok s') (hinv : FfgInvariant p s) :
    FfgInvariantAfter p s' ∧ s'.slot = s.slot := by
  obtain ⟨s1, h1, hs⟩ := process_epoch_fulu_split p f o s s' h
  exact ⟨(process_justification_and_finalization_ffg p s s1 h1 hinv).1.of_checkpointsStable hs,
    process_epoch_fulu_slot p f o s s' h⟩

/-- The Fulu `process_slots` with the Fulu `process_epoch` ends at the target slot. -/
theorem process_slots_fulu_process_epoch_slot (p : Preset) (f : FuluConfig) (o : Oracle)
    (fo : FuluOracle) (fs fs' : FuluState) (slot : Slot)
    (h : process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot = .ok fs') :
    fs'.state.slot = slot :=
  process_slots_fulu_slot p o fo (process_epoch_fulu p f o) (process_epoch_fulu_slot p f o)
    fs fs' slot h

/-- The Fulu `process_slots` with the Fulu `process_epoch` keeps `FfgInvariant`. -/
theorem process_slots_fulu_process_epoch_ffg (p : Preset) (f : FuluConfig) (o : Oracle)
    (fo : FuluOracle) (fs fs' : FuluState) (slot : Slot) (hinv : FfgInvariant p fs.state)
    (h : process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot = .ok fs') :
    FfgInvariant p fs'.state :=
  process_slots_fulu_ffg p o fo (process_epoch_fulu p f o)
    (fun s s' hs hP => process_epoch_fulu_ffg p f o s s' hs hP) fs fs' slot hinv h

/-! ## Fulu block steps -/

/-- Splits the binds and `if`s of a successful run without `simp`. -/
local macro "peel_ok" h:ident : tactic => `(tactic| repeat' first
  | (guard_hyp $h:ident : ((_ : SpecM _) >>= _) = _; obtain ⟨_, _, $h:ident⟩ := specM_bind_ok $h)
  | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
     rcases ite_ok $h with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩))

/-- Splits a Fulu operation and closes each success branch. A branch either keeps the slot and
the checkpoints by `rfl`, or ends in a Fulu exit or churn step and then writes other fields. -/
local macro "ops_cs_tac" h:ident : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    at $h:ident
  repeat' split at $h:ident
  all_goals first
    | contradiction
    | (cases $h:ident; exact ⟨rfl, rfl, rfl, rfl⟩)
    | exact initiate_validator_exit_fulu_checkpointsStable _ _ _ _ _ _ $h:ident
    | (cases $h:ident
       refine (initiate_validator_exit_fulu_checkpointsStable _ _ _ _ _ _
         ‹initiate_validator_exit_fulu _ _ _ _ _ = _›).trans ?_
       exact ⟨rfl, rfl, rfl, rfl⟩)
    | (cases $h:ident
       refine (compute_exit_epoch_and_update_churn_fulu_checkpointsStable _ _ _ _ _ _
         ‹compute_exit_epoch_and_update_churn_fulu _ _ _ _ _ = _›).trans ?_
       exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- The Fulu `process_block_header` keeps the slot and the checkpoints. -/
theorem process_block_header_fulu_checkpointsStable (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') : CheckpointsStable s s' := by
  unfold process_block_header_fulu at h
  cs_tac h

/-- `apply_withdrawals_fulu` keeps the slot and the checkpoints. -/
theorem apply_withdrawals_fulu_checkpointsStable :
    ∀ (withdrawals : List Withdrawal) (s s' : BeaconState),
      apply_withdrawals_fulu s withdrawals = .ok s' → CheckpointsStable s s'
  | [], s, s', h => by
    cases h
    exact CheckpointsStable.refl _
  | w :: rest, s, s', h => by
    simp only [apply_withdrawals_fulu] at h
    obtain ⟨b, -, h⟩ := specM_bind_ok h
    have h1 : CheckpointsStable s { s with balances := b } := ⟨rfl, rfl, rfl, rfl⟩
    exact h1.trans (apply_withdrawals_fulu_checkpointsStable rest _ s' h)

/-- The Fulu `process_withdrawals` keeps the slot and the checkpoints. -/
theorem process_withdrawals_fulu_checkpointsStable (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    CheckpointsStable s s' := by
  unfold process_withdrawals_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try contradiction
  refine (apply_withdrawals_fulu_checkpointsStable _ _ _
    ‹apply_withdrawals_fulu _ _ = _›).trans ?_
  refine (update_next_withdrawal_index_frame ‹update_next_withdrawal_index _ _ = _›).2.2.trans ?_
  exact CheckpointsStable.trans ⟨rfl, rfl, rfl, rfl⟩ (update_next_withdrawal_validator_index_frame h).2.2

/-- The Fulu `slash_validator` keeps the slot and the checkpoints. -/
theorem slash_validator_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (h : slash_validator_fulu p f s i w = .ok s') : CheckpointsStable s s' := by
  unfold slash_validator_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · refine (initiate_validator_exit_fulu_checkpointsStable p f _ s _ i
      ‹initiate_validator_exit_fulu _ _ _ _ _ = _›).trans ?_
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The Fulu `process_proposer_slashing` keeps the slot and the checkpoints. -/
theorem process_proposer_slashing_fulu_checkpointsStable (p : Preset) (o : Oracle)
    (f : FuluConfig) (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') : CheckpointsStable s s' := by
  unfold process_proposer_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | contradiction
    | exact slash_validator_fulu_checkpointsStable p f _ _ _ _ h

/-- The Fulu `process_attester_slashing` keeps the slot and the checkpoints. -/
theorem process_attester_slashing_fulu_checkpointsStable (p : Preset) (o : Oracle)
    (f : FuluConfig) (s s' : BeaconState) (a : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s a = .ok s') : CheckpointsStable s s' := by
  unfold process_attester_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine forIn_ok_invariant (fun r : MProd Bool BeaconState => CheckpointsStable s r.snd) _ ?_
    _ _ _ (CheckpointsStable.refl s) ‹forIn _ _ _ = _›
  intro index r step hr hstep
  obtain ⟨v, -, hstep⟩ := specM_bind_ok hstep
  obtain ⟨cur, -, hstep⟩ := specM_bind_ok hstep
  split at hstep
  · obtain ⟨r', hr', hstep⟩ := specM_bind_ok hstep
    cases hstep
    exact hr.trans (slash_validator_fulu_checkpointsStable p f _ _ index none hr')
  · cases hstep
    exact hr

/-- The Fulu `process_attestation` keeps the slot and the checkpoints. -/
theorem process_attestation_fulu_checkpointsStable (p : Preset) (o : Oracle)
    (s s' : BeaconState) (a : Attestation) (h : process_attestation_fulu p o s a = .ok s') :
    CheckpointsStable s s' := by
  unfold process_attestation_fulu at h
  cs_tac h

/-- The Fulu `process_voluntary_exit` keeps the slot and the checkpoints. -/
theorem process_voluntary_exit_fulu_checkpointsStable (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') : CheckpointsStable s s' := by
  unfold process_voluntary_exit_fulu at h
  ops_cs_tac h

/-- The Fulu `process_withdrawal_request` keeps the slot and the checkpoints. -/
theorem process_withdrawal_request_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (r : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s r = .ok s') : CheckpointsStable s s' := by
  unfold process_withdrawal_request_fulu at h
  ops_cs_tac h

/-- The Fulu `compute_consolidation_epoch_and_update_churn` keeps the slot and the
checkpoints. -/
theorem compute_consolidation_epoch_and_update_churn_fulu_checkpointsStable (p : Preset)
    (f : FuluConfig) (total_active_balance : Gwei) (s : BeaconState) (balance : Gwei)
    (r : Epoch × BeaconState)
    (h : compute_consolidation_epoch_and_update_churn_fulu p f total_active_balance s balance =
      .ok r) :
    CheckpointsStable s r.2 := by
  unfold compute_consolidation_epoch_and_update_churn_fulu at h
  cs_tac h

/-- The Fulu `process_consolidation_request` keeps the slot and the checkpoints. -/
theorem process_consolidation_request_fulu_checkpointsStable (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (r : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s r = .ok s') : CheckpointsStable s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | exact (switch_to_compounding_validator_effect h).stable.2.1
    | (cases h
       refine (compute_consolidation_epoch_and_update_churn_fulu_checkpointsStable _ _ _ _ _ _
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = _›).trans ?_
       exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The Fulu `process_operations` keeps the slot and the checkpoints. -/
theorem process_operations_fulu_checkpointsStable (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') : CheckpointsStable s s' := by
  unfold process_operations_fulu at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals try contradiction
  have h1 := foldlM_checkpointsStable _
    (fun s a s' h => process_proposer_slashing_fulu_checkpointsStable p o f s s' a h) _ _ _
    ‹List.foldlM (process_proposer_slashing_fulu p o f) _ _ = _›
  have h2 := foldlM_checkpointsStable _
    (fun s a s' h => process_attester_slashing_fulu_checkpointsStable p o f s s' a h) _ _ _
    ‹List.foldlM (process_attester_slashing_fulu p o f) _ _ = _›
  have h3 := foldlM_checkpointsStable _
    (fun s a s' h => process_attestation_fulu_checkpointsStable p o s s' a h) _ _ _
    ‹List.foldlM (process_attestation_fulu p o) _ _ = _›
  have h4 := foldlM_checkpointsStable _
    (fun s a s' h => process_voluntary_exit_fulu_checkpointsStable p o f s s' a h) _ _ _
    ‹List.foldlM (process_voluntary_exit_fulu p o f) _ _ = _›
  have h5 := foldlM_checkpointsStable _
    (fun s a s' h => (process_bls_to_execution_change_effects p o s s' a h).2.1) _ _ _
    ‹List.foldlM (process_bls_to_execution_change p o) _ _ = _›
  have h6 := foldlM_checkpointsStable _
    (fun s a s' h => (process_deposit_request_stable p s s' a h).2.2.1) _ _ _
    ‹List.foldlM process_deposit_request _ _ = _›
  have h7 := foldlM_checkpointsStable _
    (fun s a s' h => process_withdrawal_request_fulu_checkpointsStable p f s s' a h) _ _ _
    ‹List.foldlM (process_withdrawal_request_fulu p f) _ _ = _›
  have h8 := foldlM_checkpointsStable _
    (fun s a s' h => process_consolidation_request_fulu_checkpointsStable p f s s' a h) _ _ _ h
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

/-- The Fulu `process_block` keeps the slot and the checkpoints of the inner state. -/
theorem process_block_fulu_checkpointsStable (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (c : FuluBlockConfig) (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fs block = .ok fs') :
    CheckpointsStable fs.state fs'.state := by
  unfold process_block_fulu at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨fs3, h3, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  cases h
  have h3s := (process_execution_payload_fulu_ok p o fo c _ _ _ h3).1
  rw [h3s] at h4
  exact (process_block_header_fulu_checkpointsStable p o fo _ _ block h1).trans
    ((process_withdrawals_fulu_checkpointsStable p _ _ _ h2).trans
    ((process_randao_checkpointsStable p o _ _ _ h4).trans
    ((process_eth1_data_checkpointsStable p _ _ _ h5).trans
    ((process_operations_fulu_checkpointsStable p o f _ _ _ h6).trans
    (process_sync_aggregate_checkpointsStable p o _ _ _ h7)))))

/-! ## `state_transition_fulu` -/

/-- The Fulu `state_transition` keeps `FfgInvariant`. -/
theorem state_transition_fulu_ffg (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fs fs' : FuluState) (signed_block : FuluSignedBeaconBlock)
    (validate_result : Bool) (hinv : FfgInvariant p fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    FfgInvariant p fs'.state := by
  unfold state_transition_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact (process_slots_fulu_process_epoch_ffg p f o fo _ _ _ hinv
         ‹process_slots_fulu _ _ _ _ _ _ = _›).of_checkpointsStable
         (process_block_fulu_checkpointsStable p o fo f c _ _ _
           ‹process_block_fulu _ _ _ _ _ _ _ = _›))

/-- The Fulu `state_transition` ends at the slot of the block. -/
theorem state_transition_fulu_slot (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fs fs' : FuluState) (signed_block : FuluSignedBeaconBlock)
    (validate_result : Bool)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    fs'.state.slot = signed_block.message.slot := by
  unfold state_transition_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact (process_block_fulu_checkpointsStable p o fo f c _ _ _
         ‹process_block_fulu _ _ _ _ _ _ _ = _›).1.trans
         (process_slots_fulu_process_epoch_slot p f o fo _ _ _
           ‹process_slots_fulu _ _ _ _ _ _ = _›))

end EpochProofs.Spec
