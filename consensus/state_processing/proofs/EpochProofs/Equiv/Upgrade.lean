import EpochProofs.Equiv.Fulu
import EpochProofs.Sanity.Invariants.ForkUpgrade

/-!
# Lighthouse fork upgrades equal the reference

The values that the Fulu and Gloas upgrades compute go through translated functions:

- `upgrade_to_fulu`: `initialize_proposer_lookahead` calls
  `epoch_committees::proposer_indices_for_epoch` for the current and the next epoch, on all the
  active validators (`proposer_indices_for_epoch_spec_fulu`). Like the Fulu epoch step, this
  needs each Electra proposer loop to end before its last pass (`ProposerFin`).
- `upgrade_to_gloas`: `initialize_ptc_window` calls `epoch_committees::ptc_for_epoch` for the
  current and the next epoch (`initialize_ptc_window_lh`).

The loops over the epochs in `upgrade/fulu.rs` and `upgrade/gloas.rs`, and the field copies, are
glue: each loop concatenates the results in epoch order, after one empty epoch for the PTC
window. The onboarding of builders stays glue too. A review of it against the spec found no
difference: it keeps the spec's checks in the same order, and it appends each new builder,
which `add_builder_to_registry` does too, because a new builder has `withdrawable_epoch =
FAR_FUTURE_EPOCH` and so no index is free for reuse. Lighthouse runs the onboarding before
`initialize_ptc_window`, and the spec runs it after. The order does not matter: the onboarding
writes only the builders and the pending deposits (`onboard_builders_rel`), and the PTC reads
neither.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- `proposer_indices_for_epoch` on all the active validators returns Fulu
`get_beacon_proposer_indices`. -/
theorem proposer_indices_for_epoch_spec_fulu {H B : Type} (inst : ShuffleHashInst H)
    (ebi : EBInst B) (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_BEACON_PROPOSER.toList) (epoch : U64)
    (hindices : indices.val.map (·.val) = Spec.get_active_validator_indices state epoch.val)
    (hfin : ∀ s, Spec.ProposerFin p o state (Spec.get_active_validator_indices state epoch.val) s)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
    (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
    (c : LhSelectionConstants) (hc : SelectionConstantsMatch p c)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max) (props : List Nat)
    (hspec : Spec.get_beacon_proposer_indices_fulu p o state epoch.val = .ok props) :
    per_epoch_processing.epoch_committees.proposer_indices_for_epoch inst ebi balances indices
      domain epoch mix start_slot c ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = props ⦄ := by
  unfold Spec.get_beacon_proposer_indices_fulu at hspec
  simp only [except_bind_ok_iff] at hspec
  obtain ⟨sd, hsd, hcpi⟩ := hspec
  have hcpi' := Spec.compute_proposer_indices_fulu_ok p o state epoch.val sd _
    (fun x hx => Spec.active_validator_index_lt state epoch.val x hx) hfin props hcpi
  rw [← hindices] at hcpi'
  unfold per_epoch_processing.epoch_committees.proposer_indices_for_epoch
  apply spec_bind (compute_seed_eq inst p o hH state _ domain hdomain epoch mix hmix sd hsd)
  intro seed hseed
  exact compute_proposer_indices_spec inst ebi balances p o hH state hEB indices seed sd hseed
    epoch.val start_slot c.slots_per_epoch c.shuffle_round_count hc.shuffle_round_count
    c.max_effective_balance hc.max_effective_balance hc.slots_per_epoch hstart hn24 hus props hcpi'

/-- The reference `initialize_proposer_lookahead` concatenates the Fulu proposer indices of the
current epoch and of the next `MIN_SEED_LOOKAHEAD` epochs. -/
theorem initialize_proposer_lookahead_get (p : Spec.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (L : List Nat)
    (h : Spec.initialize_proposer_lookahead p o state = .ok L) :
    ∃ (ce : Nat) (per : List (List Nat)), Spec.get_current_epoch p state = .ok ce ∧
      L = per.flatten ∧
      per.length = p.MIN_SEED_LOOKAHEAD + 1 ∧
      ∀ i (_ : i < p.MIN_SEED_LOOKAHEAD + 1), ∃ (hi' : i < per.length) (e : Nat),
        Spec.uint64Add ce i = .ok e ∧
        Spec.get_beacon_proposer_indices_fulu p o state e = .ok per[i] := by
  unfold Spec.initialize_proposer_lookahead at h
  simp only [except_bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨ce, hce, per, hper, rfl⟩ := h
  obtain ⟨hlen, hget⟩ := Spec.mapM_ok_getElem _ _ per hper
  simp only [List.length_range] at hlen
  refine ⟨ce, per, hce, rfl, hlen, fun i hi => ⟨hlen ▸ hi, ?_⟩⟩
  have hf := hget i (by simpa using hi) (hlen ▸ hi)
  simp only [List.getElem_range, except_bind_ok_iff] at hf
  obtain ⟨e, he, hp⟩ := hf
  exact ⟨e, he, hp⟩

/-- The reference `initialize_ptc_window` is one empty epoch, then the PTCs of the slots of the
current epoch and of the next `MIN_SEED_LOOKAHEAD` epochs. -/
theorem initialize_ptc_window_get (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState)
    (w : List (List Nat)) (h : Spec.initialize_ptc_window p o state = .ok w) :
    ∃ (ce : Nat) (per : List (List (List Nat))), Spec.get_current_epoch p state = .ok ce ∧
      w = List.replicate p.SLOTS_PER_EPOCH (List.replicate p.PTC_SIZE 0) ++ per.flatten ∧
      per.length = 1 + p.MIN_SEED_LOOKAHEAD ∧
      ∀ e (_ : e < 1 + p.MIN_SEED_LOOKAHEAD), ∃ (he' : e < per.length) (epoch start : Nat),
        Spec.uint64Add ce e = .ok epoch ∧
        Spec.compute_start_slot_at_epoch p epoch = .ok start ∧
        per[e].length = p.SLOTS_PER_EPOCH ∧
        ∀ k (_ : k < p.SLOTS_PER_EPOCH), ∃ hk' : k < per[e].length,
          Spec.compute_ptc p o state (start + k) = .ok per[e][k] := by
  unfold Spec.initialize_ptc_window at h
  simp only [except_bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨ce, hce, per, hper, rfl⟩ := h
  obtain ⟨hlen, hget⟩ := Spec.mapM_ok_getElem _ _ per hper
  simp only [List.length_range] at hlen
  refine ⟨ce, per, hce, rfl, hlen, fun e he => ⟨hlen ▸ he, ?_⟩⟩
  have hf := hget e (by simpa using he) (hlen ▸ he)
  simp only [List.getElem_range, except_bind_ok_iff] at hf
  obtain ⟨epoch, hepoch, start, hstart, hm⟩ := hf
  obtain ⟨hlen2, hget2⟩ := Spec.mapM_ok_getElem _ _ _ hm
  simp only [List.length_range] at hlen2
  refine ⟨epoch, start, hepoch, hstart, hlen2, fun k hk => ⟨hlen2 ▸ hk, ?_⟩⟩
  have hk2 := hget2 k (by simpa using hk) (hlen2 ▸ hk)
  simp only [List.getElem_range, except_bind_ok_iff] at hk2
  obtain ⟨s, hs, hp⟩ := hk2
  simp only [Spec.uint64Add] at hs
  split at hs
  · cases hs; exact hp
  · simp [throw, throwThe, MonadExceptOf.throw] at hs

/-- Lighthouse `initialize_ptc_window`: for each epoch `current_epoch + e` of the window,
`ptc_for_epoch` returns the PTCs that the reference puts after the empty epoch. The loop in
`upgrade/gloas.rs` concatenates them in epoch order. -/
theorem initialize_ptc_window_lh {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (w : List (List Nat)) (hspec : Spec.initialize_ptc_window p o state = .ok w)
    (hspe : 0 < p.SLOTS_PER_EPOCH) (hus : Usize.max = U64.max) :
    ∃ (ce : Nat) (per : List (List (List Nat))), Spec.get_current_epoch p state = .ok ce ∧
      w = List.replicate p.SLOTS_PER_EPOCH (List.replicate p.PTC_SIZE 0) ++ per.flatten ∧
      per.length = 1 + p.MIN_SEED_LOOKAHEAD ∧
      ∀ e (he : e < per.length) (committees : Slice (alloc.vec.Vec Usize))
        (hclen : committees.val.length = p.SLOTS_PER_EPOCH) (domain : Array U8 4#usize)
        (hdomain : u8s domain.val = Spec.DOMAIN_PTC_ATTESTER.toList) (epoch : U64)
        (hepoch : epoch.val = ce + e)
        (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
        (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
        (hfit : start_slot.val + p.SLOTS_PER_EPOCH < 2 ^ 64)
        (hcomm : ∀ k (hk : k < committees.val.length) l,
          Spec.ptcIndices p o state epoch.val (start_slot.val + k) = .ok l →
            (committees.val[k]).val.map (·.val) = l)
        (_ : ∀ k (hk : k < committees.val.length), (committees.val[k]).val.length ≤ 2 ^ 24)
        (ptc_size : Usize) (_ : ptc_size.val = p.PTC_SIZE) (c : LhSelectionConstants)
        (_ : SelectionConstantsMatch p c),
        per_epoch_processing.epoch_committees.ptc_for_epoch inst ebi balances committees domain
          epoch mix start_slot ptc_size c ⦃ r =>
            ∃ v : alloc.vec.Vec (alloc.vec.Vec Usize), r = .Ok v ∧ ptcsOf v = per[e] ⦄ := by
  obtain ⟨ce, per, hce, hw, hlen, hget⟩ := initialize_ptc_window_get p o state w hspec
  refine ⟨ce, per, hce, hw, hlen, ?_⟩
  intro e he committees hclen domain hdomain epoch hepoch mix hmix start_slot hstart hfit hcomm
    hn24 ptc_size hptc c hc
  obtain ⟨he', ep, start, hep, hst, hplen, hk⟩ := hget e (hlen ▸ he)
  have hepv : ep = epoch.val := by
    simp only [Spec.uint64Add] at hep
    split at hep
    · cases hep; exact hepoch.symm
    · simp [throw, throwThe, MonadExceptOf.throw] at hep
  subst hepv
  rw [hstart] at hst
  have hsv : start = start_slot.val := (Except.ok.inj hst).symm
  subst hsv
  exact ptc_for_epoch_spec_gen inst ebi balances p o hH state hEB committees hclen domain hdomain
    epoch mix hmix start_slot hstart hfit per[e] hplen hk hcomm hn24 ptc_size hptc c hc hspe hus

end EpochProofs
