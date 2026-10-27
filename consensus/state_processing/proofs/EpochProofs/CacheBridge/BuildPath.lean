import EpochProofs.CacheBridge.EpochCache
import EpochProofs.CachePubkey
import EpochProofs.Sanity.Invariants.ForkUpgrade

/-!
# Cache build facts on the epoch path

`process_epoch_single_pass` starts with `initialize_epoch_cache`,
`initialize_progressive_balances_cache` and `update_pubkey_cache`. Each call keeps a cache that is
already built and builds only a missing one. So the epoch reads a cache that an earlier state of
the run built. This file carries the build facts from that earlier state to the epoch input.

- Epoch cache: the cache key is the epoch and its decision root. Inside one epoch, every block
  keeps the effective balances and the activity at the epoch (`ActiveAgree`, from
  `state_transition_epochInv`). So the active sum that the cache holds stays equal to the sum of
  the epoch input (`epoch_cache_total_carry`).
- Pubkey cache: the validator pubkeys only grow at the end (`PkPrefix`). So a cache that holds the
  pubkeys of an earlier state holds a prefix of the pubkeys of the epoch input, and
  `update_pubkey_cache` completes it (`pubkey_cache_carry`).
- Progressive balances cache: `initialize_progressive_balances_cache` now rebuilds a cache built
  for another epoch. The block operations keep the cache with the update functions that
  `CacheProofs.PB` proves (`attestation_coherent`, `slashing_coherent`,
  `effective_balance_change_coherent`, `epoch_transition_coherent`, `add_validator_coherent`).
  That each mutation calls its update function is checked by review only.
-/

namespace EpochProofs.Spec

/-- `ActiveAgree` is symmetric. -/
theorem ActiveAgree.symm {E : Epoch} {s t : BeaconState} (h : ActiveAgree E s t) :
    ActiveAgree E t s := by
  refine ⟨h.1.symm, fun i v v' hv hv' => ?_⟩
  obtain ⟨he, ha⟩ := h.2 i v' v hv' hv
  exact ⟨he.symm, ha.symm⟩

/-- The pubkeys of `s` are a prefix of the pubkeys of `s'`. -/
def PkPrefix (s s' : BeaconState) : Prop :=
  s.validators.map (·.pubkey) <+: s'.validators.map (·.pubkey)

theorem PkPrefix.refl (s : BeaconState) : PkPrefix s s := List.prefix_refl _

theorem PkPrefix.trans {s1 s2 s3 : BeaconState} (h12 : PkPrefix s1 s2) (h23 : PkPrefix s2 s3) :
    PkPrefix s1 s3 :=
  List.IsPrefix.trans h12 h23

/-- A slot change keeps the pubkeys. -/
theorem PkPrefix.bump {s t : BeaconState} {n : Slot} (h : PkPrefix s t) :
    PkPrefix s { t with slot := n } := h

theorem PkSame.pkPrefix {s s' : BeaconState} (h : PkSame s s') : PkPrefix s s' := by
  unfold PkPrefix
  rw [h]

/-- `apply_pending_deposit` keeps the pubkeys or adds one at the end. -/
theorem apply_pending_deposit_pkPrefix (p : Preset) (o : Oracle) (s s' : BeaconState)
    (deposit : PendingDeposit) (h : apply_pending_deposit p o s deposit = .ok s') :
    PkPrefix s s' := by
  have hadd : ∀ (pk : BLSPubkey) (wc : Bytes32) (amount : Gwei) (t : BeaconState),
      add_validator_to_registry p s pk wc amount = .ok t → PkPrefix s t := by
    intro pk wc amount t ht
    unfold add_validator_to_registry at ht
    obtain ⟨v, -, ht⟩ := specM_bind_ok ht
    obtain ⟨l, hl, ht⟩ := specM_bind_ok ht
    simp only [bind, Except.bind, pure, Except.pure] at ht
    repeat' split at ht
    all_goals first | contradiction | skip
    cases ht
    unfold set_or_append_list get_index_for_new_validator at hl
    simp only [beq_self_eq_true, if_true, pure, Except.pure, Except.ok.injEq] at hl
    subst hl
    unfold PkPrefix
    simp only [List.map_append]
    exact List.prefix_append _ _
  unfold apply_pending_deposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact PkPrefix.refl _)
    | exact hadd _ _ _ _ h

/-- `process_pending_deposits` with `apply_pending_deposit` keeps a pubkey prefix. -/
theorem process_pending_deposits_pkPrefix (p : Preset) (o : Oracle)
    (total_active_balance : Gwei) (s s' : BeaconState)
    (h : process_pending_deposits p total_active_balance (apply_pending_deposit p o) s = .ok s') :
    PkPrefix s s' := by
  unfold process_pending_deposits at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨_, _, _, _, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := SlashingsSanity.forIn_invariant
    (fun r : MProd (List PendingDeposit) (MProd Bool (MProd Uint64 (MProd Uint64 BeaconState))) =>
      PkPrefix s r.2.2.2.2) _ ?_ _ _ _ (PkPrefix.refl s) hr
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
         exact hst.trans (apply_pending_deposit_pkPrefix p o _ _ _
           ‹apply_pending_deposit _ _ _ _ = _›))

/-- `process_epoch` keeps a pubkey prefix. -/
theorem process_epoch_pkPrefix [PresetCfg] (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_epoch p o s = .ok s') : PkPrefix s s' := by
  unfold process_epoch at h
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
  obtain ⟨s14, h14, h⟩ := specM_bind_ok h
  obtain ⟨s15, h15, h⟩ := specM_bind_ok h
  have d6 : PkSame s s6 :=
    (PkSame.of_eq (process_justification_and_finalization_frame p s s1 h1).1.1).trans
    ((PkSame.of_eq (process_inactivity_updates_validators p _ _ h2)).trans
    ((PkSame.of_eq (process_rewards_and_penalties_validators p _ _ _ h3)).trans
    ((process_registry_updates_pkSame p _ _ _ h4).trans
    ((PkSame.of_eq (process_slashings_validators p _ _ _ h5)).trans
    (PkSame.of_eq (process_eth1_data_reset_frame p _ _ h6).1.1)))))
  have d7 := process_pending_deposits_pkPrefix p o _ _ _ h7
  have d15 : PkSame s7 s' :=
    (PkSame.of_eq (process_pending_consolidations_validators p _ _ h8)).trans
    ((PkSame.of_eq (process_builder_pending_payments_validators p _ _ _ h9)).trans
    ((process_effective_balance_updates_pkSame p _ _ h10).trans
    ((PkSame.of_eq (process_slashings_reset_frame p _ _ h11).1.1).trans
    ((PkSame.of_eq (process_randao_mixes_reset_frame p _ _ h12).1.1).trans
    ((PkSame.of_eq (process_historical_summaries_update_frame p o _ _ h13).1.1).trans
    ((PkSame.of_eq (process_sync_committee_updates_frame p o _ _ h14).1.1).trans
    ((PkSame.of_eq (process_proposer_lookahead_frame p o _ _ h15).1.1).trans
    (PkSame.of_eq (process_ptc_window_frame p o _ _ h).1.1))))))))
  exact d6.pkPrefix.trans (d7.trans d15.pkPrefix)

/-- `process_slot` keeps the pubkeys. -/
theorem process_slot_pkPrefix [PresetCfg] (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_slot p o s = .ok s') : PkPrefix s s' :=
  (PkSame.of_eq (process_slot_frame p o _ _ h).1.1).pkPrefix

/-- `process_slots` with the real `process_epoch` keeps a pubkey prefix. -/
theorem process_slots_pkPrefix [PresetCfg] (p : Preset) (o : Oracle) (s s' : BeaconState) (slot : Slot)
    (h : process_slots p o (process_epoch p o) s slot = .ok s') : PkPrefix s s' :=
  process_slots_invariant p o (process_epoch p o) (PkPrefix s)
    (fun _ _ ht hP => hP.trans (process_slot_pkPrefix p o _ _ ht))
    (fun _ _ ht hP => hP.trans (process_epoch_pkPrefix p o _ _ ht))
    (fun _ _ hP => hP) s s' slot (PkPrefix.refl s) h

/-- `state_transition` keeps a pubkey prefix. -/
theorem state_transition_pkPrefix [PresetCfg] (p : Preset) (o : Oracle)
    (max_blobs_per_block : Epoch → Uint64) (GLOAS_FORK_EPOCH : Epoch) (s s' : BeaconState)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (h : state_transition p o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
      validate_result = .ok s') :
    PkPrefix s s' := by
  unfold state_transition at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact (process_slots_pkPrefix p o _ _ _ ‹process_slots _ _ _ _ _ = _›).trans
         (process_block_pkSame p o max_blobs_per_block GLOAS_FORK_EPOCH _ _ _
           ‹process_block _ _ _ _ _ _ = _›).pkPrefix)

/-- Every state of a reachable Gloas run has the start pubkeys as a prefix. -/
theorem Reachable.pkPrefix [PresetCfg] {o : Oracle} {max_blobs_per_block : Epoch → Uint64}
    {GLOAS_FORK_EPOCH : Epoch} {init s : BeaconState}
    (hr : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH init s) : PkPrefix init s := by
  induction hr with
  | init => exact PkPrefix.refl _
  | step _ _ _ _ _ ht ih => exact ih.trans (state_transition_pkPrefix _ o _ _ _ _ _ _ ht)

/-- The Gloas slot loop keeps a pubkey prefix. -/
theorem SlotReachG.pkPrefix [PresetCfg] {o : Oracle} {s t : BeaconState} {slot : Slot}
    (hr : SlotReachG o s slot t) : PkPrefix s t := by
  induction hr with
  | refl => exact PkPrefix.refl _
  | skip _ _ ht _ ih =>
    exact PkPrefix.bump (ih.trans (process_slot_pkPrefix _ o _ _ ht))
  | epoch _ _ ht _ he ih =>
    exact PkPrefix.bump
      (ih.trans ((process_slot_pkPrefix _ o _ _ ht).trans (process_epoch_pkPrefix _ o _ _ he)))

end EpochProofs.Spec

namespace EpochProofs.CacheBridge

open EpochProofs.Spec
open CacheProofs.PB (activeAt ebAt)

theorem activeAt_pb_congr {E : Nat} {s t : BeaconState} (h : ActiveAgree E s t) (i : Nat) :
    activeAt (t.validators.map pbValidator) E i = activeAt (s.validators.map pbValidator) E i ∧
      ebAt (t.validators.map pbValidator) i = ebAt (s.validators.map pbValidator) i := by
  simp only [activeAt, ebAt, List.getElem?_map]
  cases hs : s.validators[i]? with
  | none =>
    have ht : t.validators[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hs ⊢
      rw [h.1]; exact hs
    simp [ht]
  | some v =>
    have hi : i < t.validators.length := by
      rw [h.1]; exact (List.getElem?_eq_some_iff.mp hs).1
    have ht := List.getElem?_eq_getElem hi
    obtain ⟨he, ha⟩ := h.2 i v _ hs ht
    simp only [ht, Option.map_some]
    refine ⟨?_, ?_⟩
    · show CacheProofs.Spec.is_active_validator (pbValidator _) E =
        CacheProofs.Spec.is_active_validator (pbValidator v) E
      have : ∀ w : Validator, CacheProofs.Spec.is_active_validator (pbValidator w) E =
          is_active_validator w E := fun _ => rfl
      rw [this, this, ha]
    · show (pbValidator _).effective_balance = (pbValidator v).effective_balance
      exact he

/-- The active sum that the epoch cache model computes is the same for two states that agree on
the effective balances and on the activity at epoch `E`. -/
theorem activeSum_congr {E : Nat} {s t : BeaconState} (h : ActiveAgree E s t) :
    CacheProofs.EpochCache.activeSum
        (CacheProofs.EpochCache.activeAt (t.validators.map ecValidator) E)
        (t.validators.map (·.effective_balance)) =
      CacheProofs.EpochCache.activeSum
        (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) E)
        (s.validators.map (·.effective_balance)) := by
  have hmap : ∀ vs : List Validator, vs.map (·.effective_balance) =
      (vs.map ecValidator).map (·.effective_balance) := by
    intro vs; rw [List.map_map]; rfl
  rw [hmap t.validators, hmap s.validators, activeSum_eq, activeSum_eq, h.1]
  congr 1
  rw [List.filter_congr (fun i _ => (activeAt_pb_congr h i).1)]
  exact List.map_congr_left (fun i _ => (activeAt_pb_congr h i).2)

/-- **Epoch cache carry.** Lighthouse reuses the epoch cache that a state `b` of the same epoch
built. Its total is the active sum of `b`. If the blocks between `b` and the epoch input `t` keep
the effective balances and the activity at the epoch, the total is the active sum of `t`. -/
theorem epoch_cache_total_carry {E : Nat} {b t : BeaconState} (total : Nat)
    (hb : total = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator) E)
      (b.validators.map (·.effective_balance)))
    (h : ActiveAgree E b t) :
    total = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (t.validators.map ecValidator) E)
      (t.validators.map (·.effective_balance)) := by
  rw [activeSum_congr h]; exact hb

/-- Two states of the blocks of epoch `E` on mainnet agree on the effective balances and on the
activity at `E`. `EpochInv` is what `state_transition_epochInv` keeps for each block. -/
theorem activeAgree_of_epochInv [PresetCfg] {s0 r b t : BeaconState} {E nb nt : Nat}
    (hb : EpochInv s0 r E nb b) (ht : EpochInv s0 r E nt t) : ActiveAgree E b t :=
  hb.2.2.2.1.symm.trans ht.2.2.2.1

open Aeneas Aeneas.Std Result CacheProofs in
/-- **Pubkey cache carry.** A cache that holds the pubkeys of an earlier state `b` holds a prefix
of the pubkeys of `t`. `update_pubkey_cache` inserts the rest in index order, and the result
holds the pubkeys of `t`. -/
theorem pubkey_cache_carry {M : Type} {inst : types.state.pubkey_index.IndexMap M BLSPubkey}
    {view : M → BLSPubkey → Option Usize} (laws : IndexMapLaws inst view)
    {b t : BeaconState} (hp : PkPrefix b t) {m m' : M} {len len' : Usize}
    (hc : Coherent view m len (b.validators.map (·.pubkey)))
    (hrun : insertAll inst m len ((t.validators.map (·.pubkey)).drop len.val) =
      ok (some (m', len'))) :
    Coherent view m' len' (t.validators.map (·.pubkey)) := by
  obtain ⟨tail, htail⟩ := hp
  have hlen : len.val = (b.validators.map (·.pubkey)).length := hc.1
  have htake : (t.validators.map (·.pubkey)).take len.val = b.validators.map (·.pubkey) := by
    rw [← htail, hlen, List.take_left]
  exact update_coherent laws (htake ▸ hc) hrun

end EpochProofs.CacheBridge
