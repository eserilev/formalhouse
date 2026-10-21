import EpochProofs.Equiv.BalanceWeightedSelection
import EpochProofs.Spec.EpochCommittees
import EpochProofs.Equiv.RewardsAndPenalties
import EpochProofs.Equiv.PendingDeposits
import EpochProofs.Sanity.PtcIndices

/-!
# Lighthouse Gloas committee steps equal the reference

- `next_sync_committee_indices_spec`: `epoch_committees::next_sync_committee_indices` returns
  `get_next_sync_committee_indices`.
- `compute_proposer_indices_spec` and `next_proposer_lookahead_spec`: the proposer lookahead.
- `ptc_for_epoch_spec`: the PTCs that `process_ptc_window` appends.

The glue in `single_pass.rs` and `sync_committee_updates.rs` passes the inputs. Each theorem
takes the glue facts as hypotheses:

- `SeedMixLink`: `get_seed_mix` reads the RANDAO mix that `get_seed` reads.
- the index lists: the active (and unslashed) validators, or the committees of each slot that
  the committee cache holds (see the committee cache proofs, eserilev/lighthouse-aeneas #28).
- `EBLink`: `BeaconState::get_effective_balance` reads the registry.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The RANDAO mix that `get_seed(state, epoch, ·)` reads. -/
def Spec.seedMix (p : Spec.Preset) (state : Spec.BeaconState) (epoch : Nat) :
    Spec.SpecM Spec.Bytes32 := do
  Spec.get_randao_mix p state
    (← Spec.uint64Sub (← Spec.uint64Sub (← Spec.uint64Add epoch p.EPOCHS_PER_HISTORICAL_VECTOR)
      p.MIN_SEED_LOOKAHEAD) 1)

theorem get_seed_eq (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState) (epoch : Nat)
    (domain : Spec.DomainType) :
    Spec.get_seed p o state epoch domain = (do
      let mix ← Spec.seedMix p state epoch
      pure (o.hash (domain.toList ++ Spec.uint_to_bytes 8 epoch ++ mix.toList))) := by
  simp only [Spec.get_seed, Spec.seedMix, bind_assoc]

/-- The mix that Lighthouse passes is the mix that `get_seed` reads. -/
def SeedMixLink (p : Spec.Preset) (state : Spec.BeaconState) (epoch : Nat)
    (mix : Array U8 32#usize) : Prop :=
  ∀ m, Spec.seedMix p state epoch = .ok m → u8s mix.val = m.toList

theorem compute_seed_eq {H : Type} (inst : ShuffleHashInst H) (p : Spec.Preset)
    (o : Spec.Oracle) (hH : HashLink inst o) (state : Spec.BeaconState) (domainSpec : Spec.DomainType)
    (domain : Array U8 4#usize) (hdomain : u8s domain.val = domainSpec.toList) (epoch : U64)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (s : Spec.Bytes32)
    (hs : Spec.get_seed p o state epoch.val domainSpec = .ok s) :
    types.state.balance_weighted_selection.compute_seed inst domain epoch mix ⦃ d =>
      u8s d.val = s.toList ⦄ := by
  rw [get_seed_eq] at hs
  simp only [except_bind_ok_iff, pure, Except.pure, Except.ok.injEq] at hs
  obtain ⟨m, hm, hsm⟩ := hs
  apply spec_mono (compute_seed_spec inst o hH domain epoch mix)
  intro d hd
  rw [hd, hdomain, hmix m hm, ← hsm]

abbrev LhSelectionConstants := per_epoch_processing.epoch_committees.SelectionConstants

/-- The selection constants of Lighthouse are the preset values. -/
structure SelectionConstantsMatch (p : Spec.Preset) (c : LhSelectionConstants) : Prop where
  shuffle_round_count : c.shuffle_round_count.val = p.SHUFFLE_ROUND_COUNT
  max_effective_balance : c.max_effective_balance.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA
  slots_per_epoch : c.slots_per_epoch.val = p.SLOTS_PER_EPOCH

/-- `next_sync_committee_indices` equals `get_next_sync_committee_indices`. -/
theorem next_sync_committee_indices_spec {H B : Type} (inst : ShuffleHashInst H)
    (ebi : EBInst B) (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_SYNC_COMMITTEE.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce → epoch.val = ce + 1)
    (hindices : indices.val.map (·.val) = Spec.get_active_validator_indices state epoch.val)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (size : Usize)
    (hsize : size.val = p.SYNC_COMMITTEE_SIZE) (c : LhSelectionConstants)
    (hc : SelectionConstantsMatch p c) (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max)
    (res : List Nat) (hspec : Spec.get_next_sync_committee_indices p o state = .ok res) :
    per_epoch_processing.epoch_committees.next_sync_committee_indices inst ebi balances indices
      domain epoch mix size c ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ := by
  unfold Spec.get_next_sync_committee_indices at hspec
  simp only [except_bind_ok_iff] at hspec
  obtain ⟨ce, hce, e, he, s, hs, hrun⟩ := hspec
  have hev : e = epoch.val := by
    rw [hepoch ce hce]
    simp only [Spec.uint64Add] at he
    split at he
    · exact (Except.ok.inj he).symm
    · simp [throw, throwThe, MonadExceptOf.throw] at he
  subst hev
  unfold per_epoch_processing.epoch_committees.next_sync_committee_indices
  apply spec_bind (compute_seed_eq inst p o hH state _ domain hdomain epoch mix hmix s hs)
  intro seed hseed
  rw [← hindices, ← hsize] at hrun
  exact compute_balance_weighted_selection_spec inst ebi balances p o hH state hEB indices seed s
    hseed true c.shuffle_round_count hc.shuffle_round_count c.max_effective_balance
    hc.max_effective_balance hn24 size hus res hrun

theorem mapM_ok_get {ε α β : Type} (f : α → Except ε β) (l : List α) (r : List β)
    (h : l.mapM f = .ok r) :
    r.length = l.length ∧ ∀ k (hk : k < l.length), ∃ hk' : k < r.length, f l[k] = .ok r[k] := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons a l ih =>
    simp only [List.mapM_cons, except_bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih r' hr'
    refine ⟨by simp [h1], ?_⟩
    intro k hk
    cases k with
    | zero => exact ⟨by simp, hb⟩
    | succ k =>
      obtain ⟨hk', hf⟩ := h2 k (by simpa using hk)
      exact ⟨by simpa using hk', by simpa using hf⟩

/-- The facts that the reference `compute_proposer_indices` gives for slot `start + k`. -/
theorem spec_proposers_get (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState)
    (epoch : Nat) (seedSpec : Spec.Bytes32) (idx : List Nat) (res : List Nat)
    (h : Spec.compute_proposer_indices p o state epoch seedSpec idx = .ok res) :
    ∃ start, Spec.compute_start_slot_at_epoch p epoch = .ok start ∧
      res.length = p.SLOTS_PER_EPOCH ∧ ∀ k (hk : k < p.SLOTS_PER_EPOCH),
        start + k < 2 ^ 64 ∧ ∃ l, Spec.compute_balance_weighted_selection p o state idx
          (o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (start + k))) 1 true = .ok l ∧
          ∃ hk' : k < res.length, l[0]? = some res[k] := by
  unfold Spec.compute_proposer_indices at h
  simp only [except_bind_ok_iff] at h
  obtain ⟨start, hstart, seeds, hseeds, hres⟩ := h
  refine ⟨start, hstart, ?_⟩
  obtain ⟨hl1, hg1⟩ := mapM_ok_get _ _ _ hseeds
  obtain ⟨hl2, hg2⟩ := mapM_ok_get _ _ _ hres
  simp only [List.length_range] at hl1
  refine ⟨by rw [hl2, hl1], ?_⟩
  intro k hk
  obtain ⟨hk1, hs⟩ := hg1 k (by simpa using hk)
  simp only [List.getElem_range, except_bind_ok_iff, pure, Except.pure, Except.ok.injEq] at hs
  obtain ⟨sl, hsl, hseedk⟩ := hs
  have hslv : start + k < 2 ^ 64 ∧ sl = start + k := by
    simp only [Spec.uint64Add] at hsl
    split at hsl
    · rename_i hlt; exact ⟨by unfold Spec.UINT64_SIZE at hlt; exact hlt, (Except.ok.inj hsl).symm⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hsl
  refine ⟨hslv.1, ?_⟩
  obtain ⟨hk2, hp⟩ := hg2 k (by rw [hl1]; exact hk)
  simp only [except_bind_ok_iff] at hp
  obtain ⟨l, hl, hget⟩ := hp
  refine ⟨l, ?_, hk2, ?_⟩
  · rw [← hslv.2, hseedk]; exact hl
  · simp only [Spec.listGet] at hget
    split at hget
    · rename_i a ha; rw [ha, Except.ok.inj hget]
    · simp [throw, throwThe, MonadExceptOf.throw] at hget

theorem proposer_at_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (seed : Array U8 32#usize) (seedSpec : Spec.Bytes32)
    (hseed : u8s seed.val = seedSpec.toList) (start_slot i : U64) (R : U8)
    (hR : R.val = p.SHUFFLE_ROUND_COUNT) (maxeb : U64)
    (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max)
    (hlt : start_slot.val + i.val < 2 ^ 64) (l : List Nat)
    (hl : Spec.compute_balance_weighted_selection p o state (indices.val.map (·.val))
      (o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (start_slot.val + i.val))) 1 true = .ok l)
    (pr : Nat) (hpr : l[0]? = some pr) :
    types.state.balance_weighted_selection.proposer_at inst ebi balances indices seed start_slot i
      R maxeb ⦃ r => ∃ x : Usize, r = .Ok x ∧ x.val = pr ⦄ := by
  unfold types.state.balance_weighted_selection.proposer_at
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (safe_add_spec start_slot i)
  cases r with
  | Err e => exact absurd hlt (hp.2 e rfl).2
  | Ok sl =>
  have hsl := (hp.1 sl rfl).1
  rw [hr]
  simp only [bind_tc_ok, branch_ok]
  step with hash_with_u64_spec inst o hH seed sl as ⟨ss, hss⟩
  rw [hseed, hsl] at hss
  apply spec_bind (compute_balance_weighted_selection_spec inst ebi balances p o hH state hEB
    indices ss _ hss true R hR maxeb hmaxeb hn24 1#usize hus l (by simpa using hl))
  intro r hr2
  obtain ⟨v, hrv, hv⟩ := hr2
  simp only [hrv, bind_tc_ok, branch_ok]
  have h0 : (v.val.map (·.val))[0]? = some pr := by rw [hv]; exact hpr
  cases hv0 : v.val with
  | nil => rw [hv0] at h0; simp at h0
  | cons x rest =>
    rw [hv0] at h0
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h0
    simp only [alloc.vec.Vec.deref, slice_get_usize]
    simp [hv0, h0]

theorem u64_saturating_add_one' (x : U64) (h : x.val < 2 ^ 64 - 1) :
    (core.num.U64.saturating_add x 1#u64).val = x.val + 1 :=
  u64_saturating_add_one x (by rw [U64.max_eq]; omega)

/-- `compute_proposer_indices` equals the reference, for the epoch that starts at
`start_slot`. -/
theorem compute_proposer_indices_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (seed : Array U8 32#usize) (seedSpec : Spec.Bytes32)
    (hseed : u8s seed.val = seedSpec.toList) (epoch : Nat) (start_slot spe : U64) (R : U8)
    (hR : R.val = p.SHUFFLE_ROUND_COUNT) (maxeb : U64)
    (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA) (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hstart : Spec.compute_start_slot_at_epoch p epoch = .ok start_slot.val)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max) (res : List Nat)
    (hspec : Spec.compute_proposer_indices p o state epoch seedSpec (indices.val.map (·.val)) =
      .ok res) :
    types.state.balance_weighted_selection.compute_proposer_indices inst ebi balances indices
      seed start_slot spe R maxeb ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ := by
  obtain ⟨start, hstart', hlen, hk⟩ := spec_proposers_get p o state epoch seedSpec _ res hspec
  rw [hstart] at hstart'
  have hsv : start = start_slot.val := (Except.ok.inj hstart').symm
  subst hsv
  unfold types.state.balance_weighted_selection.compute_proposer_indices
  unfold types.state.balance_weighted_selection.compute_proposer_indices_loop
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec Usize × U64) => spe.val - x.2.val)
    (inv := fun (x : alloc.vec.Vec Usize × U64) => x.2.val ≤ spe.val ∧
      x.1.val.map (·.val) = res.take x.2.val)
  · rintro ⟨props, j⟩ ⟨hj, hprops⟩
    dsimp only at hj hprops ⊢
    unfold types.state.balance_weighted_selection.compute_proposer_indices_loop.body
    split
    · rename_i hlt
      have hjs : j.val < p.SLOTS_PER_EPOCH := by rw [← hspe]; scalar_tac
      obtain ⟨hfit, l, hl, hk', hl0⟩ := hk j.val hjs
      apply spec_bind (proposer_at_spec inst ebi balances p o hH state hEB indices seed seedSpec
        hseed start_slot j R hR maxeb hmaxeb hn24 hus hfit l hl _ hl0)
      intro r hr
      obtain ⟨x, hrx, hx⟩ := hr
      simp only [hrx]
      have hpl : props.val.length < Usize.max := by
        have : props.val.length = j.val := by
          have := congrArg List.length hprops
          simp only [List.length_map, List.length_take] at this
          omega
        rw [this, hus, U64.max_eq]; scalar_tac
      step*
      have hjv := u64_saturating_add_one' j (by scalar_tac)
      simp only [lift, bind_tc_ok, spec_ok]
      rw [hjv]
      refine ⟨by omega, ?_, by omega⟩
      rw [proposers1_post, List.map_append, hprops, List.take_succ_eq_append_getElem hk']
      simp only [List.map_cons, List.map_nil, hx]
    · rename_i hge
      have : j.val = spe.val := by scalar_tac
      simp only [spec_ok]
      refine ⟨props, rfl, ?_⟩
      rw [hprops, this, hspe, ← hlen, List.take_length]
  · exact ⟨by simp, by simp⟩

theorem shift_loop0_spec (look : Slice U64) (shifted : alloc.vec.Vec U64) (spe k : Usize)
    (hk : spe.val ≤ k.val) (hkl : k.val ≤ look.val.length)
    (hs : shifted.val.map (·.val) = ((look.val.take k.val).drop spe.val).map (·.val)) :
    per_epoch_processing.epoch_committees.shift_lookahead_loop0 look shifted k ⦃ r =>
      r.val.map (·.val) = (look.val.drop spe.val).map (·.val) ⦄ := by
  unfold per_epoch_processing.epoch_committees.shift_lookahead_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec U64 × Usize) => look.val.length - x.2.val)
    (inv := fun (x : alloc.vec.Vec U64 × Usize) => spe.val ≤ x.2.val ∧
      x.2.val ≤ look.val.length ∧
      x.1.val.map (·.val) = ((look.val.take x.2.val).drop spe.val).map (·.val))
  · rintro ⟨sh, j⟩ ⟨hj1, hj2, hsh⟩
    dsimp only at hj1 hj2 hsh ⊢
    unfold per_epoch_processing.epoch_committees.shift_lookahead_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hjl : j.val < look.val.length := by simpa [Slice.len_val] using hlt
      have hshl : sh.val.length < Usize.max := by
        have := congrArg List.length hsh
        simp only [List.length_map, List.length_drop, List.length_take] at this
        have := look.property
        omega
      rw [slice_get_any, List.getElem?_eq_getElem hjl]
      simp only [bind_tc_ok]
      step*
      have hj1' := usize_saturating_add_one j (by scalar_tac)
      simp only [lift, bind_tc_ok, spec_ok]
      rw [hj1']
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [shifted1_post, List.map_append, hsh, List.take_succ_eq_append_getElem hjl,
        List.drop_append_of_le_length (by simp; omega)]
      simp
    · rename_i hge
      have : j.val = look.val.length := by
        have : ¬ j.val < look.val.length := by simpa [Slice.len_val] using hge
        omega
      simp only [spec_ok]
      rw [hsh, this, List.take_length]
  · exact ⟨hk, hkl, hs⟩

theorem shift_loop1_spec (props : Slice Usize) (shifted : alloc.vec.Vec U64) (base : List Nat)
    (hbase : shifted.val.map (·.val) = base) (hlen : base.length + props.val.length ≤ Usize.max) :
    per_epoch_processing.epoch_committees.shift_lookahead_loop1 props shifted 0#usize ⦃ r =>
      r.val.map (·.val) = base ++ props.val.map (·.val) ⦄ := by
  unfold per_epoch_processing.epoch_committees.shift_lookahead_loop1
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec U64 × Usize) => props.val.length - x.2.val)
    (inv := fun (x : alloc.vec.Vec U64 × Usize) => x.2.val ≤ props.val.length ∧
      x.1.val.map (·.val) = base ++ (props.val.take x.2.val).map (·.val))
  · rintro ⟨sh, j⟩ ⟨hj, hsh⟩
    dsimp only at hj hsh ⊢
    unfold per_epoch_processing.epoch_committees.shift_lookahead_loop1.body
    dsimp only
    split
    · rename_i hlt
      have hjl : j.val < props.val.length := by simpa [Slice.len_val] using hlt
      have hshl : sh.val.length < Usize.max := by
        have := congrArg List.length hsh
        simp only [List.length_map, List.length_append, List.length_take] at this
        omega
      rw [slice_get_usize, List.getElem?_eq_getElem hjl]
      simp only [bind_tc_ok]
      step*
      have hj1' := usize_saturating_add_one j (by omega)
      simp only [lift, bind_tc_ok, spec_ok]
      rw [hj1']
      refine ⟨by omega, ?_, by omega⟩
      rw [shifted1_post, List.map_append, hsh, List.take_succ_eq_append_getElem hjl, x_post]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        cast_u64_of_usize]
    · rename_i hge
      have : j.val = props.val.length := by
        have : ¬ j.val < props.val.length := by simpa [Slice.len_val] using hge
        omega
      simp only [spec_ok]
      rw [hsh, this, List.take_length]
  · exact ⟨by simp, by simp [hbase]⟩

theorem shift_lookahead_spec (look : Slice U64) (spe : Usize) (props : Slice Usize)
    (hspe : spe.val ≤ look.val.length) (hp : props.val.length = spe.val) :
    per_epoch_processing.epoch_committees.shift_lookahead look spe props ⦃ r =>
      ∃ v : alloc.vec.Vec U64, r = some v ∧
        v.val.map (·.val) = (look.val.drop spe.val).map (·.val) ++ props.val.map (·.val) ⦄ := by
  unfold per_epoch_processing.epoch_committees.shift_lookahead
  apply spec_bind (shift_loop0_spec look _ spe spe (le_refl _) hspe (by simp))
  intro sh hsh
  have hll := look.property
  apply spec_bind (shift_loop1_spec props sh _ hsh (by simp; omega))
  intro sh1 hsh1
  have hl : (alloc.vec.Vec.len sh1).val = (Slice.len look).val := by
    have := congrArg List.length hsh1
    simp only [List.length_map, List.length_append, List.length_drop] at this
    simp; omega
  have : alloc.vec.Vec.len sh1 = Slice.len look := UScalar.eq_of_val_eq hl
  simp only [this, if_true, spec_ok]
  exact ⟨sh1, rfl, hsh1⟩

theorem get_beacon_proposer_indices_frame (p : Spec.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (L : List Nat) (e : Nat) :
    Spec.get_beacon_proposer_indices p o { state with proposer_lookahead := L } e =
      Spec.get_beacon_proposer_indices p o state e := rfl

/-- `next_proposer_lookahead` equals `process_proposer_lookahead`. -/
theorem next_proposer_lookahead_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (look : Slice U64) (hlook : look.val.map (·.val) = state.proposer_lookahead)
    (indices : Slice Usize) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_BEACON_PROPOSER.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce →
      epoch.val = ce + p.MIN_SEED_LOOKAHEAD + 1)
    (hindices : ∀ l, (Spec.get_active_validator_indices state epoch.val).filterM
      (fun index => do pure !(← Spec.listGet state.validators index).slashed) = .ok l →
        indices.val.map (·.val) = l)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
    (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
    (c : LhSelectionConstants) (hc : SelectionConstantsMatch p c)
    (hspe32 : p.SLOTS_PER_EPOCH < 2 ^ 32)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max)
    (state' : Spec.BeaconState) (hspec : Spec.process_proposer_lookahead p o state = .ok state') :
    per_epoch_processing.epoch_committees.next_proposer_lookahead inst ebi balances look indices
      domain epoch mix start_slot c ⦃ r =>
        ∃ v : alloc.vec.Vec U64, r = .Ok v ∧ v.val.map (·.val) = state'.proposer_lookahead ⦄ := by
  unfold Spec.process_proposer_lookahead at hspec
  simp only [except_bind_ok_iff, get_beacon_proposer_indices_frame] at hspec
  obtain ⟨les, hles, ce, hce, e1, he1, e, he, props, hprops, hfin⟩ := hspec
  simp only [pure, Except.pure, Except.ok.injEq] at hfin
  have hlesv : les = state.proposer_lookahead.length - p.SLOTS_PER_EPOCH ∧
      p.SLOTS_PER_EPOCH ≤ state.proposer_lookahead.length := by
    simp only [Spec.uint64Sub] at hles
    split at hles
    · rename_i h; exact ⟨(Except.ok.inj hles).symm, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hles
  have hev : e = epoch.val := by
    rw [hepoch ce hce]
    simp only [Spec.uint64Add] at he1 he
    split at he1
    · split at he
      · rw [← Except.ok.inj he, ← Except.ok.inj he1]
      · simp [throw, throwThe, MonadExceptOf.throw] at he
    · simp [throw, throwThe, MonadExceptOf.throw] at he1
  subst hev
  unfold Spec.get_beacon_proposer_indices at hprops
  simp only [except_bind_ok_iff] at hprops
  obtain ⟨idx, hidx, sd, hsd, hcpi⟩ := hprops
  rw [← hindices idx hidx] at hcpi
  obtain ⟨_, _, hplen, _⟩ := spec_proposers_get p o state epoch.val sd _ props hcpi
  unfold per_epoch_processing.epoch_committees.next_proposer_lookahead
  apply spec_bind (compute_seed_eq inst p o hH state _ domain hdomain epoch mix hmix sd hsd)
  intro seed hseed
  apply spec_bind (compute_proposer_indices_spec inst ebi balances p o hH state hEB indices seed
    sd hseed epoch.val start_slot c.slots_per_epoch c.shuffle_round_count hc.shuffle_round_count
    c.max_effective_balance hc.max_effective_balance hc.slots_per_epoch hstart hn24 hus props hcpi)
  intro r hr
  obtain ⟨v, hrv, hv⟩ := hr
  simp only [hrv, bind_tc_ok, branch_ok, lift]
  have hspev : (UScalar.cast UScalarTy.Usize c.slots_per_epoch).val = p.SLOTS_PER_EPOCH := by
    rw [cast_usize_of_lt _ (by rw [hc.slots_per_epoch]; exact hspe32), hc.slots_per_epoch]
  have hlooklen : look.val.length = state.proposer_lookahead.length := by
    rw [← hlook]; simp
  have hvlen : (alloc.vec.Vec.deref v).val.length = p.SLOTS_PER_EPOCH := by
    have := congrArg List.length hv
    simp only [List.length_map] at this
    simp [alloc.vec.Vec.deref, this, hplen]
  apply spec_bind (shift_lookahead_spec look _ (alloc.vec.Vec.deref v)
    (by rw [hspev, hlooklen]; exact hlesv.2) (by rw [hvlen, hspev]))
  intro o1 ho1
  obtain ⟨w, hw, hwv⟩ := ho1
  simp only [hw, core.option.Option.ok_or, spec_ok]
  refine ⟨w, rfl, ?_⟩
  have hd : (look.val.drop p.SLOTS_PER_EPOCH).map (·.val) =
      state.proposer_lookahead.drop p.SLOTS_PER_EPOCH := by
    rw [List.map_drop, hlook]
  rw [hwv, ← hfin, hspev, hd, hlesv.1]
  simp only [alloc.vec.Vec.deref]
  rw [hv, List.take_append_of_le_length (by simp)]
  rw [List.take_of_length_le (by simp)]

/-- Lighthouse `compute_ptc` equals the reference selection of `compute_ptc`. -/
theorem compute_ptc_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (committee : Slice Usize) (attester_seed : Array U8 32#usize) (s : Spec.Bytes32)
    (hs : u8s attester_seed.val = s.toList) (slot : U64) (ptc_size : Usize) (R : U8)
    (hR : R.val = p.SHUFFLE_ROUND_COUNT) (maxeb : U64)
    (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn24 : committee.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max) (res : List Nat)
    (hspec : Spec.compute_balance_weighted_selection p o state (committee.val.map (·.val))
      (o.hash (s.toList ++ Spec.uint_to_bytes 8 slot.val)) ptc_size.val false = .ok res) :
    types.state.balance_weighted_selection.compute_ptc inst ebi balances committee attester_seed
      slot ptc_size R maxeb ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ := by
  unfold types.state.balance_weighted_selection.compute_ptc
  step with hash_with_u64_spec inst o hH attester_seed slot as ⟨sd, hsd⟩
  rw [hs] at hsd
  exact compute_balance_weighted_selection_spec inst ebi balances p o hH state hEB committee sd _
    hsd false R hR maxeb hmaxeb hn24 ptc_size hus res hspec

theorem compute_ptc_frame (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState)
    (L : List (List Nat)) (slot : Nat) :
    Spec.compute_ptc p o { state with ptc_window := L } slot = Spec.compute_ptc p o state slot :=
  rfl

theorem get_current_epoch_frame (p : Spec.Preset) (state : Spec.BeaconState)
    (L : List (List Nat)) :
    Spec.get_current_epoch p { state with ptc_window := L } = Spec.get_current_epoch p state :=
  rfl

/-- The facts that `process_ptc_window` gives about the PTCs it appends. -/
theorem spec_ptc_window_get (p : Spec.Preset) (o : Spec.Oracle) (state state' : Spec.BeaconState)
    (hspec : Spec.process_ptc_window p o state = .ok state') :
    ∃ epoch start ptcs, (∃ ce, Spec.get_current_epoch p state = .ok ce ∧
        epoch = ce + p.MIN_SEED_LOOKAHEAD + 1) ∧
      Spec.compute_start_slot_at_epoch p epoch = .ok start ∧
      start + p.SLOTS_PER_EPOCH < 2 ^ 64 ∧
      p.SLOTS_PER_EPOCH ≤ state.ptc_window.length ∧
      state'.ptc_window = state.ptc_window.drop p.SLOTS_PER_EPOCH ++ ptcs ∧
      ptcs.length = p.SLOTS_PER_EPOCH ∧
      ∀ k (hk : k < p.SLOTS_PER_EPOCH), ∃ hk' : k < ptcs.length,
        Spec.compute_ptc p o state (start + k) = .ok ptcs[k] := by
  unfold Spec.process_ptc_window at hspec
  simp only [except_bind_ok_iff, get_current_epoch_frame, compute_ptc_frame] at hspec
  obtain ⟨se, hse, ce, hce, e1, he1, e, he, start, hstart, en, hen, ptcs, hptcs, fs, hfs,
    hfin⟩ := hspec
  simp only [pure, Except.pure, Except.ok.injEq] at hfin
  have hsev : se = state.ptc_window.length - p.SLOTS_PER_EPOCH ∧
      p.SLOTS_PER_EPOCH ≤ state.ptc_window.length := by
    simp only [Spec.uint64Sub] at hse
    split at hse
    · rename_i h; exact ⟨(Except.ok.inj hse).symm, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hse
  have hfsv : fs = (state.ptc_window.drop p.SLOTS_PER_EPOCH ++
      state.ptc_window.drop se).length - p.SLOTS_PER_EPOCH := by
    simp only [Spec.uint64Sub] at hfs
    split at hfs
    · exact (Except.ok.inj hfs).symm
    · simp [throw, throwThe, MonadExceptOf.throw] at hfs
  have henv : en = start + p.SLOTS_PER_EPOCH ∧ start + p.SLOTS_PER_EPOCH < 2 ^ 64 := by
    simp only [Spec.uint64Add] at hen
    split at hen
    · rename_i h; exact ⟨(Except.ok.inj hen).symm, by unfold Spec.UINT64_SIZE at h; exact h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hen
  refine ⟨e, start, ptcs, ?_, hstart, henv.2, hsev.2, ?_, ?_⟩
  · refine ⟨ce, hce, ?_⟩
    simp only [Spec.uint64Add] at he1 he
    split at he1
    · split at he
      · rw [← Except.ok.inj he, ← Except.ok.inj he1]
      · simp [throw, throwThe, MonadExceptOf.throw] at he
    · simp [throw, throwThe, MonadExceptOf.throw] at he1
  · rw [← hfin]
    dsimp only
    rw [hfsv, hsev.1]
    rw [List.take_append_of_le_length (by simp)]
    rw [List.take_of_length_le (by simp)]
  · obtain ⟨hl, hg⟩ := mapM_ok_get _ _ _ hptcs
    simp only [List.length_range', henv.1, Nat.add_sub_cancel_left] at hl
    refine ⟨hl, ?_⟩
    intro k hk
    obtain ⟨hk', hf⟩ := hg k (by simp [henv.1]; omega)
    refine ⟨hk', ?_⟩
    simpa using hf

/-- Each slot of the epoch that starts at `start` is in `epoch`. -/
theorem epoch_of_slot (p : Spec.Preset) (epoch start k : Nat) (hspe : 0 < p.SLOTS_PER_EPOCH)
    (hstart : Spec.compute_start_slot_at_epoch p epoch = .ok start) (hk : k < p.SLOTS_PER_EPOCH) :
    Spec.compute_epoch_at_slot p (start + k) = .ok epoch := by
  simp only [Spec.compute_start_slot_at_epoch, Spec.uint64Mul] at hstart
  split at hstart
  · have := (Except.ok.inj hstart)
    subst this
    simp only [Spec.compute_epoch_at_slot, Spec.uint64Div, Nat.ne_of_gt hspe, if_false]
    congr 1
    rw [Nat.mul_comm, Nat.mul_add_div hspe, Nat.div_eq_of_lt hk, Nat.add_zero]
  · simp [throw, throwThe, MonadExceptOf.throw] at hstart

/-- The selection facts of slot `start + k`, from `compute_ptc`. -/
theorem ptc_slot_facts (p : Spec.Preset) (o : Spec.Oracle) (state : Spec.BeaconState)
    (epoch start k : Nat) (hspe : 0 < p.SLOTS_PER_EPOCH)
    (hstart : Spec.compute_start_slot_at_epoch p epoch = .ok start) (hk : k < p.SLOTS_PER_EPOCH)
    (ptc : List Nat) (h : Spec.compute_ptc p o state (start + k) = .ok ptc) :
    ∃ s l, Spec.get_seed p o state epoch Spec.DOMAIN_PTC_ATTESTER = .ok s ∧
      Spec.ptcIndices p o state epoch (start + k) = .ok l ∧
      Spec.compute_balance_weighted_selection p o state l
        (o.hash (s.toList ++ Spec.uint_to_bytes 8 (start + k))) p.PTC_SIZE false = .ok ptc := by
  rw [Spec.compute_ptc_eq, epoch_of_slot p epoch start k hspe hstart hk] at h
  simp only [except_bind_ok_iff] at h
  obtain ⟨e, he, s, hs, l, hl, hsel⟩ := h
  have := Except.ok.inj he
  subst this
  exact ⟨s, l, hs, hl, hsel⟩

theorem slice_get_vec (s : Slice (alloc.vec.Vec Usize)) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec Usize)) s i =
      ok s.val[i.val]? :=
  rfl

/-- The validator indices of a Lighthouse vector. -/
def natsOf (w : alloc.vec.Vec Usize) : List Nat := w.val.map (·.val)

/-- The PTCs of a Lighthouse vector, as lists of validator indices. -/
def ptcsOf (v : alloc.vec.Vec (alloc.vec.Vec Usize)) : List (List Nat) := v.val.map natsOf

/-- `ptc_for_epoch` returns the PTCs that `process_ptc_window` appends. -/
theorem ptc_for_epoch_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (committees : Slice (alloc.vec.Vec Usize))
    (hclen : committees.val.length = p.SLOTS_PER_EPOCH) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_PTC_ATTESTER.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce →
      epoch.val = ce + p.MIN_SEED_LOOKAHEAD + 1)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
    (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
    (hcomm : ∀ k (hk : k < committees.val.length) l,
      Spec.ptcIndices p o state epoch.val (start_slot.val + k) = .ok l →
        (committees.val[k]).val.map (·.val) = l)
    (hn24 : ∀ k (hk : k < committees.val.length), (committees.val[k]).val.length ≤ 2 ^ 24)
    (ptc_size : Usize) (hptc : ptc_size.val = p.PTC_SIZE) (c : LhSelectionConstants)
    (hc : SelectionConstantsMatch p c) (hspe : 0 < p.SLOTS_PER_EPOCH)
    (hus : Usize.max = U64.max)
    (state' : Spec.BeaconState) (hspec : Spec.process_ptc_window p o state = .ok state') :
    per_epoch_processing.epoch_committees.ptc_for_epoch inst ebi balances committees domain epoch
      mix start_slot ptc_size c ⦃ r =>
        ∃ v : alloc.vec.Vec (alloc.vec.Vec Usize), r = .Ok v ∧
          state'.ptc_window = state.ptc_window.drop p.SLOTS_PER_EPOCH ++
            ptcsOf v ⦄ := by
  obtain ⟨e, start, ptcs, ⟨ce, hce, he⟩, hst, hfit, -, hw, hplen, hk⟩ :=
    spec_ptc_window_get p o state state' hspec
  have hev : e = epoch.val := by rw [he, hepoch ce hce]
  subst hev
  rw [hstart] at hst
  have hsv : start = start_slot.val := (Except.ok.inj hst).symm
  subst hsv
  obtain ⟨hk0, h0⟩ := hk 0 hspe
  obtain ⟨s, -, hs, -, -⟩ := ptc_slot_facts p o state epoch.val start_slot.val 0 hspe hstart hspe
    _ h0
  unfold per_epoch_processing.epoch_committees.ptc_for_epoch
  apply spec_bind (compute_seed_eq inst p o hH state _ domain hdomain epoch mix hmix s hs)
  intro aseed haseed
  have hloop : per_epoch_processing.epoch_committees.ptc_for_epoch_loop inst ebi balances
      committees start_slot ptc_size c aseed (alloc.vec.Vec.new (alloc.vec.Vec Usize)) 0#usize
      ⦃ r => r.2 = none ∧ ptcsOf r.1 = ptcs ⦄ := by
    unfold per_epoch_processing.epoch_committees.ptc_for_epoch_loop
    obtain ⟨L, hL⟩ : ∃ L, committees.val.length = L := ⟨_, rfl⟩
    apply loop.spec_decr_nat
      (measure := fun (x : LhSelectionConstants × alloc.vec.Vec (alloc.vec.Vec Usize) × Usize) =>
        L - x.2.2.val)
      (inv := fun (x : LhSelectionConstants × alloc.vec.Vec (alloc.vec.Vec Usize) × Usize) =>
        x.1 = c ∧ x.2.2.val ≤ L ∧
        ptcsOf x.2.1 = ptcs.take x.2.2.val)
    · rintro ⟨cst, ps, i⟩ ⟨hcst, hi, hps⟩
      dsimp only at hcst hi hps ⊢
      have hc' : SelectionConstantsMatch p cst := hcst ▸ hc
      unfold per_epoch_processing.epoch_committees.ptc_for_epoch_loop.body
      dsimp only
      split
      · rename_i hlt
        have hil : i.val < committees.val.length := by simpa [Slice.len_val] using hlt
        have hiL : i.val < L := hL ▸ hil
        have hspei : i.val < p.SLOTS_PER_EPOCH := by rw [← hclen]; exact hil
        rw [slice_get_vec, List.getElem?_eq_getElem hil]
        have hn24i := hn24 i.val hil
        have hcommi := hcomm i.val hil
        generalize committees.val[i.val] = cm at hn24i hcommi ⊢
        simp only [bind_tc_ok, lift]
        have hci : (UScalar.cast UScalarTy.U64 i).val = i.val := cast_u64_of_usize i
        have hca := U64.checked_add_bv_spec start_slot (UScalar.cast UScalarTy.U64 i)
        cases hco : start_slot.checked_add (UScalar.cast UScalarTy.U64 i) with
        | none =>
          simp only [hco, hci, U64.max_eq] at hca
          try (have := Nat.lt_of_le_of_lt (Nat.add_le_add_left hspei.le _) hfit; omega)
        | some slot =>
        simp only [hco, hci] at hca
        have hslot : slot.val = start_slot.val + i.val := hca.2.1
        simp only [bind_tc_ok]
        obtain ⟨hki, hpi⟩ := hk i.val hspei
        obtain ⟨s', l, hs', hl, hsel⟩ := ptc_slot_facts p o state epoch.val start_slot.val i.val
          hspe hstart hspei _ hpi
        rw [hs] at hs'
        have := Except.ok.inj hs'
        subst this
        rw [← hcommi l hl, ← hslot, ← hptc] at hsel
        obtain ⟨r, hr, v, hrv, hv⟩ := spec_imp_exists (compute_ptc_spec inst ebi balances p o hH
          state hEB (alloc.vec.Vec.deref cm) aseed s haseed slot ptc_size
          cst.shuffle_round_count hc'.shuffle_round_count cst.max_effective_balance
          hc'.max_effective_balance (by simpa [alloc.vec.Vec.deref] using hn24i) hus _
          (by simpa [alloc.vec.Vec.deref] using hsel))
        rw [hr, hrv, bind_tc_ok, bind_tc_ok]
        have hpsl : ps.val.length < Usize.max := by
          have := congrArg List.length hps
          simp only [ptcsOf, List.length_map, List.length_take] at this
          have := committees.property
          omega
        step*
        have hi1 := usize_saturating_add_one i (by have := committees.property; omega)
        rw [hi1]
        refine ⟨hcst, by omega, ?_, by omega⟩
        simp only [ptcsOf] at hps ⊢
        rw [ptcs1_post, List.map_append, hps, List.take_succ_eq_append_getElem hki]
        simp only [List.map_cons, List.map_nil, natsOf, alloc.vec.Vec.deref, hv]
      · rename_i hge
        have : i.val = L := by
          have : ¬ i.val < committees.val.length := by simpa [Slice.len_val] using hge
          omega
        simp only [spec_ok]
        refine ⟨by simp, ?_⟩
        rw [hps, this, ← hL, hclen, ← hplen, List.take_length]
    · exact ⟨rfl, by simp, by simp [ptcsOf]⟩
  apply spec_bind hloop
  intro r hr
  obtain ⟨herr, hv⟩ := hr
  rcases r with ⟨v, err⟩
  dsimp only at herr hv
  simp only [herr, spec_ok]
  exact ⟨v, rfl, by rw [hw, hv]⟩

end EpochProofs
