import EthLib.Consensus.Proposers
import EpochProofs.EthLib.FuluSelection
import EpochProofs.Spec.EpochCommittees

/-!
# `process_proposer_lookahead`: the reference and EthLib agree

Gloas draws a proposer with the balance-weighted selection, and only among unslashed validators.
Fulu draws it with `compute_proposer_index`. EthLib has both in one function, by fork.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-! ## The proposers of an epoch -/

theorem vectorMapM_error {ε α β : Type} {n : Nat} {f : α → Except ε β} {v : Vector α n} {a : α}
    {e : ε} (hmem : a ∈ v.toList) (h : f a = .error e) : ∃ e', v.mapM f = .error e' := by
  obtain ⟨e', he'⟩ := mapM_error hmem h
  have harray : Vector.toArray <$> v.mapM f = List.toArray <$> v.toList.mapM f := by
    rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList]
    rfl
  rw [he'] at harray
  generalize v.mapM f = x at harray ⊢
  cases x with
  | ok a => cases harray
  | error e => exact ⟨e, rfl⟩

/-- The slots of an epoch, and one result for each slot. The reference computes the seeds of all
the slots first. -/
theorem slot_results_same (n : Nat) (hn : n < 2 ^ 64) (start : UInt64)
    {f : UInt64 → Except AccessorError UInt64} {seedOf : Nat → Spec.Bytes32}
    {g : Spec.Bytes32 → Spec.SpecM Nat}
    (h : ∀ slot : UInt64, SameOutcome SameNumber (f slot) (g (seedOf slot.toNat))) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      ((Vector.range n).mapM fun offset => do
        let slot ← liftArith (addChecked start offset.toUInt64)
        f slot)
      (do
        let seeds ← (List.range n).mapM fun i => do
          pure (seedOf (← Spec.uint64Add start.toNat i))
        seeds.mapM g) := by
  have hoffset (offset : Nat) (hlt : offset < n) : offset.toUInt64.toNat = offset :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hlt hn)
  by_cases hfits : ∀ i < n, start.toNat + i < 2 ^ 64
  · rw [mapM_ok (g := fun i => seedOf (start.toNat + i)) (fun i hi => by
      rw [uint64Add_fits (hfits i (List.mem_range.mp hi))]
      rfl), bind_ok, List.mapM_map]
    have hrange : (Vector.range n).toList = List.range n := by
      simp [Vector.toList, Vector.range]
    have := SameOutcome.vectorMapM (f := fun offset => do
        let slot ← liftArith (addChecked start offset.toUInt64)
        f slot) (g := fun i => g (seedOf (start.toNat + i))) id UInt64.toNat (Vector.range n)
      (fun offset hmem => by
        rw [hrange, List.mem_range] at hmem
        obtain ⟨slot, hslot, hnat⟩ : ∃ slot, addChecked start offset.toUInt64 = .ok slot ∧
            slot.toNat = start.toNat + offset := by
          have hsum : start.toNat + offset.toUInt64.toNat < 2 ^ 64 := by
            rw [hoffset offset hmem]
            exact hfits offset hmem
          refine ⟨start + offset.toUInt64, ?_, ?_⟩
          · rw [addChecked, ite_eq_left hsum]
          · rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum, hoffset offset hmem]
        rw [hslot]
        simp only [_root_.EthLib.Consensus.liftArith, Except.mapError, bind_ok, id, ← hnat]
        exact h slot)
    rw [List.map_id, hrange] at this
    exact this
  · obtain ⟨i, hi, hover⟩ : ∃ i < n, ¬start.toNat + i < 2 ^ 64 := by simpa using hfits
    obtain ⟨e, he⟩ := mapM_error (l := List.range n)
      (f := fun i => do pure (seedOf (← Spec.uint64Add start.toNat i)))
      (e := .overflow) (List.mem_range.mpr hi) (by
        rw [uint64Add_overflows hover]
        rfl)
    rw [he]
    obtain ⟨e', he'⟩ := vectorMapM_error (v := Vector.range n) (f := fun offset => do
        let slot ← liftArith (addChecked start offset.toUInt64)
        f slot) (a := i) (e := .arith .overflow) (by simp [Vector.toList, Vector.range, hi]) (by
        rw [addChecked, ite_eq_right (by rw [hoffset i hi]; exact hover)]
        rfl)
    rw [he']
    exact .failed

/-- The proposers, from the draw of the fork of one proposer. -/
theorem compute_proposer_indices_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset fork) (epoch : UInt64)
    (seed : Bytes32) (indices : Array UInt64) {draw : Spec.Bytes32 → Spec.SpecM Nat}
    (hdraw : ∀ seed, SameOutcome SameNumber (computeSlotProposer s indices seed) (draw seed)) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      (computeProposerIndices s epoch seed indices)
      (do
        let start_slot ← Spec.compute_start_slot_at_epoch (toSpecPreset preset config) epoch.toNat
        let seeds ← (List.range (toSpecPreset preset config).SLOTS_PER_EPOCH).mapM fun i => do
          pure (o.hash (seed.toList ++ Spec.uint_to_bytes 8 (← Spec.uint64Add start_slot i)))
        seeds.mapM draw) := by
  unfold computeProposerIndices
  refine .bind (mulChecked_same epoch preset.SLOTS_PER_EPOCH).liftArith ?_
  rintro start _ rfl -
  refine slot_results_same _ preset.SLOTS_PER_EPOCH.toNat_lt start
    (seedOf := fun slot => o.hash (seed.toList ++ Spec.uint_to_bytes 8 slot)) fun slot => ?_
  have hseed : o.hash (seed.toList ++ Spec.uint_to_bytes 8 slot.toNat) =
      proposerSlotSeed seed slot :=
    hash_eq ho (by simp [uint_to_bytes_eq, toArray_toList])
  rw [hseed]
  exact hdraw _

theorem gloas_slot_proposer_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (gloas : .glamsterdam ≤ fork) (s : BeaconState preset fork) (indices : List UInt64)
    (hlength : indices.length ≤ 2 ^ 40) (seed : Bytes32) :
    SameOutcome SameNumber (computeSlotProposer s indices.toArray seed)
      (do
        Spec.listGet (← Spec.compute_balance_weighted_selection (toSpecPreset preset config) o
          (toSpecState s) (indices.map UInt64.toNat) seed 1 true) 0) := by
  unfold computeSlotProposer
  rw [ite_eq_left gloas]
  refine .bind (balance_weighted_selection_same hbounds ho (Nat.le_trans (by decide) gloas) s
    indices hlength seed 1 true) ?_
  rintro selected _ rfl -
  have hselected : selected.toList.map UInt64.toNat = [selected[0].toNat] := by
    obtain ⟨⟨l⟩, hl⟩ := selected
    match l, hl with
    | [_], _ => rfl
  rw [hselected]
  exact .returned rfl

theorem filterM_ok {ε α : Type} {f : α → Except ε Bool} {g : α → Bool} (l : List α)
    (h : ∀ a ∈ l, f a = .ok (g a)) : l.filterM f = .ok (l.filter g) := by
  have haux : ∀ (l acc : List α), (∀ a ∈ l, f a = .ok (g a)) →
      l.filterAuxM f acc = .ok ((l.filter g).reverse ++ acc) := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons a l ih =>
      intro acc h
      rw [List.filterAuxM, h a List.mem_cons_self, bind_ok,
        ih _ fun b hb => h b (List.mem_cons_of_mem _ hb)]
      cases hg : g a <;> simp [hg]
  rw [List.filterM, haux l [] h, bind_ok]
  simp [pure, Except.pure]

theorem proposerCandidates_gloas (gloas : .glamsterdam ≤ fork) (s : BeaconState preset fork)
    (active : List UInt64) :
    proposerCandidates s active.toArray =
      (active.filter fun index =>
        !((s.validators.data[index.toNat]?.map (·.slashed)).getD false)).toArray := by
  unfold proposerCandidates
  rw [ite_eq_left gloas, List.filter_toArray]
  congr 1
  refine List.filter_congr fun index _ => ?_
  cases s.validators.data[index.toNat]? <;> rfl

theorem unslashed_filter_eq (s : BeaconState preset fork) (active : List UInt64)
    (hinside : ∀ index ∈ active, index.toNat < s.validators.data.size) :
    ((active.map UInt64.toNat).filterM fun index => do
      pure !(← Spec.listGet (toSpecState s).validators index).slashed) =
    (.ok ((active.filter fun index =>
      !((s.validators.data[index.toNat]?.map (·.slashed)).getD false)).map UInt64.toNat) :
      Spec.SpecM (List Nat)) := by
  rw [filterM_ok (g := fun i => !((s.validators.data[i]?.map (·.slashed)).getD false)) _ ?_,
    List.filter_map]
  · rfl
  · intro i hi
    obtain ⟨index, hmem, rfl⟩ := List.mem_map.mp hi
    rw [listGet_validators (hinside index hmem)]
    simp [toSpecValidator, hinside index hmem, pure, Except.pure, bind, Except.bind]

/-- The Gloas proposers of an epoch. -/
theorem gloas_proposer_indices_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (gloas : .glamsterdam ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (epoch : UInt64) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat) (getBeaconProposerIndices s epoch)
      (Spec.get_beacon_proposer_indices (toSpecPreset preset config) o (toSpecState s)
        epoch.toNat) := by
  unfold getBeaconProposerIndices Spec.get_beacon_proposer_indices Spec.compute_proposer_indices
  obtain ⟨heq, -, hinside⟩ := get_active_validator_indices_same hregistry epoch
  rw [getActiveValidatorIndicesChecked_of_within hregistry, heq,
    unslashed_filter_eq s _ hinside, bind_ok, bind_ok, proposerCandidates_gloas gloas]
  refine .bind (get_seed_same ho s epoch DOMAIN_BEACON_PROPOSER) ?_
  rintro _ seed rfl -
  refine compute_proposer_indices_same ho s epoch _ _ fun slotSeed => ?_
  exact gloas_slot_proposer_same hbounds ho gloas s _
    (Nat.le_trans (List.length_filter_le _ _) (active_length_le hbounds hregistry epoch)) slotSeed

/-- The Fulu proposers of an epoch. -/
theorem fulu_proposer_indices_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (electra : .pectra ≤ fork) (beforeGloas : ¬.glamsterdam ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (epoch : UInt64) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat) (getBeaconProposerIndices s epoch)
      (Spec.get_beacon_proposer_indices_fulu (toSpecPreset preset config) o (toSpecState s)
        epoch.toNat) := by
  unfold getBeaconProposerIndices Spec.get_beacon_proposer_indices_fulu
    Spec.compute_proposer_indices_fulu
  rw [getActiveValidatorIndicesChecked_of_within hregistry,
    (get_active_validator_indices_same hregistry epoch).eq, bind_ok]
  refine .bind (get_seed_same ho s epoch DOMAIN_BEACON_PROPOSER) ?_
  rintro _ seed rfl -
  refine compute_proposer_indices_same ho s epoch _ _ fun slotSeed => ?_
  unfold computeSlotProposer
  rw [proposerCandidates, ite_eq_right beforeGloas, ite_eq_right beforeGloas]
  exact compute_proposer_index_same hbounds ho electra s slotSeed _
    (active_length_le hbounds hregistry epoch)

/-! ## The lookahead -/

theorem proposer_lookahead_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (fulu : .fusaka ≤ fork)
    (s : BeaconState preset fork)
    {specProposers : Spec.BeaconState → Nat → Spec.SpecM (List Nat)}
    (hkeeps : ∀ lookahead, specProposers { toSpecState s with proposer_lookahead := lookahead } =
      specProposers (toSpecState s))
    (hproposers : ∀ epoch, SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      (getBeaconProposerIndices s epoch) (specProposers (toSpecState s) epoch.toNat)) :
    SameOutcome SameState (processProposerLookahead s fulu)
      (do
        let last_epoch_start ← Spec.uint64Sub (toSpecState s).proposer_lookahead.length
          (toSpecPreset preset config).SLOTS_PER_EPOCH
        let state := { toSpecState s with
          proposer_lookahead :=
            (toSpecState s).proposer_lookahead.drop (toSpecPreset preset config).SLOTS_PER_EPOCH ++
              (toSpecState s).proposer_lookahead.drop last_epoch_start }
        let last_epoch_proposers ← specProposers state
          (← Spec.uint64Add (← Spec.uint64Add
            (← Spec.get_current_epoch (toSpecPreset preset config) state)
            (toSpecPreset preset config).MIN_SEED_LOOKAHEAD) 1)
        pure { state with
          proposer_lookahead :=
            state.proposer_lookahead.take last_epoch_start ++ last_epoch_proposers }) := by
  have hcurrent (lookahead : List Nat) : Spec.get_current_epoch (toSpecPreset preset config)
      { toSpecState s with proposer_lookahead := lookahead } = .ok (getCurrentEpoch s).toNat :=
    get_current_epoch_eq hslots s
  have hlength : (toSpecState s).proposer_lookahead.length =
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [toSpecState_proposer_lookahead s fulu]
    simp
  have hstart : Spec.uint64Sub (toSpecState s).proposer_lookahead.length
      preset.SLOTS_PER_EPOCH.toNat =
      .ok (preset.MIN_SEED_LOOKAHEAD.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
    rw [hlength, Nat.succ_mul, Spec.uint64Sub, ite_eq_left (Nat.le_add_left _ _),
      Nat.add_sub_cancel]
    rfl
  unfold processProposerLookahead
  simp only [spec_preset, hstart, bind_ok, hcurrent, hkeeps, liftArith_bind, bind_assoc]
  refine .bind (addChecked_same (getCurrentEpoch s) preset.MIN_SEED_LOOKAHEAD).liftArith ?_
  rintro ahead _ rfl -
  refine .bind (addChecked_same ahead 1).liftArith ?_
  rintro epoch _ rfl -
  refine .bind (hproposers epoch) ?_
  rintro last _ rfl -
  refine .returned ?_
  rw [SameState, toSpecState_with_proposer_lookahead s fulu]
  refine congrArg (fun lookahead => { toSpecState s with proposer_lookahead := lookahead }) ?_
  have hdrop : ((toSpecState s).proposer_lookahead.drop preset.SLOTS_PER_EPOCH.toNat).length =
      preset.MIN_SEED_LOOKAHEAD.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [List.length_drop, hlength, Nat.succ_mul, Nat.add_sub_cancel]
  rw [← hdrop, List.take_left, toSpecState_proposer_lookahead s fulu]
  generalize s.proposerLookahead fulu = lookahead
  have hmul : (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat =
      preset.MIN_SEED_LOOKAHEAD.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat := Nat.succ_mul _ _
  apply List.ext_getElem
  · simp [Nat.succ_mul]
  · intro i _ _
    simp only [List.getElem_append, List.getElem_drop, List.getElem_map, Vector.getElem_toList,
      List.length_drop, List.length_map, Vector.length_toList, Vector.getElem_ofFn, Vector.size]
    split <;> split
    · congr 2
      omega
    · omega
    · omega
    · congr 2
      omega

theorem proposer_lookahead_gloas (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (fulu : .fusaka ≤ fork) (gloas : .glamsterdam ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processProposerLookahead s fulu)
      (Spec.process_proposer_lookahead (toSpecPreset preset config) o (toSpecState s)) :=
  proposer_lookahead_same hslots fulu s
    (specProposers := Spec.get_beacon_proposer_indices (toSpecPreset preset config) o)
    (fun _ => rfl) (gloas_proposer_indices_same hbounds ho gloas hregistry)

theorem proposer_lookahead_fulu (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (fulu : .fusaka ≤ fork)
    (beforeGloas : ¬.glamsterdam ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processProposerLookahead s fulu)
      (Spec.process_proposer_lookahead_fulu (toSpecPreset preset config) o (toSpecState s)) :=
  proposer_lookahead_same hslots fulu s
    (specProposers := Spec.get_beacon_proposer_indices_fulu (toSpecPreset preset config) o)
    (fun _ => rfl) (fulu_proposer_indices_same hbounds ho (Nat.le_trans (by decide) fulu)
      beforeGloas hregistry)

end EpochProofs.EthLib
