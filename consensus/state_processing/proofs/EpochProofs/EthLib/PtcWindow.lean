import EpochProofs.EthLib.ProposerLookahead

/-!
# `process_ptc_window`: the reference and EthLib agree

`hslotLimit` names a difference. The reference computes the end of the epoch that it fills as a
`Uint64`, as the pyspec does, so it fails if that end is exactly `2**64`. EthLib does not compute
the end.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-! ## Beacon committees -/

theorem committee_count_eq (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) (epoch : UInt64) :
    Spec.get_committee_count_per_slot (toSpecPreset preset config) (toSpecState s) epoch.toNat =
      .ok (getCommitteeCountPerSlot s epoch).toNat := by
  have hlength : (getActiveValidatorIndices s epoch).length =
      (getActiveValidatorIndices s epoch).length.toUInt64.toNat :=
    (UInt64.toNat_ofNat_of_lt'
      (Nat.lt_of_le_of_lt (active_length_le hbounds hregistry epoch) (by decide))).symm
  unfold Spec.get_committee_count_per_slot getCommitteeCountPerSlot committeeCountOf
  have hdiv := uint64Div_eq (a := (getActiveValidatorIndices s epoch).length.toUInt64) hslots
  rw [← hlength] at hdiv
  rw [(get_active_validator_indices_same hregistry epoch).eq, List.length_map]
  simp only [spec_preset, hdiv, uint64Div_eq hbounds.targetCommitteeSize, bind_ok]
  rw [toNat_max, toNat_min]
  rfl

theorem one_le_committeeCountOf (active : UInt64) : 1 ≤ (committeeCountOf preset active).toNat := by
  rw [committeeCountOf, toNat_max]
  exact Nat.le_max_left _ _

/-- One committee of the shuffled active validators. -/
theorem shuffled_committee_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o) (seed : Bytes32)
    (active : List UInt64) (hlength : active.length ≤ 2 ^ 40) (index count : UInt64) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat ∧
        a.size = active.length * (index.toNat + 1) / count.toNat -
          active.length * index.toNat / count.toNat)
      (shuffledCommittee active.toArray
        (Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed active.length) index count)
      (Spec.compute_committee (toSpecPreset preset config) o (active.map UInt64.toNat) seed
        index.toNat count.toNat) := by
  unfold shuffledCommittee Spec.compute_committee
  simp only [List.size_toArray, List.length_map]
  by_cases hcount : count = 0
  · rw [ite_eq_left hcount, hcount]
    have hzero : ∀ a, Spec.uint64Div a (0 : UInt64).toNat = .error .divisionByZero := fun _ => rfl
    simp only [hzero]
    by_cases hstart : active.length * index.toNat < 2 ^ 64
    · rw [uint64Mul_fits hstart]
      exact .failed
    · rw [uint64Mul_overflows hstart]
      exact .failed
  rw [ite_eq_right hcount]
  have hcount' : count.toNat ≠ 0 := fun h => hcount (UInt64.toNat_inj.mp h)
  simp only [uint64Div_nat hcount']
  by_cases hfits : index.toNat + 1 < 2 ^ 64 ∧ active.length * (index.toNat + 1) < 2 ^ 64
  case neg =>
    rw [ite_eq_right hfits]
    by_cases hstart : active.length * index.toNat < 2 ^ 64
    · rw [uint64Mul_fits hstart, bind_ok]
      by_cases hindex : index.toNat + 1 < 2 ^ 64
      · rw [uint64Add_fits hindex, bind_ok, bind_ok,
          uint64Mul_overflows fun h => hfits ⟨hindex, h⟩]
        exact .failed
      · rw [uint64Add_overflows hindex]
        exact .failed
    · rw [uint64Mul_overflows hstart]
      exact .failed
  rw [ite_eq_left hfits, uint64Mul_fits (Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (Nat.le_succ _)) hfits.2), uint64Add_fits hfits.1]
  simp only [bind_ok, uint64Mul_fits hfits.2]
  generalize active.length * index.toNat / count.toNat = start
  generalize active.length * (index.toNat + 1) / count.toNat = stop
  by_cases hout : start < stop ∧ active.length < stop
  · rw [ite_eq_left hout]
    obtain ⟨e, he⟩ := mapM_error (l := List.range' start (stop - start))
      (f := fun i => do
        Spec.listGet (active.map UInt64.toNat)
          (← Spec.compute_shuffled_index (toSpecPreset preset config) o i active.length seed))
      (a := max start active.length) (e := .assertionFailed)
      (by rw [List.mem_range'_1]; omega)
      (by
        rw [Spec.compute_shuffled_index, ite_eq_left
          (show ¬max start active.length < active.length by omega)]
        rfl)
    rw [he]
    exact .failed
  · rw [ite_eq_right hout]
    have hread : ∀ i ∈ List.range' start (stop - start), (do
        Spec.listGet (active.map UInt64.toNat)
          (← Spec.compute_shuffled_index (toSpecPreset preset config) o i active.length seed)) =
        (.ok (active.toArray.getD ((Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed
          active.length).getD i 0).toNat 0).toNat : Spec.SpecM Nat) := by
      intro i hi
      rw [List.mem_range'_1] at hi
      have hlt : i < active.length := by omega
      have hshuffled := Shuffle.shuffledIndex_lt (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
        (seed := seed) hlt
      have hposition : ((Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed
          active.length).getD i 0).toNat =
          Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed active.length i := by
        rw [Array.getD_eq_getD_getElem?, Shuffle.shuffledPositions_getElem hlt, Option.getD_some]
        exact UInt64.toNat_ofNat_of_lt'
          (Nat.lt_of_lt_of_le hshuffled (Nat.le_trans hlength (by decide)))
      rw [compute_shuffled_index_eq hbounds ho seed hlt hlength, bind_ok, hposition]
      simp [Spec.listGet, hshuffled, pure, Except.pure]
    rw [mapM_ok hread]
    refine .returned ⟨?_, by simp⟩
    rw [List.range'_eq_map_range]
    simp [Function.comp_def]

theorem toUInt64_toNat {i : Nat} {n : UInt64} (h : i < n.toNat) : i.toUInt64.toNat = i :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h n.toNat_lt)

/-- The committees of a slot, joined. The joined list has at most one entry for each active
validator. -/
theorem slot_committees_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    (ho : OracleMatches preset checks o) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (slot epoch : UInt64)
    (hepoch : slot / preset.SLOTS_PER_EPOCH = epoch) {seed : Bytes32}
    (hseed : Spec.get_seed (toSpecPreset preset config) o (toSpecState s) epoch.toNat
      Spec.DOMAIN_BEACON_ATTESTER = .ok seed) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat ∧ a.size ≤ 2 ^ 40)
      (slotCommitteeMembersOf preset slot (getCommitteeCountPerSlot s epoch)
        (getActiveValidatorIndices s epoch).toArray
        (Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed
          (getActiveValidatorIndices s epoch).length))
      (forIn (List.range (getCommitteeCountPerSlot s epoch).toNat) ([] : List Nat)
        fun i indices => do
          let committee ← Spec.get_beacon_committee (toSpecPreset preset config) o (toSpecState s)
            slot.toNat i
          pure (.yield (indices ++ committee))) := by
  have hlength := active_length_le hbounds hregistry epoch
  have hcountPos := one_le_committeeCountOf (preset := preset)
    (getActiveValidatorIndices s epoch).length.toUInt64
  have hcommitteeCount := committee_count_eq (config := config) hslots hbounds hregistry epoch
  have hactive := (get_active_validator_indices_same hregistry epoch).eq
  unfold slotCommitteeMembersOf
  change 1 ≤ (getCommitteeCountPerSlot s epoch).toNat at hcountPos
  generalize getCommitteeCountPerSlot s epoch = perSlot at hcountPos hcommitteeCount ⊢
  generalize getActiveValidatorIndices s epoch = active at hlength hactive ⊢
  have hsmall : (slot % preset.SLOTS_PER_EPOCH).toNat < preset.SLOTS_PER_EPOCH.toNat :=
    toNat_mod_lt hslots
  generalize hin : slot % preset.SLOTS_PER_EPOCH = inEpoch at hsmall
  have hfold := SameOutcome.forIn_range
    (f := fun members index => do
      return members ++ (← beaconCommitteeOf preset slot index.toUInt64 perSlot active.toArray
        (Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed active.length)))
    (body := fun i indices => do
      let committee ← Spec.get_beacon_committee (toSpecPreset preset config) o (toSpecState s)
        slot.toNat i
      pure (.yield (indices ++ committee)))
    (R := fun i (members : Array UInt64) (indices : List Nat) =>
      indices = members.toList.map UInt64.toNat ∧
        members.size ≤ active.length * (inEpoch.toNat * perSlot.toNat + i) /
          (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat))
    perSlot.toNat (a := #[]) (b := []) ⟨rfl, Nat.zero_le _⟩ (by
      rintro i members _ hi ⟨rfl, hsize⟩
      have hnat := toUInt64_toNat hi
      unfold beaconCommitteeOf Spec.get_beacon_committee Spec.compute_epoch_at_slot
      simp only [spec_preset, uint64Div_eq hslots, uint64Mod_eq hslots, bind_ok, hepoch, hin,
        hcommitteeCount, hseed, liftArith_bind, bind_assoc, hactive]
      refine .bind (mulChecked_same inEpoch perSlot).liftArith ?_
      rintro first _ rfl hfirst
      have hfirst' := toNat_of_mulChecked hfirst
      have hadd := (addChecked_same first i.toUInt64).liftArith
      rw [hnat] at hadd
      refine .bind hadd ?_
      rintro position _ rfl hposition
      have hposition' := toNat_of_addChecked hposition
      rw [hnat] at hposition'
      refine .bind (mulChecked_same perSlot preset.SLOTS_PER_EPOCH).liftArith ?_
      rintro count _ rfl hcount
      have hcount' := toNat_of_mulChecked hcount
      refine .bind (.mapError _ (shuffled_committee_same hbounds ho seed active hlength position
        count)) ?_
      rintro committee _ ⟨rfl, hcommittee⟩ -
      refine .returned ⟨_, rfl, by simp, ?_⟩
      rw [Array.size_append, hcommittee, hposition', hfirst', hcount', ← Nat.add_assoc]
      have hle : active.length * (inEpoch.toNat * perSlot.toNat + i) /
          (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) ≤
          active.length * (inEpoch.toNat * perSlot.toNat + i + 1) /
          (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ _))
      omega)
  refine hfold.mono fun members indices h => ⟨h.1, Nat.le_trans h.2 (Nat.le_trans ?_ hlength)⟩
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_comm]
  refine Nat.mul_le_mul_right _ ?_
  rw [Nat.mul_comm perSlot.toNat, ← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ hsmall

/-! ## The payload timeliness committee of a slot -/

theorem compute_ptc_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    (ho : OracleMatches preset checks o) (electra : .pectra ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (slot epoch : UInt64)
    (hepoch : slot / preset.SLOTS_PER_EPOCH = epoch) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      (do
        let epochSeed ← getSeed s epoch DOMAIN_PTC_ATTESTER
        let (active, shuffled) ← attesterShuffle s epoch
        computePtcOf s slot epochSeed (getCommitteeCountPerSlot s epoch) active shuffled)
      (Spec.compute_ptc (toSpecPreset preset config) o (toSpecState s) slot.toNat) := by
  unfold Spec.compute_ptc Spec.compute_epoch_at_slot
  simp only [spec_preset, uint64Div_eq hslots, bind_ok, hepoch,
    committee_count_eq (config := config) hslots hbounds hregistry epoch]
  refine .bind (get_seed_same ho s epoch DOMAIN_PTC_ATTESTER) ?_
  rintro _ epochSeed rfl -
  have hattester := get_seed_same (config := config) ho s epoch DOMAIN_BEACON_ATTESTER
  unfold attesterShuffle
  generalize hspecSeed : Spec.get_seed (toSpecPreset preset config) o (toSpecState s) epoch.toNat
    DOMAIN_BEACON_ATTESTER = specSeed at hattester
  generalize getSeed s epoch DOMAIN_BEACON_ATTESTER = attesterSeed at hattester ⊢
  cases hattester with
  | failed =>
    obtain ⟨k, hk⟩ : ∃ k, (getCommitteeCountPerSlot s epoch).toNat = k + 1 :=
      ⟨_, (Nat.sub_add_cancel (one_le_committeeCountOf _)).symm⟩
    rw [hk, List.range_succ_eq_map, List.forIn_cons]
    unfold Spec.get_beacon_committee Spec.compute_epoch_at_slot
    simp only [spec_preset, uint64Div_eq hslots, bind_ok, hepoch,
      committee_count_eq (config := config) hslots hbounds hregistry epoch]
    have hspecSeed' : Spec.get_seed (toSpecPreset preset config) o (toSpecState s) epoch.toNat
      Spec.DOMAIN_BEACON_ATTESTER = _ := hspecSeed
    rw [hspecSeed']
    exact .failed
  | @returned seed _ hsame =>
    subst hsame
    have hlength := active_length_le hbounds hregistry epoch
    have hcommittees := slot_committees_same hslots hbounds ho hregistry slot epoch hepoch
      hspecSeed
    obtain ⟨count, hcount, hnat⟩ := ofNatChecked_ok
      (n := (getActiveValidatorIndices s epoch).length) (Nat.lt_of_le_of_lt hlength (by decide))
    rw [getActiveValidatorIndicesChecked_of_within hregistry]
    simp only [bind_ok, List.size_toArray, hcount, computeShuffledPermutation, hnat,
      hlength, ite_true,
      _root_.EthLib.Consensus.liftArith, Except.mapError, pure_bind]
    unfold computePtcOf
    refine .bind hcommittees ?_
    rintro members _ ⟨rfl, hmembers⟩ -
    have hseed : o.hash (epochSeed.toList ++ Spec.uint_to_bytes 8 slot.toNat) =
        _root_.EthLib.Cryptography.Hash.Sha256.hash32
          ⟨epochSeed.toArray ++ (ByteOrder.toLE 8 slot.toNat).toArray⟩ :=
      hash_eq ho (by simp [uint_to_bytes_eq, toArray_toList])
    have := balance_weighted_selection_same (config := config) hbounds ho electra s members.toList
      (by simpa using hmembers) (_root_.EthLib.Cryptography.Hash.Sha256.hash32
          ⟨epochSeed.toArray ++ (ByteOrder.toLE 8 slot.toNat).toArray⟩) preset.PTC_SIZE false
    rw [Array.toArray_toList] at this
    rw [hseed]
    exact this

/-! ## The window -/

theorem ptcWindowSlot_eq (epoch : UInt64) {offset : Nat}
    (hoffset : offset < preset.SLOTS_PER_EPOCH.toNat) :
    ptcWindowSlot preset epoch offset =
      liftArith (mulChecked epoch preset.SLOTS_PER_EPOCH >>= fun start =>
        addChecked start offset.toUInt64) := by
  have hzero : addChecked epoch (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64 = .ok epoch := by
    rw [Nat.div_eq_of_lt hoffset]
    show addChecked epoch 0 = .ok epoch
    rw [addChecked, ite_eq_left
      (show epoch.toNat + (0 : UInt64).toNat < 2 ^ 64 from epoch.toNat_lt)]
    exact congrArg Except.ok (UInt64.add_zero epoch)
  unfold ptcWindowSlot
  simp only [hzero, bind_ok, Nat.mod_eq_of_lt hoffset]
  rfl

/-- The new committees of the window, one for each slot of the epoch. -/
theorem new_ptcs_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (epoch : UInt64)
    (hslotLimit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≠ 2 ^ 64)
    {f : UInt64 → Except AccessorError (PayloadTimelinessCommittee preset)}
    {g : Nat → Spec.SpecM (List Nat)}
    (h : ∀ slot : UInt64, slot / preset.SLOTS_PER_EPOCH = epoch →
      SameOutcome (fun a b => b = a.toList.map UInt64.toNat) (f slot) (g slot.toNat)) :
    SameOutcome
      (fun a b => b = a.toList.map fun committee => committee.toList.map UInt64.toNat)
      ((Vector.range preset.SLOTS_PER_EPOCH.toNat).mapM fun offset => do
        let slot ← ptcWindowSlot preset epoch offset
        f slot)
      (do
        let start_slot ← Spec.uint64Mul epoch.toNat preset.SLOTS_PER_EPOCH.toNat
        let end_slot ← Spec.uint64Add start_slot preset.SLOTS_PER_EPOCH.toNat
        (List.range' start_slot (end_slot - start_slot)).mapM g) := by
  have hpos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun h => hslots (UInt64.toNat_inj.mp h)
  have hrange : (Vector.range preset.SLOTS_PER_EPOCH.toNat).toList =
      List.range preset.SLOTS_PER_EPOCH.toNat := by
    simp [Vector.toList, Vector.range]
  by_cases hmul : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  case neg =>
    rw [uint64Mul_overflows hmul]
    obtain ⟨e, he⟩ := vectorMapM_error (v := Vector.range preset.SLOTS_PER_EPOCH.toNat)
      (f := fun offset => do
        let slot ← ptcWindowSlot preset epoch offset
        f slot) (a := 0) (e := .arith .overflow) (by simpa [hrange] using hpos) (by
        rw [ptcWindowSlot_eq epoch hpos, mulChecked, ite_eq_right hmul]
        rfl)
    rw [he]
    exact .failed
  have hstart : mulChecked epoch preset.SLOTS_PER_EPOCH =
      .ok (epoch * preset.SLOTS_PER_EPOCH) := by
    rw [mulChecked, ite_eq_left hmul]
  have hnat : (epoch * preset.SLOTS_PER_EPOCH).toNat =
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hmul]
  rw [uint64Mul_fits hmul, bind_ok]
  by_cases hend : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  case neg =>
    rw [uint64Add_overflows hend]
    rw [Nat.succ_mul] at hslotLimit
    have hlast : (preset.SLOTS_PER_EPOCH.toNat - 1).toUInt64.toNat =
        preset.SLOTS_PER_EPOCH.toNat - 1 := toUInt64_toNat (Nat.sub_lt hpos Nat.one_pos)
    obtain ⟨e, he⟩ := vectorMapM_error (v := Vector.range preset.SLOTS_PER_EPOCH.toNat)
      (f := fun offset => do
        let slot ← ptcWindowSlot preset epoch offset
        f slot) (a := preset.SLOTS_PER_EPOCH.toNat - 1) (e := .arith .overflow)
      (by
        rw [hrange]
        exact List.mem_range.mpr (Nat.sub_lt hpos Nat.one_pos)) (by
        rw [ptcWindowSlot_eq epoch (Nat.sub_lt hpos Nat.one_pos), hstart, bind_ok, addChecked,
          ite_eq_right (by rw [hnat, hlast]; omega)]
        rfl)
    rw [he]
    exact .failed
  rw [uint64Add_fits hend, bind_ok, Nat.add_sub_cancel_left, List.range'_eq_map_range,
    List.mapM_map]
  have := SameOutcome.vectorMapM (f := fun offset => do
      let slot ← ptcWindowSlot preset epoch offset
      f slot)
    (g := fun offset => g (epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + offset)) id
    (fun committee : PayloadTimelinessCommittee preset => committee.toList.map UInt64.toNat)
    (Vector.range preset.SLOTS_PER_EPOCH.toNat) (fun offset hmem => by
      rw [hrange, List.mem_range] at hmem
      have hoffset := toUInt64_toNat hmem
      have hsum : (epoch * preset.SLOTS_PER_EPOCH).toNat + offset.toUInt64.toNat < 2 ^ 64 := by
        rw [hnat, hoffset]
        omega
      have hslot : (epoch * preset.SLOTS_PER_EPOCH + offset.toUInt64).toNat =
          epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + offset := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum, hnat, hoffset]
      rw [ptcWindowSlot_eq epoch hmem, hstart, bind_ok, addChecked, ite_eq_left hsum]
      simp only [id, ← hslot]
      refine h _ (UInt64.toNat_inj.mp ?_)
      rw [UInt64.toNat_div, hslot, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hmem,
        Nat.add_zero])
  rw [List.map_id, hrange] at this
  exact this

theorem ptc_window_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    (ho : OracleMatches preset checks o) (gloas : .glamsterdam ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit)
    (hslotLimit : ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≠ 2 ^ 64) :
    SameOutcome SameState (processPtcWindow s gloas)
      (Spec.process_ptc_window (toSpecPreset preset config) o (toSpecState s)) := by
  have hlength : (toSpecState s).ptc_window.length =
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_EPOCH.toNat := by
    rw [toSpecState_ptc_window s gloas, ← Nat.succ_mul]
    simp
  have hshift : Spec.uint64Sub (toSpecState s).ptc_window.length preset.SLOTS_PER_EPOCH.toNat =
      .ok ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) := by
    rw [hlength, Spec.uint64Sub, ite_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]
    rfl
  have hdrop : ((toSpecState s).ptc_window.drop preset.SLOTS_PER_EPOCH.toNat).length =
      (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [List.length_drop, hlength, Nat.add_sub_cancel]
  have hdropLast : ((toSpecState s).ptc_window.drop ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat)).length = preset.SLOTS_PER_EPOCH.toNat := by
    rw [List.length_drop, hlength, Nat.add_sub_cancel_left]
  have hfill : Spec.uint64Sub ((toSpecState s).ptc_window.drop preset.SLOTS_PER_EPOCH.toNat ++
      (toSpecState s).ptc_window.drop ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat)).length preset.SLOTS_PER_EPOCH.toNat =
      .ok ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) := by
    rw [List.length_append, hdrop, hdropLast, ← hlength]
    exact hshift
  have hcurrent (window : List (List Nat)) : Spec.get_current_epoch (toSpecPreset preset config)
      { toSpecState s with ptc_window := window } = .ok (getCurrentEpoch s).toNat :=
    get_current_epoch_eq hslots s
  have hkeeps (window : List (List Nat)) (slot : Nat) :
      Spec.compute_ptc (toSpecPreset preset config) o
        { toSpecState s with ptc_window := window } slot =
      Spec.compute_ptc (toSpecPreset preset config) o (toSpecState s) slot := rfl
  unfold processPtcWindow Spec.process_ptc_window Spec.compute_start_slot_at_epoch
  simp only [spec_preset, hshift, bind_ok, hcurrent, hkeeps, hfill, liftArith_bind, bind_assoc,
    pure_bind]
  refine .bind (addChecked_same (getCurrentEpoch s) preset.MIN_SEED_LOOKAHEAD).liftArith ?_
  rintro ahead _ rfl hahead
  refine .bind (addChecked_same ahead 1).liftArith ?_
  rintro epoch _ rfl hepoch
  have hnew := new_ptcs_same hslots epoch (by
    rw [toNat_of_addChecked hepoch, toNat_of_addChecked hahead]
    exact hslotLimit) fun slot hslot =>
    compute_ptc_same (config := config) hslots hbounds ho (Nat.le_trans (by decide) gloas)
      hregistry slot epoch hslot
  simp only [← bind_assoc (m := Spec.SpecM)]
  refine .bind (M := fun a b =>
    b = a.toList.map fun committee => committee.toList.map UInt64.toNat) ?_ ?_
  · exact hnew
  rintro fresh _ rfl -
  refine .returned ?_
  rw [SameState, toSpecState_with_ptc_window s gloas]
  refine congrArg (fun window => { toSpecState s with ptc_window := window }) ?_
  rw [← hdrop, List.take_left, toSpecState_ptc_window s gloas, RootedVector.elements_shift]
  simp only [RootedVector.shiftElements, Vector.toList, Array.toList_append, Array.toList_extract,
    List.map_append]
  simp [List.map_drop]

/-- The reference fails if the epoch that it fills ends at slot `2**64`. -/
theorem ptc_window_fails_at_slot_limit (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (o : Spec.Oracle)
    (s : BeaconState preset fork)
    (hslotLimit : ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat = 2 ^ 64) :
    ∃ e, Spec.process_ptc_window (toSpecPreset preset config) o (toSpecState s) = .error e := by
  have hpos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun h => hslots (UInt64.toNat_inj.mp h)
  have hcurrent (window : List (List Nat)) : Spec.get_current_epoch (toSpecPreset preset config)
      { toSpecState s with ptc_window := window } = .ok (getCurrentEpoch s).toNat :=
    get_current_epoch_eq hslots s
  have hle : (getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2 ≤ 2 ^ 64 := by
    rw [← hslotLimit]
    exact Nat.le_mul_of_pos_right _ hpos
  have hepoch : (getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2 =
      ((getCurrentEpoch s).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) + 1 := rfl
  rw [hepoch, Nat.succ_mul] at hslotLimit
  unfold Spec.process_ptc_window Spec.compute_start_slot_at_epoch
  simp only [spec_preset]
  cases Spec.uint64Sub (toSpecState s).ptc_window.length preset.SLOTS_PER_EPOCH.toNat with
  | error e => exact ⟨e, rfl⟩
  | ok shift =>
    simp only [bind_ok, hcurrent]
    rw [uint64Add_fits (by omega), bind_ok, uint64Add_fits (by omega), bind_ok,
      uint64Mul_fits (by omega), bind_ok, uint64Add_overflows (by omega)]
    exact ⟨_, rfl⟩

end EpochProofs.EthLib
