import EthLib.Consensus.Accessors
import EpochProofs.EthLib.Selection
import EpochProofs.Spec.Fulu

/-!
# The Fulu selections: the reference and EthLib agree

Fulu draws a proposer with `compute_proposer_index`, and its sync committee with the Electra loop.
EthLib has the first one as a search of its own. It draws the sync committee of every fork with the
balance-weighted selection.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem mod16_eq (i : Nat) : Spec.uint64Mod i 16 = .ok (i % 16) := rfl

theorem offset_eq (i : Nat) : Spec.uint64Mul (i % 16) 2 = .ok (i % 16 * 2) := by
  refine ite_eq_left ?_
  show i % 16 * 2 < 2 ^ 64
  omega

theorem uint64Mod_nat {a b : Nat} (hb : 0 < b) : Spec.uint64Mod a b = .ok (a % b) := by
  rw [Spec.uint64Mod, ite_eq_right (Nat.ne_of_gt hb)]
  rfl

theorem listGet_validators_same (s : BeaconState preset fork) (index : UInt64) :
    Spec.listGet (toSpecState s).validators index.toNat =
      match s.validators.data[index.toNat]? with
      | some v => .ok (toSpecValidator v)
      | none => .error .indexOutOfRange := by
  unfold Spec.listGet
  simp only [toSpecState, readList, List.getElem?_map, Array.getElem?_toList]
  cases s.validators.data[index.toNat]? <;> rfl

/-! ## The proposer -/

theorem proposerSearch_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork) (seed : Bytes32)
    (indices : List UInt64) (hpos : 0 < indices.length) (hlength : indices.length ≤ 2 ^ 40) :
    ∀ (fuel i : Nat), i + fuel = 2 ^ 64 → 0 < fuel →
      SameOutcome SameNumber
        (proposerSearch preset fork s.validators.data indices.toArray
          (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed indices.length) seed i)
        (Spec.compute_proposer_index_loop (toSpecPreset preset config) o (toSpecState s).validators
          (indices.map UInt64.toNat) seed indices.length fuel i)
  | 0, _, _, hfuel => absurd hfuel (by decide)
  | fuel + 1, i, hsum, _ => by
    rw [proposerSearch, Spec.compute_proposer_index_loop]
    have hmodlt := Nat.mod_lt i hpos
    have hlt := Shuffle.shuffledIndex_lt (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
      (seed := seed) hmodlt
    simp only [List.size_toArray, uint64Mod_nat hpos, bind_ok, spec_preset,
      compute_shuffled_index_eq hbounds ho seed hmodlt hlength, mod16_eq, offset_eq,
      random_bytes_eq ho electra, random_value_eq]
    have hindex : Spec.listGet (indices.map UInt64.toNat)
        (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed indices.length
          (i % indices.length)) =
        .ok (indices.toArray.getD (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed
          indices.length (i % indices.length)) 0).toNat := by
      simp [Spec.listGet, hlt, pure, Except.pure]
    rw [hindex, bind_ok]
    generalize indices.toArray.getD (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed
      indices.length (i % indices.length)) 0 = candidate
    rw [listGet_validators_same]
    cases hv : s.validators.data[candidate.toNat]? with
    | none => exact .failed
    | some v =>
      simp only [bind_ok]
      rw [proposerDraw]
      have hbalance : (toSpecValidator v).effective_balance = v.effectiveBalance.toNat := rfl
      rw [hbalance]
      rcases draw_same (preset := preset) electra (drawHash fork seed i) i v.effectiveBalance with
        ⟨accepted, weight, threshold, hdraw, hweight, hthreshold, haccepted⟩ |
        ⟨⟨e, hdraw⟩, hfail⟩
      · rw [hdraw, hweight, hthreshold]
        simp only [bind_ok]
        cases accepted
        · have hrejected : ¬weight ≥ threshold := by simpa using haccepted
          rw [ite_eq_right hrejected]
          simp only [Bool.false_eq_true, ite_false]
          unfold Spec.uint64Add Spec.UINT64_SIZE
          by_cases hi : i + 1 < 2 ^ 64
          · rw [dite_eq_left hi, ite_eq_left hi, pure_eq_ok, bind_ok]
            exact proposerSearch_same hbounds ho electra s seed indices hpos hlength fuel (i + 1)
              (by omega) (by omega)
          · rw [dite_eq_right hi, ite_eq_right hi]
            exact .failed
        · have haccepted' : weight ≥ threshold := by simpa using haccepted
          rw [ite_eq_left haccepted']
          exact .returned rfl
      · rw [hdraw]
        rcases hfail with ⟨e', he'⟩ | ⟨e', he'⟩
        · rw [he']
          exact .failed
        · rw [he']
          cases Spec.uint64Mul v.effectiveBalance.toNat (2 ^ 16 - 1) <;> exact .failed

theorem compute_proposer_index_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork) (seed : Bytes32)
    (indices : List UInt64) (hlength : indices.length ≤ 2 ^ 40) :
    SameOutcome SameNumber (computeProposerIndex s indices.toArray seed)
      (Spec.compute_proposer_index (toSpecPreset preset config) o (toSpecState s)
        (indices.map UInt64.toNat) seed) := by
  unfold computeProposerIndex Spec.compute_proposer_index
  simp only [List.length_map, List.size_toArray]
  by_cases hempty : indices.length = 0
  · have hzero : ¬indices.length > 0 := by omega
    rw [ite_eq_left hempty, ite_eq_left hzero]
    exact .failed
  have hpositive : ¬¬indices.length > 0 := by omega
  rw [ite_eq_right hempty, ite_eq_left (Nat.lt_of_le_of_lt hlength (by decide)),
    ite_eq_right hpositive, ite_eq_right (Nat.not_lt.mpr hlength)]
  exact proposerSearch_same hbounds ho electra s seed indices (Nat.pos_of_ne_zero hempty) hlength
    Spec.UINT64_SIZE 0 (Nat.zero_add _) (Nat.two_pow_pos 64)

/-! ## The sync committee -/

/-- The Electra loop and the balance-weighted loop of the reference are equal, if each candidate
names a validator. -/
theorem sync_committee_loop_eq (p : Spec.Preset) (o : Spec.Oracle) (validators : List Spec.Validator)
    (indices : List Nat) (balances : List Nat)
    (hbalances : ∀ index ∈ indices, index < validators.length)
    (heq : balances = indices.map fun index =>
      ((validators[index]?).map (·.effective_balance)).getD 0) (seed : Spec.Bytes32) :
    ∀ (fuel i : Nat) (selected : List Nat) (random : Spec.Bytes32),
      (i % 16 ≠ 0 → random = o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16))) →
      Spec.next_sync_committee_indices_loop p o validators indices seed indices.length fuel selected
        i =
      Spec.compute_balance_weighted_selection_loop p o indices seed p.SYNC_COMMITTEE_SIZE true
        indices.length balances fuel selected i random
  | 0, _, _, _, _ => rfl
  | fuel + 1, i, selected, random, hrandom => by
    rw [Spec.next_sync_committee_indices_loop, Spec.compute_balance_weighted_selection_loop]
    have hbytes : (if (i % 16 * 2 == 0) = true then
        o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16)) else random) =
        o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16)) := by
      split
      · rfl
      · rename_i h
        exact hrandom fun h' => h (by rw [h']; rfl)
    simp only [mod16_eq, offset_eq, bind_ok, hbytes, ite_true]
    split
    · refine bind_congr fun position => ?_
      refine bind_congr fun shuffled => ?_
      cases hc : indices[shuffled]? with
      | none =>
        have hb : balances[shuffled]? = none := by rw [heq]; simp [hc]
        simp [Spec.listGet, hc, hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      | some candidate =>
        have hlt := hbalances candidate (List.mem_of_getElem? hc)
        have hb : balances[shuffled]? = some validators[candidate].effective_balance := by
          rw [heq]
          simp [hc, hlt]
        have hv : validators[candidate]? = some validators[candidate] :=
          List.getElem?_eq_getElem hlt
        simp only [Spec.listGet, hc, hb, hv, pure_eq_ok, bind_ok]
        simp only [random_value_eq, bind_ok]
        have hnext (selected' : List Nat) :
            (do
              let i ← Spec.uint64Add i 1
              Spec.next_sync_committee_indices_loop p o validators indices seed indices.length fuel
                selected' i) =
            (do
              let i' ← Spec.uint64Add i 1
              Spec.compute_balance_weighted_selection_loop p o indices seed p.SYNC_COMMITTEE_SIZE
                true indices.length balances fuel selected' i'
                (o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16)))) := by
          unfold Spec.uint64Add
          split
          · simp only [pure_eq_ok, bind_ok]
            refine sync_committee_loop_eq p o validators indices balances hbalances heq seed fuel
              (i + 1) selected' _ fun h => ?_
            congr 3
            omega
          · rfl
        simp only [hnext]
    · rfl

theorem active_length_le (hbounds : CommitteeBounds preset) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (epoch : UInt64) :
    (getActiveValidatorIndices s epoch).length ≤ 2 ^ 40 :=
  Nat.le_trans (length_getActiveValidatorIndices_le s epoch)
    (Nat.le_trans hregistry hbounds.registryLimit)

theorem effective_balances_eq (s : BeaconState preset fork) (indices : List Nat)
    (hinside : ∀ index ∈ indices, index < (toSpecState s).validators.length) :
    (indices.mapM fun index => do
      pure (← Spec.listGet (toSpecState s).validators index).effective_balance) =
    (.ok (indices.map fun index =>
      (((toSpecState s).validators[index]?).map (·.effective_balance)).getD 0) :
      Spec.SpecM (List Nat)) := by
  refine mapM_ok fun index hmem => ?_
  simp [Spec.listGet, hinside index hmem, pure, Except.pure, bind, Except.bind]

theorem fulu_sync_committee_indices_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    (ho : OracleMatches preset checks o) (electra : .pectra ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat) (getNextSyncCommitteeIndices s)
      (Spec.get_next_sync_committee_indices_fulu (toSpecPreset preset config) o
        (toSpecState s)) := by
  unfold getNextSyncCommitteeIndices Spec.get_next_sync_committee_indices_fulu
  rw [get_current_epoch_eq hslots]
  simp only [bind_ok]
  refine .bind (addChecked_same (getCurrentEpoch s) 1).liftArith ?_
  rintro next _ rfl -
  refine .bind (get_seed_same ho s next DOMAIN_SYNC_COMMITTEE) ?_
  rintro _ seed rfl -
  obtain ⟨heq, -, hinside⟩ := get_active_validator_indices_same hregistry next
  rw [getActiveValidatorIndicesChecked_of_within hregistry, bind_ok]
  have hselection := balance_weighted_selection_same (config := config) hbounds ho electra s
    (getActiveValidatorIndices s next) (active_length_le hbounds hregistry next) seed
    preset.SYNC_COMMITTEE_SIZE true
  rw [← heq] at hselection
  unfold Spec.compute_balance_weighted_selection at hselection
  have hinside' : ∀ index ∈ Spec.get_active_validator_indices (toSpecState s) next.toNat,
      index < (toSpecState s).validators.length := by
    rw [heq]
    intro index hmem
    obtain ⟨index, hmem', rfl⟩ := List.mem_map.mp hmem
    simpa [toSpecState, readList] using hinside index hmem'
  generalize Spec.get_active_validator_indices (toSpecState s) next.toNat = active
    at hselection hinside' ⊢
  by_cases hempty : active.length = 0
  · have hzero : ¬active.length > 0 := by omega
    simp only [hzero, not_false_eq_true, ite_true] at hselection
    have hfail : ∃ e, computeBalanceWeightedSelection s
        (getActiveValidatorIndices s next).toArray seed preset.SYNC_COMMITTEE_SIZE true =
        .error e := by
      generalize computeBalanceWeightedSelection s _ seed preset.SYNC_COMMITTEE_SIZE true = x
        at hselection
      cases hselection
      exact ⟨_, rfl⟩
    obtain ⟨e, he⟩ := hfail
    rw [he]
    obtain ⟨k, hk⟩ : ∃ k, Spec.UINT64_SIZE = k + 1 :=
      ⟨Spec.UINT64_SIZE - 1, (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm⟩
    have hsize : 0 < preset.SYNC_COMMITTEE_SIZE.toNat := by
      refine Nat.pos_of_ne_zero fun h => hbounds.syncCommitteeSize (UInt64.toNat_inj.mp h)
    rw [hk, Spec.next_sync_committee_indices_loop, hempty]
    simp only [List.length_nil, spec_preset, hsize, ite_true, Spec.uint64Mod]
    exact .failed
  · have hpositive : ¬¬active.length > 0 := by omega
    simp only [hpositive, ite_false, effective_balances_eq s active hinside', bind_ok]
      at hselection
    rw [sync_committee_loop_eq _ _ _ _ _ hinside' rfl seed _ _ _ Spec.Bytes32.zero
      (fun h => absurd rfl h)]
    exact hselection

theorem sync_committee_indices_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hslots : preset.SLOTS_PER_EPOCH ≠ 0) (hbounds : CommitteeBounds preset)
    (ho : OracleMatches preset checks o) (electra : .pectra ≤ fork) {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat) (getNextSyncCommitteeIndices s)
      (Spec.get_next_sync_committee_indices (toSpecPreset preset config) o (toSpecState s)) := by
  unfold getNextSyncCommitteeIndices Spec.get_next_sync_committee_indices
  rw [get_current_epoch_eq hslots]
  simp only [bind_ok]
  refine .bind (addChecked_same (getCurrentEpoch s) 1).liftArith ?_
  rintro next _ rfl -
  refine .bind (get_seed_same ho s next DOMAIN_SYNC_COMMITTEE) ?_
  rintro _ seed rfl -
  rw [getActiveValidatorIndicesChecked_of_within hregistry, bind_ok,
    (get_active_validator_indices_same hregistry next).eq]
  exact balance_weighted_selection_same hbounds ho electra s _
    (active_length_le hbounds hregistry next) seed preset.SYNC_COMMITTEE_SIZE true

end EpochProofs.EthLib
