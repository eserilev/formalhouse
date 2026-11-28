import EthLib.Consensus.PayloadTimeliness
import EthLib.Consensus.Proofs.ShufflePermutation
import EpochProofs.EthLib.Consolidations
import EpochProofs.EthLib.Loops
import EpochProofs.EthLib.Shuffle

/-!
# The balance-weighted selection: the reference and EthLib agree

Both loops count the draws with a 64-bit counter, and both fail when the counter overflows.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-! ## One draw -/

/-- The random bytes of draw `i`. -/
theorem random_bytes_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (electra : .pectra ≤ fork) (seed : Bytes32) (i : Nat) :
    o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16)) = drawHash fork seed i := by
  rw [drawHash, drawInput, drawsPerHash, ite_eq_left electra]
  exact hash_eq ho (by simp [uint_to_bytes_eq, toArray_toList])

/-- The random value of draw `i`, from two bytes. -/
def drawValue (random : Bytes32) (i : Nat) : UInt64 :=
  have small : i % 16 * 2 + 1 < 32 := by omega
  random[i % 16 * 2].toUInt64 + 256 * random[i % 16 * 2 + 1].toUInt64

theorem random_value_eq (random : Bytes32) (i : Nat) :
    Spec.bytes_to_uint64 ((random.toList.drop (i % 16 * 2)).take 2) =
      .ok (drawValue random i).toNat := by
  have small : i % 16 * 2 + 1 < 32 := by omega
  have hbytes : (random.toList.drop (i % 16 * 2)).take 2 =
      [random[i % 16 * 2], random[i % 16 * 2 + 1]] := by
    apply List.ext_getElem?
    intro j
    match j with
    | 0 => simp [List.getElem?_drop]
    | 1 => simp [List.getElem?_drop]
    | j + 2 => simp
  rw [hbytes, Spec.bytes_to_uint64, drawValue]
  have h₀ := random[i % 16 * 2].toNat_lt
  have h₁ := random[i % 16 * 2 + 1].toNat_lt
  refine (ite_eq_left ?_).trans (congrArg Except.ok ?_)
  · show random[i % 16 * 2].toNat + 256 * (random[i % 16 * 2 + 1].toNat + 256 * 0) < 2 ^ 64
    omega
  show random[i % 16 * 2].toNat + 256 * (random[i % 16 * 2 + 1].toNat + 256 * 0) = _
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64]
  have h256 : (256 : UInt64).toNat = 256 := rfl
  rw [h256]
  omega

/-- One draw: both sides fail, or both compare the same weight and threshold. -/
theorem draw_same (electra : .pectra ≤ fork) (random : Bytes32) (i : Nat) (balance : UInt64) :
    (∃ accepted weight threshold, drawAccepts preset fork random i balance = .ok accepted ∧
      Spec.uint64Mul balance.toNat (2 ^ 16 - 1) = .ok weight ∧
      Spec.uint64Mul preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat (drawValue random i).toNat =
        .ok threshold ∧
      (accepted = true ↔ weight ≥ threshold)) ∨
    ((∃ e, drawAccepts preset fork random i balance = .error e) ∧
      ((∃ e, Spec.uint64Mul balance.toNat (2 ^ 16 - 1) = .error e) ∨
       ∃ e, Spec.uint64Mul preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (drawValue random i).toNat = .error e)) := by
  have hdraw : drawAccepts preset fork random i balance = liftArith (do
      let threshold ← mulChecked preset.MAX_EFFECTIVE_BALANCE_ELECTRA (drawValue random i)
      let weight ← mulChecked balance (2 ^ 16 - 1)
      return decide (threshold ≤ weight)) := by
    rw [drawAccepts, ite_eq_left electra]
    rfl
  have hweight := mulChecked_same balance (2 ^ 16 - 1)
  have hthreshold := mulChecked_same preset.MAX_EFFECTIVE_BALANCE_ELECTRA (drawValue random i)
  have hmax : ((2 : UInt64) ^ 16 - 1).toNat = 2 ^ 16 - 1 := by decide
  rw [hmax] at hweight
  rw [hdraw]
  generalize mulChecked balance (2 ^ 16 - 1) = x at hweight ⊢
  generalize Spec.uint64Mul balance.toNat (2 ^ 16 - 1) = x' at hweight ⊢
  generalize mulChecked preset.MAX_EFFECTIVE_BALANCE_ELECTRA (drawValue random i) = y
    at hthreshold ⊢
  generalize Spec.uint64Mul preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    (drawValue random i).toNat = y' at hthreshold ⊢
  cases hthreshold with
  | failed => exact .inr ⟨⟨_, rfl⟩, .inr ⟨_, rfl⟩⟩
  | returned ht =>
    cases hweight with
    | failed => exact .inr ⟨⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩
    | returned hw =>
      refine .inl ⟨_, _, _, rfl, rfl, rfl, ?_⟩
      rw [ht, hw, decide_eq_true_eq, UInt64.le_iff_toNat_le]

/-! ## The search -/

theorem balanceWeightedSearch_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (electra : .pectra ≤ fork) (seed : Bytes32)
    (indices balances : Array UInt64) (hsize : balances.size = indices.size)
    (hpos : 0 < indices.size) (shuffle : Bool) (order : Nat → Nat)
    (horder : ∀ k < indices.size, order k < indices.size ∧
      (if shuffle = true then
        Spec.compute_shuffled_index (toSpecPreset preset config) o k indices.size seed
      else .ok k) = .ok (order k)) (size : Nat) :
    ∀ (fuel i : Nat) (selected : Array UInt64) (bound : selected.size ≤ size)
      (random : { random // random = drawHash fork seed i }) (specRandom : Bytes32),
      i + fuel = 2 ^ 64 → 0 < fuel → (i % 16 ≠ 0 → specRandom = drawHash fork seed i) →
      SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
        (balanceWeightedSearch preset fork indices balances order seed size selected bound i random)
        (Spec.compute_balance_weighted_selection_loop (toSpecPreset preset config) o
          (readList UInt64.toNat indices) seed size shuffle indices.size
          (readList UInt64.toNat balances) fuel (readList UInt64.toNat selected) i specRandom)
  | 0, _, _, _, _, _, _, hfuel, _ => absurd hfuel (by decide)
  | fuel + 1, i, selected, bound, ⟨random, hrandom⟩, specRandom, hsum, _, hspecRandom => by
    rw [balanceWeightedSearch, Spec.compute_balance_weighted_selection_loop]
    have hlength : (readList UInt64.toNat selected).length = selected.size := by simp [readList]
    rw [hlength]
    by_cases hfull : selected.size = size
    · rw [dite_eq_left hfull, ite_eq_right (by rw [hfull]; exact Nat.lt_irrefl _)]
      exact .returned (by simp [readList])
    rw [dite_eq_right hfull, ite_eq_left (Nat.lt_of_le_of_ne bound hfull)]
    have hmod16 : Spec.uint64Mod i 16 = .ok (i % 16) := rfl
    have hoffset : Spec.uint64Mul (i % 16) 2 = .ok (i % 16 * 2) := by
      refine ite_eq_left ?_
      show i % 16 * 2 < 2 ^ 64
      omega
    have hmod : Spec.uint64Mod i indices.size = .ok (i % indices.size) := by
      rw [Spec.uint64Mod, ite_eq_right (Nat.ne_of_gt hpos)]
      rfl
    have hbytes : (if (i % 16 * 2 == 0) = true then
        o.hash (seed.toList ++ Spec.uint_to_bytes 8 (i / 16)) else specRandom) = random := by
      rw [hrandom, random_bytes_eq ho electra]
      split
      · rfl
      · rename_i h
        refine hspecRandom fun h' => h ?_
        rw [h']
        rfl
    simp only [hmod16, hoffset, hmod, bind_ok, hbytes, spec_preset]
    obtain ⟨hlt, hposition⟩ := horder _ (Nat.mod_lt i hpos)
    have hbalance : Spec.listGet (readList UInt64.toNat balances) (order (i % indices.size)) =
        .ok (balances.getD (order (i % indices.size)) 0).toNat := by
      rw [listGet_readList (by omega)]
      simp [Array.getD, hsize, hlt]
    have hindex : Spec.listGet (readList UInt64.toNat indices) (order (i % indices.size)) =
        .ok (indices.getD (order (i % indices.size)) 0).toNat := by
      rw [listGet_readList hlt]
      simp [Array.getD, hlt]
    have hbranch {α : Type} (f : Nat → Spec.SpecM α) :
        (if shuffle = true then
          Spec.compute_shuffled_index (toSpecPreset preset config) o (i % indices.size)
            indices.size seed >>= f
        else f (i % indices.size)) = f (order (i % indices.size)) := by
      cases shuffle
      · have h : i % indices.size = order (i % indices.size) := by
          simpa using hposition
        rw [← h]
        rfl
      · simp only [ite_true] at hposition ⊢
        rw [hposition]
        rfl
    rw [hbranch]
    simp only [hbalance, hindex, random_value_eq, bind_ok]
    -- The counter, after the draw.
    have hnext (selected' : Array UInt64) (bound' : selected'.size ≤ size)
        (random' : { random // random = drawHash fork seed (i + 1) }) :
        SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
          (if i + 1 < 2 ^ 64 then
            balanceWeightedSearch preset fork indices balances order seed size selected' bound'
              (i + 1) random'
          else throw (.arith .overflow))
          (do
            let i ← Spec.uint64Add i 1
            Spec.compute_balance_weighted_selection_loop (toSpecPreset preset config) o
              (readList UInt64.toNat indices) seed size shuffle indices.size
              (readList UInt64.toNat balances) fuel (readList UInt64.toNat selected') i random) := by
      unfold Spec.uint64Add Spec.UINT64_SIZE
      by_cases hi : i + 1 < 2 ^ 64
      · rw [ite_eq_left hi, ite_eq_left hi, pure_eq_ok, bind_ok]
        refine balanceWeightedSearch_same ho electra seed indices balances hsize hpos shuffle order
          horder size fuel (i + 1) selected' bound' random' random (by omega) (by omega) ?_
        intro hmod
        rw [hrandom, drawHash, drawHash, drawsPerHash, ite_eq_left electra]
        congr 2
        omega
      · rw [ite_eq_right hi, ite_eq_right hi]
        exact .failed
    rcases draw_same (preset := preset) electra random i
        (balances.getD (order (i % indices.size)) 0) with
      ⟨accepted, weight, threshold, hdraw, hweight, hthreshold, haccepted⟩ |
      ⟨⟨e, hdraw⟩, hfail⟩
    · rw [hdraw, hweight, hthreshold]
      simp only [bind_ok]
      cases accepted
      · have hrejected : ¬weight ≥ threshold := by simpa using haccepted
        rw [ite_eq_right hrejected]
        simp only [pure_eq_ok, bind_ok]
        exact hnext selected bound _
      · have haccepted' : weight ≥ threshold := by simpa using haccepted
        rw [ite_eq_left haccepted']
        simp only [pure_eq_ok, bind_ok]
        have hpush : readList UInt64.toNat selected ++
            [(indices.getD (order (i % indices.size)) 0).toNat] =
            readList UInt64.toNat (selected.push (indices.getD (order (i % indices.size)) 0)) := by
          simp [readList]
        rw [hpush]
        exact hnext _ _ _
    · rw [hdraw]
      rcases hfail with ⟨e', he'⟩ | ⟨e', he'⟩
      · rw [he']
        exact .failed
      · rw [he']
        cases Spec.uint64Mul (balances.getD (order (i % indices.size)) 0).toNat (2 ^ 16 - 1) <;>
          exact .failed

theorem balance_weighted_selection_same {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork) (indices : List UInt64)
    (hlength : indices.length ≤ 2 ^ 40) (seed : Bytes32) (size : UInt64) (shuffle : Bool) :
    SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      (computeBalanceWeightedSelection s indices.toArray seed size shuffle)
      (Spec.compute_balance_weighted_selection (toSpecPreset preset config) o (toSpecState s)
        (indices.map UInt64.toNat) seed size.toNat shuffle) := by
  unfold computeBalanceWeightedSelection Spec.compute_balance_weighted_selection
  simp only [List.length_map, List.size_toArray, List.mapM_toArray]
  by_cases hempty : indices.length = 0
  · have hzero : ¬indices.length > 0 := by omega
    rw [ite_eq_left hempty, ite_eq_left hzero]
    exact .failed
  have hpositive : ¬¬indices.length > 0 := by omega
  rw [ite_eq_right hempty, ite_eq_left (Nat.lt_of_le_of_lt hlength (by decide)),
    ite_eq_right hpositive]
  have hbalances := SameOutcome.mapM (f := fun index => do
      return (← getValidator s index).effectiveBalance)
    (g := fun index => do
      pure (← Spec.listGet (toSpecState s).validators index).effective_balance)
    UInt64.toNat UInt64.toNat indices fun index _ => by
      refine .bind (getValidator_same s index) ?_
      rintro v _ rfl -
      exact .returned rfl
  rw [map_eq_pure_bind, bind_assoc]
  refine .bind hbalances ?_
  rintro balances _ rfl hok
  have hsize : balances.length = indices.length := mapM_length hok
  simp only [pure_bind]
  rw [ite_eq_right (fun h => by omega)]
  have hsearch := balanceWeightedSearch_same (config := config) ho electra seed indices.toArray
    balances.toArray (by simpa using hsize) (by simpa using Nat.pos_of_ne_zero hempty) shuffle
    (if shuffle = true then Shuffle.shuffledIndexBy
      (if shuffle = true then Shuffle.pivots preset.SHUFFLE_ROUND_COUNT.toNat seed indices.length
        else #[]) seed indices.length else id)
    (by
      intro k hk
      rw [List.size_toArray] at hk ⊢
      cases shuffle
      · exact ⟨hk, rfl⟩
      · exact ⟨Shuffle.shuffledIndex_lt hk, compute_shuffled_index_eq hbounds ho seed hk hlength⟩)
    size.toNat (2 ^ 64) 0 #[] (Nat.zero_le _) ⟨drawHash fork seed 0, rfl⟩ Spec.Bytes32.zero
    (by simp) (by decide) (fun h => absurd rfl h)
  simpa [readList, Spec.UINT64_SIZE] using hsearch

end EpochProofs.EthLib
