import EthLib.Consensus.Proofs.Shuffle
import EpochProofs.EthLib.Oracle
import EpochProofs.SpecFacts.ShuffleClosedForm

/-!
# The shuffle and the seeds: the reference and EthLib agree

The reference shuffles the whole list of positions. EthLib runs the rounds on one position. Both
give `Shuffle.shuffledIndex` for at most `2^40` positions.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- Bounds on preset values that the committee computations use. -/
structure CommitteeBounds (preset : Preset) : Prop where
  rounds : preset.SHUFFLE_ROUND_COUNT.toNat ≤ 256
  registryLimit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40
  syncCommitteeSize : preset.SYNC_COMMITTEE_SIZE ≠ 0
  targetCommitteeSize : preset.TARGET_COMMITTEE_SIZE ≠ 0

theorem committeeBounds_mainnet : CommitteeBounds Preset.mainnet := by constructor <;> decide

theorem committeeBounds_minimal : CommitteeBounds Preset.minimal := by constructor <;> decide

/-! ## Bytes -/

theorem toArray_toList {α : Type} {n : Nat} (v : Vector α n) : v.toArray.toList = v.toList := rfl

theorem uint_to_bytes_eq (width n : Nat) :
    Spec.uint_to_bytes width n = (ByteOrder.toLE width n).toList := by
  apply List.ext_getElem
  · simp [Spec.uint_to_bytes]
  · intro i _ _
    apply UInt8.toNat_inj.mp
    simp [Spec.uint_to_bytes, ByteOrder.toLE, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem littleEndianValue_eq {n : Nat} (bytes : Vector UInt8 n) :
    Spec.littleEndianValue bytes.toList = ByteOrder.ofLE bytes := by
  rw [Spec.littleEndianValue, ByteOrder.ofLE, ← Array.foldr_toList]
  rfl

/-- The hash of the reference, on bytes that EthLib keeps in an array. -/
theorem hash_eq {checks : SignatureChecks} {o : Spec.Oracle} (ho : OracleMatches preset checks o)
    {bytes : List UInt8} {data : Array UInt8} (h : bytes = data.toList) :
    o.hash bytes = _root_.EthLib.Cryptography.Hash.Sha256.hash32 ⟨data⟩ := by
  rw [ho.hash, h]

/-! ## The shuffle -/

theorem pivotOf_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (seed : Bytes32) (n round : Nat) :
    Spec.pivotOf o seed.toList n round = Shuffle.pivot seed round n := by
  unfold Spec.pivotOf Shuffle.pivot Shuffle.roundInput
  rw [hash_eq ho (data := seed.toArray.push (UInt8.ofNat round)) (by simp [toArray_toList]), ← littleEndianValue_eq]
  congr 2

theorem sigma_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (seed : Bytes32) (n round x : Nat) :
    Spec.sigma o seed.toList n round x = Shuffle.indexRound seed n round x := by
  unfold Spec.sigma Shuffle.indexRound Shuffle.swapOrNot
  rw [pivotOf_eq ho]
  have hbit (position : Nat) : (Spec.bitOf o seed.toList round position ≠ 0) ↔
      Shuffle.bitAt (Shuffle.bucketBits seed round (position / 256)) position = true := by
    unfold Spec.bitOf Shuffle.bitAt Shuffle.bucketBits Shuffle.bucketInput Shuffle.roundInput
    rw [hash_eq ho (data := seed.toArray.push (UInt8.ofNat round) ++
      (ByteOrder.toLE 4 (position / 256)).toArray) (by simp [uint_to_bytes_eq, toArray_toList])]
    generalize _root_.EthLib.Cryptography.Hash.Sha256.hash32 _ = bits
    have hlt : position % 256 / 8 < 32 := by omega
    have hget : bits.toList.getD (position % 256 / 8) 0 = bits[position % 256 / 8] := by
      simp [hlt]
    have hand (x : UInt8) : (x &&& 1 == 1) = (x % 2 != 0) := by
      have hx : (x &&& 1).toNat = x.toNat % 2 := by
        rw [UInt8.toNat_and]
        exact Nat.and_one_is_mod _
      rw [Bool.eq_iff_iff, beq_iff_eq, bne_iff_ne, ne_eq, ← UInt8.toNat_inj, ← UInt8.toNat_inj, hx,
        UInt8.toNat_mod]
      show x.toNat % 2 = 1 ↔ ¬x.toNat % 2 = 0
      omega
    have hshift := Spec.shift_mod_two bits[position % 256 / 8] (position % 8)
      (Nat.mod_lt _ (by decide))
    rw [hget]
    simp only [hand]
    rw [← decide_eq_true_iff (p := _ ≠ 0), ← hshift]
  simp only [hbit]

theorem shuffledIndexAfterRounds_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (seed : Bytes32) (n rounds x : Nat) :
    Spec.shuffledIndexAfterRounds o seed.toList n rounds x = Shuffle.shuffledIndex rounds seed n x := by
  rw [Shuffle.shuffledIndex_eq_foldl]
  simp only [Spec.shuffledIndexAfterRounds, sigma_eq ho]

theorem compute_shuffled_index_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (hbounds : CommitteeBounds preset) (ho : OracleMatches preset checks o) (seed : Bytes32)
    {index n : Nat} (hindex : index < n) (hn : n ≤ 2 ^ 40) :
    Spec.compute_shuffled_index (toSpecPreset preset config) o index n seed =
      .ok (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed n index) := by
  rw [Spec.compute_shuffled_index_eq _ _ _ _ _ hindex hn hbounds.rounds, shuffledIndexAfterRounds_eq ho]
  rfl

/-! ## Seeds -/

theorem get_seed_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset fork) (epoch : UInt64)
    (domain : DomainType) :
    SameOutcome (fun a b => b = a) (getSeed s epoch domain)
      (Spec.get_seed (toSpecPreset preset config) o (toSpecState s) epoch.toNat domain) := by
  unfold getSeed Spec.get_seed Spec.get_randao_mix getRandaoMix
  simp only [liftArith_bind, bind_assoc]
  refine .bind (addChecked_same epoch preset.EPOCHS_PER_HISTORICAL_VECTOR).liftArith ?_
  rintro a _ rfl -
  refine .bind (subChecked_same a preset.MIN_SEED_LOOKAHEAD).liftArith ?_
  rintro b _ rfl -
  refine .bind (subChecked_same b 1).liftArith ?_
  rintro shifted _ rfl -
  rw [← bind_assoc]
  refine .bind (readCircular_same s.randaoMixes.elements shifted) ?_
  rintro _ mix rfl -
  refine .returned ?_
  exact hash_eq ho (by simp [uint_to_bytes_eq, toArray_toList])

end EpochProofs.EthLib
