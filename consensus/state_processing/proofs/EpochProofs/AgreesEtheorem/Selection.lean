import EpochProofs.Etheorem.Committees
import EpochProofs.AgreesEtheorem.CommitteesTotal

/-!
# When Etheorem's selection returns, the reference selection returns

`compute_balance_weighted_selection_ok` (`Etheorem/Shuffle.lean`) goes from the reference to
Etheorem: if the reference selection returns, Etheorem returns the same items. This file goes the
other way. If Etheorem's `computeBalanceWeightedSelection` returns, the reference returns too,
with at least `size` items, each one a candidate (`SelOk`). So on the selection, the reference
and Etheorem succeed together or fail together.

Both loops count passes with the spec's `uint64` counter `i` and fail at `i = 2**64`. The
reference raises on an empty candidate list, and Etheorem asserts `total > 0` (Etheorem PRs #6
and #7). `selection_loop_of_cbwsAux` runs the two loops one pass at a time: each pass of
Etheorem's `cbwsAux` is the pass of `bws_step`, which `TotalityCommittees.lean` writes in closed
form (`bwsAccept`, `bwsNext`, `bwsBytes`).

The reference reads more than Etheorem can fail on: `effective_balance * MAX_RANDOM_VALUE` is a
checked `uint64` product in the reference and a `Nat` product in Etheorem. So the theorem takes
the effective balance bound `MAX_EFFECTIVE_BALANCE_ELECTRA` and the registry bound `2^40`, both
facts of reachable states.

Each proof here holds for Gloas and for Fulu. `forkproof EpochEtheorem` (see
`Etheorem/Forks.lean`) elaborates the shared text once per fork.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

omit [EthCLSpecs.Gloas.Preset] in
/-- The random bytes of pass `i`, as the reference reads them, are Etheorem's hash of the same
input. -/
theorem bwsBytes_eq (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (seed : Spec.Bytes32) (i : Nat) (hi : i < 2 ^ 64) :
    Spec.bwsBytes o seed i =
      bytesToRoot (sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))) := by
  unfold Spec.bwsBytes
  rw [hash_eq o ho]
  congr 2
  apply ba_eq_of_toList
  have h16 : (UInt64.ofNat (i / 16)).toNat = i / 16 :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  rw [toBA_data, append_data_toList, vecToBytes_toList, ← uint_to_bytes_8, h16]

/-- The candidate position of pass `i` in Etheorem is the reference's `bwsNext`. With the
shuffle, Etheorem reads its permutation, and the reference folds the shuffle rounds
(`compute_shuffled_index_eq`). -/
theorem bwsNext_eq (p : Spec.Preset) (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hc : CommitteePresetAgrees p) (seed : Spec.Bytes32) (n : Nat) (shuffle : Bool) (i : Nat)
    (hn : 0 < n) (hn40 : n ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256) :
    (if shuffle then
        ((if shuffle then EthCLSpecs.Gloas.computeShuffledPermutation n (vecToBytes seed)
          else #[])[i % n]!).toNat
      else i % n) = Spec.bwsNext p o seed n shuffle i := by
  unfold Spec.bwsNext
  cases shuffle with
  | false => rfl
  | true =>
    simp only [if_true]
    have hlt : i % n < n := Nat.mod_lt _ hn
    have hcs := Spec.compute_shuffled_index_eq p o seed (i % n) n hlt hn40 hR
    exact ((compute_shuffled_index_ok p o ho hc.shuffleRoundCount hc.shuffleRoundCountPos
      (i % n) n seed hcs).2).symm

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
/-- Two bytes of a root at `offset`, read as the reference reads them, are Etheorem's `le2`. -/
theorem leNat_take2_eq (b : ByteArray) (offset : Nat) (h : offset + 2 ≤ 32) :
    Spec.leNat (((bytesToRoot b).toList.drop offset).take 2) = le2 b offset := by
  have h1 := bytes_to_uint64_take2 b offset h
  rw [Spec.bytes_to_uint64_take2] at h1
  exact Except.ok.inj h1

/-- When Etheorem's selection loop returns, the reference loop returns, one pass at a time.

`n = UInt64.size - i` is the measure that `cbwsAux` recurses on. `erb` and `rb` are the random
bytes that each loop carries into pass `i`. They are only read when `i % 16 ≠ 0`, and then both
hold the hash of block `i / 16`. The reference result has at least `size` items, all of them
candidates. -/
theorem selection_loop_of_cbwsAux (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hc : CommitteePresetAgrees p)
    (idxArr : Array UInt64) (seed : Spec.Bytes32) (size : Nat) (shuffle : Bool)
    (effBals : Array Nat)
    (hlen : effBals.size = idxArr.size) (htot : 0 < idxArr.size)
    (hn40 : idxArr.size ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (heb : ∀ x ∈ effBals.toList, x ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hmax : p.MAX_EFFECTIVE_BALANCE_ELECTRA ≤ 2 ^ 41) :
    ∀ (n i : Nat) (erb : ByteArray) (sel res : Array UInt64) (rb : Spec.Bytes32),
      UInt64.size - i = n →
      (i % 16 ≠ 0 → erb = sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))) →
      (i % 16 ≠ 0 → rb = Spec.bwsBytes o seed i) →
      (∀ x ∈ sel.toList.map UInt64.toNat, x ∈ idxArr.toList.map UInt64.toNat) →
      EthCLSpecs.Gloas.cbwsAux (idxArr.map UInt64.toNat) effBals
        (if shuffle then EthCLSpecs.Gloas.computeShuffledPermutation idxArr.size (vecToBytes seed)
          else #[])
        (vecToBytes seed) idxArr.size size shuffle i erb sel = .ok res →
      ∃ r, Spec.compute_balance_weighted_selection_loop p o (idxArr.toList.map UInt64.toNat) seed
          size shuffle effBals.toList.length effBals.toList (2 ^ 64 - i)
          (sel.toList.map UInt64.toNat) i rb = .ok r ∧
        size ≤ r.length ∧ ∀ x ∈ r, x ∈ idxArr.toList.map UInt64.toNat := by
  have hlenL : effBals.toList.length = idxArr.size := by simpa using hlen
  have hlenI : effBals.toList.length = (idxArr.toList.map UInt64.toNat).length := by simp [hlen]
  intro n
  induction n with
  | zero =>
    intro i erb sel res rb hn _ _ _ h
    rw [EthCLSpecs.Gloas.cbwsAux, if_pos (by omega)] at h
    exact absurd h (by simp [throwArithmetic, liftErr, MonadExcept.ofExcept, Except.mapError])
  | succ m ih =>
    intro i erb sel res rb hn herb hrb hsub h
    have hi : i < 2 ^ 64 := by simp only [UInt64.size] at hn; omega
    rw [EthCLSpecs.Gloas.cbwsAux, if_neg (cbws_counter_lt hi)] at h
    split at h
    · -- `size` items selected: both loops stop.
      rename_i hge
      simp only [pure, Except.pure, Except.ok.injEq] at h
      have hfuel : 2 ^ 64 - i = (2 ^ 64 - i - 1) + 1 := by omega
      rw [hfuel, Spec.compute_balance_weighted_selection_loop, if_neg (by simp; omega)]
      exact ⟨_, rfl, by simp; omega, hsub⟩
    · rename_i hlt
      -- The next call does not throw, so `i + 1 < 2^64`.
      have hi1 : i + 1 < 2 ^ 64 := by
        by_contra hcon
        rw [EthCLSpecs.Gloas.cbwsAux, if_pos (by simp only [UInt64.size]; omega)] at h
        exact absurd h (by simp [throwArithmetic, liftErr, MonadExcept.ofExcept, Except.mapError])
      -- The random bytes of this pass.
      have hE : (if (i % 16 * 2 == 0) = true then
            sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else erb) =
          sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) := by
        split
        · rfl
        · rename_i h0
          exact herb (by simp at h0; omega)
      simp only [] at h
      rw [hE] at h
      generalize hH : sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) = H at h
      have hbytes : Spec.bwsBytes o seed i = bytesToRoot H := by
        rw [← hH]; exact bwsBytes_eq o ho seed i hi
      -- The candidate position of this pass.
      have hnext := bwsNext_eq p o ho hc seed idxArr.size shuffle i htot hn40 hR
      generalize hk : (if shuffle then
          ((if shuffle then
            EthCLSpecs.Gloas.computeShuffledPermutation idxArr.size (vecToBytes seed)
            else #[])[i % idxArr.size]!).toNat
          else i % idxArr.size) = k at h hnext
      have hkn : k < idxArr.size := by
        rw [hnext]
        unfold Spec.bwsNext
        split
        · exact Spec.csiFold_lt _ _ _ _ _ htot (Nat.mod_lt _ htot)
        · exact Nat.mod_lt _ htot
      -- The acceptance test of this pass.
      have hoff : i % 16 * 2 + 2 ≤ 32 := by omega
      have hacc : (effBals[k]! * EthCLSpecs.Gloas.Const.maxRandomValue ≥
            EthCLSpecs.Gloas.Const.maxEffectiveBalanceElectra * le2 H (i % 16 * 2)) ↔
          Spec.bwsAccept p o seed effBals.toList shuffle i = true := by
        unfold Spec.bwsAccept
        rw [hbytes, leNat_take2_eq H _ hoff, hlenL, ← hnext, hc.maxEffectiveBalanceElectra]
        rw [getElem!_pos effBals k (by omega)]
        simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList,
          Array.getElem?_eq_getElem (show k < effBals.size by omega), Option.getD_some,
          decide_eq_true_eq]
        rfl
      -- The item that an accepting pass adds.
      have hpush : (sel.push (UInt64.ofNat ((idxArr.map UInt64.toNat)[k]!))).toList.map
            UInt64.toNat =
          sel.toList.map UInt64.toNat ++
            [(idxArr.toList.map UInt64.toNat).getD (Spec.bwsNext p o seed
              effBals.toList.length shuffle i) 0] := by
        rw [hlenL, ← hnext, getElem!_pos (idxArr.map UInt64.toNat) k (by simpa using hkn)]
        simp [List.getD_eq_getElem?_getD, hkn]
      have hmem : (idxArr.toList.map UInt64.toNat).getD (Spec.bwsNext p o seed
          effBals.toList.length shuffle i) 0 ∈ idxArr.toList.map UInt64.toNat := by
        rw [hlenL, ← hnext]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by simpa using hkn), Option.getD_some]
        exact List.getElem_mem _
      -- One reference pass, in closed form.
      have hfuel : 2 ^ 64 - i = (2 ^ 64 - (i + 1)) + 1 := by omega
      rw [hfuel, Spec.bws_step p o _ seed size shuffle effBals.toList _ _ i rb (by simp; omega)
        hlenI (by omega) (by omega) hR heb hmax hi1 hrb]
      have hrb1 : (i + 1) % 16 ≠ 0 → Spec.bwsBytes o seed i = Spec.bwsBytes o seed (i + 1) := by
        intro h16
        simp only [Spec.bwsBytes]
        congr 3
        omega
      have herb1 : (i + 1) % 16 ≠ 0 →
          H = sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat ((i + 1) / 16))) := by
        intro h16
        rw [← hH]
        congr 4
        omega
      by_cases ha : Spec.bwsAccept p o seed effBals.toList shuffle i = true
      · rw [if_pos ((hacc).mpr ha)] at h
        rw [if_pos ha, ← hpush]
        refine ih (i + 1) H _ res _ (by simp only [UInt64.size] at hn ⊢; omega) herb1 hrb1 ?_ h
        rw [hpush]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hsub x hx
        · rw [List.mem_singleton.mp hx]; exact hmem
      · rw [if_neg (fun hh => ha ((hacc).mp hh))] at h
        rw [if_neg ha]
        exact ih (i + 1) H _ res _ (by simp only [UInt64.size] at hn ⊢; omega) herb1 hrb1 hsub h

/-- When Etheorem's selection returns, the reference selection over the same candidates returns
at least `size` items, each one a candidate (`SelOk`).

- `hin`: each candidate is a validator. The reference reads its effective balance with a checked
  list read.
- `heb`, `hn40`: the effective balances are at most `MAX_EFFECTIVE_BALANCE_ELECTRA`, and there
  are at most `2^40` candidates. The reference checks the `uint64` products of the pass and the
  shuffle arithmetic. Etheorem computes them in `Nat`.
- `hR`, `hmax`: preset bounds. -/
theorem selOk_of_etheorem (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hc : CommitteePresetAgrees p) (e : EtheoremState)
    (idxArr : Array UInt64) (seed : Spec.Bytes32) (size : Nat) (shuffle : Bool)
    (hin : ∀ j ∈ idxArr.toList.map UInt64.toNat, j < (toSpecState e).validators.length)
    (heb : ∀ v ∈ (toSpecState e).validators, v.effective_balance ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn40 : idxArr.size ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (hmax : p.MAX_EFFECTIVE_BALANCE_ELECTRA ≤ 2 ^ 41) {res : Array UInt64}
    (h : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) idxArr (vecToBytes seed)
      size shuffle = .ok res) :
    Spec.SelOk p o (toSpecState e) (idxArr.toList.map UInt64.toNat) seed size shuffle := by
  unfold EthCLSpecs.Gloas.computeBalanceWeightedSelection at h
  simp only [view_uncachedBox] at h
  split at h
  swap
  · exact absurd h throw_bind_ne_ok
  rename_i htot
  simp only [pure_bind] at h
  -- Etheorem's effective balances, as the reference reads them.
  let effBals : Array Nat := idxArr.map fun vi => (e.validators[vi.toNat]!).effectiveBalance.toNat
  have hmapM : (idxArr.toList.map UInt64.toNat).mapM (fun index => do
      pure (← Spec.listGet (toSpecState e).validators index).effective_balance :
        Nat → Spec.SpecM Nat) = .ok effBals.toList := by
    have := Spec.tot_mapM (fun index => do
      pure (← Spec.listGet (toSpecState e).validators index).effective_balance :
        Nat → Spec.SpecM Nat)
      (fun j => (e.validators.val[j]!).effectiveBalance.toNat) (idxArr.toList.map UInt64.toNat)
      (by
        intro j hj
        have hjl := hin j hj
        rw [Spec.tot_get hjl, Spec.tot_bind_ok]
        simp only [toSpecState_validators, List.getElem_map, Array.getElem_toList] at hjl ⊢
        rw [getElem!_pos e.validators.val j (by simpa using hjl)]
        rfl)
    rw [this]
    simp [effBals, sszList_getElem!_val]
  have hlen : effBals.size = idxArr.size := by simp [effBals]
  have hebs : ∀ x ∈ effBals.toList, x ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA := by
    intro x hx
    simp only [effBals, Array.toList_map, List.mem_map] at hx
    obtain ⟨vi, hvi, rfl⟩ := hx
    have hjl := hin vi.toNat (List.mem_map_of_mem hvi)
    have h1 := heb _ (List.getElem_mem hjl)
    simp only [toSpecState_validators, List.getElem_map, Array.getElem_toList] at h1 hjl
    rw [sszList_getElem!_val, getElem!_pos e.validators.val _ (by simpa using hjl)]
    exact h1
  obtain ⟨r, hr, hsz, hmem⟩ := selection_loop_of_cbwsAux p o ho hc idxArr seed size shuffle
    effBals hlen htot hn40 hR hebs hmax _ 0 ByteArray.empty #[] res Spec.Bytes32.zero rfl
    (by simp) (by simp) (by simp) h
  refine ⟨r, ?_, hsz, hmem⟩
  unfold Spec.compute_balance_weighted_selection
  rw [if_neg (by simp only [List.length_map, Array.length_toList]; omega)]
  simp only [pure_bind]
  rw [hmapM, Spec.tot_bind_ok]
  have hl : (idxArr.toList.map UInt64.toNat).length = effBals.toList.length := by
    simp [hlen]
  rw [hl]
  simpa [Spec.UINT64_SIZE] using hr

end forkproof
