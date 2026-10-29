import EpochProofs.Sanity.Invariants.Totality
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.PresetBounds
import EpochProofs.Sanity.ShuffleClosedForm
import EpochProofs.Sanity.PtcIndices

/-!
# The committee steps of the epoch succeed

`committee_steps_total` proves that `process_sync_committee_updates`,
`process_proposer_lookahead` and `process_ptc_window` return `ok` on mainnet. It needs two
kinds of facts about the state that the three steps read:

- `CommitteeStepFacts`: the registry limit, `effective_balance ≤ MAX_EFFECTIVE_BALANCE_ELECTRA`, the two
  vector lengths and valid public keys. These are invariants of reachable states.
- `CommitteeStepPreconds`: preconditions of the pyspec itself. Without them the pyspec raises.

Error sources and why they do not fire:
- The shuffle (`compute_shuffled_permutation`): `0 < n ≤ 2^40` and `SHUFFLE_ROUND_COUNT ≤ 256`
  (`compute_shuffled_permutation_eq`).
- `get_seed` reads `randao_mixes[epoch + EPOCHS_PER_HISTORICAL_VECTOR - 2]`: the vector has
  `EPOCHS_PER_HISTORICAL_VECTOR` items, and the epoch is far below `2^64`.
- `compute_balance_weighted_selection`: `assert total > 0` needs a candidate.
  `effective_balance * (2^16 - 1)` fits a `Uint64` because the effective balance is at most
  `2048 ETH`. The counter `i` is a `Uint64`, so the loop must accept its candidates within `2^64`
  passes (`SelFin`). That depends on the hash values.
- `eth_aggregate_pubkeys` asserts `KeyValidate` on each key.
- The two `len(...) - SLOTS_PER_EPOCH` need the SSZ vector lengths.

`process_ptc_window_few_active_error` is a pyspec halt: with fewer than `SLOTS_PER_EPOCH`
validators active at `current + 2`, the first slot of that epoch has no beacon committee
members, and `compute_ptc` raises at `assert total > 0`.
-/

namespace EpochProofs.Spec


/-- The random bytes of pass `i`. -/
def bwsBytes (o : Oracle) (seed : Bytes32) (i : Nat) : Bytes32 :=
  o.hash (seed.toList ++ uint_to_bytes 8 (i / 16))

/-- The candidate position of pass `i`. -/
def bwsNext (p : Preset) (o : Oracle) (seed : Bytes32) (total : Nat) (shuffle : Bool) (i : Nat) :
    Nat :=
  if shuffle then csiFold o seed.toList total p.SHUFFLE_ROUND_COUNT (i % total) else i % total

/-- Pass `i` accepts its candidate. -/
def bwsAccept (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei) (shuffle : Bool)
    (i : Nat) : Bool :=
  decide (ebs.getD (bwsNext p o seed ebs.length shuffle i) 0 * (2 ^ 16 - 1) ≥
    p.MAX_EFFECTIVE_BALANCE_ELECTRA *
      leNat (((bwsBytes o seed i).toList.drop (i % 16 * 2)).take 2))

theorem leNat_take2_lt (l : List UInt8) : leNat (l.take 2) < 2 ^ 16 := by
  have h := leNat_lt (l.take 2)
  have hl : (l.take 2).length ≤ 2 := by simp
  have : 256 ^ (l.take 2).length ≤ 256 ^ 2 := Nat.pow_le_pow_right (by decide) hl
  omega

theorem bytes_to_uint64_take2 (l : List UInt8) :
    bytes_to_uint64 (l.take 2) = .ok (leNat (l.take 2)) := by
  have h := leNat_take2_lt l
  simp only [bytes_to_uint64, leNat] at h ⊢
  rw [if_pos (by unfold UINT64_SIZE; omega)]
  rfl

theorem bws_step (p : Preset) (o : Oracle) (indices : List ValidatorIndex) (seed : Bytes32)
    (size : Nat) (shuffle : Bool) (ebs : List Gwei) (fuel : Nat) (selected : List ValidatorIndex)
    (i : Nat) (rb : Bytes32)
    (hsel : selected.length < size) (hlen : ebs.length = indices.length) (htot : 0 < ebs.length)
    (hn40 : ebs.length ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (heb : ∀ e ∈ ebs, e ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hmax : p.MAX_EFFECTIVE_BALANCE_ELECTRA ≤ 2 ^ 41)
    (hi : i + 1 < 2 ^ 64) (hrb : i % 16 ≠ 0 → rb = bwsBytes o seed i) :
    compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs
        (fuel + 1) selected i rb =
      compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs fuel
        (if bwsAccept p o seed ebs shuffle i then
          selected ++ [indices.getD (bwsNext p o seed ebs.length shuffle i) 0] else selected)
        (i + 1) (bwsBytes o seed i) := by
  have htot0 : ebs.length ≠ 0 := Nat.pos_iff_ne_zero.mp htot
  have hrb' : (if i % 16 * 2 == 0 then o.hash (seed.toList ++ uint_to_bytes 8 (i / 16)) else rb) =
      bwsBytes o seed i := by
    by_cases h : i % 16 = 0
    · simp [h, bwsBytes]
    · rw [hrb h]; simp [bwsBytes]; try omega
  have hnext : i % ebs.length < ebs.length := Nat.mod_lt _ htot
  have hcsi : bwsNext p o seed ebs.length shuffle i < ebs.length := by
    unfold bwsNext; split
    · exact csiFold_lt o seed.toList ebs.length p.SHUFFLE_ROUND_COUNT _ htot hnext
    · exact hnext
  rw [compute_balance_weighted_selection_loop, if_pos hsel]
  simp only [tot_mod (show (16:Nat) ≠ 0 by decide), tot_mul (show i % 16 * 2 < 2 ^ 64 by omega),
    tot_mod htot0, tot_bind_ok, hrb']
  have key : ∀ k, k < ebs.length → bwsNext p o seed ebs.length shuffle i = k →
      (do
        let __do_lift ← listGet ebs k
        let weight ← uint64Mul __do_lift (2 ^ 16 - 1)
        let random_value ← bytes_to_uint64
          (List.take 2 (List.drop (i % 16 * 2) (Vector.toList (bwsBytes o seed i))))
        let threshold ← uint64Mul p.MAX_EFFECTIVE_BALANCE_ELECTRA random_value
        if weight ≥ threshold then do
            let __do_lift ← listGet indices k
            let y ← pure (selected ++ [__do_lift])
            let i_1 ← uint64Add i 1
            compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs
              fuel y i_1 (bwsBytes o seed i)
          else do
            let y ← pure selected
            let i_1 ← uint64Add i 1
            compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs
              fuel y i_1 (bwsBytes o seed i) : SpecM (List ValidatorIndex)) =
      compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs fuel
        (if bwsAccept p o seed ebs shuffle i then
          selected ++ [indices.getD (bwsNext p o seed ebs.length shuffle i) 0] else selected)
        (i + 1) (bwsBytes o seed i) := by
    intro k hk hkdef
    have hki : k < indices.length := hlen ▸ hk
    have heb1 : ebs[k] * (2 ^ 16 - 1) < 2 ^ 64 := by
      have h2 : ebs[k] ≤ 2 ^ 41 := Nat.le_trans (heb _ (List.getElem_mem hk)) hmax
      calc ebs[k] * (2 ^ 16 - 1) ≤ 2 ^ 41 * (2 ^ 16 - 1) := Nat.mul_le_mul_right _ h2
        _ < 2 ^ 64 := by decide
    have hthr : p.MAX_EFFECTIVE_BALANCE_ELECTRA *
        leNat (List.take 2 (List.drop (i % 16 * 2) (bwsBytes o seed i).toList)) < 2 ^ 64 := by
      have h1 := leNat_take2_lt (List.drop (i % 16 * 2) (bwsBytes o seed i).toList)
      calc _ ≤ 2 ^ 41 * leNat (List.take 2 (List.drop (i % 16 * 2) (bwsBytes o seed i).toList)) :=
            Nat.mul_le_mul_right _ hmax
        _ < 2 ^ 41 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_left h1 (by decide)
        _ < 2 ^ 64 := by decide
    have hacc : bwsAccept p o seed ebs shuffle i =
        decide (ebs[k] * (2 ^ 16 - 1) ≥ p.MAX_EFFECTIVE_BALANCE_ELECTRA *
          leNat (List.take 2 (List.drop (i % 16 * 2) (bwsBytes o seed i).toList))) := by
      simp only [bwsAccept, hkdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
        Option.getD_some]
    have hgetI : indices.getD (bwsNext p o seed ebs.length shuffle i) 0 = indices[k] := by
      simp only [hkdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hki,
        Option.getD_some]
    rw [hacc, hgetI]
    simp only [tot_get hk, tot_bind_ok, tot_mul heb1, bytes_to_uint64_take2, tot_mul hthr,
      tot_add hi]
    by_cases hc : ebs[k] * (2 ^ 16 - 1) ≥ p.MAX_EFFECTIVE_BALANCE_ELECTRA *
        leNat (List.take 2 (List.drop (i % 16 * 2) (bwsBytes o seed i).toList))
    · simp only [hc, if_true, decide_true, tot_get hki, tot_bind_ok]; rfl
    · simp only [hc, if_false, decide_false, Bool.false_eq_true]; rfl
  cases shuffle with
  | true =>
    have hcs := compute_shuffled_index_eq p o seed (i % ebs.length) ebs.length hnext hn40 hR
    simp only [if_true, hcs, tot_bind_ok]
    exact key _ hcsi rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact key _ hcsi rfl

/-- The number of accepting passes among the first `m`. -/
def bwsCount (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei) (shuffle : Bool)
    (m : Nat) : Nat :=
  ((List.range m).filter (bwsAccept p o seed ebs shuffle)).length

theorem bwsCount_succ (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (i : Nat) :
    bwsCount p o seed ebs shuffle (i + 1) =
      bwsCount p o seed ebs shuffle i + if bwsAccept p o seed ebs shuffle i then 1 else 0 := by
  unfold bwsCount
  rw [List.range_succ, List.filter_append, List.length_append]
  split <;> simp [*]

theorem bwsCount_mono (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) {i j : Nat} (h : i ≤ j) :
    bwsCount p o seed ebs shuffle i ≤ bwsCount p o seed ebs shuffle j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [bwsCount_succ]; exact Nat.le_trans (ih (Nat.lt_succ_iff.mp h)) (Nat.le_add_right _ _)
    · rw [h]

theorem bws_loop_total (p : Preset) (o : Oracle) (indices : List ValidatorIndex) (seed : Bytes32)
    (size : Nat) (shuffle : Bool) (ebs : List Gwei)
    (hlen : ebs.length = indices.length) (htot : 0 < ebs.length)
    (hn40 : ebs.length ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (heb : ∀ e ∈ ebs, e ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hmax : p.MAX_EFFECTIVE_BALANCE_ELECTRA ≤ 2 ^ 41)
    (m : Nat) (hm : m < 2 ^ 64) (hfin : size ≤ bwsCount p o seed ebs shuffle m) :
    ∀ k i selected rb, i + k = m →
      selected.length = bwsCount p o seed ebs shuffle i →
      (i % 16 ≠ 0 → rb = bwsBytes o seed i) →
      (∀ x ∈ selected, x ∈ indices) →
      ∃ r, compute_balance_weighted_selection_loop p o indices seed size shuffle ebs.length ebs
          (2 ^ 64 - i) selected i rb = .ok r ∧ size ≤ r.length ∧ ∀ x ∈ r, x ∈ indices := by
  intro k
  induction k with
  | zero =>
    intro i selected rb hik hsel _ hsub
    have hi : i = m := by omega
    subst hi
    have hfuel : 2 ^ 64 - i = (2 ^ 64 - i - 1) + 1 := by omega
    rw [hfuel, compute_balance_weighted_selection_loop, if_neg (by omega)]
    exact ⟨selected, rfl, by omega, hsub⟩
  | succ k ih =>
    intro i selected rb hik hsel hrb hsub
    have hfuel : 2 ^ 64 - i = (2 ^ 64 - (i + 1)) + 1 := by omega
    by_cases hs : selected.length < size
    · rw [hfuel, bws_step p o indices seed size shuffle ebs _ selected i rb hs hlen htot hn40 hR heb
        hmax (by omega) hrb]
      apply ih (i + 1) _ _ (by omega)
      · rw [bwsCount_succ]; split <;> simp_all
      · intro h16
        simp only [bwsBytes]
        congr 3
        omega
      · intro x hx
        split at hx
        · rcases List.mem_append.mp hx with h | h
          · exact hsub x h
          · rw [List.mem_singleton.mp h]
            have hk : bwsNext p o seed ebs.length shuffle i < indices.length := by
              rw [← hlen]
              unfold bwsNext; split
              · exact csiFold_lt _ _ _ _ _ htot (Nat.mod_lt _ htot)
              · exact Nat.mod_lt _ htot
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
            exact List.getElem_mem hk
        · exact hsub x hx
    · rw [hfuel, compute_balance_weighted_selection_loop, if_neg hs]
      exact ⟨selected, rfl, by omega, hsub⟩

theorem tot_mapM {α β : Type} (f : α → SpecM β) (g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = .ok (g x)) : l.mapM f = .ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), tot_bind_ok,
      ih (fun y hy => h y (by simp [hy])), tot_bind_ok]
    rfl

/-- The effective balances of `indices`, as `compute_balance_weighted_selection` reads them. -/
def ebsOf (s : BeaconState) (indices : List ValidatorIndex) : List Gwei :=
  indices.map fun j => (s.validators[j]?.map (·.effective_balance)).getD 0

/-- The selection loop accepts `size` candidates within `2^64` passes, so the `Uint64` counter
`i` does not overflow. This is a fact about the hash values, not about the state. -/
def SelFin (p : Preset) (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffle : Bool) : Prop :=
  ∃ m, m < 2 ^ 64 ∧ size ≤ bwsCount p o seed (ebsOf s indices) shuffle m

theorem compute_balance_weighted_selection_total (p : Preset) (o : Oracle) (s : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (size : Nat) (shuffle : Bool)
    (hne : indices ≠ []) (hin : ∀ j ∈ indices, j < s.validators.length)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn40 : indices.length ≤ 2 ^ 40) (hR : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (hmax : p.MAX_EFFECTIVE_BALANCE_ELECTRA ≤ 2 ^ 41)
    (hfin : SelFin p o s indices seed size shuffle) :
    ∃ r, compute_balance_weighted_selection p o s indices seed size shuffle = .ok r ∧
      size ≤ r.length ∧ ∀ x ∈ r, x ∈ indices := by
  obtain ⟨m, hm, hc⟩ := hfin
  have hpos : 0 < indices.length := List.length_pos_iff.mpr hne
  have hmap : indices.mapM (fun index => do
      pure (← listGet s.validators index).effective_balance : ValidatorIndex → SpecM Gwei) =
      .ok (ebsOf s indices) := by
    apply tot_mapM
    intro j hj
    have hjl := hin j hj
    simp only [tot_get hjl, tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  have hlen : (ebsOf s indices).length = indices.length := by simp [ebsOf]
  have hebs : ∀ e ∈ ebsOf s indices, e ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA := by
    intro e he
    simp only [ebsOf, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    have hjl := hin j hj
    simp only [List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
    exact heb _ (List.getElem_mem hjl)
  unfold compute_balance_weighted_selection
  rw [if_neg (by omega)]
  simp only [pure_bind]
  rw [hmap, tot_bind_ok, ← hlen]
  have := bws_loop_total p o indices seed size shuffle (ebsOf s indices) hlen (by omega)
    (by omega) hR hebs hmax m hm hc m 0 [] Bytes32.zero (by omega) (by simp [bwsCount])
    (by simp) (by simp)
  simpa [UINT64_SIZE] using this

/-! ## Seeds and committees -/

theorem get_seed_total [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) (epoch : Nat)
    (dt : DomainType) (he : epoch + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR) :
    ∃ r, get_seed P o s epoch dt = .ok r := by
  unfold get_seed get_randao_mix
  have hH2 := P_hist_ge2 (h := inferInstance)
  have h2 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  have hlt : (epoch + P.EPOCHS_PER_HISTORICAL_VECTOR - 1 - 1) % P.EPOCHS_PER_HISTORICAL_VECTOR <
      s.randao_mixes.length := by
    rw [hr]; exact Nat.mod_lt _ (Nat.pos_iff_ne_zero.mpr P_hist_ne)
  simp only [h2, tot_add he, tot_bind_ok,
    tot_sub (show @LE.le Nat _ 1 (epoch + P.EPOCHS_PER_HISTORICAL_VECTOR) by omega),
    tot_sub (show @LE.le Nat _ 1 (epoch + P.EPOCHS_PER_HISTORICAL_VECTOR - 1) by omega),
    tot_mod P_hist_ne]
  rw [tot_get hlt]
  exact ⟨_, rfl⟩

theorem get_committee_count_per_slot_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]
    (s : BeaconState) (epoch : Epoch) :
    get_committee_count_per_slot P s epoch =
      .ok (max 1 (min P.MAX_COMMITTEES_PER_SLOT
        ((get_active_validator_indices s epoch).length / P.SLOTS_PER_EPOCH /
          P.TARGET_COMMITTEE_SIZE))) := by
  unfold get_committee_count_per_slot
  simp only [tot_div P_slots_ne, tot_bind_ok, tot_div P_target_ne]
  rfl

theorem compute_committee_total [PresetCfg] [PresetCfg.Bounds] (o : Oracle) (indices : List ValidatorIndex) (seed : Bytes32)
    (index count : Nat) (hic : index < count) (hc : count ≤ 2048)
    (hn40 : indices.length ≤ 2 ^ 40) :
    ∃ r, compute_committee P o indices seed index count = .ok r ∧
      r.length = indices.length * (index + 1) / count - indices.length * index / count ∧
      ∀ x ∈ r, x ∈ indices := by
  have hR : (P).SHUFFLE_ROUND_COUNT ≤ 256 := P_shuffle_le
  have hc0 : count ≠ 0 := by omega
  have hm1 : indices.length * index < 2 ^ 64 :=
    calc indices.length * index ≤ 2 ^ 40 * 2048 := Nat.mul_le_mul hn40 (by omega)
      _ < 2 ^ 64 := by decide
  have hm2 : indices.length * (index + 1) < 2 ^ 64 :=
    calc indices.length * (index + 1) ≤ 2 ^ 40 * 2048 := Nat.mul_le_mul hn40 (by omega)
      _ < 2 ^ 64 := by decide
  have hend : indices.length * (index + 1) / count ≤ indices.length :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm count]; exact Nat.mul_le_mul_left _ hic)
  unfold compute_committee
  simp only [tot_mul hm1, tot_bind_ok, tot_div hc0, tot_add (show index + 1 < 2 ^ 64 by omega),
    tot_mul hm2]
  have hrng : ∀ i ∈ List.range' (indices.length * index / count)
      (indices.length * (index + 1) / count - indices.length * index / count), i < indices.length := by
    intro i hi
    rw [List.mem_range'] at hi
    omega
  rw [tot_mapM _ (fun i => indices[csiFold o seed.toList indices.length
      (P).SHUFFLE_ROUND_COUNT i]!) _ (by
    intro i hi
    have hil := hrng i hi
    have hcl := csiFold_lt o seed.toList indices.length (P).SHUFFLE_ROUND_COUNT i
      (by omega) hil
    rw [compute_shuffled_index_eq _ _ _ _ _ hil hn40 hR, tot_bind_ok, tot_get hcl,
      getElem!_pos indices _ hcl])]
  refine ⟨_, rfl, by simp, ?_⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hil := hrng i hi
  have hcl := csiFold_lt o seed.toList indices.length (P).SHUFFLE_ROUND_COUNT i
    (by omega) hil
  rw [getElem!_pos indices _ hcl]
  exact List.getElem_mem hcl

theorem forIn_append_total {α : Type} (l : List Nat) (g : Nat → SpecM (List α)) (L : Nat → Nat)
    (Q : α → Prop) (hg : ∀ i ∈ l, ∃ c, g i = .ok c ∧ c.length = L i ∧ ∀ x ∈ c, Q x)
    (acc : List α) :
    ∃ r, forIn l acc (fun i r => do
        let c ← g i
        pure PUnit.unit
        pure (ForInStep.yield (r ++ c))) = .ok r ∧
      r.length = acc.length + (l.map L).sum ∧ ∀ x ∈ r, x ∈ acc ∨ Q x := by
  induction l generalizing acc with
  | nil => exact ⟨acc, rfl, by simp, fun x hx => Or.inl hx⟩
  | cons i is ih =>
    obtain ⟨c, hc, hcl, hcq⟩ := hg i (by simp)
    rw [List.forIn_cons, hc]
    obtain ⟨r, hr, hrl, hrq⟩ := ih (fun j hj => hg j (by simp [hj])) (acc ++ c)
    refine ⟨r, hr, by simp [hrl, hcl]; omega, ?_⟩
    intro x hx
    rcases hrq x hx with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (hcq x h)
    · exact Or.inr h

theorem sum_range_diff (F : Nat → Nat) (hF : ∀ i, F i ≤ F (i + 1)) (C : Nat) :
    ((List.range C).map (fun i => F (i + 1) - F i)).sum = F C - F 0 := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have h1 : F 0 ≤ F C := by
      clear ih
      induction C with
      | zero => exact Nat.le_refl _
      | succ C ih2 => exact Nat.le_trans ih2 (hF C)
    have h2 := hF C
    simp
    omega

/-- The committee count per slot. -/
def cpsOf [PresetCfg] (s : BeaconState) (epoch : Nat) : Nat :=
  max 1 (min P.MAX_COMMITTEES_PER_SLOT
    ((get_active_validator_indices s epoch).length / P.SLOTS_PER_EPOCH / P.TARGET_COMMITTEE_SIZE))

theorem cpsOf_pos [PresetCfg] (s : BeaconState) (epoch : Nat) : 0 < cpsOf s epoch := by
  unfold cpsOf; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)

theorem cpsOf_le [PresetCfg] [PresetCfg.Bounds] (s : BeaconState) (epoch : Nat) :
    cpsOf s epoch ≤ 64 := by
  have h := P_max_committees_le (b := inferInstance)
  unfold cpsOf
  exact Nat.max_le.mpr ⟨by decide, Nat.le_trans (Nat.min_le_left _ _) h⟩

theorem get_beacon_committee_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState) (slot i : Nat)
    (hi : i < cpsOf s (slot / P.SLOTS_PER_EPOCH))
    (hslot : slot / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hn40 : (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length ≤ 2 ^ 40) :
    ∃ r, get_beacon_committee P o s slot i = .ok r ∧
      r.length = (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length *
          (slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) + i + 1) /
            (cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH) -
        (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length *
          (slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) + i) /
            (cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH) ∧
      ∀ x ∈ r, x ∈ get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH) := by
  have hC := cpsOf_le s (slot / P.SLOTS_PER_EPOCH)
  have hS : P.SLOTS_PER_EPOCH ≤ 32 := P_slots_le
  have hk : slot % P.SLOTS_PER_EPOCH < P.SLOTS_PER_EPOCH := Nat.mod_lt _ P_slots_pos
  obtain ⟨seed, hseed⟩ := get_seed_total o s (slot / P.SLOTS_PER_EPOCH) DOMAIN_BEACON_ATTESTER
    hslot hr
  have hle : slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) +
      cpsOf s (slot / P.SLOTS_PER_EPOCH) ≤ cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH := by
    rw [← Nat.succ_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ hk
  have hidx : slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) + i <
      cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH := by omega
  have hcount : cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH ≤ 2048 :=
    Nat.mul_le_mul hC hS
  obtain ⟨r, hr1, hr2, hr3⟩ := compute_committee_total o
    (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)) seed _ _ hidx hcount hn40
  refine ⟨r, ?_, hr2, hr3⟩
  unfold get_beacon_committee compute_epoch_at_slot
  have hcps : get_committee_count_per_slot P s (slot / P.SLOTS_PER_EPOCH) =
      .ok (cpsOf s (slot / P.SLOTS_PER_EPOCH)) :=
    get_committee_count_per_slot_total s _
  simp only [tot_div P_slots_ne, tot_bind_ok, tot_mod P_slots_ne]
  rw [hcps, tot_bind_ok, hseed, tot_bind_ok]
  rw [tot_mul (show slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) < 2 ^ 64 by
      omega), tot_bind_ok,
    tot_add (show slot % P.SLOTS_PER_EPOCH * cpsOf s (slot / P.SLOTS_PER_EPOCH) + i < 2 ^ 64 by
      omega), tot_bind_ok,
    tot_mul (show cpsOf s (slot / P.SLOTS_PER_EPOCH) * P.SLOTS_PER_EPOCH < 2 ^ 64 by omega),
    tot_bind_ok]
  exact hr1

theorem mul_div_cps (n k C S : Nat) (hC : 0 < C) : n * (k * C) / (C * S) = n * k / S := by
  rw [← Nat.mul_assoc, Nat.mul_comm C S]
  exact Nat.mul_div_mul_right _ _ hC

theorem ptcIndices_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState) (slot : Nat)
    (hslot : slot / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hn40 : (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length ≤ 2 ^ 40) :
    ∃ l, ptcIndices P o s (slot / P.SLOTS_PER_EPOCH) slot = .ok l ∧
      l.length = (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length *
          (slot % P.SLOTS_PER_EPOCH + 1) / P.SLOTS_PER_EPOCH -
        (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length *
          (slot % P.SLOTS_PER_EPOCH) / P.SLOTS_PER_EPOCH ∧
      ∀ x ∈ l, x ∈ get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH) := by
  have hC := cpsOf_pos s (slot / P.SLOTS_PER_EPOCH)
  generalize hn : (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length = n at *
  generalize hCdef : cpsOf s (slot / P.SLOTS_PER_EPOCH) = C at hC
  unfold ptcIndices
  rw [get_committee_count_per_slot_total, tot_bind_ok]
  have hcps : max 1 (min P.MAX_COMMITTEES_PER_SLOT
      ((get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length / P.SLOTS_PER_EPOCH /
        P.TARGET_COMMITTEE_SIZE)) = C := by
    rw [← hCdef]; rfl
  rw [hcps]
  obtain ⟨r, hr1, hr2, hr3⟩ := forIn_append_total (List.range C)
    (fun i => get_beacon_committee P o s slot i)
    (fun i => n * (slot % P.SLOTS_PER_EPOCH * C + i + 1) / (C * P.SLOTS_PER_EPOCH) -
      n * (slot % P.SLOTS_PER_EPOCH * C + i) / (C * P.SLOTS_PER_EPOCH))
    (fun x => x ∈ get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH))
    (by
      intro i hi
      rw [List.mem_range] at hi
      obtain ⟨c, hc1, hc2, hc3⟩ := get_beacon_committee_total o s slot i (hCdef ▸ hi) hslot hr
        (hn ▸ hn40)
      refine ⟨c, hc1, ?_, hc3⟩
      rw [hc2, hn, hCdef])
    []
  refine ⟨r, by rw [hr1]; rfl, ?_, fun x hx => (hr3 x hx).resolve_left (by simp)⟩
  rw [hr2, List.length_nil, Nat.zero_add]
  have := sum_range_diff (fun j => n * (slot % P.SLOTS_PER_EPOCH * C + j) / (C * P.SLOTS_PER_EPOCH))
    (fun j => Nat.div_le_div_right (Nat.mul_le_mul_left n (by omega))) C
  simp only [Nat.add_assoc] at this ⊢
  rw [this, Nat.add_zero, mul_div_cps n _ C _ hC]
  have hk1 : slot % P.SLOTS_PER_EPOCH * C + C = (slot % P.SLOTS_PER_EPOCH + 1) * C := by
    rw [Nat.succ_mul]
  rw [hk1, mul_div_cps n _ C _ hC]

theorem ptc_len_pos (n k S : Nat) (hS : 0 < S) (hn : S ≤ n) :
    0 < n * (k + 1) / S - n * k / S := by
  rw [Nat.mul_succ]
  have h1 : (n * k + S) / S ≤ (n * k + n) / S := Nat.div_le_div_right (by omega)
  rw [Nat.add_div_right _ hS] at h1
  exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1)

theorem ptc_len_le (n k S : Nat) (hS : 0 < S) (hk : k < S) : n * (k + 1) / S - n * k / S ≤ n := by
  have h : n * (k + 1) / S ≤ n :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm S n]; exact Nat.mul_le_mul_left _ hk)
  exact Nat.le_trans (Nat.sub_le _ _) h

theorem active_lt (s : BeaconState) (e x : Nat) (h : x ∈ get_active_validator_indices s e) :
    x < s.validators.length :=
  active_index_lt _ _ _ h

theorem active_len_le (s : BeaconState) (e : Nat) :
    (get_active_validator_indices s e).length ≤ s.validators.length := by
  unfold get_active_validator_indices
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem compute_ptc_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState) (slot : Nat)
    (hslot : slot / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hn40 : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (h32 : P.SLOTS_PER_EPOCH ≤ (get_active_validator_indices s (slot / P.SLOTS_PER_EPOCH)).length)
    (hfin : ∀ l, ptcIndices P o s (slot / P.SLOTS_PER_EPOCH) slot = .ok l →
      ∀ seed, SelFin P o s l seed P.PTC_SIZE false) :
    ∃ r, compute_ptc P o s slot = .ok r := by
  have hn := (active_len_le s (slot / P.SLOTS_PER_EPOCH)).trans hn40
  obtain ⟨seed, hseed⟩ := get_seed_total o s (slot / P.SLOTS_PER_EPOCH) DOMAIN_PTC_ATTESTER
    hslot hr
  obtain ⟨l, hl1, hl2, hl3⟩ := ptcIndices_total o s slot hslot hr hn
  have hk : slot % P.SLOTS_PER_EPOCH < P.SLOTS_PER_EPOCH := Nat.mod_lt _ P_slots_pos
  have hne : l ≠ [] := by
    intro h; rw [h] at hl2
    have := ptc_len_pos _ (slot % P.SLOTS_PER_EPOCH) _ P_slots_pos h32
    simp at hl2; omega
  have hll : l.length ≤ 2 ^ 40 := by
    rw [hl2]; exact (ptc_len_le _ _ _ P_slots_pos hk).trans hn
  obtain ⟨r, hr1, -, -⟩ := compute_balance_weighted_selection_total P o s l
    (o.hash (seed.toList ++ uint_to_bytes 8 slot)) P.PTC_SIZE false hne
    (fun j hj => active_lt s _ j (hl3 j hj)) heb hll P_shuffle_le (by rw [P_maxeb]; decide)
    (hfin l hl1 _)
  refine ⟨r, ?_⟩
  rw [compute_ptc_eq]
  unfold compute_epoch_at_slot
  rw [tot_div P_slots_ne, tot_bind_ok]
  rw [hseed, tot_bind_ok, hl1, tot_bind_ok]
  exact hr1

theorem tot_filterAuxM {α : Type} (f : α → SpecM Bool) (g : α → Bool) (l acc : List α)
    (h : ∀ a ∈ l, f a = .ok (g a)) :
    List.filterAuxM f l acc = .ok ((l.filter g).reverse ++ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterAuxM]
    rw [h x (by simp), tot_bind_ok, ih _ (fun a ha => h a (by simp [ha]))]
    cases hg : g x <;> simp [hg]

theorem tot_filterM {α : Type} (f : α → SpecM Bool) (g : α → Bool) (l : List α)
    (h : ∀ a ∈ l, f a = .ok (g a)) : l.filterM f = .ok (l.filter g) := by
  simp only [List.filterM]
  rw [tot_filterAuxM f g l [] h, tot_bind_ok]
  simp; rfl

/-- The proposer candidates of `epoch`: active and not slashed. -/
def unslashedActive (s : BeaconState) (e : Nat) : List ValidatorIndex :=
  (get_active_validator_indices s e).filter fun i =>
    !((s.validators[i]?.map (·.slashed)).getD true)

/-! ## The three steps -/

/-- State facts that the three committee steps read. Each one holds on reachable states: the
slot bound and the RANDAO length are in `CommFrame`, the registry limit is
`VALIDATOR_REGISTRY_LIMIT`, `effective_balance ≤ MAX_EFFECTIVE_BALANCE_ELECTRA` is `EBOk`, the
two vector lengths are SSZ lengths, and a deposit adds a validator only after its signature
checks, which validates the key. -/
structure CommFacts [PresetCfg] (o : Oracle) (s : BeaconState) : Prop where
  slot : s.slot + 8192 < 2 ^ 64
  randao : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR
  regLen : s.validators.length ≤ 2 ^ 40
  ebMax : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000
  lookahead : s.proposer_lookahead.length = 2 * P.SLOTS_PER_EPOCH
  ptcLen : s.ptc_window.length = 3 * P.SLOTS_PER_EPOCH
  keys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true

/-- Preconditions of the pyspec itself. Without them the pyspec raises.

- `syncActive`: some validator is active at the next epoch (the sync committee selection asserts
  `total > 0`).
- `proposers` (F4): some active validator at `current + 2` is not slashed (the proposer
  selection asserts `total > 0`).
- `ptc32` (F12): at least `SLOTS_PER_EPOCH` validators are active at `current + 2`. With fewer,
  the first slot of that epoch has no committee members, and `compute_ptc` asserts `total > 0`.
- `selSync`, `selProp`, `selPtc`: each selection accepts its candidates within `2^64`
  passes, so the `Uint64` counter does not overflow. This depends on the hash values. With
  effective balances of at least `16 ETH` each pass accepts with probability at least `1/128`. -/
structure CommitteeStepPreconds [PresetCfg] (o : Oracle) (s : BeaconState) : Prop where
  syncActive : get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1) ≠ []
  proposers : unslashedActive s (s.slot / P.SLOTS_PER_EPOCH + 2) ≠ []
  ptc32 : P.SLOTS_PER_EPOCH ≤ (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 2)).length
  selSync : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1))
    seed P.SYNC_COMMITTEE_SIZE true
  selProp : ∀ seed, SelFin P o s (unslashedActive s (s.slot / P.SLOTS_PER_EPOCH + 2)) seed 1 true
  selPtc : ∀ slot, slot / P.SLOTS_PER_EPOCH = s.slot / P.SLOTS_PER_EPOCH + 2 → ∀ l,
    ptcIndices P o s (slot / P.SLOTS_PER_EPOCH) slot = .ok l →
      ∀ seed, SelFin P o s l seed P.PTC_SIZE false

theorem get_next_sync_committee_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hkeys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true)
    (hsa : get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1) ≠ [])
    (hsel : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1))
      seed P.SYNC_COMMITTEE_SIZE true) :
    ∃ c, get_next_sync_committee P o s = .ok c := by
  have he : s.slot / P.SLOTS_PER_EPOCH + 1 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 :=
    P_ep_bound hslot 1 (by decide)
  obtain ⟨seed, hseed⟩ := get_seed_total o s (s.slot / P.SLOTS_PER_EPOCH + 1)
    DOMAIN_SYNC_COMMITTEE he hr
  have hn := (active_len_le s (s.slot / P.SLOTS_PER_EPOCH + 1)).trans hreg
  have hsz := P_sync_pos (h := inferInstance)
  obtain ⟨r, hr1, hr2, hr3⟩ := compute_balance_weighted_selection_total P o s
    (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1)) seed P.SYNC_COMMITTEE_SIZE
    true hsa (fun j hj => active_lt s _ j hj) heb hn P_shuffle_le (by rw [P_maxeb]; decide)
    (hsel seed)
  have hrl : ∀ j ∈ r, j < s.validators.length := fun j hj => active_lt s _ j (hr3 j hj)
  have hpk : r.mapM (fun index => do pure (← listGet s.validators index).pubkey :
      ValidatorIndex → SpecM BLSPubkey) =
      .ok (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero) := by
    apply tot_mapM
    intro j hj
    have hjl := hrl j hj
    simp only [tot_get hjl, tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  have hagg : eth_aggregate_pubkeys o
      (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero) =
      .ok (o.bls_AggregatePKs
        (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero)) := by
    unfold eth_aggregate_pubkeys
    rw [if_neg (by rw [List.length_map]; exact fun h => h (by omega))]
    rw [if_neg (by
      simp only [List.all_eq_true, List.mem_map, Bool.not_eq_true, not_forall, not_exists]
      intro x ⟨j, hj, hx⟩
      subst hx
      have hjl := hrl j hj
      simp only [List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
      rw [hkeys _ (List.getElem_mem hjl)]
      simp)]
    rfl
  unfold get_next_sync_committee get_next_sync_committee_indices
  rw [tot_current_epoch, tot_bind_ok, tot_add (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) he),
    tot_bind_ok, hseed, tot_bind_ok]
  simp only [hr1, tot_bind_ok, hpk, hagg]
  exact ⟨_, rfl⟩

theorem tot_mapM_ex {α β : Type} (f : α → SpecM β) (l : List α)
    (h : ∀ x ∈ l, ∃ y, f x = .ok y) : ∃ ys, l.mapM f = .ok ys := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
    rw [List.mapM_cons, hy, tot_bind_ok, hys, tot_bind_ok]
    exact ⟨_, rfl⟩

theorem get_beacon_proposer_indices_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]
    (o : Oracle) (s : BeaconState) (e : Nat)
    (he : e + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hstart : e * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hne : unslashedActive s e ≠ [])
    (hsel : ∀ seed, SelFin P o s (unslashedActive s e) seed 1 true) :
    ∃ r, get_beacon_proposer_indices P o s e = .ok r := by
  have hfil : (get_active_validator_indices s e).filterM (fun index => do
      pure !(← listGet s.validators index).slashed : ValidatorIndex → SpecM Bool) =
      .ok (unslashedActive s e) := by
    apply tot_filterM
    intro j hj
    have hjl := active_lt s e j hj
    simp only [tot_get hjl, tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  obtain ⟨seed, hseed⟩ := get_seed_total o s e DOMAIN_BEACON_PROPOSER he hr
  have hul : ∀ j ∈ unslashedActive s e, j < s.validators.length := fun j hj =>
    active_lt s e j (List.mem_of_mem_filter hj)
  have hulen : (unslashedActive s e).length ≤ 2 ^ 40 :=
    ((List.length_filter_le _ _).trans (active_len_le s e)).trans hreg
  unfold get_beacon_proposer_indices compute_proposer_indices compute_start_slot_at_epoch
  rw [hfil, tot_bind_ok, hseed, tot_bind_ok]
  rw [tot_mul (show e * P.SLOTS_PER_EPOCH < 2 ^ 64 by omega), tot_bind_ok]
  obtain ⟨seeds, hseeds⟩ := tot_mapM_ex (fun i => do
      pure (o.hash (seed.toList ++ uint_to_bytes 8 (← uint64Add (e * P.SLOTS_PER_EPOCH) i))) :
        Nat → SpecM Bytes32)
    (List.range P.SLOTS_PER_EPOCH) (by
      intro i hi
      rw [List.mem_range] at hi
      rw [tot_add (show e * P.SLOTS_PER_EPOCH + i < 2 ^ 64 by omega), tot_bind_ok]
      exact ⟨_, rfl⟩)
  rw [hseeds, tot_bind_ok]
  apply tot_mapM_ex
  intro sd _
  obtain ⟨r, hr1, hr2, -⟩ := compute_balance_weighted_selection_total P o s
    (unslashedActive s e) sd 1 true hne hul heb hulen P_shuffle_le (by rw [P_maxeb]; decide)
    (hsel sd)
  rw [hr1, tot_bind_ok, tot_get (show 0 < r.length by omega)]
  exact ⟨_, rfl⟩

theorem process_proposer_lookahead_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]
    (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hlen : s.proposer_lookahead.length = 2 * P.SLOTS_PER_EPOCH)
    (hne : unslashedActive s (s.slot / P.SLOTS_PER_EPOCH + 2) ≠ [])
    (hsel : ∀ seed, SelFin P o s (unslashedActive s (s.slot / P.SLOTS_PER_EPOCH + 2)) seed 1 true) :
    OkWith (process_proposer_lookahead P o s) (fun s' =>
      s'.slot = s.slot ∧ s'.validators = s.validators ∧ s'.randao_mixes = s.randao_mixes ∧
        s'.ptc_window = s.ptc_window) := by
  have he : s.slot / P.SLOTS_PER_EPOCH + 2 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 :=
    P_ep_bound hslot 2 (by decide)
  obtain ⟨r, hr1⟩ := get_beacon_proposer_indices_total o
    { s with proposer_lookahead := s.proposer_lookahead.drop P.SLOTS_PER_EPOCH ++
      s.proposer_lookahead.drop (2 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) }
    (s.slot / P.SLOTS_PER_EPOCH + 2) he (P_ep_start_bound hslot 2 (by decide)) hr hreg heb hne hsel
  unfold process_proposer_lookahead
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.proposer_lookahead.length by omega), tot_bind_ok]
  rw [hlen]
  dsimp only
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
    rw [Nat.add_assoc], hr1, tot_bind_ok]
  exact OkWith.pure ⟨rfl, rfl, rfl, rfl⟩

theorem ptcIndices_congr [PresetCfg] (o : Oracle) {s1 s2 : BeaconState} (hv : s1.validators = s2.validators)
    (hr : s1.randao_mixes = s2.randao_mixes) :
    ptcIndices P o s1 = ptcIndices P o s2 := by
  funext e slot
  simp only [ptcIndices, get_committee_count_per_slot_congr hv,
    get_beacon_committee_congr (slot := slot) hv (fun _ _ => by
      rw [get_seed_congr (p := P) (o := o) hr])]

theorem slot_div_window {a j S : Nat} (hS : 0 < S) (hj : j < S) : (a * S + j) / S = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem process_ptc_window_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hlen : s.ptc_window.length = 3 * P.SLOTS_PER_EPOCH)
    (h32 : P.SLOTS_PER_EPOCH ≤
      (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 2)).length)
    (hfin : ∀ slot, slot / P.SLOTS_PER_EPOCH = s.slot / P.SLOTS_PER_EPOCH + 2 → ∀ l,
      ptcIndices P o s (slot / P.SLOTS_PER_EPOCH) slot = .ok l →
        ∀ seed, SelFin P o s l seed P.PTC_SIZE false) :
    OkWith (process_ptc_window P o s) (fun _ => True) := by
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  have hst := P_ep_start_bound hslot 2 (by decide)
  unfold process_ptc_window compute_start_slot_at_epoch
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.ptc_window.length by omega), tot_bind_ok, hlen]
  dsimp only
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
      rw [Nat.add_assoc],
    tot_mul (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hst), tot_bind_ok,
    tot_add hst, tot_bind_ok, Nat.add_sub_cancel_left]
  obtain ⟨ptcs, hptcs⟩ := tot_mapM_ex (fun slot =>
      compute_ptc P o
        { s with ptc_window := List.drop P.SLOTS_PER_EPOCH s.ptc_window ++
          List.drop (3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) s.ptc_window } slot)
    (List.range' ((s.slot / P.SLOTS_PER_EPOCH + 2) * P.SLOTS_PER_EPOCH) P.SLOTS_PER_EPOCH) (by
      intro slot hslot'
      rw [List.mem_range'] at hslot'
      obtain ⟨j, hj, rfl⟩ := hslot'
      rw [Nat.one_mul]
      have hdiv := slot_div_window (a := s.slot / P.SLOTS_PER_EPOCH + 2) P_slots_pos hj
      apply compute_ptc_total o _ _ (by rw [hdiv]; exact P_ep_bound hslot 2 (by decide)) hr hreg
        heb (by rw [hdiv]; exact h32)
      intro l hl seed
      rw [ptcIndices_congr o (s2 := s) rfl rfl] at hl
      exact hfin _ hdiv l hl seed)
  rw [hptcs, tot_bind_ok]
  simp only [List.length_append, List.length_drop, hlen]
  rw [tot_sub (show P.SLOTS_PER_EPOCH ≤ 3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH +
    (3 * P.SLOTS_PER_EPOCH - (3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH)) by omega), tot_bind_ok]
  exact OkWith.pure trivial

theorem unslashedActive_congr {s1 s2 : BeaconState} (hv : s1.validators = s2.validators) :
    unslashedActive s1 = unslashedActive s2 := by
  funext e
  simp only [unslashedActive, get_active_validator_indices_congr hv, hv]

theorem ebsOf_congr {s1 s2 : BeaconState} (hv : s1.validators = s2.validators) :
    ebsOf s1 = ebsOf s2 := by
  funext l
  simp only [ebsOf, hv]

theorem CommitteeStepPreconds.congr [PresetCfg] {o : Oracle} {s1 s2 : BeaconState} (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes)
    (h : CommitteeStepPreconds o s2) : CommitteeStepPreconds o s1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [get_active_validator_indices_congr hv, hs]; exact h1
  · rw [unslashedActive_congr hv, hs]; exact h2
  · rw [get_active_validator_indices_congr hv, hs]; exact h3
  · intro seed
    simp only [SelFin, ebsOf_congr hv, get_active_validator_indices_congr hv, hs]
    exact h4 seed
  · intro seed
    simp only [SelFin, ebsOf_congr hv, unslashedActive_congr hv, hs]
    exact h5 seed
  · intro slot hslot l hl seed
    rw [hs] at hslot
    rw [ptcIndices_congr o hv hr] at hl
    simp only [SelFin, ebsOf_congr hv]
    exact h6 slot hslot l hl seed

theorem CommFacts.congr [PresetCfg] {o : Oracle} {s1 s2 : BeaconState} (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes)
    (hl : s1.proposer_lookahead = s2.proposer_lookahead) (hw : s1.ptc_window = s2.ptc_window)
    (h : CommFacts o s2) : CommFacts o s1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hs ▸ h1, hr ▸ h2, hv ▸ h3, hv ▸ h4, hl ▸ h5, hw ▸ h6, hv ▸ h7⟩

theorem process_sync_committee_updates_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]
    (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hkeys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true)
    (hsa : get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1) ≠ [])
    (hsel : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1))
      seed P.SYNC_COMMITTEE_SIZE true) :
    OkWith (process_sync_committee_updates P o s) (fun s' =>
      s'.slot = s.slot ∧ s'.validators = s.validators ∧ s'.randao_mixes = s.randao_mixes ∧
        s'.proposer_lookahead = s.proposer_lookahead ∧ s'.ptc_window = s.ptc_window) := by
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  obtain ⟨c, hc⟩ := get_next_sync_committee_total o
    { s with current_sync_committee := s.next_sync_committee } hslot hr hreg heb hkeys hsa hsel
  unfold process_sync_committee_updates
  rw [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_bind_ok,
    tot_mod P_sync_period_ne, tot_bind_ok]
  split
  · dsimp only
    rw [hc, tot_bind_ok]
    exact OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The sync committee, proposer lookahead and PTC window steps succeed from the state facts and
the pyspec preconditions. -/
theorem committee_steps_total [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle) (s : BeaconState) (hf : CommFacts o s)
    (hp : CommitteeStepPreconds o s) :
    OkWith (do
      let s ← process_sync_committee_updates P o s
      let s ← process_proposer_lookahead P o s
      process_ptc_window P o s) (fun _ => True) := by
  obtain ⟨s1, h1, e1s, e1v, e1r, e1l, e1w⟩ := process_sync_committee_updates_total o s hf.slot
    hf.randao hf.regLen hf.ebMax hf.keys hp.syncActive hp.selSync
  have hf1 := CommFacts.congr e1s e1v e1r e1l e1w hf
  have hp1 := CommitteeStepPreconds.congr e1s e1v e1r hp
  rw [h1, tot_bind_ok]
  obtain ⟨s2, h2, e2s, e2v, e2r, e2w⟩ := process_proposer_lookahead_total o s1 hf1.slot hf1.randao
    hf1.regLen hf1.ebMax hf1.lookahead hp1.proposers hp1.selProp
  rw [h2, tot_bind_ok]
  have hp2 := CommitteeStepPreconds.congr e2s e2v e2r hp1
  exact process_ptc_window_total o s2 (e2s ▸ hf1.slot) (e2r ▸ hf1.randao) (e2v ▸ hf1.regLen)
    (e2v ▸ hf1.ebMax) (e2w ▸ hf1.ptcLen) hp2.ptc32 hp2.selPtc

/-! ## Fewer than `SLOTS_PER_EPOCH` active validators halt the PTC window -/

theorem mapM_range'_head_error {α : Type} (f : Nat → SpecM α) (a n : Nat) (hn : 0 < n)
    (e : SpecError) (h : f a = .error e) : (List.range' a n).mapM f = .error e := by
  cases n with
  | zero => omega
  | succ n => rw [List.range'_succ, List.mapM_cons, h]; rfl

/-- With fewer than `SLOTS_PER_EPOCH` active validators at the epoch of `slot`, the first slot of
that epoch has no beacon committee members, so `compute_ptc` raises at `assert total > 0`. -/
theorem compute_ptc_first_slot_error [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle)
    (s : BeaconState) (a : Nat)
    (ha : a + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (hfew : (get_active_validator_indices s a).length < P.SLOTS_PER_EPOCH) :
    compute_ptc P o s (a * P.SLOTS_PER_EPOCH) = .error .assertionFailed := by
  have hdiv : a * P.SLOTS_PER_EPOCH / P.SLOTS_PER_EPOCH = a := Nat.mul_div_cancel _ P_slots_pos
  have hmod : a * P.SLOTS_PER_EPOCH % P.SLOTS_PER_EPOCH = 0 := Nat.mul_mod_left _ _
  have hn := (active_len_le s a).trans hreg
  obtain ⟨seed, hseed⟩ := get_seed_total o s a DOMAIN_PTC_ATTESTER ha hr
  obtain ⟨l, hl1, hl2, -⟩ := ptcIndices_total o s (a * P.SLOTS_PER_EPOCH) (by rw [hdiv]; exact ha)
    hr (by rw [hdiv]; exact hn)
  rw [hdiv, hmod] at hl2
  rw [hdiv] at hl1
  have hl0 : l = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hl2]
    generalize (get_active_validator_indices s a).length = n at hfew
    rw [Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.zero_div, Nat.div_eq_of_lt hfew]
  subst hl0
  rw [compute_ptc_eq]
  unfold compute_epoch_at_slot
  rw [tot_div P_slots_ne, tot_bind_ok]
  rw [hdiv, hseed, tot_bind_ok, hl1, tot_bind_ok]
  unfold compute_balance_weighted_selection
  rfl

/-- The pyspec `process_ptc_window` raises when fewer than `SLOTS_PER_EPOCH` validators are active
at `current + 2`. This is a pyspec halt: no state passes this epoch boundary. -/
theorem process_ptc_window_few_active_error [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]
    (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40) (hlen : s.ptc_window.length = 3 * P.SLOTS_PER_EPOCH)
    (hfew : (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 2)).length <
      P.SLOTS_PER_EPOCH) :
    process_ptc_window P o s = .error .assertionFailed := by
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  have hst := P_ep_start_bound hslot 2 (by decide)
  unfold process_ptc_window compute_start_slot_at_epoch
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.ptc_window.length by omega), tot_bind_ok, hlen]
  dsimp only
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
      rw [Nat.add_assoc],
    tot_mul (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hst), tot_bind_ok,
    tot_add hst, tot_bind_ok, Nat.add_sub_cancel_left]
  rw [mapM_range'_head_error _ _ _ P_slots_pos _
    (compute_ptc_first_slot_error o
      { s with ptc_window := List.drop P.SLOTS_PER_EPOCH s.ptc_window ++
        List.drop (3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) s.ptc_window }
      (s.slot / P.SLOTS_PER_EPOCH + 2) (P_ep_bound hslot 2 (by decide)) hr hreg hfew)]
  rfl

/-! ## `CommitteesOk` -/

/-- The state facts that the three committee steps read beyond `CommFrame`. Each one is an
invariant of reachable states: the registry limit is `VALIDATOR_REGISTRY_LIMIT`, the effective
balance bound is `EBOk`, the two lengths are SSZ vector lengths, and a deposit adds a validator
only after its signature checks, which validates the key. -/
structure CommitteeStepFacts [PresetCfg] (o : Oracle) (s : BeaconState) : Prop where
  regLen : s.validators.length ≤ 2 ^ 40
  ebMax : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000
  lookahead : s.proposer_lookahead.length = 2 * P.SLOTS_PER_EPOCH
  ptcLen : s.ptc_window.length = 3 * P.SLOTS_PER_EPOCH
  keys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true

/-- The committee conditions at the epoch input `t`: the state conditions and the pyspec
preconditions hold at the state that the epoch passes to the committee steps
(`epochToCommittees`). That state is a function of `t`, so this is one fact about one state.

An earlier version stated them at every state `s` with `CommFrame t s`. `CommFrame` fixes only
the slot, the list lengths and the RANDAO length, so it admits `t` with every validator list
emptied, where `syncActive` fails: that hypothesis was false for every `t`. -/
def AtCommitteeStepState [PresetCfg] (o : Oracle) (t : BeaconState) : Prop :=
  ∀ s, epochToCommittees P o t = .ok s → CommitteeStepFacts o s ∧ CommitteeStepPreconds o s

/-- The committee steps succeed on the state that `epochToCommittees` returns, from the state
conditions and the pyspec preconditions there. -/
theorem committeesOk_of [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] (o : Oracle) (t : BeaconState) (hslot : t.slot + 8192 < 2 ^ 64)
    (h : AtCommitteeStepState o t) : CommitteesOk o t := by
  intro s hs hf
  obtain ⟨hc, hp⟩ := h s hs
  exact committee_steps_total o s
    ⟨hf.slot ▸ hslot, hf.randao, hc.regLen, hc.ebMax, hc.lookahead, hc.ptcLen, hc.keys⟩ hp

end EpochProofs.Spec
