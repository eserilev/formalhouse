import EpochProofs.Caches
import EpochProofs.Spec.PresetCfg
import EpochProofs.Sanity.PtcIndices
import EpochProofs.Sanity.ShuffleClosedForm
import EpochProofs.Equiv.EpochCommittees

/-!
# The committee cache in the PTC window

Lighthouse builds the committees of the PTC window from a committee cache
(`process_ptc_window` in `single_pass.rs`): slot `start + k` gets the beacon committees of that
slot from the cache, joined in order. `ptc_for_epoch_spec` (`Equiv/EpochCommittees.lean`) takes
"these joined committees are `ptcIndices`" as its hypothesis `hcomm`.

`CacheProofs` proves the committee cache equal to its own spec model
(`get_beacon_committee_equiv`, `shuffling_spec`). The two projects state the shuffle hash
differently: the epoch reference has `Oracle.hash` on bytes, the cache reference has a function
on byte values. `natHash o` is `o.hash` on byte values, and `csiFold_eq` proves the two closed
forms of the shuffle equal for it.

`ptcIndices_of_cache` gives `hcomm` from the committee cache build facts: the shuffling is the
spec shuffling of the active indices with the spec seed, and the committee count is the spec
count. `lh_ptc_window_from_cache` is `ptc_for_epoch_spec` with `hcomm` replaced by these facts.
-/

namespace EpochProofs.CacheBridge

open Aeneas Aeneas.Std Result

/-- `o.hash` on byte values, the hash form of the cache reference. -/
def natHash (o : Spec.Oracle) (l : List Nat) : List Nat :=
  (o.hash (l.map UInt8.ofNat)).toList.map UInt8.toNat

/-- Bytes as byte values. -/
def natBytes (l : List UInt8) : List Nat := l.map UInt8.toNat

theorem natHash_length (o : Spec.Oracle) (l : List Nat) : (natHash o l).length = 32 := by
  simp [natHash]

theorem ofNat_natBytes (l : List UInt8) : (natBytes l).map UInt8.ofNat = l := by
  simp [natBytes, Function.comp_def]

theorem le4_ofNat (x : Nat) :
    (CacheProofs.Shuffle.le4 x).map UInt8.ofNat = Spec.uint_to_bytes 4 x := by
  simp [CacheProofs.Shuffle.le4, Spec.uint_to_bytes, List.range_succ]

theorem pivotOf_eq (o : Spec.Oracle) (seed : List UInt8) (n r : Nat) :
    CacheProofs.Shuffle.pivotOf (natHash o) (natBytes seed) n r = Spec.pivotOf o seed n r := by
  simp only [CacheProofs.Shuffle.pivotOf, Spec.pivotOf, natHash, List.map_append,
    ofNat_natBytes, List.map_cons, List.map_nil, CacheProofs.Spec.CommitteeCache.bytes_to_uint64,
    Spec.leNat, ← List.map_take, List.foldr_map]

theorem bitOf_eq (o : Spec.Oracle) (seed : List UInt8) (r position : Nat) :
    CacheProofs.Shuffle.bitOf (natHash o) (natBytes seed) r position =
      Spec.bitOf o seed r position := by
  simp only [CacheProofs.Shuffle.bitOf, Spec.bitOf, natHash, List.map_append, ofNat_natBytes,
    List.map_cons, List.map_nil, le4_ofNat]
  congr 2
  rw [show (0 : Nat) = UInt8.toNat 0 from rfl, List.getD_map]

theorem sigma_eq (o : Spec.Oracle) (seed : List UInt8) (n r x : Nat) :
    CacheProofs.Shuffle.sigma (natHash o) (natBytes seed) n r x = Spec.sigma o seed n r x := by
  simp only [CacheProofs.Shuffle.sigma, Spec.sigma, pivotOf_eq, bitOf_eq]

/-- The closed form of the shuffle is the same in both references. -/
theorem csiFold_eq (o : Spec.Oracle) (seed : List UInt8) (n R x : Nat) :
    CacheProofs.Shuffle.csiFold (natHash o) (natBytes seed) n R x = Spec.csiFold o seed n R x := by
  simp only [CacheProofs.Shuffle.csiFold, Spec.csiFold, sigma_eq]

/-! ## The committees of the epoch reference, from a shuffling -/

open CacheProofs.CommitteeCache (IsShuffling shuffledAt)

theorem ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- Entry `i` of a cache-form shuffling is `indices[compute_shuffled_index(i, len(indices),
seed)]` of the epoch reference. -/
theorem epoch_shuffled_at (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hR : cp.SHUFFLE_ROUND_COUNT = p.SHUFFLE_ROUND_COUNT) (hR256 : p.SHUFFLE_ROUND_COUNT ≤ 256)
    (o : Spec.Oracle) (indices : List Nat) (seed : Spec.Bytes32) (shuffling : List Nat)
    (hshuf : IsShuffling cp (natHash o) indices (natBytes seed.toList) shuffling)
    (hn24 : indices.length ≤ 2 ^ 24) (i : Nat) (hi : i < indices.length) :
    (do let k ← Spec.compute_shuffled_index p o i indices.length seed; Spec.listGet indices k) =
      .ok (shuffling.getD i 0) := by
  have h := hshuf.2 i hi
  unfold shuffledAt at h
  rw [CacheProofs.Shuffle.compute_shuffled_index_eq cp (natHash o) (natHash_length o)
    (natBytes seed.toList) indices.length (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
    (by simpa using hn24) (hR ▸ hR256) i hi, csiFold_eq, hR] at h
  rw [Spec.compute_shuffled_index_eq p o seed i indices.length hi
    (Nat.le_trans hn24 (by norm_num)) hR256]
  generalize Spec.csiFold o seed.toList indices.length p.SHUFFLE_ROUND_COUNT i = k at h ⊢
  simp only [Bind.bind, Except.bind, CacheProofs.Spec.CommitteeCache.listGet] at h
  simp only [Bind.bind, Except.bind, Spec.listGet]
  split at h
  · rename_i a ha
    rw [ha]
    simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
    exact h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `compute_committee` of the epoch reference is a slice of the shuffling. -/
theorem epoch_compute_committee_slice (p : Spec.Preset) (o : Spec.Oracle) (indices : List Nat)
    (seed : Spec.Bytes32) (shuffling : List Nat) (hlen : shuffling.length = indices.length)
    (hsh : ∀ i, i < indices.length →
      (do let k ← Spec.compute_shuffled_index p o i indices.length seed; Spec.listGet indices k) =
        .ok (shuffling.getD i 0))
    (index count : Nat) (hindex : index < count) (hcount : count < 2 ^ 64)
    (hfit : indices.length * count < 2 ^ 64) :
    Spec.compute_committee p o indices seed index count =
      .ok ((shuffling.drop (indices.length * index / count)).take
        (indices.length * (index + 1) / count - indices.length * index / count)) := by
  have h2 : indices.length * (index + 1) ≤ indices.length * count := Nat.mul_le_mul_left _ hindex
  have h1 : indices.length * index ≤ indices.length * count :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hindex)
  have hc0 : count ≠ 0 := by omega
  have hend : indices.length * (index + 1) / count ≤ indices.length := by
    apply Nat.div_le_of_le_mul; rw [Nat.mul_comm count]; exact h2
  have hse : indices.length * index / count ≤ indices.length * (index + 1) / count :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ _))
  unfold Spec.compute_committee
  simp only [Spec.uint64Mul, Spec.uint64Div, Spec.uint64Add, hc0,
    show indices.length * index < Spec.UINT64_SIZE by unfold Spec.UINT64_SIZE; omega,
    show index + 1 < Spec.UINT64_SIZE by unfold Spec.UINT64_SIZE; omega,
    if_true, if_false, pure_bind]
  simp only [show indices.length * (index + 1) < Spec.UINT64_SIZE by
    unfold Spec.UINT64_SIZE; omega, if_true, pure_bind]
  rw [CacheProofs.CommitteeCache.mapM_except_ok _ (fun i => shuffling.getD i 0)]
  · rw [CacheProofs.CommitteeCache.range'_map_getD]; omega
  · intro x hx
    simp only [List.mem_range'_1] at hx
    exact hsh x (by omega)

theorem epoch_cps_eq (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hspe : cp.SLOTS_PER_EPOCH = p.SLOTS_PER_EPOCH)
    (hmax : cp.MAX_COMMITTEES_PER_SLOT = p.MAX_COMMITTEES_PER_SLOT)
    (htcs : cp.TARGET_COMMITTEE_SIZE = p.TARGET_COMMITTEE_SIZE) (hspe0 : 0 < p.SLOTS_PER_EPOCH)
    (htcs0 : 0 < p.TARGET_COMMITTEE_SIZE) (state : Spec.BeaconState) (epoch cps : Nat)
    (h : CacheProofs.Spec.CommitteeCache.get_committee_count_per_slot cp
      (Spec.get_active_validator_indices state epoch).length = .ok cps) :
    Spec.get_committee_count_per_slot p state epoch = .ok cps := by
  simp only [CacheProofs.Spec.CommitteeCache.get_committee_count_per_slot,
    CacheProofs.Spec.CommitteeCache.uint64Div, hspe, hmax, htcs, Nat.ne_of_gt hspe0,
    Nat.ne_of_gt htcs0, if_false, pure_bind] at h
  simp only [Spec.get_committee_count_per_slot, Spec.uint64Div, Nat.ne_of_gt hspe0,
    Nat.ne_of_gt htcs0, if_false, pure_bind]
  simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
  exact h

/-- `get_beacon_committee` of the epoch reference is a slice of the shuffling of its epoch. -/
theorem epoch_get_beacon_committee_slice (p : Spec.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (slot index epoch cps : Nat) (seed : Spec.Bytes32)
    (shuffling : List Nat)
    (hepoch : Spec.compute_epoch_at_slot p slot = .ok epoch)
    (hcps : Spec.get_committee_count_per_slot p state epoch = .ok cps)
    (hseed : Spec.get_seed p o state epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (hlen : shuffling.length = (Spec.get_active_validator_indices state epoch).length)
    (hsh : ∀ i, i < (Spec.get_active_validator_indices state epoch).length →
      (do let k ← Spec.compute_shuffled_index p o i
            (Spec.get_active_validator_indices state epoch).length seed
          Spec.listGet (Spec.get_active_validator_indices state epoch) k) =
        .ok (shuffling.getD i 0))
    (hspe0 : 0 < p.SLOTS_PER_EPOCH) (hindex : index < cps)
    (hn : 0 < (Spec.get_active_validator_indices state epoch).length)
    (hfit : (Spec.get_active_validator_indices state epoch).length * (cps * p.SLOTS_PER_EPOCH) <
      2 ^ 64) :
    Spec.get_beacon_committee p o state slot index =
      let n := (Spec.get_active_validator_indices state epoch).length
      let k := slot % p.SLOTS_PER_EPOCH * cps + index
      let c := cps * p.SLOTS_PER_EPOCH
      .ok ((shuffling.drop (n * k / c)).take (n * (k + 1) / c - n * k / c)) := by
  have hcount : cps * p.SLOTS_PER_EPOCH < 2 ^ 64 := by
    have := Nat.le_mul_of_pos_left (cps * p.SLOTS_PER_EPOCH) hn
    omega
  have hmod : slot % p.SLOTS_PER_EPOCH < p.SLOTS_PER_EPOCH := Nat.mod_lt _ hspe0
  have hidx : slot % p.SLOTS_PER_EPOCH * cps + index < cps * p.SLOTS_PER_EPOCH := by
    have : (slot % p.SLOTS_PER_EPOCH + 1) * cps ≤ p.SLOTS_PER_EPOCH * cps :=
      Nat.mul_le_mul_right _ hmod
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm cps]
    omega
  unfold Spec.get_beacon_committee
  have hm1 : slot % p.SLOTS_PER_EPOCH * cps < Spec.UINT64_SIZE := by
    unfold Spec.UINT64_SIZE; omega
  have hm2 : slot % p.SLOTS_PER_EPOCH * cps + index < Spec.UINT64_SIZE := by
    unfold Spec.UINT64_SIZE; omega
  have hm3 : cps * p.SLOTS_PER_EPOCH < Spec.UINT64_SIZE := by unfold Spec.UINT64_SIZE; omega
  simp only [hepoch, ok_bind', hcps, hseed, Spec.uint64Mod, Spec.uint64Mul, Spec.uint64Add,
    Nat.ne_of_gt hspe0, if_false, hm1, hm2, hm3, if_true, pure_bind]
  exact epoch_compute_committee_slice p o _ seed shuffling hlen hsh _ _ hidx hcount
    (by omega)

/-! ## The Lighthouse committee cache gives the beacon committees of the epoch reference -/

/-- The preset values that the two references share. -/
structure CommitteePresetLink (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset) :
    Prop where
  slots_per_epoch : cp.SLOTS_PER_EPOCH = p.SLOTS_PER_EPOCH
  max_committees_per_slot : cp.MAX_COMMITTEES_PER_SLOT = p.MAX_COMMITTEES_PER_SLOT
  target_committee_size : cp.TARGET_COMMITTEE_SIZE = p.TARGET_COMMITTEE_SIZE
  shuffle_round_count : cp.SHUFFLE_ROUND_COUNT = p.SHUFFLE_ROUND_COUNT
  slots_pos : 0 < p.SLOTS_PER_EPOCH
  target_pos : 0 < p.TARGET_COMMITTEE_SIZE
  rounds_le : p.SHUFFLE_ROUND_COUNT ≤ 256
  rounds_pos : 0 < p.SHUFFLE_ROUND_COUNT

theorem committeePresetLink_mainnet [EpochProofs.Spec.PresetCfg] :
    CommitteePresetLink Spec.P CacheProofs.Spec.CommitteeCache.P where
  slots_per_epoch := rfl
  max_committees_per_slot := rfl
  target_committee_size := rfl
  shuffle_round_count := rfl
  slots_pos := by decide
  target_pos := by decide
  rounds_le := by decide
  rounds_pos := by decide

theorem usize_max_lt' : Usize.max < 2 ^ 64 := CacheProofs.CommitteeCache.usize_max_lt

/-- A committee that Lighthouse reads from its committee cache is the beacon committee of the
epoch reference. The cache holds the spec shuffling of the active indices with the spec seed,
and the spec committee count. -/
theorem lh_committee_eq (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hp : CommitteePresetLink p cp) (o : Spec.Oracle) (state : Spec.BeaconState) (epoch : Nat)
    (seed : Spec.Bytes32)
    (hseed : Spec.get_seed p o state epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (shuffling : Slice Usize)
    (hshuf : IsShuffling cp (natHash o) (Spec.get_active_validator_indices state epoch)
      (natBytes seed.toList) (shuffling.val.map (·.val)))
    (cps spe : Usize)
    (hcps : CacheProofs.Spec.CommitteeCache.get_committee_count_per_slot cp
      (Spec.get_active_validator_indices state epoch).length = .ok cps.val)
    (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hn : 0 < (Spec.get_active_validator_indices state epoch).length)
    (hn24 : (Spec.get_active_validator_indices state epoch).length ≤ 2 ^ 24)
    (hfit : (Spec.get_active_validator_indices state epoch).length * (cps.val * spe.val) ≤
      Usize.max)
    (slot index : Usize) (hslot : Spec.compute_epoch_at_slot p slot.val = .ok epoch)
    (hindex : index.val < cps.val) :
    ∃ committee, CacheProofs.CommitteeCache.lhGetBeaconCommittee (some (slot.val / spe.val))
        shuffling cps spe slot index = ok (some committee) ∧
      Spec.get_beacon_committee p o state slot.val index.val = .ok (committee.map (·.val)) := by
  have hspe0 : 0 < spe.val := hspe ▸ hp.slots_pos
  have hspeC : spe.val = cp.SLOTS_PER_EPOCH := hspe.trans hp.slots_per_epoch.symm
  obtain ⟨committee, hlh, hgbc⟩ := CacheProofs.CommitteeCache.get_beacon_committee_equiv cp
    (natHash o) _ _ shuffling hshuf cps spe slot index hcps hspeC hspe0 hindex hn hfit
  refine ⟨committee, hlh, ?_⟩
  have h64 := usize_max_lt'
  rw [CacheProofs.CommitteeCache.get_beacon_committee_slice cp (natHash o) _ _ _ hshuf cps.val
    slot.val index.val hcps (hspeC ▸ hspe0) hindex hn (by rw [← hspeC]; omega)] at hgbc
  have hcpsE := epoch_cps_eq p cp hp.slots_per_epoch hp.max_committees_per_slot
    hp.target_committee_size hp.slots_pos hp.target_pos state epoch cps.val hcps
  have hlen : (shuffling.val.map (·.val)).length =
      (Spec.get_active_validator_indices state epoch).length := hshuf.1
  rw [epoch_get_beacon_committee_slice p o state slot.val index.val epoch cps.val seed
    (shuffling.val.map (·.val)) hslot hcpsE hseed hlen
    (epoch_shuffled_at p cp hp.shuffle_round_count hp.rounds_le o _ seed _ hshuf hn24)
    hp.slots_pos hindex hn (by rw [← hspe]; omega)]
  dsimp only at hgbc ⊢
  rw [hp.slots_per_epoch] at hgbc
  exact congrArg Except.ok (Except.ok.inj hgbc)

theorem foldl_append_range {β : Type} (f : Nat → List β) (n : Nat) (acc : List β) :
    (List.range n).foldl (fun a i => a ++ f i) acc = acc ++ ((List.range n).map f).flatten := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldl_append, ih]

theorem map_range_getD {α β : Type} (cs : List α) (d : α) (g : α → β) :
    (List.range cs.length).map (fun i => g (cs.getD i d)) = cs.map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem exists_usize (n : Nat) (h : n ≤ Usize.max) : ∃ u : Usize, u.val = n := by
  have h1 := Usize.max_succ_eq_pow
  have h2 : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
  exact ⟨UScalar.ofNatCore n (by rw [h2]; omega), UScalar.ofNatCore_val_eq _⟩

/-- The beacon committees of one slot that Lighthouse reads from its committee cache, joined in
order, are `ptcIndices` of the epoch reference. `cs[i]` is the cache committee `i` of the slot. -/
theorem ptcIndices_of_cache (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hp : CommitteePresetLink p cp) (o : Spec.Oracle) (state : Spec.BeaconState) (epoch : Nat)
    (seed : Spec.Bytes32)
    (hseed : Spec.get_seed p o state epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (shuffling : Slice Usize)
    (hshuf : IsShuffling cp (natHash o) (Spec.get_active_validator_indices state epoch)
      (natBytes seed.toList) (shuffling.val.map (·.val)))
    (cps spe : Usize)
    (hcps : CacheProofs.Spec.CommitteeCache.get_committee_count_per_slot cp
      (Spec.get_active_validator_indices state epoch).length = .ok cps.val)
    (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hn : 0 < (Spec.get_active_validator_indices state epoch).length)
    (hn24 : (Spec.get_active_validator_indices state epoch).length ≤ 2 ^ 24)
    (hfit : (Spec.get_active_validator_indices state epoch).length * (cps.val * spe.val) ≤
      Usize.max)
    (start k : Nat) (hstart : Spec.compute_start_slot_at_epoch p epoch = .ok start)
    (hk : k < p.SLOTS_PER_EPOCH) (slot : Usize) (hslotv : slot.val = start + k)
    (cs : List (List Usize)) (hcslen : cs.length = cps.val)
    (hcs : ∀ index : Usize, index.val < cps.val →
      CacheProofs.CommitteeCache.lhGetBeaconCommittee (some epoch) shuffling cps spe slot index =
        ok cs[index.val]?) :
    Spec.ptcIndices p o state epoch (start + k) = .ok (cs.map (·.map (·.val))).flatten := by
  have hep := EpochProofs.epoch_of_slot p epoch start k hp.slots_pos hstart hk
  have hslot : Spec.compute_epoch_at_slot p slot.val = .ok epoch := hslotv ▸ hep
  have hdiv : slot.val / spe.val = epoch := by
    simp only [Spec.compute_epoch_at_slot, Spec.uint64Div, Nat.ne_of_gt hp.slots_pos,
      if_false] at hslot
    rw [hspe]; exact Except.ok.inj hslot
  have hcpsE := epoch_cps_eq p cp hp.slots_per_epoch hp.max_committees_per_slot
    hp.target_committee_size hp.slots_pos hp.target_pos state epoch cps.val hcps
  have hcomm : ∀ i, i < cps.val →
      Spec.get_beacon_committee p o state (start + k) i = .ok ((cs.getD i []).map (·.val)) := by
    intro i hi
    have hcmax : cps.val ≤ Usize.max := by
      have h1 : cps.val ≤ cps.val * spe.val := Nat.le_mul_of_pos_right _ (hspe ▸ hp.slots_pos)
      have h2 : cps.val * spe.val ≤
          (Spec.get_active_validator_indices state epoch).length * (cps.val * spe.val) :=
        Nat.le_mul_of_pos_left _ hn
      omega
    obtain ⟨u, hu⟩ := exists_usize i (by omega)
    obtain ⟨committee, hlh, hgbc⟩ := lh_committee_eq p cp hp o state epoch seed hseed shuffling
      hshuf cps spe hcps hspe hn hn24 hfit slot u hslot (hu ▸ hi)
    have hc := hcs u (hu ▸ hi)
    rw [hdiv, hc] at hlh
    have hci : cs[i]? = some committee := by rw [← hu]; simpa using hlh
    rw [← hslotv, ← hu, hgbc, List.getD_eq_getElem?_getD, hu, hci]
    rfl
  unfold Spec.ptcIndices
  rw [hcpsE, ok_bind']
  rw [Spec.forIn_yield (List.range cps.val) []
    _ (fun a i => a ++ (cs.getD i []).map (·.val)) (fun _ => True) trivial]
  · rw [foldl_append_range, List.nil_append, ← hcslen,
      map_range_getD cs [] (fun c => c.map (·.val))]
    rfl
  · intro x hx a _
    rw [List.mem_range] at hx
    refine ⟨?_, trivial⟩
    simp only [hcomm x hx, ok_bind']
    rfl

/-! ## The committee cache build facts -/

/-- The committee cache of `epoch` holds the spec shuffling of the active indices with the spec
seed, and the spec committee count. This is what `CommitteeCache::initialized` builds. -/
structure CommitteeCacheBuilt (cp : CacheProofs.Spec.CommitteeCache.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32) (shuffling : Slice Usize)
    (cps : Usize) : Prop where
  shuffling_spec : IsShuffling cp (natHash o) (Spec.get_active_validator_indices state epoch)
    (natBytes seed.toList) (shuffling.val.map (·.val))
  count_spec : CacheProofs.Spec.CommitteeCache.get_committee_count_per_slot cp
    (Spec.get_active_validator_indices state epoch).length = .ok cps.val

/-- The build facts from the Rust build functions: the cache shuffling is the output of the
Aeneas-checked `committee_assignment::shuffling` on the active indices and the seed, and the
committee count is the output of `committee_count_per_slot`. -/
theorem committeeCacheBuilt_of_rust {H : Type} (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (p : Spec.Preset) (hp : CommitteePresetLink p cp) (o : Spec.Oracle)
    (instC : CacheProofs.Shuffle.HashInst H) (hH : CacheProofs.Shuffle.HashLink instC (natHash o))
    (state : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32)
    (indices : alloc.vec.Vec Usize)
    (hindices : indices.val.map (·.val) = Spec.get_active_validator_indices state epoch)
    (hn : 0 < indices.val.length) (hn24 : indices.val.length ≤ 2 ^ 24)
    (rounds : U8) (hrounds : rounds.val = p.SHUFFLE_ROUND_COUNT)
    (seedS : Slice U8) (hseedS : seedS.val.map (·.val) = natBytes seed.toList)
    (v : alloc.vec.Vec Usize)
    (hrun : types.state.committee_assignment.shuffling instC indices rounds seedS = ok (some v))
    (shuffling : Slice Usize) (hsv : shuffling.val = v.val)
    (active_count spe max_cps target cps : Usize)
    (hcount : active_count.val = indices.val.length) (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hmax : max_cps.val = p.MAX_COMMITTEES_PER_SLOT)
    (htarget : target.val = p.TARGET_COMMITTEE_SIZE)
    (hcps : types.state.committee_assignment.committee_count_per_slot active_count spe max_cps
      target = ok (.Ok cps)) :
    CommitteeCacheBuilt cp o state epoch seed shuffling cps := by
  have hseedlen : seedS.val.length = 32 := by
    have := congrArg List.length hseedS
    simpa [natBytes] using this
  have hs := CacheProofs.Shuffle.shuffling_spec instC (natHash o) hH (natHash_length o) cp seedS
    hseedlen indices rounds (hp.shuffle_round_count.trans hrounds.symm) hn hn24
    (hrounds ▸ hp.rounds_pos)
  rw [hrun, Aeneas.Std.WP.spec_ok] at hs
  obtain ⟨v', hv', hshuf⟩ := hs
  cases hv'
  have hc := CacheProofs.CommitteeCache.committee_count_per_slot_equiv cp active_count spe max_cps
    target (hspe.trans hp.slots_per_epoch.symm) (hmax.trans hp.max_committees_per_slot.symm)
    (htarget.trans hp.target_committee_size.symm)
  rw [hcps, Aeneas.Std.WP.spec_ok] at hc
  refine ⟨?_, ?_⟩
  · rw [hindices, hseedS] at hshuf
    rw [hsv]
    exact hshuf
  · rw [← hindices, List.length_map, ← hcount]
    exact hc.symm

/-! ## The PTC committees of Lighthouse -/

/-- How Lighthouse builds the committees of the PTC window (`process_ptc_window`): entry `k`
joins, in order, the committees of slot `start + k` that `CommitteeCache::get_beacon_committee`
returns. -/
def CommitteesFromCache (shuffling : Slice Usize) (cps spe : Usize) (epoch start : Nat)
    (committees : Slice (alloc.vec.Vec Usize)) : Prop :=
  ∀ k (_ : k < committees.val.length), ∃ (slot : Usize) (cs : List (List Usize)),
    slot.val = start + k ∧ cs.length = cps.val ∧ (committees.val[k]).val = cs.flatten ∧
    ∀ index : Usize, index.val < cps.val →
      CacheProofs.CommitteeCache.lhGetBeaconCommittee (some epoch) shuffling cps spe slot index =
        ok cs[index.val]?

/-- The hypothesis `hcomm` of `ptc_for_epoch_spec`, from the committee cache build facts. -/
theorem hcomm_of_cache (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hp : CommitteePresetLink p cp) (o : Spec.Oracle) (state : Spec.BeaconState) (epoch : Nat)
    (seed : Spec.Bytes32)
    (hseed : Spec.get_seed p o state epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (shuffling : Slice Usize) (cps spe : Usize)
    (hbuilt : CommitteeCacheBuilt cp o state epoch seed shuffling cps)
    (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hn : 0 < (Spec.get_active_validator_indices state epoch).length)
    (hn24 : (Spec.get_active_validator_indices state epoch).length ≤ 2 ^ 24)
    (hfit : (Spec.get_active_validator_indices state epoch).length * (cps.val * spe.val) ≤
      Usize.max)
    (start : Nat) (hstart : Spec.compute_start_slot_at_epoch p epoch = .ok start)
    (committees : Slice (alloc.vec.Vec Usize))
    (hclen : committees.val.length = p.SLOTS_PER_EPOCH)
    (hglue : CommitteesFromCache shuffling cps spe epoch start committees) :
    ∀ k (hk : k < committees.val.length) l,
      Spec.ptcIndices p o state epoch (start + k) = .ok l →
        (committees.val[k]).val.map (·.val) = l := by
  intro k hk l hl
  obtain ⟨slot, cs, hslotv, hcslen, hck, hcs⟩ := hglue k hk
  rw [ptcIndices_of_cache p cp hp o state epoch seed hseed shuffling hbuilt.shuffling_spec cps
    spe hbuilt.count_spec hspe hn hn24 hfit start k hstart (hclen ▸ hk) slot hslotv cs hcslen
    hcs] at hl
  rw [hck, List.map_flatten]
  exact Except.ok.inj hl

open Aeneas.Std.WP in
/-- Lighthouse's `ptc_for_epoch` on the committees that `process_ptc_window` reads from the
committee cache returns the PTCs that the spec `process_ptc_window` appends. This is
`ptc_for_epoch_spec` with its committee hypothesis replaced by the committee cache build facts
(`CommitteeCacheBuilt`) and the way Lighthouse joins the cache committees
(`CommitteesFromCache`). -/
theorem lh_ptc_window_from_cache {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (cp : CacheProofs.Spec.CommitteeCache.Preset)
    (hp : CommitteePresetLink p cp) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (committees : Slice (alloc.vec.Vec Usize))
    (hclen : committees.val.length = p.SLOTS_PER_EPOCH) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_PTC_ATTESTER.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce →
      epoch.val = ce + p.MIN_SEED_LOOKAHEAD + 1)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
    (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
    (seed : Spec.Bytes32)
    (hseed : Spec.get_seed p o state epoch.val Spec.DOMAIN_BEACON_ATTESTER = .ok seed)
    (shuffling : Slice Usize) (cps spe : Usize)
    (hbuilt : CommitteeCacheBuilt cp o state epoch.val seed shuffling cps)
    (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (hn : 0 < (Spec.get_active_validator_indices state epoch.val).length)
    (hn24 : (Spec.get_active_validator_indices state epoch.val).length ≤ 2 ^ 24)
    (hfit : (Spec.get_active_validator_indices state epoch.val).length * (cps.val * spe.val) ≤
      Usize.max)
    (hglue : CommitteesFromCache shuffling cps spe epoch.val start_slot.val committees)
    (hn24c : ∀ k (hk : k < committees.val.length), (committees.val[k]).val.length ≤ 2 ^ 24)
    (ptc_size : Usize) (hptc : ptc_size.val = p.PTC_SIZE) (c : LhSelectionConstants)
    (hc : SelectionConstantsMatch p c) (hus : Usize.max = U64.max)
    (state' : Spec.BeaconState) (hspec : Spec.process_ptc_window p o state = .ok state') :
    state_processing.per_epoch_processing.epoch_committees.ptc_for_epoch inst ebi balances
      committees domain epoch mix start_slot ptc_size c ⦃ r =>
        ∃ v : alloc.vec.Vec (alloc.vec.Vec Usize), r = core.result.Result.Ok v ∧
          state'.ptc_window = state.ptc_window.drop p.SLOTS_PER_EPOCH ++ ptcsOf v ⦄ :=
  ptc_for_epoch_spec inst ebi balances p o hH state hEB committees hclen domain hdomain epoch
    hepoch mix hmix start_slot hstart
    (hcomm_of_cache p cp hp o state epoch.val seed hseed shuffling cps spe hbuilt hspe hn hn24
      hfit start_slot.val hstart committees hclen hglue)
    hn24c ptc_size hptc c hc hp.slots_pos hus state' hspec

end EpochProofs.CacheBridge
