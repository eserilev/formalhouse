import CacheProofs.AeneasCompat
import CacheProofs.Generated
import CacheProofs.Spec.PubkeyCache

/-!
# Pubkey cache: the Rust insert keeps the cache equal to the reference model

`types::state::pubkey_index::insert` takes the map as a trait, `IndexMap`. Production uses
`rpds::HashTrieMap`. `BehavesAsFiniteMap` states the laws of a finite map that the proofs assume of
it: a get reads the lookup, and an insert updates the lookup at one key.

- `insert_spec`: the insert never fails. It adds the key at the next index, or returns `None`
  and leaves the map unchanged.
- `PubkeyCacheCorrect`: the cache for `keys` holds `keys.length` and `indexOfPubkey keys`.
- `insert_correct`, `insertPubkeys_correct`, `update_correct`: inserting keys in index order
  keeps `PubkeyCacheCorrect`. This is what `BeaconState::update_pubkey_cache` and
  `add_validator_to_registry` do.
- `get_correct_of_nodup`: with unique pubkeys, a get returns the spec's
  `validator_pubkeys.index(pubkey)`, or `None` for a pubkey that is not a validator.
-/

namespace CacheProofs

open Aeneas Aeneas.Std Result types

variable {K M : Type} [DecidableEq K]

/-- The finite map laws of the production map, read through `lookup`. -/
structure BehavesAsFiniteMap (inst : state.pubkey_index.IndexMap M K)
    (lookup : M → K → Option Usize) :
    Prop where
  get : ∀ m k, inst.get_index m k = ok (lookup m k)
  insert : ∀ m k i, ∃ m', inst.insert_index m k i = ok m' ∧
    ∀ k', lookup m' k' = if k' = k then some i else lookup m k'

/-- The cache `(m, len)` holds exactly the keys `keys`, inserted in index order. -/
def PubkeyCacheCorrect (lookup : M → K → Option Usize) (m : M) (len : Usize)
    (keys : List K) : Prop :=
  len.val = keys.length ∧ ∀ k, (lookup m k).map (·.val) = indexOfPubkey keys k

/-- An empty map with length 0 holds no keys. -/
theorem correct_empty (lookup : M → K → Option Usize) (m : M) (hm : ∀ k, lookup m k = none) :
    PubkeyCacheCorrect lookup m 0#usize [] := by
  refine ⟨by simp, fun k => ?_⟩
  simp [hm, indexOfPubkey_nil]

theorem insert_spec {inst : state.pubkey_index.IndexMap M K} {lookup : M → K → Option Usize}
    (laws : BehavesAsFiniteMap inst lookup) (m : M) (len : Usize) (key : K) (index : Usize) :
    ∃ r m', state.pubkey_index.insert inst m len key index = ok (r, m') ∧
      match r with
      | some len' => index = len ∧ len'.val = len.val + 1 ∧
          ∀ k, lookup m' k = if k = key then some index else lookup m k
      | none => m' = m ∧ (index ≠ len ∨ Usize.max < len.val + 1) := by
  unfold state.pubkey_index.insert
  by_cases hne : index = len
  · subst hne
    have hc := Usize.checked_add_bv_spec index 1#usize
    cases ho : Usize.checked_add index 1#usize with
    | none =>
      simp only [ho] at hc
      refine ⟨none, m, ?_, rfl, Or.inr (by scalar_tac)⟩
      simp [lift]
    | some v =>
      simp only [ho] at hc
      obtain ⟨m', hins, hview⟩ := laws.insert m key index
      refine ⟨some v, m', ?_, rfl, by scalar_tac, hview⟩
      simp [lift, hins]
  · refine ⟨none, m, ?_, rfl, Or.inl hne⟩
    simp [hne]

/-- A successful insert at the next index appends the key. -/
theorem insert_correct {inst : state.pubkey_index.IndexMap M K} {lookup : M → K → Option Usize}
    (laws : BehavesAsFiniteMap inst lookup) {m m' : M} {len len' : Usize} {keys : List K} {key : K}
    {index : Usize} (hc : PubkeyCacheCorrect lookup m len keys)
    (h : state.pubkey_index.insert inst m len key index = ok (some len', m')) :
    PubkeyCacheCorrect lookup m' len' (keys ++ [key]) := by
  obtain ⟨r, m'', hrun, hr⟩ := insert_spec laws m len key index
  rw [hrun] at h
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hidx, hlen, hview⟩ := hr
  obtain ⟨hl, hk⟩ := hc
  refine ⟨by simp [hlen, hl], fun k => ?_⟩
  rw [hview, indexOfPubkey_append]
  by_cases hkk : k = key
  · simp [hkk, hidx, hl]
  · simp [hkk, hk k]

/-- The loop of `BeaconState::update_pubkey_cache`: insert each key at the current length,
and stop with `none` (the Rust `PubkeyCacheInconsistent` error) when an insert fails. -/
def insertPubkeys (inst : state.pubkey_index.IndexMap M K) :
    M → Usize → List K → Result (Option (M × Usize))
  | m, len, [] => ok (some (m, len))
  | m, len, key :: rest => do
    let (r, m') ← state.pubkey_index.insert inst m len key len
    match r with
    | some len' => insertPubkeys inst m' len' rest
    | none => ok none

/-- A loop that finishes holds all the keys. -/
theorem insertPubkeys_correct {inst : state.pubkey_index.IndexMap M K}
    {lookup : M → K → Option Usize} (laws : BehavesAsFiniteMap inst lookup) :
    ∀ (more : List K) (m : M) (len : Usize) (keys : List K) (m' : M) (len' : Usize),
      PubkeyCacheCorrect lookup m len keys → insertPubkeys inst m len more = ok (some (m', len')) →
      PubkeyCacheCorrect lookup m' len' (keys ++ more)
  | [], m, len, keys, m', len', hc, h => by
    simp only [insertPubkeys, ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hc
  | key :: rest, m, len, keys, m', len', hc, h => by
    obtain ⟨r, m1, hrun, hr⟩ := insert_spec laws m len key len
    simp only [insertPubkeys, hrun, bind_tc_ok] at h
    cases r with
    | none => simp at h
    | some len1 =>
      have hc1 := insert_correct laws hc hrun
      have := insertPubkeys_correct laws rest m1 len1 (keys ++ [key]) m' len' hc1 h
      simpa using this

/-- The loop never fails unless the length overflows `usize`. -/
theorem insertPubkeys_ok {inst : state.pubkey_index.IndexMap M K} {lookup : M → K → Option Usize}
    (laws : BehavesAsFiniteMap inst lookup) :
    ∀ (more : List K) (m : M) (len : Usize), len.val + more.length ≤ Usize.max →
      ∃ m' len', insertPubkeys inst m len more = ok (some (m', len')) ∧
        len'.val = len.val + more.length
  | [], m, len, _ => ⟨m, len, rfl, by simp⟩
  | key :: rest, m, len, hb => by
    obtain ⟨r, m1, hrun, hr⟩ := insert_spec laws m len key len
    cases r with
    | none =>
      obtain ⟨-, hr⟩ := hr
      simp only [ne_eq, not_true_eq_false, false_or] at hr
      simp only [List.length_cons] at hb
      omega
    | some len1 =>
      obtain ⟨-, hl1, -⟩ := hr
      simp only [List.length_cons] at hb
      obtain ⟨m', len', h, hl⟩ := insertPubkeys_ok laws rest m1 len1 (by omega)
      refine ⟨m', len', ?_, by simp [hl, hl1]; omega⟩
      simp [insertPubkeys, hrun, h]

/-- `BeaconState::update_pubkey_cache`: a cache that holds the first `len` validator pubkeys,
after the loop over the rest, holds all of them. -/
theorem update_correct {inst : state.pubkey_index.IndexMap M K} {lookup : M → K → Option Usize}
    (laws : BehavesAsFiniteMap inst lookup) {m m' : M} {len len' : Usize} {pks : List K}
    (hc : PubkeyCacheCorrect lookup m len (pks.take len.val))
    (h : insertPubkeys inst m len (pks.drop len.val) = ok (some (m', len'))) :
    PubkeyCacheCorrect lookup m' len' pks := by
  have := insertPubkeys_correct laws _ m len _ m' len' hc h
  rwa [List.take_append_drop] at this

/-- With unique pubkeys, a get on a correct cache is the spec lookup:
`validator_pubkeys.index(pubkey)` for a validator, and `None` for any other pubkey. -/
theorem get_correct_of_nodup {inst : state.pubkey_index.IndexMap M K}
    {lookup : M → K → Option Usize} (laws : BehavesAsFiniteMap inst lookup) {m : M} {len : Usize}
    {keys : List K} (hc : PubkeyCacheCorrect lookup m len keys) (hnd : keys.Nodup) (k : K) :
    ∃ r, inst.get_index m k = ok r ∧
      r.map (·.val) = if k ∈ keys then some (keys.idxOf k) else none := by
  refine ⟨lookup m k, laws.get m k, ?_⟩
  rw [hc.2 k, indexOfPubkey_of_nodup keys hnd k]

end CacheProofs
