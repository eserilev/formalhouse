import EpochProofs.Caches

/-!
# Pubkey cache bridge

The pending deposits model reads a deposit's validator as the spec does:
`s.validators[(s.validators.map (·.pubkey)).idxOf d.pubkey]?`, and `d.pubkey ∈ pubkeys`
before a top-up. Lighthouse reads `state.pubkey_cache().get(&deposit.pubkey)`.
`pubkey_cache_deposit_lookup` shows that the two agree on a coherent cache when the pubkeys
are unique (`PubkeysUnique`, a reachable-state invariant).

Trusted: `rpds::HashTrieMap` obeys `IndexMapLaws`, and the cache at the start of the epoch
holds the first `len` validator pubkeys (`update_coherent` then gives all of them).
-/

namespace EpochProofs.Spec

open Aeneas Aeneas.Std Result CacheProofs

/-- The `BEq` that `idxOf` uses on pubkeys is the one from `DecidableEq`. -/
theorem idxOf_pubkey_eq (l : List BLSPubkey) (k : BLSPubkey) :
    @List.idxOf _ instBEqOfDecidableEq k l = l.idxOf k := by
  congr
  exact lawful_beq_subsingleton _ _

theorem pubkey_cache_deposit_lookup {M : Type}
    {inst : types.state.pubkey_index.IndexMap M BLSPubkey}
    {view : M → BLSPubkey → Option Usize} (laws : IndexMapLaws inst view) {m : M}
    {len : Usize} (s : BeaconState)
    (hc : Coherent view m len (s.validators.map (·.pubkey))) (hu : PubkeysUnique s)
    (pk : BLSPubkey) :
    ∃ r, inst.get_index m pk = ok r ∧
      (r.map (·.val)).bind (fun i => s.validators[i]?) =
        s.validators[(s.validators.map (·.pubkey)).idxOf pk]? ∧
      (r.isSome ↔ pk ∈ s.validators.map (·.pubkey)) ∧
      ∀ i, r.map (·.val) = some i → i = (s.validators.map (·.pubkey)).idxOf pk := by
  obtain ⟨r, hget, hr⟩ := get_coherent_of_nodup laws hc hu pk
  rw [idxOf_pubkey_eq] at hr
  refine ⟨r, hget, ?_, ?_, ?_⟩
  · by_cases hm : pk ∈ s.validators.map (·.pubkey)
    · rw [if_pos hm] at hr
      rw [hr]
      rfl
    · rw [if_neg hm] at hr
      have hlen : (s.validators.map (·.pubkey)).idxOf pk = s.validators.length := by
        rw [List.idxOf_eq_length hm, List.length_map]
      rw [hr, hlen]
      simp
  · by_cases hm : pk ∈ s.validators.map (·.pubkey)
    · rw [if_pos hm] at hr
      cases r <;> simp_all
    · rw [if_neg hm] at hr
      cases r <;> simp_all
  · intro i hi
    by_cases hm : pk ∈ s.validators.map (·.pubkey)
    · rw [if_pos hm, hi] at hr
      exact (Option.some.inj hr)
    · rw [if_neg hm, hi] at hr
      cases hr

end EpochProofs.Spec
