import Mathlib

/-!
# Pubkey cache: reference model

`PubkeyCache` maps each validator pubkey to its index. The cache inserts the keys in index
order, and an insert of a key that is already present overwrites its index. So the cache for
the keys `keys` is `indexView keys`: the last index of each key.

The spec reads `validator_pubkeys.index(pubkey)`: the first index. `indexView_of_nodup` shows
that the two agree when no two validators share a pubkey.
-/

namespace CacheProofs

variable {K : Type} [DecidableEq K]

/-- The map that inserting `keys` in order, key `i` at index `i`, builds. -/
def indexView (keys : List K) : K → Option Nat :=
  keys.zipIdx.foldl (fun f x => fun k => if k = x.1 then some x.2 else f k) (fun _ => none)

theorem indexView_nil : indexView ([] : List K) = fun _ => none := rfl

/-- Inserting one more key at the next index. -/
theorem indexView_append (keys : List K) (x : K) (k : K) :
    indexView (keys ++ [x]) k = if k = x then some keys.length else indexView keys k := by
  unfold indexView
  rw [List.zipIdx_append, List.foldl_append]
  simp

/-- With no duplicate keys, the last index is the first index, and a missing key has none. -/
theorem indexView_of_nodup (keys : List K) (h : keys.Nodup) (k : K) :
    indexView keys k = if k ∈ keys then some (keys.idxOf k) else none := by
  induction keys using List.reverseRecOn with
  | nil => simp [indexView_nil]
  | append_singleton keys x ih =>
    rw [List.nodup_append] at h
    obtain ⟨hk, -, hx⟩ := h
    have hxk : x ∉ keys := fun hm => hx x hm x (by simp) rfl
    rw [indexView_append, ih hk]
    by_cases hkx : k = x
    · subst hkx
      simp [hxk, List.idxOf_append_of_notMem hxk]
    · by_cases hm : k ∈ keys
      · simp [hkx, hm, List.idxOf_append_of_mem hm]
      · simp [hkx, hm]

end CacheProofs
