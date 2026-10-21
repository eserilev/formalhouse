import EpochProofs.Etheorem.Helpers
import EpochProofs.Etheorem.Oracle
import EpochProofs.Spec.EpochCommittees

/-!
# The shuffle, the seed and the balance weighted selection equal Etheorem's

The reference reads bytes from `o.hash`. Etheorem reads them from `sha` through `get!`. With
`OracleAgrees`, `o.hash data` is `bytesToRoot (sha data)`, so each byte the reference reads is
the same `get!` read.

Each lemma has the form "if the reference returns `r`, then Etheorem's value reads as `r`".

Etheorem's `compute_balance_weighted_selection` stops after `10^7` passes. pyspec loops until
it has `size` items. So `compute_balance_weighted_selection_ok` assumes that Etheorem's result
has `size` items.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs

/-! ## `Except` -/

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem except_pure_eq_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-! ## Bytes -/

/-- A list of bytes as a `ByteArray`. -/
def toBA (l : List UInt8) : ByteArray := ⟨l.toArray⟩

theorem toBA_data (l : List UInt8) : (toBA l).data.toList = l := rfl

theorem ba_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem vecToBytes_toList {n : Nat} (v : Vector UInt8 n) :
    (vecToBytes v).data.toList = v.toList := rfl

@[simp] theorem append_data_toList (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

@[simp] theorem push_data_toList (a : ByteArray) (x : UInt8) :
    (a.push x).data.toList = a.data.toList ++ [x] := by
  simp [ByteArray.data_push]

/-- A root read back from `bytesToRoot`: byte `i` is `b.get! i`. -/
theorem bytesToRoot_toList (b : ByteArray) :
    (bytesToRoot b).toList = (List.range 32).map b.get! := by
  apply List.ext_getElem
  · simp [bytesToRoot, bytesToVec]
  · intro i h1 h2
    simp [bytesToRoot, bytesToVec]

theorem bytesToRoot_getElem? (b : ByteArray) (i : Nat) (hi : i < 32) :
    (bytesToRoot b).toList[i]? = some (b.get! i) := by
  rw [bytesToRoot_toList]; simp [hi]

/-- `vecToBytes (bytesToRoot b) = b` when `b` has 32 bytes. -/
theorem vecToBytes_bytesToRoot (b : ByteArray) (hb : b.size = 32) :
    vecToBytes (bytesToRoot b) = b := by
  apply ba_eq_of_toList
  rw [vecToBytes_toList, bytesToRoot_toList]
  obtain ⟨data⟩ := b
  simp only [ByteArray.size] at hb
  apply List.ext_getElem
  · simp [hb]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, ByteArray.get!]
    exact getElem!_pos data i (by simp at h2; omega)

theorem uint8_ofNat_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  simp

/-- `uint_to_bytes` for a `Uint8`. -/
theorem uint_to_bytes_1 (n : Nat) : Spec.uint_to_bytes 1 n = [UInt8.ofNat n] := by
  show [UInt8.ofNat (n / 256 ^ 0 % 256)] = _
  simp [uint8_ofNat_mod]

/-- `uint_to_bytes` for a `Uint32` is Etheorem's `u32leBytes`. -/
theorem uint_to_bytes_4 (n : Nat) : Spec.uint_to_bytes 4 n = (u32leBytes n).data.toList := by
  apply List.ext_getElem
  · simp [Spec.uint_to_bytes, u32leBytes]
  · intro i h1 h2
    simp only [Spec.uint_to_bytes, List.getElem_map, List.getElem_range, u32leBytes,
      Array.getElem_toList, Array.getElem_ofFn, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- `uint_to_bytes` for a `Uint64` is Etheorem's `uint64ToBytes`. -/
theorem uint_to_bytes_8 (x : UInt64) :
    Spec.uint_to_bytes 8 x.toNat = (uint64ToBytes x).data.toList := by
  apply List.ext_getElem
  · simp [Spec.uint_to_bytes, uint64ToBytes]
  · intro i h1 h2
    have hi : i < 8 := by simpa [Spec.uint_to_bytes] using h1
    simp only [Spec.uint_to_bytes, List.getElem_map, List.getElem_range, uint64ToBytes,
      Array.getElem_toList, Array.getElem_ofFn]
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega),
      Nat.mod_eq_of_lt (by omega : 8 * i < 64), Nat.shiftRight_eq_div_pow, Nat.pow_mul]
    simp

/-- The little endian value of a byte list, as `bytes_to_uint64` computes it. -/
def leValue (l : List UInt8) : Nat := l.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem leValue_append (xs ys : List UInt8) :
    leValue (xs ++ ys) = leValue xs + 256 ^ xs.length * leValue ys := by
  induction xs with
  | nil => simp [leValue]
  | cons x xs ih =>
    simp only [leValue, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.mul_add, Nat.pow_succ, Nat.add_assoc]
    congr 2
    rw [Nat.mul_comm (256 ^ xs.length) 256, Nat.mul_assoc]

theorem leValue_lt (l : List UInt8) : leValue l < 256 ^ l.length := by
  induction l with
  | nil => simp [leValue]
  | cons x xs ih =>
    simp only [leValue, List.foldr_cons, List.length_cons] at ih ⊢
    have hx := x.toNat_lt
    rw [Nat.pow_succ]
    have : 256 * (List.foldr (fun b acc => b.toNat + 256 * acc) 0 xs + 1) ≤
        256 * 256 ^ xs.length :=
      Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (256 ^ xs.length)]
    omega

theorem leValue_range (g : Nat → UInt8) (n : Nat) :
    leValue ((List.range n).map g) =
      (List.range n).foldl (fun acc i => acc + (g i).toNat * 256 ^ i) 0 := by
  induction n with
  | zero => simp [leValue]
  | succ n ih =>
    rw [List.range_succ, List.map_append, leValue_append, ih, List.foldl_append]
    simp [leValue, Nat.mul_comm]

theorem bytes_to_uint64_eq (l : List UInt8) (h : l.length ≤ 8) :
    Spec.bytes_to_uint64 l = .ok (leValue l) := by
  have hlt := leValue_lt l
  have hp : 256 ^ l.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
  unfold Spec.bytes_to_uint64
  rw [if_pos (by unfold Spec.UINT64_SIZE leValue at *; omega)]
  rfl

theorem take_range_map {α : Type} (g : Nat → α) (k n : Nat) (h : k ≤ n) :
    ((List.range n).map g).take k = (List.range k).map g := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2; simp

/-- The first 8 bytes of a root as a `Uint64` are Etheorem's `le8`. -/
theorem bytes_to_uint64_take8 (b : ByteArray) :
    Spec.bytes_to_uint64 ((bytesToRoot b).toList.take 8) = .ok (le8 b) := by
  rw [bytesToRoot_toList, take_range_map _ 8 32 (by decide),
    bytes_to_uint64_eq _ (by simp), leValue_range]
  rfl

/-- Two bytes of a root at `offset` as a `Uint64` are Etheorem's `le2`. -/
theorem bytes_to_uint64_take2 (b : ByteArray) (offset : Nat) (h : offset + 2 ≤ 32) :
    Spec.bytes_to_uint64 (((bytesToRoot b).toList.drop offset).take 2) =
      .ok (le2 b offset) := by
  rw [bytesToRoot_toList]
  have hd : (((List.range 32).map b.get!).drop offset).take 2 =
      [b.get! offset, b.get! (offset + 1)] := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp at h1
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> simp
  rw [hd, bytes_to_uint64_eq _ (by simp)]
  simp only [leValue, le2, List.foldr_cons, List.foldr_nil]
  rw [Except.ok.injEq, Nat.mul_zero, Nat.add_zero, Nat.mul_comm]

/-- A byte of a root, read with `listGet`, is `get!`. -/
theorem listGet_bytesToRoot (b : ByteArray) (i : Nat) (hi : i < 32) :
    Spec.listGet (bytesToRoot b).toList i = .ok (b.get! i) := by
  unfold Spec.listGet
  rw [bytesToRoot_getElem? b i hi]
  rfl

/-- The shuffle bit test. `UInt8` in the reference, `Nat` in Etheorem. -/
theorem shuffle_bit_eq (b : UInt8) (s : Nat) (hs : s < 8) :
    ((b >>> UInt8.ofNat s) % 2 != 0) = ((b.toNat >>> s) % 2 == 1) := by
  have hb : ((b >>> UInt8.ofNat s) % 2).toNat = (b.toNat >>> s) % 2 := by
    rw [UInt8.toNat_mod, UInt8.toNat_shiftRight, UInt8.toNat_ofNat]
    simp only [UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hs (by decide)), Nat.mod_eq_of_lt hs]
  have h2 : (b.toNat >>> s) % 2 < 2 := Nat.mod_lt _ (by decide)
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · intro h
    have : ((b >>> UInt8.ofNat s) % 2).toNat ≠ 0 := by
      intro h0; exact h (UInt8.toNat_inj.mp (by simpa using h0))
    omega
  · intro h h0
    rw [h0] at hb
    simp at hb
    omega

/-! ## Loops -/

/-- A `for` loop that succeeds relates to a `foldl` through `R`, one step at a time. -/
theorem forIn_ok_rel {ε α β γ : Type} (R : β → γ → Prop) (step : γ → α → γ)
    (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b c r, R b c → f a b = .ok r → ∃ b', r = .yield b' ∧ R b' (step c a)) :
    ∀ (l : List α) (b : β) (c : γ) (res : β), R b c → forIn l b f = .ok res →
      R res (l.foldl step c) := by
  intro l
  induction l with
  | nil =>
    intro b c res hR h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hR
  | cons a l ih =>
    intro b c res hR h
    rw [List.forIn_cons, except_bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨b', rfl, hR'⟩ := hf a b c r hR hr
    exact ih b' _ res hR' h


theorem throw_bind_ne_ok {ε α β : Type} {e : ε} {f : α → Except ε β} {b : β} :
    ((throw e : Except ε α) >>= f) ≠ .ok b := fun h => nomatch h

theorem listGet_ok {α : Type} [Inhabited α] {l : List α} {i : Nat} {a : α}
    (h : Spec.listGet l i = .ok a) : i < l.length ∧ l[i]! = a := by
  unfold Spec.listGet at h
  split at h
  · rename_i a' ha
    cases h
    have hi : i < l.length := by
      rcases Nat.lt_or_ge i l.length with hi | hi
      · exact hi
      · simp [List.getElem?_eq_none hi] at ha
    refine ⟨hi, ?_⟩
    rw [getElem!_pos l i hi]
    simp [List.getElem?_eq_getElem hi] at ha
    exact ha
  · cases h

theorem listSet_ok {α : Type} {l : List α} {i : Nat} {a : α} {r : List α}
    (h : Spec.listSet l i a = .ok r) : i < l.length ∧ r = l.set i a := by
  unfold Spec.listSet at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem uint64Add_eq {a b s : Nat} (h : Spec.uint64Add a b = .ok s) :
    s = a + b ∧ a + b < 2 ^ 64 := by
  unfold Spec.uint64Add at h
  split at h
  · cases h; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
  · cases h

theorem uint64Sub_eq {a b s : Nat} (h : Spec.uint64Sub a b = .ok s) : s = a - b ∧ b ≤ a := by
  unfold Spec.uint64Sub at h
  split at h
  · cases h; exact ⟨rfl, ‹_›⟩
  · cases h

theorem uint64Mul_eq {a b s : Nat} (h : Spec.uint64Mul a b = .ok s) :
    s = a * b ∧ a * b < 2 ^ 64 := by
  unfold Spec.uint64Mul at h
  split at h
  · cases h; exact ⟨rfl, by simpa [Spec.UINT64_SIZE] using ‹_›⟩
  · cases h

theorem uint64Mod_eq {a b s : Nat} (h : Spec.uint64Mod a b = .ok s) : s = a % b ∧ b ≠ 0 := by
  unfold Spec.uint64Mod at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, ‹_›⟩

theorem uint64Div_eq {a b s : Nat} (h : Spec.uint64Div a b = .ok s) : s = a / b ∧ b ≠ 0 := by
  unfold Spec.uint64Div at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, ‹_›⟩


variable [EthCLSpecs.Gloas.Preset] [HasherTag]

omit [EthCLSpecs.Gloas.Preset] in
theorem hash_eq (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d) (d : List UInt8) :
    o.hash d = bytesToRoot (sha (toBA d)) := ho d

/-! ## The shuffle -/

/-- One position of one shuffle round, as Etheorem computes it. -/
def shuffleNext (seedRound : ByteArray) (n pivot cur : Nat) : Nat :=
  let flip := (pivot + n - cur) % n
  let position := max cur flip
  let source := sha (seedRound ++ u32leBytes (position / 256))
  let byteVal := (source.get! ((position % 256) / 8)).toNat
  if (byteVal >>> (position % 8)) % 2 == 1 then flip else cur

omit [EthCLSpecs.Gloas.Preset] in
theorem inner_body_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (seed : Spec.Bytes32) (round : Nat) (n pivot : Nat) (i : Nat) (cur : List Nat)
    {res : ForInStep (List Nat)}
    (h : (do
        let __do_lift ← Spec.uint64Add pivot n
        let __do_lift_1 ← Spec.listGet cur i
        let __do_lift ← Spec.uint64Sub __do_lift __do_lift_1
        let flip ← Spec.uint64Mod __do_lift n
        let __do_lift ← Spec.listGet cur i
        let position : Nat := max __do_lift flip
        let position_bucket ← Spec.uint64Div position 256
        let __do_jp : List Nat → PUnit → Spec.SpecM (ForInStep (List Nat)) := fun indices _ =>
          let source :=
            o.hash (seed.toList ++ Spec.uint_to_bytes 1 round ++ Spec.uint_to_bytes 4 position_bucket)
          do
          let byte_val ← Spec.listGet source.toList (position % 256 / 8)
          let bit : UInt8 := byte_val >>> UInt8.ofNat (position % 8) % 2
          let current ← Spec.listGet indices i
          let r ← Spec.listSet indices i (if (bit != 0) = true then flip else current)
          let indices : List Nat := r
          pure PUnit.unit
          pure (ForInStep.yield indices)
        if ¬position_bucket < 2 ^ 32 then do
            let y ← throw Spec.SpecError.overflow
            __do_jp cur y
          else do
            let y ← pure PUnit.unit
            __do_jp cur y : Spec.SpecM (ForInStep (List Nat))) = .ok res) :
    i < cur.length ∧ pivot + n < 2 ^ 64 ∧
      res = .yield (cur.set i (shuffleNext ((vecToBytes seed).push (UInt8.ofNat round)) n pivot
        cur[i]!)) := by
  simp only [except_bind_eq_ok] at h
  obtain ⟨s, h1, c, h2, d, h3, flip, h4, c', h5, pb, h6, h⟩ := h
  obtain ⟨hi, hc⟩ := listGet_ok h2
  obtain ⟨-, hc'⟩ := listGet_ok h5
  obtain ⟨rfl, hs⟩ := uint64Add_eq h1
  obtain ⟨rfl, hcs⟩ := uint64Sub_eq h3
  obtain ⟨rfl, hn⟩ := uint64Mod_eq h4
  obtain ⟨rfl, -⟩ := uint64Div_eq h6
  rw [hc] at hc'; subst hc'
  split at h
  · exact absurd h throw_bind_ne_ok
  simp only [pure_bind, except_bind_eq_ok] at h
  obtain ⟨bv, hbv, cur', hcur', r, hr, h⟩ := h
  rw [hash_eq o ho, listGet_bytesToRoot _ _ (by omega)] at hbv
  obtain ⟨-, rfl⟩ := listGet_ok hcur'
  obtain ⟨-, rfl⟩ := listSet_ok hr
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨hi, hs, ?_⟩
  rw [Except.ok.injEq] at hbv
  subst hbv
  have hba : toBA (seed.toList ++ Spec.uint_to_bytes 1 round ++
      Spec.uint_to_bytes 4 ((max c ((pivot + n - c) % n)) / 256)) =
      (vecToBytes seed).push (UInt8.ofNat round) ++
        u32leBytes (max c ((pivot + n - c) % n) / 256) := by
    apply ba_eq_of_toList
    simp only [toBA_data, uint_to_bytes_1, uint_to_bytes_4, append_data_toList,
      push_data_toList, vecToBytes_toList, List.append_assoc]
  rw [hba, shuffle_bit_eq _ _ (Nat.mod_lt _ (by decide)), hc]
  rfl


omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
theorem foldl_set_range (g : Nat → Nat) (L : List Nat) :
    ∀ k, k ≤ L.length →
      (List.range k).foldl (fun c i => c.set i (g c[i]!)) L = (L.take k).map g ++ L.drop k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hlen : ((L.take k).map g).length = k := by simp; omega
    have hdrop : L.drop k = L[k] :: L.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
    rw [hdrop]
    have hget : (((L.take k).map g) ++ L[k] :: L.drop (k + 1))[k]! = L[k] := by
      rw [getElem!_pos _ k (by simp; omega)]
      rw [List.getElem_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
    rw [hget, List.set_append_right _ _ (by omega), hlen, Nat.sub_self]
    simp only [List.set_cons_zero]
    rw [List.take_succ_eq_append_getElem (by omega)]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    rfl

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
theorem forIn_range_set_ok {ε : Type} (g : Nat → Nat)
    (f : Nat → List Nat → Except ε (ForInStep (List Nat)))
    (hf : ∀ i cur res, f i cur = .ok res → i < cur.length ∧ res = .yield (cur.set i (g cur[i]!)))
    (L : List Nat) (n : Nat) (hL : L.length = n) {res : List Nat}
    (h : forIn (List.range n) L f = .ok res) :
    res = L.map g := by
  subst hL
  have := forIn_ok_rel (fun b c => b = c) (fun c i => c.set i (g c[i]!)) f
    (by
      intro a b c r hbc hr
      subst hbc
      exact ⟨_, (hf a b r hr).2, rfl⟩)
    (List.range L.length) L L res rfl h
  rw [this, foldl_set_range g L L.length (Nat.le_refl _)]
  simp

/-- One round of Etheorem's `computeShuffledPermutation`. -/
def etheoremRound (seed : ByteArray) (n : Nat) (indices : Array UInt64) (round : Nat) :
    Array UInt64 :=
  let seedRound := seed.push (UInt8.ofNat round)
  let pivot := (le8 (sha seedRound)) % n
  Array.ofFn (n := n) (fun i : Fin n =>
    let cur := (indices[i.val]!).toNat
    let flip := (pivot + n - cur) % n
    let position := Nat.max cur flip
    let source := sha (seedRound ++ u32leBytes (position / 256))
    let byteVal := (source.get! ((position % 256) / 8)).toNat
    let bit := (byteVal >>> (position % 8)) % 2
    if bit == 1 then UInt64.ofNat flip else UInt64.ofNat cur)

theorem computeShuffledPermutation_eq (n : Nat) (seed : ByteArray) :
    EthCLSpecs.Gloas.computeShuffledPermutation n seed =
      if n == 0 then #[] else
        (List.range EthCLSpecs.Gloas.Const.shuffleRoundCount).foldl (etheoremRound seed n)
          (Array.ofFn (n := n) (fun i : Fin n => UInt64.ofNat i.val)) := rfl

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
theorem forIn_first_ok {ε β : Type} (f : Nat → β → Except ε (ForInStep β)) (n : Nat) (b : β)
    {res : β} (hn : 0 < n) (h : forIn (List.range n) b f = .ok res) : ∃ r, f 0 b = .ok r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.forIn_cons, except_bind_eq_ok] at h
  obtain ⟨r, hr, -⟩ := h
  exact ⟨r, hr⟩

omit [EthCLSpecs.Gloas.Preset] in
theorem round_rel (seed : Spec.Bytes32) (n : Nat) (L : List Nat) (A : Array UInt64)
    (hLA : L = A.toList.map UInt64.toNat) (hsize : A.size = n) (round pivot : Nat)
    (hpivot : pivot = le8 (sha ((vecToBytes seed).push (UInt8.ofNat round))) % n)
    (hbound : n = 0 ∨ n < 2 ^ 64) :
    L.map (shuffleNext ((vecToBytes seed).push (UInt8.ofNat round)) n pivot) =
      (etheoremRound (vecToBytes seed) n A round).toList.map UInt64.toNat := by
  subst hLA hpivot
  apply List.ext_getElem
  · simp [etheoremRound, hsize]
  · intro i h1 h2
    simp only [List.length_map, Array.length_toList] at h1
    simp only [List.getElem_map, Array.getElem_toList, etheoremRound, Array.getElem_ofFn]
    rw [getElem!_pos A i h1]
    unfold shuffleNext
    simp only []
    split
    · rw [UInt64.toNat_ofNat_of_lt']
      rcases hbound with h0 | hb
      · omega
      · have := Nat.mod_lt
          (le8 (sha ((vecToBytes seed).push (UInt8.ofNat round))) % n + n - A[i].toNat)
          (show n > 0 by omega)
        simp only [UInt64.size]
        omega
    · simp

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
theorem foldl_flag {α γ : Type} (f : γ → α → γ) (l : List α) (c : γ) (b : Bool) :
    l.foldl (fun (x : γ × Bool) a => (f x.1 a, true)) (c, b) =
      (l.foldl f c, if l = [] then b else true) := by
  induction l generalizing c b with
  | nil => simp
  | cons a l ih => simp [ih]

/-- `compute_shuffled_permutation` equals Etheorem's `computeShuffledPermutation`. -/
theorem compute_shuffled_permutation_ok (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d)
    (hR : EthCLSpecs.Gloas.Const.shuffleRoundCount = p.SHUFFLE_ROUND_COUNT)
    (hR0 : 0 < p.SHUFFLE_ROUND_COUNT)
    (n : Nat) (seed : Spec.Bytes32) {res : List Nat}
    (h : Spec.compute_shuffled_permutation p o n seed = .ok res) :
    res = (EthCLSpecs.Gloas.computeShuffledPermutation n (vecToBytes seed)).toList.map
      UInt64.toNat := by
  unfold Spec.compute_shuffled_permutation at h
  rw [except_bind_eq_ok] at h
  obtain ⟨r, hr, hpure⟩ := h
  rw [except_pure_eq_ok] at hpure
  subst hpure
  let A0 : Array UInt64 := Array.ofFn (n := n) (fun i : Fin n => UInt64.ofNat i.val)
  have hA0 : (n = 0 ∨ n < 2 ^ 64) → List.range n = A0.toList.map UInt64.toNat ∧ A0.size = n := by
    intro hb
    refine ⟨?_, by simp [A0]⟩
    apply List.ext_getElem
    · simp [A0]
    · intro i h1 h2
      simp only [List.length_range] at h1
      simp only [List.getElem_range, List.getElem_map, Array.getElem_toList, A0,
        Array.getElem_ofFn]
      rw [UInt64.toNat_ofNat_of_lt']
      simp only [UInt64.size]; omega
  have key := forIn_ok_rel
    (fun L (c : Array UInt64 × Bool) => L.length = n ∧
      (c.2 = false → L = List.range n ∧ c.1 = A0) ∧
      (c.2 = true → (n = 0 ∨ n < 2 ^ 64) ∧ L = c.1.toList.map UInt64.toNat ∧ c.1.size = n))
    (fun c a => (etheoremRound (vecToBytes seed) n c.1 a, true)) _ ?hf
    (List.range p.SHUFFLE_ROUND_COUNT) (List.range n) (A0, false) r
    ⟨by simp, fun _ => ⟨rfl, rfl⟩, fun h => nomatch h⟩ hr
  case hf =>
    intro round L c res ⟨hlen, hfalse, htrue⟩ hbody
    simp only [] at hbody
    split at hbody
    · exact absurd hbody throw_bind_ne_ok
    simp only [pure_bind, except_bind_eq_ok] at hbody
    obtain ⟨v, hv, pivot, hpiv, r', hr', hfin⟩ := hbody
    have hsr : toBA (seed.toList ++ Spec.uint_to_bytes 1 round) =
        (vecToBytes seed).push (UInt8.ofNat round) := by
      apply ba_eq_of_toList
      simp only [toBA_data, uint_to_bytes_1, push_data_toList, vecToBytes_toList]
    rw [hash_eq o ho, hsr, bytes_to_uint64_take8, Except.ok.injEq] at hv
    subst hv
    obtain ⟨hpv, hn⟩ := uint64Mod_eq hpiv
    have hbody' := fun i cur (res : ForInStep (List Nat)) hb =>
      inner_body_ok (res := res) o ho seed round n pivot i cur hb
    have hbound : n = 0 ∨ n < 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact Or.inl h0
      · obtain ⟨r0, hr0⟩ := forIn_first_ok _ n L hpos hr'
        exact Or.inr (by have := (hbody' 0 L r0 hr0).2.1; omega)
    have hmap := forIn_range_set_ok _ _ (fun i cur res hb =>
      ⟨(hbody' i cur res hb).1, (hbody' i cur res hb).2.2⟩) L n hlen hr'
    simp only [pure, Except.pure, Except.ok.injEq] at hfin
    subst hfin hmap
    have hLA : L = c.1.toList.map UInt64.toNat ∧ c.1.size = n := by
      cases hc : c.2
      · obtain ⟨hL, hc1⟩ := hfalse hc
        rw [hL, hc1]; exact hA0 hbound
      · exact (htrue hc).2
    refine ⟨_, rfl, by simp [hlen], fun h => by simp at h, fun _ => ⟨hbound, ?_, by simp [etheoremRound]⟩⟩
    exact round_rel seed n L c.1 hLA.1 hLA.2 round _ hpv hbound
  rw [foldl_flag] at key
  have hne : List.range p.SHUFFLE_ROUND_COUNT ≠ [] := by
    intro h
    have h' := congrArg List.length h
    simp only [List.length_range, List.length_nil] at h'
    exact absurd h' (Nat.pos_iff_ne_zero.mp hR0)
  simp only [hne, if_false] at key
  obtain ⟨hlen, -, htrue⟩ := key
  obtain ⟨-, hres, -⟩ := htrue trivial
  rw [computeShuffledPermutation_eq, hR]
  by_cases h0 : n = 0
  · subst h0
    simp at hlen
    simp [hlen]
  · simp only [beq_iff_eq, h0, if_false]
    exact hres


/-- `compute_shuffled_index` reads Etheorem's permutation. -/
theorem compute_shuffled_index_ok (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d)
    (hR : EthCLSpecs.Gloas.Const.shuffleRoundCount = p.SHUFFLE_ROUND_COUNT)
    (hR0 : 0 < p.SHUFFLE_ROUND_COUNT)
    (i n : Nat) (seed : Spec.Bytes32) {v : Nat}
    (h : Spec.compute_shuffled_index p o i n seed = .ok v) :
    i < n ∧ v = ((EthCLSpecs.Gloas.computeShuffledPermutation n (vecToBytes seed))[i]!).toNat := by
  unfold Spec.compute_shuffled_index at h
  split at h
  · exact absurd h throw_bind_ne_ok
  rename_i hi
  simp only [Decidable.not_not] at hi
  simp only [pure_bind, except_bind_eq_ok] at h
  obtain ⟨perm, hperm, hget⟩ := h
  rw [compute_shuffled_permutation_ok p o ho hR hR0 n seed hperm] at hget
  obtain ⟨hlt, hv⟩ := listGet_ok hget
  refine ⟨hi, ?_⟩
  rw [← hv]
  simp only [List.length_map, Array.length_toList] at hlt
  rw [getElem!_pos _ i (by simpa using hlt), getElem!_pos _ i hlt]
  simp

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
theorem mapM_ok_map {ε α β : Type} (f : α → Except ε β) (g : α → β) (l : List α) {r : List β}
    (hf : ∀ a ∈ l, ∀ b, f a = .ok b → b = g a) (h : l.mapM f = .ok r) : r = l.map g := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons a l ih =>
    rw [List.mapM_cons, except_bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    rw [except_bind_eq_ok] at h
    obtain ⟨bs, hbs, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [hf a (by simp) b hb, ih (fun a ha b hb => hf a (by simp [ha]) b hb) hbs]
    rfl

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
/-- An array read through the `toNat` map. -/
theorem map_toNat_getElem! (A : Array UInt64) (k : Nat) (hk : k < A.size) :
    (A.toList.map UInt64.toNat)[k]! = (A[k]!).toNat := by
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos A k hk]
  simp

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
/-- An array read through the `toNat` map, at any index. Past the end both read zero. -/
theorem map_toNat_getElem!_all (A : Array UInt64) (k : Nat) :
    (A.toList.map UInt64.toNat)[k]! = (A[k]!).toNat := by
  by_cases hk : k < A.size
  · exact map_toNat_getElem! A k hk
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg A k hk]
    rfl

open EthCLSpecs.Gloas in
/-- The Etheorem preset holds the committee values of `p`. -/
structure CommitteePresetAgrees (p : Spec.Preset) : Prop where
  shuffleRoundCount : Const.shuffleRoundCount = p.SHUFFLE_ROUND_COUNT
  shuffleRoundCountPos : 0 < p.SHUFFLE_ROUND_COUNT
  targetCommitteeSize : Const.targetCommitteeSize = p.TARGET_COMMITTEE_SIZE
  maxCommitteesPerSlot : Const.maxCommitteesPerSlot = p.MAX_COMMITTEES_PER_SLOT
  syncCommitteeSize : Const.syncCommitteeSize = p.SYNC_COMMITTEE_SIZE
  ptcSize : Const.ptcSize = p.PTC_SIZE
  epochsPerSyncCommitteePeriod : Const.epochsPerSyncCommitteePeriod = p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
  maxEffectiveBalanceElectra : Const.maxEffectiveBalanceElectra = p.MAX_EFFECTIVE_BALANCE_ELECTRA


/-! ## The balance weighted selection -/

/-- The selection loop equals Etheorem's `cbwsAux`, one pass at a time. `fuel` is Etheorem's
pass limit and `ourFuel` the reference's. The two agree when Etheorem's result has `size`
items. -/
theorem selection_loop_lockstep (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hc : CommitteePresetAgrees p)
    (idxArr : Array UInt64) (seed : Spec.Bytes32) (size : Nat) (shuffle : Bool)
    (effBals : Array Nat) :
    ∀ (fuel ourFuel : Nat) (sel : Array UInt64) (i : Nat) (rb : Spec.Bytes32) (erb : ByteArray)
      (r : List Nat), i < 2 ^ 64 → (i % 16 = 0 ∨ rb = bytesToRoot erb) →
      Spec.compute_balance_weighted_selection_loop p o (idxArr.toList.map UInt64.toNat) seed size
        shuffle idxArr.size effBals.toList ourFuel (sel.toList.map UInt64.toNat) i rb = .ok r →
      size ≤ (EthCLSpecs.Gloas.cbwsAux (idxArr.map UInt64.toNat) effBals
        (if shuffle then EthCLSpecs.Gloas.computeShuffledPermutation idxArr.size (vecToBytes seed)
          else #[])
        (vecToBytes seed) idxArr.size size shuffle fuel i erb sel).size →
      r = (EthCLSpecs.Gloas.cbwsAux (idxArr.map UInt64.toNat) effBals
        (if shuffle then EthCLSpecs.Gloas.computeShuffledPermutation idxArr.size (vecToBytes seed)
          else #[])
        (vecToBytes seed) idxArr.size size shuffle fuel i erb sel).toList.map UInt64.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro ourFuel sel i rb erb r _ _ h hfull
    simp only [EthCLSpecs.Gloas.cbwsAux] at hfull ⊢
    cases ourFuel with
    | zero => exact absurd h (by simp [Spec.compute_balance_weighted_selection_loop])
    | succ g =>
      unfold Spec.compute_balance_weighted_selection_loop at h
      rw [if_neg (by simp; omega)] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
  | succ f ih =>
    intro ourFuel sel i rb erb r hi hinv h hfull
    cases ourFuel with
    | zero => exact absurd h (by simp [Spec.compute_balance_weighted_selection_loop])
    | succ g =>
    unfold Spec.compute_balance_weighted_selection_loop at h
    unfold EthCLSpecs.Gloas.cbwsAux at hfull ⊢
    split at h
    · rename_i hlt
      simp only [List.length_map, Array.length_toList] at hlt
      rw [if_neg (by omega)] at hfull ⊢
      simp only [except_bind_eq_ok, pure_bind] at h
      obtain ⟨a, ha, off, hoff, ni, hni, h⟩ := h
      obtain ⟨hh, -⟩ := uint64Mod_eq ha; subst hh
      obtain ⟨hh, -⟩ := uint64Mul_eq hoff; subst hh
      obtain ⟨hh, htot⟩ := uint64Mod_eq hni; subst hh
      have hrb : (if (i % 16 * 2 == 0) = true then
            o.hash (Vector.toList seed ++ Spec.uint_to_bytes 8 (i / 16)) else rb) =
          bytesToRoot (if (i % 16 * 2 == 0) = true then
            sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else erb) := by
        split
        · rw [hash_eq o ho]
          congr 2
          apply ba_eq_of_toList
          have h16 : (UInt64.ofNat (i / 16)).toNat = i / 16 :=
            UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
          rw [toBA_data, append_data_toList, vecToBytes_toList, ← uint_to_bytes_8, h16]
        · rename_i h0
          rcases hinv with h1 | h1
          · exfalso; simp at h0; omega
          · exact h1
      rw [hrb] at h
      simp only [] at hfull ⊢
      generalize (if (i % 16 * 2 == 0) = true then
            sha (vecToBytes seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) else erb) = E at h hfull ⊢
      have hoff : i % 16 * 2 + 2 ≤ 32 := by omega
      have hmr : (2 : Nat) ^ 16 - 1 = EthCLSpecs.Gloas.Const.maxRandomValue := rfl
      cases shuffle
      · simp only [Bool.false_eq_true, if_false] at h hfull ⊢
        simp only [except_bind_eq_ok] at h
        obtain ⟨ef, hef, w, hw, rv, hrv, th, hth, h⟩ := h
        obtain ⟨hnx, hef⟩ := listGet_ok hef
        rw [bytes_to_uint64_take2 E _ hoff, Except.ok.injEq] at hrv
        obtain ⟨hh, -⟩ := uint64Mul_eq hw; subst hh
        obtain ⟨hh, -⟩ := uint64Mul_eq hth; subst hh
        subst hrv
        simp only [Array.length_toList] at hnx
        subst hef
        rw [getElem!_pos effBals.toList _ (by simpa using hnx)] at h
        simp only [Array.getElem_toList] at h
        rw [← hmr, hc.maxEffectiveBalanceElectra, getElem!_pos effBals _ hnx] at hfull ⊢
        split at h <;> rename_i hge
        · rw [if_pos hge] at hfull ⊢
          simp only [except_bind_eq_ok] at h
          obtain ⟨x, hx, i1, hi1, h⟩ := h
          obtain ⟨hidx, rfl⟩ := listGet_ok hx
          obtain ⟨hh, hi1'⟩ := uint64Add_eq hi1; subst hh
          simp only [List.length_map, Array.length_toList] at hidx
          have hsel : sel.toList.map UInt64.toNat ++ [(idxArr.toList.map UInt64.toNat)[i % idxArr.size]!] =
              (sel.push (UInt64.ofNat ((idxArr.map UInt64.toNat)[i % idxArr.size]!))).toList.map
                UInt64.toNat := by
            rw [getElem!_pos (idxArr.toList.map UInt64.toNat) _ (by simpa using hidx),
              getElem!_pos (idxArr.map UInt64.toNat) _ (by simpa using hidx)]
            simp
          rw [hsel] at h
          exact ih _ _ _ _ _ _ hi1' (Or.inr rfl) h hfull
        · rw [if_neg hge] at hfull ⊢
          simp only [except_bind_eq_ok] at h
          obtain ⟨i1, hi1, h⟩ := h
          obtain ⟨hh, hi1'⟩ := uint64Add_eq hi1; subst hh
          exact ih _ _ _ _ _ _ hi1' (Or.inr rfl) h hfull
      · simp only [if_true] at h hfull ⊢
        simp only [except_bind_eq_ok] at h
        obtain ⟨nx, hnx, ef, hef, w, hw, rv, hrv, th, hth, h⟩ := h
        obtain ⟨-, hnx⟩ := compute_shuffled_index_ok p o ho hc.shuffleRoundCount
          hc.shuffleRoundCountPos _ _ seed hnx
        subst hnx
        obtain ⟨hnx, hef⟩ := listGet_ok hef
        rw [bytes_to_uint64_take2 E _ hoff, Except.ok.injEq] at hrv
        obtain ⟨hh, -⟩ := uint64Mul_eq hw; subst hh
        obtain ⟨hh, -⟩ := uint64Mul_eq hth; subst hh
        subst hrv
        simp only [Array.length_toList] at hnx
        subst hef
        rw [getElem!_pos effBals.toList _ (by simpa using hnx)] at h
        simp only [Array.getElem_toList] at h
        rw [← hmr, hc.maxEffectiveBalanceElectra, getElem!_pos effBals _ hnx] at hfull ⊢
        split at h <;> rename_i hge
        · rw [if_pos hge] at hfull ⊢
          simp only [except_bind_eq_ok] at h
          obtain ⟨x, hx, i1, hi1, h⟩ := h
          obtain ⟨hidx, rfl⟩ := listGet_ok hx
          obtain ⟨hh, hi1'⟩ := uint64Add_eq hi1; subst hh
          simp only [List.length_map, Array.length_toList] at hidx
          generalize ((EthCLSpecs.Gloas.computeShuffledPermutation idxArr.size (vecToBytes seed))[
            i % idxArr.size]!).toNat = k at h hidx hfull ⊢
          have hsel : sel.toList.map UInt64.toNat ++ [(idxArr.toList.map UInt64.toNat)[k]!] =
              (sel.push (UInt64.ofNat ((idxArr.map UInt64.toNat)[k]!))).toList.map
                UInt64.toNat := by
            rw [getElem!_pos (idxArr.toList.map UInt64.toNat) _ (by simpa using hidx),
              getElem!_pos (idxArr.map UInt64.toNat) _ (by simpa using hidx)]
            simp
          rw [hsel] at h
          exact ih _ _ _ _ _ _ hi1' (Or.inr rfl) h hfull
        · rw [if_neg hge] at hfull ⊢
          simp only [except_bind_eq_ok] at h
          obtain ⟨i1, hi1, h⟩ := h
          obtain ⟨hh, hi1'⟩ := uint64Add_eq hi1; subst hh
          exact ih _ _ _ _ _ _ hi1' (Or.inr rfl) h hfull
    · rename_i hlt
      simp only [List.length_map, Array.length_toList] at hlt
      rw [if_pos (by omega)]
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h.symm

/-- `compute_balance_weighted_selection` equals Etheorem's when Etheorem's result is full.

Etheorem stops after `10^7` passes. pyspec loops until it has `size` items. So the two agree
when Etheorem's result has `size` items. -/
theorem compute_balance_weighted_selection_ok (p : Spec.Preset) (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hc : CommitteePresetAgrees p) (e : EState)
    (idxArr : Array UInt64) (seed : Spec.Bytes32) (size : Nat) (shuffle : Bool) {r : List Nat}
    (hfull : size ≤ (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) idxArr
      (vecToBytes seed) size shuffle).size)
    (h : Spec.compute_balance_weighted_selection p o (absEState e) (idxArr.toList.map UInt64.toNat)
      seed size shuffle = .ok r) :
    r = (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) idxArr (vecToBytes seed)
      size shuffle).toList.map UInt64.toNat := by
  unfold Spec.compute_balance_weighted_selection at h
  simp only [] at h
  split at h
  · exact absurd h throw_bind_ne_ok
  simp only [pure_bind, except_bind_eq_ok] at h
  obtain ⟨effs, heffs, h⟩ := h
  have heffs' := mapM_ok_map _
    (fun v => (e.validators.val[v]!).effectiveBalance.toNat) _ ?hf heffs
  case hf =>
    intro v _ b hb
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨val, hval, rfl⟩ := hb
    simp only [absEState_validators] at hval
    obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator v hval
    rfl
  subst heffs'
  unfold EthCLSpecs.Gloas.computeBalanceWeightedSelection at hfull ⊢
  simp only [view_uncachedBox] at hfull ⊢
  have heff : (idxArr.toList.map UInt64.toNat).map
      (fun v => (e.validators.val[v]!).effectiveBalance.toNat) =
      (idxArr.map (fun vi => (e.validators[vi.toNat]!).effectiveBalance.toNat)).toList := by
    simp [sszList_getElem!_val]
  rw [heff] at h
  simp only [List.length_map, Array.length_toList] at h
  exact selection_loop_lockstep p o ho hc idxArr seed size shuffle _ _ _ #[] 0 _ _ r
    (by decide) (Or.inl rfl) h hfull
/-! ## Seeds and committees -/

section Seeds

variable [EthCLSpecs.Gloas.Config] {p : Spec.Preset} (hp : PresetAgrees p)
include hp

/-- `get_seed` equals Etheorem's `getSeed`. `domBA` is the domain as Etheorem stores it. -/
theorem get_seed_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d) (e : EState)
    (epoch : UInt64) (dom : Spec.DomainType) (domBA : ByteArray)
    (hdom : dom.toList = domBA.data.toList) {s : Spec.Bytes32}
    (h : Spec.get_seed p o (absEState e) epoch.toNat dom = .ok s) :
    s = EthCLSpecs.Gloas.getSeed (pureState e) epoch domBA := by
  have hlt := EthCLSpecs.Gloas.Const.epochsPerHistoricalVectorLt
  have hpos := EthCLSpecs.Gloas.Const.epochsPerHistoricalVectorPos
  have hE : (UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerHistoricalVector).toNat =
      p.EPOCHS_PER_HISTORICAL_VECTOR := by
    rw [UInt64.toNat_ofNat_of_lt' hlt, hp.epochsPerHistoricalVector]
  unfold Spec.get_seed Spec.get_randao_mix at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨a, ha, b, hb, c, hc, mix, ⟨idx, hidx, hmix⟩, hs⟩ := h
  rw [except_pure_eq_ok] at hs
  subst hs
  rw [← hE] at ha hidx
  rw [← hp.minSeedLookahead] at hb
  have ha' := uint64Add_ok ha
  rw [← ha'] at hb
  have hb' := uint64Sub_ok hb
  rw [← hb'] at hc
  have hc' := uint64Sub_ok (b := 1) hc
  rw [← hc'] at hidx
  have hidx' := uint64Mod_ok hidx
  subst hidx'
  simp only [absEState_randao_mixes] at hmix
  obtain ⟨hk, hmix⟩ := listGet_ok hmix
  subst hmix
  unfold EthCLSpecs.Gloas.getSeed
  simp only [view_uncachedBox, vmodGet]
  rw [hash_eq o ho]
  congr 2
  apply ba_eq_of_toList
  simp only [toBA_data, append_data_toList, hdom, uint_to_bytes_8]
  congr 2
  simp only [Vector.length_toList] at hk
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp


/-- `get_committee_count_per_slot` equals Etheorem's. -/
theorem get_committee_count_per_slot_ok (hc : CommitteePresetAgrees p) (e : EState)
    (epoch : UInt64) {c : Nat}
    (h : Spec.get_committee_count_per_slot p (absEState e) epoch.toNat = .ok c) :
    c = EthCLSpecs.Gloas.getCommitteeCountPerSlot (pureState e) epoch := by
  unfold Spec.get_committee_count_per_slot at h
  simp only [except_bind_eq_ok, except_pure_eq_ok] at h
  obtain ⟨a, ha, b, hb, hc'⟩ := h
  obtain ⟨hh, -⟩ := uint64Div_eq ha; subst hh
  obtain ⟨hh, -⟩ := uint64Div_eq hb; subst hh
  subst hc'
  unfold EthCLSpecs.Gloas.getCommitteeCountPerSlot
  rw [get_active_validator_indices_eq hp, hc.maxCommitteesPerSlot, hc.targetCommitteeSize,
    hp.slotsPerEpoch]
  simp only [List.length_map, Array.length_toList]

omit [EthCLSpecs.Gloas.Config] hp in
/-- `compute_committee` equals Etheorem's `computeCommittee`. -/
theorem compute_committee_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hc : CommitteePresetAgrees p) (A : Array UInt64) (seed : Spec.Bytes32) (index count : Nat)
    {r : List Nat}
    (h : Spec.compute_committee p o (A.toList.map UInt64.toNat) seed index count = .ok r) :
    r = (EthCLSpecs.Gloas.computeCommittee A seed index count).toList.map UInt64.toNat := by
  unfold Spec.compute_committee at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨a, ha, start, hs, c, hc1, b, hb, stop, hstop, h⟩ := h
  obtain ⟨hh, -⟩ := uint64Mul_eq ha; subst hh
  obtain ⟨hh, -⟩ := uint64Div_eq hs; subst hh
  obtain ⟨hh, -⟩ := uint64Add_eq hc1; subst hh
  obtain ⟨hh, -⟩ := uint64Mul_eq hb; subst hh
  obtain ⟨hh, -⟩ := uint64Div_eq hstop; subst hh
  have hr := mapM_ok_map _ (fun i => (A.toList.map UInt64.toNat)[((EthCLSpecs.Gloas.computeShuffledPermutation
      A.size (vecToBytes seed))[i]!).toNat]!) _ ?hf h
  case hf =>
    intro i _ w hw
    simp only [except_bind_eq_ok] at hw
    obtain ⟨v, hv, hw⟩ := hw
    simp only [List.length_map, Array.length_toList] at hv
    obtain ⟨-, rfl⟩ := compute_shuffled_index_ok p o ho hc.shuffleRoundCount hc.shuffleRoundCountPos
      i A.size seed hv
    exact (listGet_ok hw).2.symm
  subst hr
  unfold EthCLSpecs.Gloas.computeCommittee
  simp only [List.length_map, Array.length_toList, Array.toList_map, Array.toList_range,
    List.map_map, List.range'_eq_map_range]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [map_toNat_getElem!_all]
  rfl

/-- `get_beacon_committee` equals Etheorem's `getBeaconCommittee`. -/
theorem get_beacon_committee_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hc : CommitteePresetAgrees p) (e : EState) (slot : UInt64) (index : Nat) {r : List Nat}
    (h : Spec.get_beacon_committee p o (absEState e) slot.toNat index = .ok r) :
    r = (EthCLSpecs.Gloas.getBeaconCommittee (pureState e) slot index).toList.map
      UInt64.toNat := by
  unfold Spec.get_beacon_committee at h
  rw [compute_epoch_at_slot_eq hp] at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨ep, hep, cps, hcps, seed, hseed, a3, h3, a4, h4, a5, h5, a6, h6, h⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hcps' := get_committee_count_per_slot_ok hp hc e _ hcps
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Gloas.Const.domainBeaconAttester rfl hseed
  obtain ⟨hh, -⟩ := uint64Mod_eq h3; subst hh
  obtain ⟨hh, -⟩ := uint64Mul_eq h4; subst hh
  obtain ⟨hh, -⟩ := uint64Add_eq h5; subst hh
  obtain ⟨hh, -⟩ := uint64Mul_eq h6; subst hh
  subst hcps' hseed'
  rw [get_active_validator_indices_eq hp] at h
  rw [compute_committee_ok o ho hc _ _ _ _ h]
  unfold EthCLSpecs.Gloas.getBeaconCommittee
  have hlt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hlt, hp.slotsPerEpoch]
end Seeds

end EpochProofs.Etheorem
