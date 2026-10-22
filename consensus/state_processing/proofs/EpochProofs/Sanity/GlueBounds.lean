import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Sanity.Invariants.TotalityRows

/-! # Bounds for the glue error sites of `single_pass.rs`

Each theorem here proves the condition that rules out one group of `?` sites in
`single_pass.rs`. The link from the Rust expression to the formula is listed in
`EpochProofs/Trusted/EpochGlue.lean`. -/

namespace EpochProofs.Spec

/-- Sites 170, 189 (`next_epoch`), 534, 535, 594, 595 and 1356: the current epoch plus 1 or 2
fits in a `u64`. -/
theorem glue_epoch_add_fits {slot : Nat} (h : slot + 8192 < 2 ^ 64) (k : Nat) (hk : k ≤ 2) :
    slot / 32 + k < 2 ^ 64 := by
  have : slot / 32 ≤ slot := Nat.div_le_self _ _
  omega

/-- Site 603: each slot of the lookahead epoch fits in a `u64`. -/
theorem glue_lookahead_slot_fits {slot : Nat} (h : slot + 8192 < 2 ^ 64) (i : Nat) (hi : i < 32) :
    (slot / 32 + 2) * 32 + i < 2 ^ 64 := by
  have : slot / 32 * 32 ≤ slot := Nat.div_mul_le_self _ _
  omega

/-- Sites 549 and 611: `BeaconState::get_seed_mix` at the lookahead epoch. The sum does not
overflow, the two subtractions do not underflow, and the index is in range. -/
theorem glue_seed_mix_index {slot : Nat} (h : slot + 8192 < 2 ^ 64) (len : Nat)
    (hlen : len = 65536) :
    slot / 32 + 2 + 65536 < 2 ^ 64 ∧ 1 + 1 ≤ slot / 32 + 2 + 65536 ∧
      (slot / 32 + 2 + 65536 - 1 - 1) % len < len := by
  have : slot / 32 ≤ slot := Nat.div_le_self _ _
  refine ⟨by omega, by omega, ?_⟩
  subst hlen
  exact Nat.mod_lt _ (by decide)

theorem mapM_length_ok {α β : Type} (f : α → SpecM β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons x xs ih =>
    intro r h
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e => simp only [hxs, bind, Except.bind] at h; cases h
      | ok ys =>
        simp only [hxs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [ih ys hxs]

theorem glue_bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem compute_proposer_indices_length (p : Preset) (o : Oracle) (s : BeaconState) (e : Nat)
    (seed : Bytes32) (indices : List ValidatorIndex) (r : List ValidatorIndex)
    (h : compute_proposer_indices p o s e seed indices = .ok r) :
    r.length = p.SLOTS_PER_EPOCH := by
  unfold compute_proposer_indices at h
  rw [glue_bind_ok_iff] at h
  obtain ⟨st, -, h⟩ := h
  rw [glue_bind_ok_iff] at h
  obtain ⟨seeds, hseeds, h⟩ := h
  rw [mapM_length_ok _ _ _ h, mapM_length_ok _ _ _ hseeds, List.length_range]

theorem get_beacon_proposer_indices_length (p : Preset) (o : Oracle) (s : BeaconState) (e : Nat)
    (r : List ValidatorIndex) (h : get_beacon_proposer_indices p o s e = .ok r) :
    r.length = p.SLOTS_PER_EPOCH := by
  unfold get_beacon_proposer_indices at h
  rw [glue_bind_ok_iff] at h
  obtain ⟨l, -, h⟩ := h
  rw [glue_bind_ok_iff] at h
  obtain ⟨seed, -, h⟩ := h
  exact compute_proposer_indices_length p o s e _ _ r h

/-- Site 564: the spec lookahead keeps its length, so the vector that
`next_proposer_lookahead` returns (`next_proposer_lookahead_spec`) has the length that
`Vector::new` checks. -/
theorem process_proposer_lookahead_length (o : Oracle) (s s' : BeaconState)
    (hlen : s.proposer_lookahead.length = 64)
    (h : process_proposer_lookahead Preset.mainnet o s = .ok s') :
    s'.proposer_lookahead.length = 64 := by
  unfold process_proposer_lookahead at h
  simp only [glue_bind_ok_iff] at h
  obtain ⟨les, hles, ce, -, e1, -, e, -, props, hprops, hfin⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at hfin
  subst hfin
  have h32 : (Preset.mainnet).SLOTS_PER_EPOCH = 32 := rfl
  rw [h32, hlen, tot_sub (show 32 ≤ 64 by omega)] at hles
  cases hles
  have hrl := get_beacon_proposer_indices_length _ _ _ _ _ hprops
  rw [h32] at hrl
  simp only [List.length_append, List.length_take, List.length_drop, hrl, hlen]
  try omega

theorem filter_sum_le (l : List Nat) (q : Nat → Bool) : (l.filter q).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hq : q x
    · simp [hq]; omega
    · simp [hq]; omega

/-- Site 1440: the deposits of one validator sum to less than `2^61`, so the per-validator sum
does not overflow. -/
theorem glue_validator_deposit_sum [PresetCfg] (t : BeaconState) (hb : RowBounds t) (q : Nat → Bool) :
    ((t.pending_deposits.map (·.amount)).filter q).sum < 2 ^ 61 := by
  have key : ∀ a l c : Nat, a + l + c < 2 ^ 61 → l < 2 ^ 61 := by intros; omega
  exact Nat.lt_of_le_of_lt (filter_sum_le _ q) (key _ _ _ hb.funds)

/-- Site 163: the exit cache counts exits per epoch. Each count is at most the number of
validators, which is below `2^40`. -/
theorem glue_exit_count [PresetCfg] (t : BeaconState) (hb : RowBounds t) (q : Validator → Bool) :
    (t.validators.filter q).length < 2 ^ 64 := by
  have h1 := List.length_filter_le q t.validators
  have h2 := hb.count
  have : (2 : Nat) ^ 40 < 2 ^ 64 := by decide
  omega

end EpochProofs.Spec
