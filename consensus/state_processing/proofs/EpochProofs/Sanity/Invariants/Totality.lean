import EpochProofs.Sanity.Invariants.LighthouseOrder
import EpochProofs.Spec.PresetCfg

/-!
# The spec epoch succeeds on reachable states

`SameOk` says that the Lighthouse model returns `ok v` exactly when the spec returns `ok v`. This
file proves the other half of liveness: the spec `process_epoch` returns `ok` at the last slot
of an epoch, on mainnet.

Each step gets a lemma of the form "the step returns `ok`, and the facts that the next steps
read still hold". `process_epoch_total` chains them. The per-validator steps and the pending
deposits are the hypotheses `MidOk` and `DepOk`, which `TotalityRows.lean` proves. The committee
steps are the hypothesis `CommitteesOk`, which `TotalityCommittees.lean` proves.

Error sources and why they do not fire:
- `get_block_root` computes `start_slot + SLOTS_PER_HISTORICAL_ROOT`. This raises when the slot
  is within `8192` of `2^64`, so the chain needs `slot + 8192 < 2^64`.
- The vector reads (`block_roots`, `randao_mixes`, `slashings`, `justification_bits`) need the
  SSZ lengths (`VectorLengths`). The Lean state holds the vectors as lists.
- The balance sums stay below `2^64` because the effective balance total is below `2^60`
  (`EpochSupply`), and a consolidation moves balance without raising the sum
  (`process_pending_consolidations_total`).
- `apply_pending_deposit` raises only if a balance plus the deposit passes `2^64`
  (`apply_pending_deposit_total`).
-/

namespace EpochProofs.Spec

/-! ## Success of `SpecM` values -/

/-- `x` returns `ok` with a value that has `P`. -/
def OkWith {α : Type} (x : SpecM α) (P : α → Prop) : Prop := ∃ v, x = .ok v ∧ P v

theorem OkWith.pure {α : Type} {a : α} {P : α → Prop} (h : P a) : OkWith (pure a : SpecM α) P :=
  ⟨a, rfl, h⟩

theorem OkWith.of_eq {α : Type} {x : SpecM α} {a : α} {P : α → Prop} (hx : x = .ok a) (h : P a) :
    OkWith x P :=
  ⟨a, hx, h⟩

theorem OkWith.bind {α β : Type} {x : SpecM α} {f : α → SpecM β} {P : α → Prop} {Q : β → Prop}
    (hx : OkWith x P) (hf : ∀ a, P a → OkWith (f a) Q) : OkWith (x >>= f) Q := by
  obtain ⟨a, ha, hp⟩ := hx
  obtain ⟨b, hb, hq⟩ := hf a hp
  exact ⟨b, by rw [ha]; exact hb, hq⟩

theorem OkWith.mono {α : Type} {x : SpecM α} {P Q : α → Prop} (h : OkWith x P)
    (hpq : ∀ a, P a → Q a) : OkWith x Q := by
  obtain ⟨a, ha, hp⟩ := h
  exact ⟨a, ha, hpq a hp⟩

theorem tot_add {a b : Nat} (h : a + b < 2 ^ 64) : uint64Add a b = .ok (a + b) := by
  unfold uint64Add UINT64_SIZE; rw [if_pos h]; rfl

theorem tot_sub {a b : Nat} (h : b ≤ a) : uint64Sub a b = .ok (a - b) := by
  simp [uint64Sub, h, pure, Except.pure]

theorem tot_mul {a b : Nat} (h : a * b < 2 ^ 64) : uint64Mul a b = .ok (a * b) := by
  unfold uint64Mul UINT64_SIZE; rw [if_pos h]; rfl

theorem tot_div {a b : Nat} (h : b ≠ 0) : uint64Div a b = .ok (a / b) := by
  simp [uint64Div, h, pure, Except.pure]

theorem tot_mod {a b : Nat} (h : b ≠ 0) : uint64Mod a b = .ok (a % b) := by
  simp [uint64Mod, h, pure, Except.pure]

theorem tot_get {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    listGet l i = .ok l[i] := by
  simp [listGet, List.getElem?_eq_getElem h, pure, Except.pure]

theorem tot_set {α : Type} {l : List α} {i : Nat} (a : α) (h : i < l.length) :
    listSet l i a = .ok (l.set i a) := by
  simp [listSet, h, pure, Except.pure]

/-- A `for` loop whose body always returns `ok` returns `ok`. -/
theorem forIn_total {α β : Type} (l : List α) (b : β) (f : α → β → SpecM (ForInStep β))
    (hf : ∀ a ∈ l, ∀ b, ∃ r, f a b = .ok r) : ∃ r, forIn l b f = .ok r := by
  induction l generalizing b with
  | nil => exact ⟨b, rfl⟩
  | cons x xs ih =>
    rw [List.forIn_cons]
    obtain ⟨r, hr⟩ := hf x (by simp) b
    rw [hr]
    cases r with
    | done c => exact ⟨c, rfl⟩
    | yield c => exact ih c (fun a ha => hf a (by simp [ha]))

/-- A `for` loop whose body always returns `ok` does not return an error. -/
theorem forIn_ne_error {α β : Type} (l : List α) (b : β) (f : α → β → SpecM (ForInStep β))
    (hf : ∀ a ∈ l, ∀ b, ∃ r, f a b = .ok r) (e : SpecError) : forIn l b f ≠ .error e := by
  obtain ⟨r, hr⟩ := forIn_total l b f hf
  rw [hr]; exact fun h => by cases h

/-- `n` names the value of a `Nat` abbreviation, so that `omega` sees a `Nat`. -/
theorem tot_slot_bound [PresetCfg] [PresetCfg.Ok] {x : Nat} (h : x < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 := by
  have := P_slot_epoch_lt h
  omega

theorem tot_current_epoch [PresetCfg] [PresetCfg.Ok] (s : BeaconState) :
    get_current_epoch P s = .ok (s.slot / P.SLOTS_PER_EPOCH) := by
  unfold get_current_epoch compute_epoch_at_slot; exact tot_div (Nat.ne_of_gt P_slots_pos)

theorem tot_previous_epoch [PresetCfg] [PresetCfg.Ok] (s : BeaconState) :
    get_previous_epoch P s = .ok (saturating_sub (s.slot / P.SLOTS_PER_EPOCH) 1) := by
  simp [get_previous_epoch, tot_current_epoch, bind, Except.bind, pure, Except.pure]

theorem tot_quorum_bound [PresetCfg] [PresetCfg.Ok] {x : Nat} (h : x < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH * 6 < 2 ^ 64 := by
  obtain ⟨S, R, hS, -, hS6, -, -⟩ := P_slots_nat
  rw [hS]
  have h1 : x / S ≤ x / 6 := Nat.div_le_div_left hS6 (by decide)
  have h2 : x / 6 * 6 ≤ x := Nat.div_mul_le_self x 6
  have h' : x < 18446744073709551616 := h
  show x / S * 6 < 18446744073709551616
  have : x / S * 6 ≤ x / 6 * 6 := Nat.mul_le_mul_right _ h1
  omega

/-! ## The resets and the participation rotation -/

/-- `process_eth1_data_reset` succeeds and writes only `eth1_data_votes`. -/
theorem process_eth1_data_reset_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hslot : s.slot < 2 ^ 64) :
    OkWith (process_eth1_data_reset P s)
      (fun s' => s' = s ∨ s' = { s with eth1_data_votes := [] }) := by
  have hadd : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 := tot_slot_bound hslot
  unfold process_eth1_data_reset
  rw [tot_current_epoch]
  simp only [bind, Except.bind, tot_add hadd, tot_mod (Nat.ne_of_gt P_eth1_period_pos)]
  split
  · exact OkWith.pure (Or.inr rfl)
  · exact OkWith.pure (Or.inl rfl)

/-- `process_slashings_reset` succeeds and keeps the length of `slashings`. -/
theorem process_slashings_reset_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hslot : s.slot < 2 ^ 64)
    (hlen : s.slashings.length = P.EPOCHS_PER_SLASHINGS_VECTOR) :
    OkWith (process_slashings_reset P s)
      (fun s' => ∃ i a, s' = { s with slashings := s.slashings.set i a }) := by
  have hadd : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 := tot_slot_bound hslot
  have hlt : (s.slot / P.SLOTS_PER_EPOCH + 1) % P.EPOCHS_PER_SLASHINGS_VECTOR <
      s.slashings.length := by rw [hlen]; exact Nat.mod_lt _ P_slashings_vector_pos
  unfold process_slashings_reset
  rw [tot_current_epoch]
  simp only [bind, Except.bind, tot_add hadd,
    tot_mod (Nat.ne_of_gt P_slashings_vector_pos)]
  rw [tot_set 0 hlt]
  exact OkWith.pure ⟨_, _, rfl⟩

/-- `process_randao_mixes_reset` succeeds and keeps the length of `randao_mixes`. -/
theorem process_randao_mixes_reset_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hslot : s.slot < 2 ^ 64)
    (hlen : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR) :
    OkWith (process_randao_mixes_reset P s)
      (fun s' => ∃ i a, s' = { s with randao_mixes := s.randao_mixes.set i a }) := by
  have hadd : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 := tot_slot_bound hslot
  have hlt : (s.slot / P.SLOTS_PER_EPOCH + 1) % P.EPOCHS_PER_HISTORICAL_VECTOR <
      s.randao_mixes.length := by
    rw [hlen]; exact Nat.mod_lt _ P_historical_vector_pos
  have hlt' : s.slot / P.SLOTS_PER_EPOCH % P.EPOCHS_PER_HISTORICAL_VECTOR <
      s.randao_mixes.length := by
    rw [hlen]; exact Nat.mod_lt _ P_historical_vector_pos
  unfold process_randao_mixes_reset get_randao_mix
  rw [tot_current_epoch]
  simp only [bind, Except.bind, tot_add hadd,
    tot_mod (Nat.ne_of_gt P_historical_vector_pos)]
  simp only [tot_get hlt', tot_set _ hlt]
  exact OkWith.pure ⟨_, _, rfl⟩

/-- `process_historical_summaries_update` succeeds and only appends to
`historical_summaries`. The spec list has no limit in beta.4. -/
theorem process_historical_summaries_update_total [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState)
    (hslot : s.slot < 2 ^ 64) :
    OkWith (process_historical_summaries_update P o s)
      (fun s' => ∃ l, s' = { s with historical_summaries := s.historical_summaries ++ l }) := by
  have hadd : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 := tot_slot_bound hslot
  unfold process_historical_summaries_update
  rw [tot_current_epoch]
  have hR : P.SLOTS_PER_HISTORICAL_ROOT / P.SLOTS_PER_EPOCH ≠ 0 := by
    obtain ⟨S, R, hS, hR, hS6, hSR, -⟩ := P_slots_nat
    rw [hS, hR]
    exact Nat.ne_of_gt (Nat.div_pos (by omega) (by omega))
  simp only [bind, Except.bind, tot_add hadd, tot_div (Nat.ne_of_gt P_slots_pos), tot_mod hR]
  split
  · exact OkWith.pure ⟨_, rfl⟩
  · exact OkWith.pure ⟨[], by simp⟩

/-! ## Builder payments -/

/-- `process_builder_pending_payments` succeeds for any total below `2^64`. -/
theorem process_builder_pending_payments_total [PresetCfg] [PresetCfg.Ok] (tab : Gwei) (htab : tab < 2 ^ 64)
    (s : BeaconState) :
    OkWith (process_builder_pending_payments P tab s)
      (fun s' => ∃ w q, s' = { s with
        builder_pending_withdrawals := w
        builder_pending_payments := q }) := by
  unfold process_builder_pending_payments get_builder_payment_quorum_threshold
  simp only [BUILDER_PAYMENT_THRESHOLD_NUMERATOR, BUILDER_PAYMENT_THRESHOLD_DENOMINATOR]
  rw [tot_div (Nat.ne_of_gt P_slots_pos)]
  simp only [bind, Except.bind]
  rw [tot_mul (tot_quorum_bound htab)]
  simp only [tot_div (show (10 : Nat) ≠ 0 by decide)]
  split
  · rename_i e heq
    exact absurd heq (forIn_ne_error _ _ _ (by intro a _ b; split <;> exact ⟨_, rfl⟩) _)
  · exact OkWith.pure ⟨_, _, rfl⟩

/-! ## Justification and finalization -/

/-- `has_flag` succeeds for the three flag indices. -/
theorem tot_has_flag (flags : ParticipationFlags) (f : Nat) (hf : f < 3) :
    has_flag flags f = .ok (rewardsHasFlag flags f) := by
  have h : 2 ^ f < 256 := by
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl <;> decide
  simp [has_flag, rewardsHasFlag, h, pure, Except.pure]

/-- The flags of a row in the participation list that the spec reads at `epoch`. -/
def rowFlags (epoch current_epoch : Epoch) (r : Row) : ParticipationFlags :=
  if epoch == current_epoch then r.current_participation else r.previous_participation

theorem tot_get_rows_current {state : BeaconState} (hrows : RowsOk state) {r : Row}
    (h : r ∈ rowsOf state) :
    listGet state.current_epoch_participation r.index = .ok r.current_participation := by
  obtain ⟨i, hi, rfl⟩ := mem_rowsOf h
  have hi' : i < state.current_epoch_participation.length := by rw [hrows.2.2.2]; exact hi
  simp [listGet, hi', pure, Except.pure]

/-- `get_unslashed_participating_indices` succeeds at the previous and the current epoch, and
gives the indices of the rows that are active, have the flag and are not slashed. -/
theorem participating_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hrows : RowsOk s) (f : Nat) (hf : f < 3)
    (epoch : Epoch)
    (hepoch : epoch = saturating_sub (s.slot / P.SLOTS_PER_EPOCH) 1 ∨ epoch = s.slot / P.SLOTS_PER_EPOCH) :
    get_unslashed_participating_indices P s f epoch =
      .ok (((((rowsOf s).filter fun r => is_active_validator r.validator epoch).filter
        fun r => rewardsHasFlag (rowFlags epoch (s.slot / P.SLOTS_PER_EPOCH) r) f).filter
          fun r => !r.validator.slashed).map (·.index)) := by
  unfold get_unslashed_participating_indices
  have hassert : (epoch == saturating_sub (s.slot / P.SLOTS_PER_EPOCH) 1 || epoch == s.slot / P.SLOTS_PER_EPOCH) = true := by
    rcases hepoch with h | h <;> simp [h]
  simp only [bind, Except.bind, tot_previous_epoch, tot_current_epoch, hassert, Bool.not_true,
    Bool.false_eq_true, if_false, pure, Except.pure, get_active_validator_indices_rows]
  rw [forIn_yield_eq_foldlM (step := filterStep (fun i => do
      has_flag (← listGet (if (epoch == s.slot / P.SLOTS_PER_EPOCH) = true then s.current_epoch_participation
        else s.previous_epoch_participation) i) f) id)]
  rotate_left
  · intro i acc
    simp only [filterStep, bind, Except.bind, pure, Except.pure]
    cases listGet (if (epoch == s.slot / P.SLOTS_PER_EPOCH) = true then s.current_epoch_participation
        else s.previous_epoch_participation) i with
    | error e => rfl
    | ok fl =>
      simp only [tot_has_flag fl f hf]
      cases rewardsHasFlag fl f <;> rfl
  rw [foldlM_filterStep_map,
    foldlM_filterStep_ok _ (fun r => rewardsHasFlag (rowFlags epoch (s.slot / P.SLOTS_PER_EPOCH) r) f)]
  rotate_left
  · intro r hr
    have hr' := (List.mem_filter.mp hr).1
    unfold rowFlags
    by_cases hc : (epoch == s.slot / P.SLOTS_PER_EPOCH) = true
    · simp only [hc, if_true, bind, Except.bind, tot_get_rows_current hrows hr', tot_has_flag _ f hf]
    · simp only [hc, Bool.false_eq_true, if_false, bind, Except.bind, listGet_rows_previous hrows hr',
        tot_has_flag _ f hf]
  simp only [List.nil_append]
  rw [forIn_yield_eq_foldlM (step := filterStep (fun i => do
      pure !(← listGet s.validators i).slashed) id)]
  rotate_left
  · intro i acc
    simp only [filterStep, bind, Except.bind, pure, Except.pure]
    cases listGet s.validators i with
    | error e => rfl
    | ok v =>
      dsimp only
      cases v.slashed <;> rfl
  rw [foldlM_filterStep_map, foldlM_filterStep_ok _ (fun r => !r.validator.slashed)]
  · rfl
  · intro r hr
    have hr' := (List.mem_filter.mp (List.mem_filter.mp hr).1).1
    simp only [bind, Except.bind, listGet_rows_validator hr', pure, Except.pure]

/-- Filtering rows twice more is filtering once with the conjunction. -/
theorem tot_filter3 (l : List Row) (P Q R : Row → Bool) :
    ((l.filter P).filter Q).filter R = l.filter fun r => P r && Q r && R r := by
  simp [List.filter_filter, Bool.and_comm, Bool.and_left_comm]

theorem tot_nat_add_lt {a b c : Nat} (h1 : a ≤ b) (h2 : b < 2 ^ 64) (hc : c ≤ 8192) :
    a + c < 2 ^ 64 + 8192 := by omega

theorem get_block_root_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (e : Epoch)
    (h1 : e * P.SLOTS_PER_EPOCH < s.slot)
    (h2 : s.slot ≤ e * P.SLOTS_PER_EPOCH + P.SLOTS_PER_HISTORICAL_ROOT)
    (hslot : s.slot + 8192 < 2 ^ 64)
    (hbr : s.block_roots.length = P.SLOTS_PER_HISTORICAL_ROOT) :
    ∃ r, get_block_root P s e = .ok r := by
  obtain ⟨S, R, hS, hR, hS6, hSR, hR8⟩ := P_slots_nat
  rw [hS] at h1 h2
  rw [hR] at h2 hbr
  have hm : e * S < 2 ^ 64 := Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.le_add_right _ _)
    (Nat.le_of_lt hslot))
  have ha : e * S + R < 2 ^ 64 := by
    have : e * S + R < s.slot + 8192 := by epoch_omega
    epoch_omega
  have hidx : e * S % R < s.block_roots.length := by rw [hbr]; exact Nat.mod_lt _ (by epoch_omega)
  unfold get_block_root get_block_root_at_slot compute_start_slot_at_epoch
  rw [hS, tot_mul hm]
  have hc1 : (!decide (e * S < s.slot)) = false := by simp [h1]
  have hc2 : (!decide (s.slot ≤ e * S + R)) = false := by simp [h2]
  rw [hR]
  refine ⟨s.block_roots[e * S % R], ?_⟩
  change (Except.bind (Except.ok (e * S)) fun __do_lift => _) = _
  dsimp only [Except.bind]
  rw [hc1]
  rw [if_neg Bool.false_ne_true, tot_add ha]
  rw [pure_bind, show (Except.ok (e * S + R) : SpecM Nat) = pure (e * S + R) from rfl,
    pure_bind, hc2, if_neg Bool.false_ne_true, pure_bind]
  exact tot_get hidx


theorem tot_bind_ok {α β : Type} {a : α} (f : α → SpecM β) : (Except.ok a >>= f) = f a := rfl

theorem tot_epoch_facts {x S R : Nat} (hS : 1 < S) (hSR : 2 * S ≤ R) (hR : R ≤ 8192)
    (hlast : (x + 1) % S = 0) (h64 : 2 * S ≤ x) (hx : x + 8192 < 2 ^ 64) :
    (x / S - 1) * S < x ∧ x ≤ (x / S - 1) * S + R ∧ x / S * S < x ∧
      x ≤ x / S * S + R ∧ saturating_sub (x / S) 1 = x / S - 1 := by
  have hq := Nat.div_add_mod (x + 1) S
  rw [hlast, Nat.add_zero, succ_div_of_mod_eq hlast] at hq
  generalize hqq : x / S = q at hq ⊢
  have hq2 : 2 ≤ q := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have : S * (q + 1) ≤ S * 2 := Nat.mul_le_mul_left S (by omega)
    omega
  have hsub : (q - 1) * S = q * S - S := Nat.sub_one_mul q S
  have hqS : S * (q + 1) = q * S + S := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  have hSq : S ≤ q * S := Nat.le_mul_of_pos_left S (by omega)
  rw [hqS] at hq
  rw [hsub]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  unfold saturating_sub
  rw [if_pos (show q > 1 by omega)]

theorem tot_lt62_mul {a k : Nat} (h : a < 2 ^ 62) (hk : k ≤ 3) : a * k < 2 ^ 64 := by
  have h' : a < 4611686018427387904 := h
  show a * k < 18446744073709551616
  have : a * k ≤ a * 3 := Nat.mul_le_mul_left _ hk
  omega

theorem tot_lt63_add {a k : Nat} (h : a < 2 ^ 63) (hk : k ≤ 3) : a + k < 2 ^ 64 := by
  have h' : a < 9223372036854775808 := h
  show a + k < 18446744073709551616
  omega

theorem tot_set_length {α : Type} (l : List α) (i : Nat) (a : α) :
    (l.set i a).length = l.length := List.length_set

theorem get_block_root_congr [PresetCfg] (t s : BeaconState) (e : Epoch) (h1 : t.slot = s.slot)
    (h2 : t.block_roots = s.block_roots) :
    get_block_root P t e = get_block_root P s e := by
  unfold get_block_root get_block_root_at_slot
  rw [h1, h2]

/-- The justification bits have their `BitVector[4]` length. -/
def BL4 (st : BeaconState) : Prop := st.justification_bits.length = 4

theorem fin_block {P : BeaconState → Prop} (b : Bool) (cp k E : Nat) (hcp : cp + k < 2 ^ 64)
    (A B : BeaconState) (hA : P A) (hB : P B) :
    OkWith (if b = true then (do
        let x ← uint64Add cp k
        if (x == E) = true then pure A else pure B) else pure B) P := by
  split
  · rw [tot_add hcp, tot_bind_ok]
    split
    · exact OkWith.pure hA
    · exact OkWith.pure hB
  · exact OkWith.pure hB

theorem weigh_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (tab pb cb : Gwei) (htab : tab < 2 ^ 62) (hpb : pb < 2 ^ 62)
    (hcb : cb < 2 ^ 62) (hslot : s.slot + 8192 < 2 ^ 64) (h64 : 2 * P.SLOTS_PER_EPOCH ≤ s.slot)
    (hlast : (s.slot + 1) % P.SLOTS_PER_EPOCH = 0)
    (hbr : s.block_roots.length = P.SLOTS_PER_HISTORICAL_ROOT)
    (hbits : s.justification_bits.length = 4)
    (hcp : s.previous_justified_checkpoint.epoch < 2 ^ 63 ∧
      s.current_justified_checkpoint.epoch < 2 ^ 63) :
    OkWith (weigh_justification_and_finalization P s tab pb cb)
      (fun s' => s'.justification_bits.length = 4) := by
  obtain ⟨S, R, hS, hR, hS6, hSR, hR8⟩ := P_slots_nat
  have hfacts := tot_epoch_facts (S := P.SLOTS_PER_EPOCH) (R := P.SLOTS_PER_HISTORICAL_ROOT)
    (by rw [hS]; omega) (by rw [hS, hR]; omega) (by rw [hR]; omega) hlast h64 hslot
  obtain ⟨hp1, hp2, hc1, hc2, hsat⟩ := hfacts
  have hb' : (s.justification_bits.take 1 ++
      s.justification_bits.take (JUSTIFICATION_BITS_LENGTH - 1)).length = 4 := by
    simp [hbits, JUSTIFICATION_BITS_LENGTH]
  unfold weigh_justification_and_finalization
  rw [tot_previous_epoch, tot_bind_ok, tot_current_epoch, tot_bind_ok]
  dsimp only
  rw [tot_set _ (by rw [hb']; decide), tot_bind_ok]
  refine OkWith.bind (P := fun st : BeaconState => st.slot = s.slot ∧
    st.block_roots = s.block_roots ∧ st.justification_bits.length = 4) ?_ (fun st1 h1 => ?_)
  · rw [tot_mul (tot_lt62_mul hpb (by decide)), tot_bind_ok,
      tot_mul (tot_lt62_mul htab (by decide)), tot_bind_ok]
    split
    · obtain ⟨r, hr⟩ := get_block_root_total s (s.slot / P.SLOTS_PER_EPOCH - 1) hp1 hp2 hslot hbr
      have hr2 : ∀ t : BeaconState, t.slot = s.slot → t.block_roots = s.block_roots →
          get_block_root P t (s.slot / P.SLOTS_PER_EPOCH - 1) = .ok r := fun t h1 h2 => by
        rw [get_block_root_congr t s _ h1 h2, hr]
      rw [hsat, hr2, tot_bind_ok]
      · rw [tot_set _ (by simp [hb']), tot_bind_ok]
        exact OkWith.pure ⟨rfl, rfl, by simp [hb']⟩
      · rfl
      · rfl
    · exact OkWith.pure ⟨rfl, rfl, by simp [hb']⟩
  · obtain ⟨hs1, hbr1, hl1⟩ := h1
    have hpc : s.previous_justified_checkpoint.epoch + 3 < 2 ^ 64 := tot_lt63_add hcp.1 (le_refl _)
    have hpc2 : s.previous_justified_checkpoint.epoch + 2 < 2 ^ 64 := tot_lt63_add hcp.1 (by decide)
    have hcc2 : s.current_justified_checkpoint.epoch + 2 < 2 ^ 64 := tot_lt63_add hcp.2 (by decide)
    have hcc1 : s.current_justified_checkpoint.epoch + 1 < 2 ^ 64 := tot_lt63_add hcp.2 (by decide)
    refine OkWith.bind (P := BL4) ?_ (fun st2 h2 => ?_)
    · rw [tot_mul (tot_lt62_mul hcb (by decide)), tot_bind_ok,
        tot_mul (tot_lt62_mul htab (by decide)), tot_bind_ok]
      split
      · obtain ⟨r, hr⟩ := get_block_root_total s (s.slot / P.SLOTS_PER_EPOCH) hc1 hc2 hslot hbr
        rw [get_block_root_congr st1 s _ hs1 hbr1, hr, tot_bind_ok,
          tot_set _ (by rw [hl1]; decide), tot_bind_ok]
        exact OkWith.pure (by simp [BL4, hl1])
      · exact OkWith.pure hl1
    · refine OkWith.bind (fin_block (P := BL4) _ _ _ _ hpc _ _ h2 h2) (fun st3 h3 => ?_)
      refine OkWith.bind (fin_block (P := BL4) _ _ _ _ hpc2 _ _ h3 h3) (fun st4 h4 => ?_)
      refine OkWith.bind (fin_block (P := BL4) _ _ _ _ hcc2 _ _ h4 h4) (fun st5 h5 => ?_)
      exact fin_block (P := BL4) _ _ _ _ hcc1 _ _ h5 h5

theorem tot_sum_filter_le {α : Type} (P : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter P).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hp : P x <;> simp [hp] <;> omega

theorem tot_rows_sum_le [PresetCfg] (s : BeaconState) (Q : Row → Bool) :
    (((rowsOf s).filter Q).map (·.validator.effective_balance)).sum ≤ totalEffectiveBalance s := by
  have h := tot_sum_filter_le Q (·.validator.effective_balance) (rowsOf s)
  have hm : (rowsOf s).map (·.validator.effective_balance) = s.validators.map (·.effective_balance) := by
    rw [← rowsOf_map_validator s, List.map_map]; rfl
  unfold totalEffectiveBalance
  rw [hm] at h
  exact h

theorem tot_max_lt [PresetCfg] {x : Nat} (h : x < 2 ^ 60) : max (P).EFFECTIVE_BALANCE_INCREMENT x < 2 ^ 62 := by
  have h' : x < 1152921504606846976 := h
  show max 1000000000 x < 4611686018427387904
  omega

theorem tot_ge64 [PresetCfg] [PresetCfg.Ok] {x : Nat} (h : ¬ x / P.SLOTS_PER_EPOCH ≤ 1) :
    2 * P.SLOTS_PER_EPOCH ≤ x := by
  obtain ⟨S, R, hS, -, -, -, -⟩ := P_slots_nat
  rw [hS] at h ⊢
  have := Nat.div_mul_le_self x S
  have h2 : 2 ≤ x / S := by omega
  have := Nat.mul_le_mul_right S h2
  omega

theorem process_justification_and_finalization_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hrows : RowsOk s)
    (hslot : s.slot + 8192 < 2 ^ 64) (hlast : (s.slot + 1) % P.SLOTS_PER_EPOCH = 0)
    (hbr : s.block_roots.length = P.SLOTS_PER_HISTORICAL_ROOT)
    (hbits : s.justification_bits.length = 4)
    (hcp : s.previous_justified_checkpoint.epoch < 2 ^ 63 ∧
      s.current_justified_checkpoint.epoch < 2 ^ 63)
    (hsup : totalEffectiveBalance s < 2 ^ 60) :
    OkWith (process_justification_and_finalization P s) BL4 := by
  unfold process_justification_and_finalization
  rw [tot_current_epoch, tot_bind_ok]
  split
  · exact OkWith.pure hbits
  · rename_i hE
    have h64 : 2 * P.SLOTS_PER_EPOCH ≤ s.slot := tot_ge64 (by simpa [GENESIS_EPOCH] using hE)
    have hsup64 : totalEffectiveBalance s < 2 ^ 64 := Nat.lt_trans hsup (by decide)
    dsimp only
    rw [pure_bind, tot_previous_epoch, tot_bind_ok,
      participating_total s hrows TIMELY_TARGET_FLAG_INDEX (by decide) _ (Or.inl rfl), tot_bind_ok,
      tot_bind_ok,
      participating_total s hrows TIMELY_TARGET_FLAG_INDEX (by decide) _ (Or.inr rfl), tot_bind_ok]
    obtain ⟨t, ht, -, htle⟩ := get_total_active_balance_bounds P s _
      (tot_current_epoch s) hsup64
    rw [ht, tot_bind_ok, tot_filter3, get_total_balance_rows _ _ _ hsup64, tot_bind_ok,
      tot_filter3, get_total_balance_rows _ _ _ hsup64, tot_bind_ok]
    exact weigh_total s _ _ _
      (Nat.lt_of_le_of_lt htle (tot_max_lt hsup))
      (tot_max_lt (Nat.lt_of_le_of_lt (tot_rows_sum_le s _) hsup))
      (tot_max_lt (Nat.lt_of_le_of_lt (tot_rows_sum_le s _) hsup))
      hslot h64 hlast hbr hbits hcp

/-! ## Passes over rows -/

/-- A pass whose step succeeds on every row succeeds. -/
theorem passM_total {A R : Type} (f : A → R → SpecM (A × R)) (rows : List R)
    (hf : ∀ a r, r ∈ rows → ∃ x, f a r = .ok x) (a : A) : ∃ y, passM f a rows = .ok y := by
  induction rows generalizing a with
  | nil => exact ⟨_, rfl⟩
  | cons r rs ih =>
    obtain ⟨x, hx⟩ := hf a r (by simp)
    obtain ⟨y, hy⟩ := ih (fun a r' h => hf a r' (by simp [h])) x.1
    exact ⟨_, by rw [passM_cons, hx, tot_bind_ok, hy, tot_bind_ok]; rfl⟩

/-! ## Effective balance updates -/

theorem tot_hysteresis [PresetCfg] : hysteresisThresholds P = .ok (250000000, 1250000000) :=
  hysteresisThresholds_mainnet

theorem tot_lt63_add_small {a k : Nat} (h : a < 2 ^ 63) (hk : k ≤ 1250000000) : a + k < 2 ^ 64 := by
  have h' : a < 9223372036854775808 := h
  show a + k < 18446744073709551616
  omega

theorem newEffectiveBalance_total [PresetCfg] (v : Validator) (b : Gwei) (hb : b < 2 ^ 63)
    (hv : v.effective_balance < 2 ^ 63) :
    ∃ e, newEffectiveBalance P 250000000 1250000000 v b = .ok e := by
  unfold newEffectiveBalance
  rw [tot_add (tot_lt63_add_small hb (by decide)), tot_bind_ok]
  have hup := tot_add (tot_lt63_add_small hv (le_refl _))
  split
  · rw [pure_bind, tot_mod (by pdecide), tot_bind_ok, tot_sub (Nat.mod_le _ _), tot_bind_ok]
    exact ⟨_, rfl⟩
  · rw [hup, tot_bind_ok, pure_bind]
    dsimp only
    split
    · rw [tot_mod (by pdecide), tot_bind_ok, tot_sub (Nat.mod_le _ _), tot_bind_ok]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- `process_effective_balance_updates` succeeds when the balances and the effective balances
are below `2^63`. It changes only `validators`, and keeps their number. -/
theorem process_effective_balance_updates_total [PresetCfg] (s : BeaconState) (hrows : RowsOk s)
    (hb : ∀ b ∈ s.balances, b < 2 ^ 63) (hv : ∀ v ∈ s.validators, v.effective_balance < 2 ^ 63) :
    OkWith (process_effective_balance_updates P s)
      (fun s' => ∃ vs : List Validator, vs.length = s.validators.length ∧
        s' = { s with validators := vs }) := by
  rw [process_effective_balance_updates_rows P s _ _ tot_hysteresis hrows]
  obtain ⟨y, hy⟩ := passM_total (effectiveBalanceRowStep P 250000000 1250000000)
    (rowsOf s) (fun a r hr => by
      have hrb : r.balance ∈ s.balances := by
        rw [← rowsOf_map_balance s hrows.1]; exact List.mem_map_of_mem hr
      have hrv : r.validator ∈ s.validators := by
        rw [← rowsOf_map_validator s]; exact List.mem_map_of_mem hr
      obtain ⟨e, he⟩ := newEffectiveBalance_total r.validator r.balance (hb _ hrb)
        (hv _ hrv)
      exact ⟨_, by simp only [effectiveBalanceRowStep, he, tot_bind_ok]; rfl⟩) ()
  rw [hy]
  refine ⟨_, rfl, ?_⟩
  have hb2 := passM_map_eq _ (·.balance) (fun a r x hx => by
    rw [effectiveBalanceRowStep_preserves _ _ _ a r x hx]) () (rowsOf s) y hy
  have hs2 := passM_map_eq _ (·.inactivity_score) (fun a r x hx => by
    rw [effectiveBalanceRowStep_preserves _ _ _ a r x hx]) () (rowsOf s) y hy
  have hk := passM_rowKey _ (fun a r x h => by
    obtain ⟨u, r'⟩ := x
    rw [effectiveBalanceRowStep_preserves _ _ _ a r _ h]; rfl) () _ y hy
  rw [rowsOf_map_balance s hrows.1] at hb2
  rw [rowsOf_map_inactivity_score s hrows.2.1] at hs2
  refine ⟨y.2.map (·.validator), ?_, ?_⟩
  · have := congrArg List.length hk
    simp only [List.length_map, rowsOf_length] at this
    simpa using this
  · simp only [BeaconState.withRows, hb2, hs2]

/-- The value inside a loop step. -/
def stepVal {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

/-- A `for` loop succeeds if each step succeeds and keeps an invariant. -/
theorem forIn_total_inv {α β : Type} (I : β → Prop) (l : List α) (b : β)
    (f : α → β → SpecM (ForInStep β))
    (hf : ∀ a ∈ l, ∀ b, I b → ∃ r, f a b = .ok r ∧ I (stepVal r)) (hb : I b) :
    ∃ r, forIn l b f = .ok r ∧ I r := by
  induction l generalizing b with
  | nil => exact ⟨b, rfl, hb⟩
  | cons x xs ih =>
    rw [List.forIn_cons]
    obtain ⟨r, hr, hi⟩ := hf x (by simp) b hb
    rw [hr]
    cases r with
    | done c => exact ⟨c, rfl, hi⟩
    | yield c => exact ih c (fun a ha => hf a (by simp [ha])) hi

/-! ## Pending consolidations -/

theorem tot_sum_set_le (l : List Nat) (i : Nat) (a : Nat) (hi : i < l.length) :
    (l.set i a).sum + l[i] = l.sum + a := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp; omega
    | succ j =>
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      have := ih j (by simpa using hi)
      omega

theorem tot_get_le_sum (l : List Nat) (i : Nat) (hi : i < l.length) : l[i] ≤ l.sum := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.sum_cons, List.getElem_cons_succ]
      have := ih j (by simpa using hi)
      omega

theorem OkWith.forIn [PresetCfg] {α β : Type} (I : β → Prop) (l : List α) (b : β)
    (f : α → β → SpecM (ForInStep β))
    (hf : ∀ a ∈ l, ∀ b, I b → ∃ r, f a b = .ok r ∧ I (stepVal r)) (hb : I b) :
    OkWith (forIn l b f) I :=
  forIn_total_inv I l b f hf hb

theorem tot_sat_sub_le {a x : Nat} (h : x ≤ a) : saturating_sub a x = a - x := by
  unfold saturating_sub
  split
  · rfl
  · rename_i hn
    have : a = x := Nat.le_antisymm (Nat.le_of_not_gt hn) h
    subst this; rfl

theorem cons_step (B : List Nat) (i j x : Nat) (hi : i < B.length)
    (hj : j < (B.set i (B[i] - x)).length) (hx : x ≤ B[i]) (hsum : B.sum < 2 ^ 64) :
    (B.set i (B[i] - x))[j] + x < 2 ^ 64 ∧
      ((B.set i (B[i] - x)).set j ((B.set i (B[i] - x))[j] + x)).sum ≤ B.sum := by
  have hs1 := tot_sum_set_le B i (B[i] - x) hi
  have ht := tot_get_le_sum (B.set i (B[i] - x)) j hj
  have hs2 := tot_sum_set_le (B.set i (B[i] - x)) j ((B.set i (B[i] - x))[j] + x) hj
  constructor <;> omega

/-- The loop state of `process_pending_consolidations` is `s` with other balances: the same
number of balances, and a sum that is not larger. -/
def ConsInv (s : BeaconState) (r : MProd Nat BeaconState) : Prop :=
  ∃ B : List Gwei, r.snd = { s with balances := B } ∧ B.length = s.validators.length ∧
    B.sum ≤ s.balances.sum

theorem process_pending_consolidations_total [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (hrows : RowsOk s)
    (hslot : s.slot < 2 ^ 64) (hcr : ConsolidationsInRange s) (hsum : s.balances.sum < 2 ^ 64) :
    OkWith (process_pending_consolidations P s) (fun s' => ∃ (B : List Gwei) (k : Nat),
      s' = { s with balances := B, pending_consolidations := s.pending_consolidations.drop k } ∧
      B.length = s.validators.length ∧ B.sum ≤ s.balances.sum) := by
  unfold process_pending_consolidations
  rw [tot_current_epoch, tot_bind_ok, tot_add (tot_slot_bound hslot), tot_bind_ok]
  dsimp only
  refine OkWith.bind (OkWith.forIn (ConsInv s) _ _ _ (fun c hc b hb => ?_)
    ⟨s.balances, (by prfl), hrows.1, le_refl _⟩) (fun r hr => ?_)
  · obtain ⟨n, st⟩ := b
    obtain ⟨B, hst, hl, hs⟩ := hb
    dsimp only at hst
    subst hst
    have hsrc : c.source_index < s.validators.length := (hcr c hc).1
    have htgt : c.target_index < s.validators.length := (hcr c hc).2
    rw [tot_get hsrc, tot_bind_ok]
    split
    · exact ⟨_, rfl, ⟨B, rfl, hl, hs⟩⟩
    · split
      · exact ⟨_, rfl, ⟨B, rfl, hl, hs⟩⟩
      · rw [pure_bind]
        have hsb : c.source_index < B.length := by rw [hl]; exact hsrc
        rw [tot_get hsb, tot_bind_ok]
        unfold decrease_balance
        rw [tot_get hsb, tot_bind_ok, tot_set _ hsb, tot_bind_ok]
        unfold increase_balance
        have hxle := Nat.min_le_left B[c.source_index] s.validators[c.source_index].effective_balance
        have htb : c.target_index < (B.set c.source_index
            (B[c.source_index] - min B[c.source_index]
              s.validators[c.source_index].effective_balance)).length := by
          rw [List.length_set, hl]; exact htgt
        simp only [tot_sat_sub_le hxle]
        obtain ⟨hlt, hsum2⟩ := cons_step B c.source_index c.target_index _ hsb htb hxle
          (Nat.lt_of_le_of_lt hs hsum)
        rw [tot_get htb, tot_bind_ok, tot_add hlt, tot_bind_ok, tot_set _ htb, tot_bind_ok]
        refine ⟨_, rfl, ⟨_, rfl, ?_, Nat.le_trans hsum2 hs⟩⟩
        rw [List.length_set, List.length_set, hl]
  · obtain ⟨n, st⟩ := r
    obtain ⟨B, hst, hl, hs⟩ := hr
    dsimp only at hst
    subst hst
    exact OkWith.pure ⟨B, n, rfl, hl, hs⟩

/-! ## Pending deposits -/

/-- What `apply_pending_deposit` keeps: the fields that the later steps read, the per-validator
lists, and bounds on the balance and effective balance sums. -/
structure DepStep (s s' : BeaconState) (amount : Gwei) : Prop where
  slot : s'.slot = s.slot
  randao : s'.randao_mixes = s.randao_mixes
  slashings : s'.slashings = s.slashings
  cons : s'.pending_consolidations = s.pending_consolidations
  fin : s'.finalized_checkpoint = s.finalized_checkpoint
  dbtc : s'.deposit_balance_to_consume = s.deposit_balance_to_consume
  pend : s'.pending_deposits = s.pending_deposits
  vlen : s.validators.length ≤ s'.validators.length
  rows : RowsOk s'
  bsum : s'.balances.sum ≤ s.balances.sum + amount
  teb : totalEffectiveBalance s' ≤ totalEffectiveBalance s + amount
  ebs : ∀ v ∈ s'.validators, v ∈ s.validators ∨ v.effective_balance ≤ amount
  pk : s'.validators.map (·.pubkey) = s.validators.map (·.pubkey) ∨
    ∃ v, s'.validators = s.validators ++ [v]

theorem tot_set_or_append {α : Type} (l : List α) (a : α) :
    set_or_append_list l l.length a = .ok (l ++ [a]) := by
  simp [set_or_append_list, pure, Except.pure]

theorem tot_set_or_append_eq {α : Type} (l : List α) (n : Nat) (a : α) (h : l.length = n) :
    set_or_append_list l n a = .ok (l ++ [a]) := by
  subst h; exact tot_set_or_append l a

theorem tot_sum_set_add (B : List Nat) (i : Nat) (hi : i < B.length) (x : Nat) :
    (B.set i (B[i] + x)).sum = B.sum + x := by
  have := tot_sum_set_le B i (B[i] + x) hi
  omega

theorem apply_pending_deposit_total [PresetCfg] (o : Oracle) (s : BeaconState) (d : PendingDeposit)
    (hrows : RowsOk s) (hsum : s.balances.sum + d.amount < 2 ^ 64) :
    OkWith (apply_pending_deposit P o s d) (fun s' => DepStep s s' d.amount) := by
  obtain ⟨h1, h2, h3, h4⟩ := hrows
  unfold apply_pending_deposit
  dsimp only
  split
  · split
    · unfold add_validator_to_registry get_validator_from_deposit get_index_for_new_validator
      rw [tot_mod (by pdecide), tot_bind_ok, tot_sub (Nat.mod_le _ _), tot_bind_ok, pure_bind,
        tot_set_or_append, tot_bind_ok]
      try dsimp only
      rw [tot_set_or_append_eq _ _ _ h1, tot_bind_ok]
      try dsimp only
      rw [tot_set_or_append_eq _ _ _ h3, tot_bind_ok]
      try dsimp only
      rw [tot_set_or_append_eq _ _ _ h4, tot_bind_ok]
      try dsimp only
      rw [tot_set_or_append_eq _ _ _ h2, tot_bind_ok]
      refine OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, ?_, by simp, ?_, ?_,
        Or.inr ⟨_, rfl⟩⟩
      · unfold RowsOk
        exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4]⟩
      · unfold totalEffectiveBalance
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero]
        exact Nat.add_le_add_left (Nat.le_trans (Nat.min_le_left _ _) (Nat.sub_le _ _)) _
      · intro v hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact Or.inl hv
        · exact Or.inr (Nat.le_trans (Nat.min_le_left _ _) (Nat.sub_le _ _))
    · exact OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_refl _, ⟨h1, h2, h3, h4⟩,
        Nat.le_add_right _ _, Nat.le_add_right _ _, fun v hv => Or.inl hv, Or.inl rfl⟩
  · rename_i hmem
    have hlt : (s.validators.map (·.pubkey)).idxOf d.pubkey < s.balances.length := by
      rw [h1, ← List.length_map (f := (·.pubkey))]
      exact List.idxOf_lt_length_iff.mpr (by simpa using hmem)
    unfold increase_balance
    have hb := tot_get_le_sum s.balances _ hlt
    have hadd : s.balances[(s.validators.map (·.pubkey)).idxOf d.pubkey] + d.amount < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right hb _) hsum
    rw [tot_get hlt, tot_bind_ok, tot_add hadd, tot_bind_ok, tot_set _ hlt, tot_bind_ok]
    refine OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_refl _, ?_, ?_, Nat.le_add_right _ _,
      fun v hv => Or.inl hv, Or.inl rfl⟩
    · unfold RowsOk
      exact ⟨by simp [h1], h2, h3, h4⟩
    · exact Nat.le_of_eq (tot_sum_set_add s.balances _ hlt d.amount)

/-! ## The whole epoch -/

/-- The facts that the steps after `process_slashings` read. -/
structure TailFrame [PresetCfg] (t s : BeaconState) : Prop where
  slot : s.slot = t.slot
  rows : RowsOk s
  randao : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR
  slashings : s.slashings.length = P.EPOCHS_PER_SLASHINGS_VECTOR
  cons : ConsolidationsInRange s
  bsum : s.balances.sum < 2 ^ 62
  ebs : ∀ v ∈ s.validators, v.effective_balance < 2 ^ 62
  teb : totalEffectiveBalance s < 2 ^ 62

/-- The facts that the last three steps read: the slot, the RANDAO mixes and the per-validator
lists. -/
structure CommFrame [PresetCfg] (t s : BeaconState) : Prop where
  slot : s.slot = t.slot
  rows : RowsOk s
  randao : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR

/-- The facts that `process_pending_deposits` reads from the state after the per-validator
steps, besides `TailFrame`: the deposit queue and the churn left from the last epoch, the
number of validators, the balance sum after the rewards, and the finalized epoch. -/
structure DepFrame [PresetCfg] (t s : BeaconState) : Prop where
  pend : s.pending_deposits = t.pending_deposits
  dbtc : s.deposit_balance_to_consume = t.deposit_balance_to_consume
  vlen : s.validators.length = t.validators.length
  bsum : s.balances.sum ≤ t.balances.sum + 4 * totalEffectiveBalance t
  teb : totalEffectiveBalance s = totalEffectiveBalance t
  fin : s.finalized_checkpoint.epoch ≤ t.slot / P.SLOTS_PER_EPOCH

/-- The inactivity, rewards, registry and slashings steps succeed after justification and
finalization. `TotalityRows.lean` proves it (`midOk_of_rowBounds`). -/
def MidOk [PresetCfg] (t : BeaconState) : Prop :=
  ∀ s1, JFShape t s1 → s1.finalized_checkpoint.epoch ≤ t.slot / P.SLOTS_PER_EPOCH →
    (t.slot / P.SLOTS_PER_EPOCH ≠ 0 → s1.finalized_checkpoint.epoch + 1 ≤ t.slot / P.SLOTS_PER_EPOCH) →
    OkWith (specFourSteps P s1) (fun s => TailFrame t s ∧ DepFrame t s)

/-- `process_pending_deposits` succeeds after the eth1 data reset. `TotalityRows.lean` proves it
(`depOk_of_rowBounds`). -/
def DepOk [PresetCfg] (o : Oracle) (t : BeaconState) : Prop :=
  ∀ s tab, TailFrame t s → DepFrame t s → get_total_active_balance P s = .ok tab →
    OkWith (process_pending_deposits P tab (apply_pending_deposit P o) s)
      (TailFrame t)

/-- The steps of `process_epoch` before the three committee steps. Its result is the state that
`process_sync_committee_updates` reads. -/
def epochToCommittees (p : Preset) (o : Oracle) (state : BeaconState) : SpecM BeaconState := do
  let state ← process_justification_and_finalization p state
  let state ← process_inactivity_updates p state
  let state ← process_rewards_and_penalties p (← get_total_active_balance p state) state
  let state ← process_registry_updates p (← get_total_active_balance p state) state
  let state ← process_slashings p (← get_total_active_balance p state) state
  let state ← process_eth1_data_reset p state
  let state ←
    process_pending_deposits p (← get_total_active_balance p state) (apply_pending_deposit p o)
      state
  let state ← process_pending_consolidations p state
  let state ← process_builder_pending_payments p (← get_total_active_balance p state) state
  let state ← process_effective_balance_updates p state
  let state ← process_slashings_reset p state
  let state ← process_randao_mixes_reset p state
  let state ← process_historical_summaries_update p o state
  pure (process_participation_flag_updates state)

/-- The three committee steps of `process_epoch`. -/
def committeeSteps (p : Preset) (o : Oracle) (state : BeaconState) : SpecM BeaconState := do
  let state ← process_sync_committee_updates p o state
  let state ← process_proposer_lookahead p o state
  process_ptc_window p o state

/-- `process_epoch` is `epochToCommittees`, then the committee steps. -/
theorem process_epoch_committees (p : Preset) (o : Oracle) (s : BeaconState) :
    process_epoch p o s = epochToCommittees p o s >>= committeeSteps p o := by
  simp only [process_epoch, epochToCommittees, committeeSteps, bind_assoc, pure_bind]

/-- The steps of `epochRest` before the committee steps. -/
def epochRestToCommittees (p : Preset) (o : Oracle) (state : BeaconState) :
    SpecM BeaconState := do
  let state ← process_eth1_data_reset p state
  let state ←
    process_pending_deposits p (← get_total_active_balance p state) (apply_pending_deposit p o)
      state
  let state ← process_pending_consolidations p state
  let state ← process_builder_pending_payments p (← get_total_active_balance p state) state
  let state ← process_effective_balance_updates p state
  let state ← process_slashings_reset p state
  let state ← process_randao_mixes_reset p state
  let state ← process_historical_summaries_update p o state
  pure (process_participation_flag_updates state)

/-- `epochToCommittees` in three parts, as `process_epoch_parts`. -/
theorem epochToCommittees_parts (p : Preset) (o : Oracle) (s : BeaconState) :
    epochToCommittees p o s = (do
      let s1 ← process_justification_and_finalization p s
      let s5 ← specFourSteps p s1
      epochRestToCommittees p o s5) := by
  simp only [epochToCommittees, specFourSteps, epochRestToCommittees, bind_assoc]

/-- The sync committee, proposer lookahead and PTC window steps succeed on the state that
`epochToCommittees` returns. `committeesOk_of` proves it. -/
def CommitteesOk [PresetCfg] (o : Oracle) (t : BeaconState) : Prop :=
  ∀ s, epochToCommittees P o t = .ok s → CommFrame t s → OkWith (committeeSteps P o s)
    (fun _ => True)

theorem tot_cp [PresetCfg] [PresetCfg.Ok] {a b x : Nat} (hab : a ≤ b)
    (hb : b < x / P.SLOTS_PER_EPOCH ∨ b = 0) (hx : x < 2 ^ 64) :
    a < 2 ^ 63 ∧ b < 2 ^ 63 := by
  have := P_slot_epoch_lt hx
  have h63 : x / P.SLOTS_PER_EPOCH < 9223372036854775808 := this
  show a < 9223372036854775808 ∧ b < 9223372036854775808
  omega

theorem tot_lt_of_le_lt {a b c : Nat} (h1 : a ≤ b) (h2 : b < c) : a < c := Nat.lt_of_le_of_lt h1 h2

theorem tot_mem_le_sum {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact tot_get_le_sum l i hi

theorem tot_max_lt64 {x : Nat} (h : x < 2 ^ 62) : max 1000000000 x < 2 ^ 64 := by
  have h' : x < 4611686018427387904 := h
  show max 1000000000 x < 18446744073709551616
  omega

theorem tot_rowsOk_validators {s : BeaconState} (h : RowsOk s) (vs : List Validator)
    (hl : vs.length = s.validators.length) : RowsOk { s with validators := vs } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.trans hl.symm, h2.trans hl.symm, h3.trans hl.symm, h4.trans hl.symm⟩

theorem tot_tab_lt [PresetCfg] [PresetCfg.Ok] (s : BeaconState) (h : totalEffectiveBalance s < 2 ^ 62) :
    ∃ tab, get_total_active_balance P s = .ok tab ∧ tab < 2 ^ 64 := by
  obtain ⟨tab, ht, -, hle⟩ := get_total_active_balance_bounds P s _
    (tot_current_epoch s) (Nat.lt_trans h (by decide))
  exact ⟨tab, ht, Nat.lt_of_le_of_lt hle (tot_max_lt64 h)⟩

/-- The steps before the committee steps succeed on mainnet at the last slot of an epoch, from
the reachable-state facts at the epoch input and the open steps, and keep `CommFrame`. -/
theorem epochToCommittees_total [PresetCfg] [PresetCfg.Ok] (o : Oracle) (t : BeaconState)
    (hrows : RowsOk t)
    (hslot : t.slot + 8192 < 2 ^ 64) (hlast : (t.slot + 1) % P.SLOTS_PER_EPOCH = 0)
    (hvec : t.VectorLengths P) (hffg : FfgInvariant P t)
    (hsup : totalEffectiveBalance t < 2 ^ 60) (hmid : MidOk t) (hdep : DepOk o t) :
    ∃ s, epochToCommittees P o t = .ok s ∧ CommFrame t s := by
  have hslot64 : t.slot < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hslot
  obtain ⟨hbr, -, -, -, hbits, -⟩ := hvec
  have hcp := tot_cp hffg.1.2 hffg.2 hslot64
  rw [epochToCommittees_parts]
  obtain ⟨s1, h1, -⟩ := process_justification_and_finalization_total t hrows hslot hlast hbr hbits
    hcp hsup
  rw [h1, tot_bind_ok]
  have hfin : t.slot / P.SLOTS_PER_EPOCH ≠ 0 → s1.finalized_checkpoint.epoch + 1 ≤ t.slot / P.SLOTS_PER_EPOCH := fun hne =>
    process_justification_and_finalization_finalized _ t s1 _ (tot_current_epoch t)
      (by simpa [GENESIS_EPOCH] using hne) hffg h1
  have hfin0 : s1.finalized_checkpoint.epoch ≤ t.slot / P.SLOTS_PER_EPOCH := by
    rcases process_justification_and_finalization_step _ t s1 h1 with rfl | ⟨h2, -⟩
    · exact hffg.finalized_le
    · have h2' : 2 ≤ t.slot / P.SLOTS_PER_EPOCH := h2
      exact Nat.le_of_succ_le (hfin (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide) h2')))
  obtain ⟨s5, h5, f5, d5⟩ := hmid s1 (process_justification_and_finalization_shape _ t s1 h1)
    hfin0 hfin
  rw [h5, tot_bind_ok]
  unfold epochRestToCommittees
  -- eth1 data reset
  obtain ⟨s6, h6, e6⟩ := process_eth1_data_reset_total s5 (f5.slot ▸ hslot64)
  have f6 : TailFrame t s6 ∧ DepFrame t s6 := by
    rcases e6 with rfl | rfl
    · exact ⟨f5, d5⟩
    · exact ⟨⟨f5.slot, f5.rows, f5.randao, f5.slashings, f5.cons, f5.bsum, f5.ebs, f5.teb⟩,
        ⟨d5.pend, d5.dbtc, d5.vlen, d5.bsum, d5.teb, d5.fin⟩⟩
  rw [h6, tot_bind_ok]
  -- pending deposits
  obtain ⟨tab6, ht6, -⟩ := tot_tab_lt s6 f6.1.teb
  rw [ht6, tot_bind_ok]
  obtain ⟨s7, h7, f7⟩ := hdep s6 tab6 f6.1 f6.2 ht6
  rw [h7, tot_bind_ok]
  -- pending consolidations
  obtain ⟨s8, h8, B, k, rfl, hBl, hBs⟩ := process_pending_consolidations_total s7 f7.rows
    (f7.slot ▸ hslot64) f7.cons (Nat.lt_trans f7.bsum (by decide))
  rw [h8, tot_bind_ok]
  have f8 : TailFrame t { s7 with balances := B, pending_consolidations := s7.pending_consolidations.drop k } :=
    ⟨f7.slot, ⟨hBl, f7.rows.2.1, f7.rows.2.2.1, f7.rows.2.2.2⟩, f7.randao, f7.slashings,
      fun c hc => f7.cons c (List.mem_of_mem_drop hc), Nat.lt_of_le_of_lt hBs f7.bsum, f7.ebs,
      f7.teb⟩
  generalize hs8 : ({ s7 with balances := B, pending_consolidations := s7.pending_consolidations.drop k } : BeaconState) = s8 at f8 ⊢
  -- builder pending payments
  obtain ⟨tab8, ht8, htab8⟩ := tot_tab_lt s8 f8.teb
  rw [ht8, tot_bind_ok]
  obtain ⟨s9, h9, w, q, e9⟩ := process_builder_pending_payments_total tab8 htab8 s8
  rw [h9, tot_bind_ok]
  have g9 : RowsOk s9 ∧ (∀ b ∈ s9.balances, b < 2 ^ 63) ∧
      (∀ v ∈ s9.validators, v.effective_balance < 2 ^ 63) := by
    subst e9
    exact ⟨f8.rows,
      fun b hb => Nat.lt_of_le_of_lt (tot_mem_le_sum hb) (Nat.lt_trans f8.bsum (by decide)),
      fun v hv => Nat.lt_trans (f8.ebs v hv) (by decide)⟩
  have k9 : s9.slot = t.slot ∧ s9.slashings.length = P.EPOCHS_PER_SLASHINGS_VECTOR ∧
      s9.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR := by
    subst e9; exact ⟨f8.slot, f8.slashings, f8.randao⟩
  -- effective balance updates
  obtain ⟨s10, h10, vs, hvs, e10⟩ := process_effective_balance_updates_total s9 g9.1 g9.2.1 g9.2.2
  rw [h10, tot_bind_ok]
  have r10 : RowsOk s10 := by subst e10; exact tot_rowsOk_validators g9.1 vs hvs
  have k10 : s10.slot = t.slot ∧ s10.slashings.length = P.EPOCHS_PER_SLASHINGS_VECTOR ∧
      s10.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR := by subst e10; exact k9
  -- slashings reset
  obtain ⟨s11, h11, i11, a11, e11⟩ := process_slashings_reset_total s10 (k10.1 ▸ hslot64) k10.2.1
  rw [h11, tot_bind_ok]
  have k11 : RowsOk s11 ∧ s11.slot = t.slot ∧ s11.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR := by
    subst e11; exact ⟨r10, k10.1, k10.2.2⟩
  -- RANDAO mixes reset
  obtain ⟨s12, h12, i12, a12, e12⟩ := process_randao_mixes_reset_total s11 (k11.2.1 ▸ hslot64)
    k11.2.2
  rw [h12, tot_bind_ok]
  have k12 : RowsOk s12 ∧ s12.slot = t.slot ∧ s12.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR := by
    subst e12; exact ⟨k11.1, k11.2.1, by simp [k11.2.2]⟩
  -- historical summaries
  obtain ⟨s13, h13, l13, e13⟩ := process_historical_summaries_update_total o s12
    (k12.2.1 ▸ hslot64)
  rw [h13, tot_bind_ok]
  have k13 : RowsOk s13 ∧ s13.slot = t.slot ∧ s13.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR := by
    subst e13; exact k12
  -- participation flags
  exact ⟨_, rfl,
    ⟨k13.2.1, ⟨k13.1.1, k13.1.2.1, k13.1.2.2.2, by simp [process_participation_flag_updates]⟩,
      k13.2.2⟩⟩

/-- The spec `process_epoch` succeeds on mainnet at the last slot of an epoch, from the
reachable-state facts at its input and the open steps. -/
theorem process_epoch_total [PresetCfg] [PresetCfg.Ok] (o : Oracle) (t : BeaconState) (hrows : RowsOk t)
    (hslot : t.slot + 8192 < 2 ^ 64) (hlast : (t.slot + 1) % P.SLOTS_PER_EPOCH = 0)
    (hvec : t.VectorLengths P) (hffg : FfgInvariant P t)
    (hsup : totalEffectiveBalance t < 2 ^ 60) (hmid : MidOk t) (hdep : DepOk o t)
    (hcomm : CommitteesOk o t) :
    ∃ s', process_epoch P o t = .ok s' := by
  obtain ⟨s, hs, hf⟩ := epochToCommittees_total o t hrows hslot hlast hvec hffg hsup hmid hdep
  obtain ⟨s', hs', -⟩ := hcomm s hs hf
  exact ⟨s', by rw [process_epoch_committees, hs, tot_bind_ok]; exact hs'⟩

end EpochProofs.Spec
