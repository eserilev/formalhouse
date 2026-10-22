import EpochProofs.Spec.PresetCfg

/-!
# More facts about the preset values

`PresetCfg.Ok` holds the facts that the epoch proofs up to `Totality` use. The totality proofs
for the per-validator steps and the committee steps need more facts: bounds on the churn
values, the committee sizes and the window lengths. `PresetCfg.Bounds` holds them. Both
presets satisfy them by `decide`.
-/

namespace EpochProofs.Spec

/-- The bounds on the preset values that the totality proofs use. -/
class PresetCfg.Bounds [c : PresetCfg] : Prop where
  slots_le : c.v.SLOTS_PER_EPOCH ≤ 32
  min_churn_ge : 64000000000 ≤ c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  min_churn_le : c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA ≤ 128000000000
  min_churn_inc : c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA % 1000000000 = 0
  churn_quot_pos : 0 < c.v.CHURN_LIMIT_QUOTIENT_GLOAS
  max_act_churn_ge : 128000000000 ≤ c.v.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
  max_act_churn_le : c.v.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS ≤ 256000000000
  consolidation_quot_pos : 0 < c.v.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
  target_committee_pos : 0 < c.v.TARGET_COMMITTEE_SIZE
  target_committee_le : c.v.TARGET_COMMITTEE_SIZE ≤ 128
  max_committees_pos : 0 < c.v.MAX_COMMITTEES_PER_SLOT
  max_committees_le : c.v.MAX_COMMITTEES_PER_SLOT ≤ 64
  shuffle_rounds_le : c.v.SHUFFLE_ROUND_COUNT ≤ 256
  shuffle_rounds_pos : 0 < c.v.SHUFFLE_ROUND_COUNT
  ptc_pos : 0 < c.v.PTC_SIZE
  ptc_le : c.v.PTC_SIZE ≤ 512
  sync_le : c.v.SYNC_COMMITTEE_SIZE ≤ 512
  sync_period_pos : 0 < c.v.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
  sync_period_le : c.v.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≤ 256

theorem mainnetCfg_bounds : @PresetCfg.Bounds mainnetCfg :=
  letI := mainnetCfg
  { slots_le := by decide, min_churn_ge := by decide, min_churn_le := by decide,
    min_churn_inc := by decide, churn_quot_pos := by decide, max_act_churn_ge := by decide,
    max_act_churn_le := by decide, consolidation_quot_pos := by decide,
    target_committee_pos := by decide, target_committee_le := by decide,
    max_committees_pos := by decide, max_committees_le := by decide,
    shuffle_rounds_le := by decide, shuffle_rounds_pos := by decide, ptc_pos := by decide, ptc_le := by decide,
    sync_le := by decide, sync_period_pos := by decide, sync_period_le := by decide }

theorem minimalCfg_bounds : @PresetCfg.Bounds minimalCfg :=
  letI := minimalCfg
  { slots_le := by decide, min_churn_ge := by decide, min_churn_le := by decide,
    min_churn_inc := by decide, churn_quot_pos := by decide, max_act_churn_ge := by decide,
    max_act_churn_le := by decide, consolidation_quot_pos := by decide,
    target_committee_pos := by decide, target_committee_le := by decide,
    max_committees_pos := by decide, max_committees_le := by decide,
    shuffle_rounds_le := by decide, shuffle_rounds_pos := by decide, ptc_pos := by decide, ptc_le := by decide,
    sync_le := by decide, sync_period_pos := by decide, sync_period_le := by decide }

/-- The slots per epoch as a `Nat` with its bounds. -/
theorem P_slots_bounds [PresetCfg] [h : PresetCfg.Ok] [b : PresetCfg.Bounds] :
    ∃ S : Nat, P.SLOTS_PER_EPOCH = S ∧ 6 ≤ S ∧ S ≤ 32 :=
  ⟨_, rfl, h.slots_ge_six, b.slots_le⟩

/-- The epoch of a slot is at most the slot divided by 6. -/
theorem P_epoch_le_div6 [PresetCfg] [PresetCfg.Ok] (x : Nat) : x / P.SLOTS_PER_EPOCH ≤ x / 6 :=
  Nat.div_le_div_left (PresetCfg.Ok.slots_ge_six) (by decide)

/-- The epoch of a slot times the slots per epoch is at most the slot. -/
theorem P_epoch_mul_le [PresetCfg] (x : Nat) : x / P.SLOTS_PER_EPOCH * P.SLOTS_PER_EPOCH ≤ x :=
  Nat.div_mul_le_self _ _

theorem P_slots_ne [PresetCfg] [PresetCfg.Ok] : P.SLOTS_PER_EPOCH ≠ 0 :=
  Nat.pos_iff_ne_zero.mp P_slots_pos
theorem P_slots_le [PresetCfg] [b : PresetCfg.Bounds] : P.SLOTS_PER_EPOCH ≤ 32 := b.slots_le
theorem P_slots_ge6 [PresetCfg] [h : PresetCfg.Ok] : 6 ≤ P.SLOTS_PER_EPOCH := h.slots_ge_six
theorem P_target_ne [PresetCfg] [b : PresetCfg.Bounds] : P.TARGET_COMMITTEE_SIZE ≠ 0 :=
  Nat.pos_iff_ne_zero.mp b.target_committee_pos
theorem P_max_committees_le [PresetCfg] [b : PresetCfg.Bounds] :
    @LE.le Nat _ P.MAX_COMMITTEES_PER_SLOT 64 :=
  b.max_committees_le
theorem P_shuffle_pos [PresetCfg] [b : PresetCfg.Bounds] :
    @LT.lt Nat _ 0 P.SHUFFLE_ROUND_COUNT := b.shuffle_rounds_pos
theorem P_shuffle_le [PresetCfg] [b : PresetCfg.Bounds] :
    @LE.le Nat _ P.SHUFFLE_ROUND_COUNT 256 :=
  b.shuffle_rounds_le
theorem P_hist_ne [PresetCfg] [PresetCfg.Ok] : P.EPOCHS_PER_HISTORICAL_VECTOR ≠ 0 :=
  Nat.pos_iff_ne_zero.mp P_historical_vector_pos
theorem P_hist_ge2 [PresetCfg] [h : PresetCfg.Ok] :
    @LE.le Nat _ 2 P.EPOCHS_PER_HISTORICAL_VECTOR :=
  h.historical_vector_ge
theorem P_hist_le [PresetCfg] [h : PresetCfg.Ok] :
    @LE.le Nat _ P.EPOCHS_PER_HISTORICAL_VECTOR 65536 :=
  h.historical_vector_le
theorem P_sync_period_ne [PresetCfg] [b : PresetCfg.Bounds] :
    P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0 := Nat.pos_iff_ne_zero.mp b.sync_period_pos
theorem P_ptc_pos [PresetCfg] [b : PresetCfg.Bounds] : @LT.lt Nat _ 0 P.PTC_SIZE := b.ptc_pos
theorem P_ptc_le [PresetCfg] [b : PresetCfg.Bounds] : @LE.le Nat _ P.PTC_SIZE 512 := b.ptc_le
theorem P_sync_le [PresetCfg] [b : PresetCfg.Bounds] : @LE.le Nat _ P.SYNC_COMMITTEE_SIZE 512 :=
  b.sync_le
theorem P_sync_pos [PresetCfg] [h : PresetCfg.Ok] : @LT.lt Nat _ 0 P.SYNC_COMMITTEE_SIZE :=
  h.sync_size_pos
theorem P_target_pos [PresetCfg] [b : PresetCfg.Bounds] : @LT.lt Nat _ 0 P.TARGET_COMMITTEE_SIZE :=
  b.target_committee_pos
theorem P_slv_le [PresetCfg] [h : PresetCfg.Ok] : @LE.le Nat _ P.EPOCHS_PER_SLASHINGS_VECTOR 8192 :=
  h.slashings_vector_le
theorem P_maxeb [PresetCfg] : P.MAX_EFFECTIVE_BALANCE_ELECTRA = 2048000000000 := rfl
theorem P_min_seed [PresetCfg] : P.MIN_SEED_LOOKAHEAD = 1 := rfl

/-- `x + 8192 < 2 ^ 64` leaves room for a few epochs and the historical vector. -/
theorem P_ep_bound [PresetCfg] [PresetCfg.Ok] {x : Nat} (h : x + 8192 < 2 ^ 64) (k : Nat)
    (hk : k ≤ 3) : x / P.SLOTS_PER_EPOCH + k + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 := by
  have h6 := P_epoch_le_div6 x
  have hH := P_hist_le (h := inferInstance)
  have h' : x < 18446744073709543424 := by
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  refine Nat.lt_of_le_of_lt (Nat.add_le_add_left hH _) ?_
  show x / P.SLOTS_PER_EPOCH + k + 65536 < 18446744073709551616
  omega

/-- The start slot of a near epoch, plus one epoch, fits in a `u64`. -/
theorem P_ep_start_bound [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds] {x : Nat}
    (h : x + 8192 < 2 ^ 64) (k : Nat) (hk : k ≤ 3) :
    (x / P.SLOTS_PER_EPOCH + k) * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64 := by
  have h1 := P_epoch_mul_le x
  have hS : P.SLOTS_PER_EPOCH ≤ 32 := P_slots_le
  have h2 : k * P.SLOTS_PER_EPOCH ≤ 3 * 32 := Nat.mul_le_mul hk hS
  have h' : x < 18446744073709543424 := by
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  rw [Nat.add_mul]
  show x / P.SLOTS_PER_EPOCH * P.SLOTS_PER_EPOCH + k * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH <
    18446744073709551616
  omega

end EpochProofs.Spec
