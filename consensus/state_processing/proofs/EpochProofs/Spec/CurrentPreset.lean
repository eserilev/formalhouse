import EpochProofs.Spec.Types

/-!
# The preset as a parameter

`PresetValues` holds every preset value where minimal differs from mainnet. `Preset.ofValues v` takes the
mainnet value for every other field.
The proofs take the preset from the class `CurrentPreset`, and the facts they need about the
varying values from the class `CurrentPreset.Valid`. Both presets are instances of `Preset.ofValues`
by `rfl`.
-/

namespace EpochProofs.Spec

/-- The preset values that differ between mainnet and minimal. -/
structure PresetValues where
  SLOTS_PER_EPOCH : Nat
  EPOCHS_PER_SLASHINGS_VECTOR : Uint64
  MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA : Gwei
  CHURN_LIMIT_QUOTIENT_GLOAS : Uint64
  MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS : Gwei
  SLOTS_PER_HISTORICAL_ROOT : Uint64
  EPOCHS_PER_HISTORICAL_VECTOR : Uint64
  EPOCHS_PER_ETH1_VOTING_PERIOD : Uint64
  SYNC_COMMITTEE_SIZE : Uint64
  PTC_SIZE : Uint64
  EPOCHS_PER_SYNC_COMMITTEE_PERIOD : Uint64
  GENESIS_FORK_VERSION : Vector UInt8 4
  CAPELLA_FORK_VERSION : Vector UInt8 4
  SHUFFLE_ROUND_COUNT : Uint64
  MAX_COMMITTEES_PER_SLOT : Uint64
  TARGET_COMMITTEE_SIZE : Uint64
  SHARD_COMMITTEE_PERIOD : Uint64
  MAX_WITHDRAWALS_PER_PAYLOAD : Uint64
  MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP : Uint64
  MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP : Uint64
  MAX_BUILDERS_PER_WITHDRAWALS_SWEEP : Uint64
  PENDING_PARTIAL_WITHDRAWALS_LIMIT : Uint64
  PENDING_CONSOLIDATIONS_LIMIT : Uint64
  CONSOLIDATION_CHURN_LIMIT_QUOTIENT : Uint64
  MIN_BUILDER_WITHDRAWABILITY_DELAY : Epoch

/-- The preset with the values of `v` and the mainnet value everywhere else. -/
def Preset.ofValues (v : PresetValues) : Preset :=
  { SLOTS_PER_EPOCH := v.SLOTS_PER_EPOCH
    EPOCHS_PER_SLASHINGS_VECTOR := v.EPOCHS_PER_SLASHINGS_VECTOR
    MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA := v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    CHURN_LIMIT_QUOTIENT_GLOAS := v.CHURN_LIMIT_QUOTIENT_GLOAS
    MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS := v.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
    SLOTS_PER_HISTORICAL_ROOT := v.SLOTS_PER_HISTORICAL_ROOT
    EPOCHS_PER_HISTORICAL_VECTOR := v.EPOCHS_PER_HISTORICAL_VECTOR
    EPOCHS_PER_ETH1_VOTING_PERIOD := v.EPOCHS_PER_ETH1_VOTING_PERIOD
    SYNC_COMMITTEE_SIZE := v.SYNC_COMMITTEE_SIZE
    PTC_SIZE := v.PTC_SIZE
    EPOCHS_PER_SYNC_COMMITTEE_PERIOD := v.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
    GENESIS_FORK_VERSION := v.GENESIS_FORK_VERSION
    CAPELLA_FORK_VERSION := v.CAPELLA_FORK_VERSION
    SHUFFLE_ROUND_COUNT := v.SHUFFLE_ROUND_COUNT
    MAX_COMMITTEES_PER_SLOT := v.MAX_COMMITTEES_PER_SLOT
    TARGET_COMMITTEE_SIZE := v.TARGET_COMMITTEE_SIZE
    SHARD_COMMITTEE_PERIOD := v.SHARD_COMMITTEE_PERIOD
    MAX_WITHDRAWALS_PER_PAYLOAD := v.MAX_WITHDRAWALS_PER_PAYLOAD
    MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP := v.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP
    MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP := v.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP
    MAX_BUILDERS_PER_WITHDRAWALS_SWEEP := v.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP
    PENDING_PARTIAL_WITHDRAWALS_LIMIT := v.PENDING_PARTIAL_WITHDRAWALS_LIMIT
    PENDING_CONSOLIDATIONS_LIMIT := v.PENDING_CONSOLIDATIONS_LIMIT
    CONSOLIDATION_CHURN_LIMIT_QUOTIENT := v.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
    MIN_BUILDER_WITHDRAWABILITY_DELAY := v.MIN_BUILDER_WITHDRAWABILITY_DELAY }

def PresetValues.mainnet : PresetValues :=
  ⟨32, 8192, 128000000000, 32768, 256000000000, 8192, 65536, 64, 512, 512, 256,
    #v[0, 0, 0, 0], #v[3, 0, 0, 0], 90, 64, 128, 256, 16, 16384, 8, 16384, 134217728, 262144,
    65536, 64⟩

def PresetValues.minimal : PresetValues :=
  ⟨8, 64, 64000000000, 16, 128000000000, 64, 64, 4, 32, 16, 8,
    #v[0, 0, 0, 1], #v[3, 0, 0, 1], 10, 4, 4, 64, 4, 16, 2, 16, 64, 64, 32, 2⟩

theorem Preset.mainnet_eq_ofVar : Preset.mainnet = Preset.ofValues PresetValues.mainnet := rfl
theorem Preset.minimal_eq_ofVar : Preset.minimal = Preset.ofValues PresetValues.minimal := rfl

/-- The preset that the generic proofs read. -/
class CurrentPreset where
  values : PresetValues

/-- The preset of the current `CurrentPreset`. -/
@[reducible] def P [c : CurrentPreset] : Preset := Preset.ofValues c.values

/-- The facts about the varying values that the generic proofs use. Both presets satisfy them. -/
class CurrentPreset.Valid [c : CurrentPreset] : Prop where
  slots_pos : 0 < c.values.SLOTS_PER_EPOCH
  slots_gt_one : 1 < c.values.SLOTS_PER_EPOCH
  slots_ge_six : 6 ≤ c.values.SLOTS_PER_EPOCH
  hist_root_ge : 2 * c.values.SLOTS_PER_EPOCH ≤ c.values.SLOTS_PER_HISTORICAL_ROOT
  hist_root_le : c.values.SLOTS_PER_HISTORICAL_ROOT ≤ 8192
  slashings_vector_pos : 0 < c.values.EPOCHS_PER_SLASHINGS_VECTOR
  slashings_vector_ge : 64 ≤ c.values.EPOCHS_PER_SLASHINGS_VECTOR
  slashings_vector_le : c.values.EPOCHS_PER_SLASHINGS_VECTOR ≤ 8192
  historical_vector_pos : 0 < c.values.EPOCHS_PER_HISTORICAL_VECTOR
  historical_vector_ge : 2 ≤ c.values.EPOCHS_PER_HISTORICAL_VECTOR
  historical_vector_le : c.values.EPOCHS_PER_HISTORICAL_VECTOR ≤ 65536
  eth1_period_pos : 0 < c.values.EPOCHS_PER_ETH1_VOTING_PERIOD
  sync_size_pos : 0 < c.values.SYNC_COMMITTEE_SIZE
  sync_seats_even : (c.values.SLOTS_PER_EPOCH * c.values.SYNC_COMMITTEE_SIZE) % 2 = 0

theorem P_slots_pos [CurrentPreset] [h : CurrentPreset.Valid] : 0 < P.SLOTS_PER_EPOCH := h.slots_pos
theorem P_slots_gt_one [CurrentPreset] [h : CurrentPreset.Valid] : 1 < P.SLOTS_PER_EPOCH := h.slots_gt_one
theorem P_slashings_vector_pos [CurrentPreset] [h : CurrentPreset.Valid] : 0 < P.EPOCHS_PER_SLASHINGS_VECTOR :=
  h.slashings_vector_pos
theorem P_slashings_vector_ge [CurrentPreset] [h : CurrentPreset.Valid] : 64 ≤ P.EPOCHS_PER_SLASHINGS_VECTOR :=
  h.slashings_vector_ge
theorem P_slashings_vector_le [CurrentPreset] [h : CurrentPreset.Valid] : P.EPOCHS_PER_SLASHINGS_VECTOR ≤ 8192 :=
  h.slashings_vector_le
/-- The slashings vector length as a `Nat` with its bounds. -/
theorem P_slashings_vector_nat [CurrentPreset] [CurrentPreset.Valid] :
    ∃ V : Nat, P.EPOCHS_PER_SLASHINGS_VECTOR = V ∧ 64 ≤ V ∧ V ≤ 8192 :=
  ⟨_, rfl, P_slashings_vector_ge, P_slashings_vector_le⟩
/-- The slashings target epoch fits in a `u64` for epochs below `2 ^ 63`. -/
theorem P_slashings_target_lt [CurrentPreset] [CurrentPreset.Valid] {e : Nat} (he : e < 2 ^ 63) :
    e + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE := by
  obtain ⟨V, hV, -, hV2⟩ := P_slashings_vector_nat
  rw [hV]
  simp only [UINT64_SIZE]
  omega
/-- The slashings target of the epoch of a `u64` slot fits in a `u64`. -/
theorem P_slot_target_lt [CurrentPreset] [CurrentPreset.Valid] {x : Nat} (hx : x < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE := by
  obtain ⟨q, hq⟩ : ∃ q : Nat, x / P.SLOTS_PER_EPOCH = q := ⟨_, rfl⟩
  have h2 : q ≤ x / 2 := by
    rw [← hq]; exact Nat.div_le_div_left (Nat.lt_iff_add_one_le.mp P_slots_gt_one) (by decide)
  rw [hq]
  exact P_slashings_target_lt (by omega)

/-- From a fitting slashings target: the epoch is at least 32 below `2 ^ 64`. -/
theorem P_target_bound [CurrentPreset] [CurrentPreset.Valid] {e : Nat}
    (h : e + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE) : e + 32 < 2 ^ 64 := by
  obtain ⟨V, hV, hV1, -⟩ := P_slashings_vector_nat
  rw [hV] at h
  simp only [UINT64_SIZE] at h
  omega
theorem P_target_activation [CurrentPreset] [CurrentPreset.Valid] {e : Nat}
    (h : e + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE) :
    e + 1 + P.MAX_SEED_LOOKAHEAD < UINT64_SIZE := by
  have := P_target_bound h
  simp only [P, Preset.ofValues, UINT64_SIZE]
  omega

theorem P_target_succ [CurrentPreset] [CurrentPreset.Valid] {e : Nat}
    (h : e + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE) : e + 1 < UINT64_SIZE := by
  have := P_target_bound h
  simp only [UINT64_SIZE]
  omega

theorem P_target_far [CurrentPreset] [CurrentPreset.Valid] {e : Nat}
    (h : e + P.EPOCHS_PER_SLASHINGS_VECTOR / 2 < UINT64_SIZE) :
    e < FAR_FUTURE_EPOCH ∧ e + 1 < FAR_FUTURE_EPOCH := by
  have := P_target_bound h
  simp only [FAR_FUTURE_EPOCH]
  omega
theorem P_historical_vector_pos [CurrentPreset] [h : CurrentPreset.Valid] :
    0 < P.EPOCHS_PER_HISTORICAL_VECTOR := h.historical_vector_pos
/-- The historical vector length as a `Nat` with its bounds. -/
theorem P_historical_vector_nat [CurrentPreset] [h : CurrentPreset.Valid] :
    ∃ H : Nat, P.EPOCHS_PER_HISTORICAL_VECTOR = H ∧ 2 ≤ H ∧ H ≤ 65536 :=
  ⟨_, rfl, h.historical_vector_ge, h.historical_vector_le⟩
/-- The epoch of a slot below `2 ^ 64` is below `2 ^ 63`. -/
theorem P_slot_epoch_lt [CurrentPreset] [CurrentPreset.Valid] {x : Nat} (hx : x < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH < 2 ^ 63 := by
  have h2 : x / P.SLOTS_PER_EPOCH ≤ x / 2 :=
    Nat.div_le_div_left (Nat.lt_iff_add_one_le.mp P_slots_gt_one) (by decide)
  omega

theorem P_slot_room [CurrentPreset] [CurrentPreset.Valid] {x : Nat} (hx : x + 1 < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH + 65538 < 2 ^ 64 := by
  have := P_slot_epoch_lt (x := x) (by omega); omega

theorem P_slot_hist_fit [CurrentPreset] [CurrentPreset.Valid] {x : Nat} (hx : x + 1 < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH + 1 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 := by
  obtain ⟨H, hH, -, hH2⟩ := P_historical_vector_nat
  have := P_slot_epoch_lt (x := x) (by omega)
  rw [hH]; omega

theorem P_slot_slash_fit [CurrentPreset] [CurrentPreset.Valid] {x : Nat} (hx : x + 1 < 2 ^ 64) :
    x / P.SLOTS_PER_EPOCH + 1 + P.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64 := by
  obtain ⟨V, hV, -, hV2⟩ := P_slashings_vector_nat
  have := P_slot_epoch_lt (x := x) (by omega)
  rw [hV]; omega
/-- The slots per epoch and per historical root as `Nat` with their bounds. -/
theorem P_slots_nat [CurrentPreset] [h : CurrentPreset.Valid] :
    ∃ S R : Nat, P.SLOTS_PER_EPOCH = S ∧ P.SLOTS_PER_HISTORICAL_ROOT = R ∧ 6 ≤ S ∧ 2 * S ≤ R ∧
      R ≤ 8192 :=
  ⟨_, _, rfl, rfl, h.slots_ge_six, h.hist_root_ge, h.hist_root_le⟩
theorem P_eth1_period_pos [CurrentPreset] [h : CurrentPreset.Valid] : 0 < P.EPOCHS_PER_ETH1_VOTING_PERIOD :=
  h.eth1_period_pos

theorem P_sync_size_pos [CurrentPreset] [h : CurrentPreset.Valid] : 0 < P.SYNC_COMMITTEE_SIZE :=
  h.sync_size_pos
theorem P_sync_seats_even [CurrentPreset] [h : CurrentPreset.Valid] :
    (P.SLOTS_PER_EPOCH * P.SYNC_COMMITTEE_SIZE) % 2 = 0 := h.sync_seats_even

@[reducible] def currentPresetMainnet : CurrentPreset := ⟨PresetValues.mainnet⟩
@[reducible] def currentPresetMinimal : CurrentPreset := ⟨PresetValues.minimal⟩

theorem currentPresetMainnet_ok : @CurrentPreset.Valid currentPresetMainnet :=
  letI := currentPresetMainnet
  { slots_pos := by decide, slots_gt_one := by decide, slots_ge_six := by decide,
    hist_root_ge := by decide, hist_root_le := by decide, slashings_vector_pos := by decide, slashings_vector_ge := by decide,
    slashings_vector_le := by decide,
    historical_vector_pos := by decide, historical_vector_ge := by decide,
    historical_vector_le := by decide, eth1_period_pos := by decide,
    sync_size_pos := by decide, sync_seats_even := by decide }

theorem currentPresetMinimal_ok : @CurrentPreset.Valid currentPresetMinimal :=
  letI := currentPresetMinimal
  { slots_pos := by decide, slots_gt_one := by decide, slots_ge_six := by decide,
    hist_root_ge := by decide, hist_root_le := by decide, slashings_vector_pos := by decide, slashings_vector_ge := by decide,
    slashings_vector_le := by decide,
    historical_vector_pos := by decide, historical_vector_ge := by decide,
    historical_vector_le := by decide, eth1_period_pos := by decide,
    sync_size_pos := by decide, sync_seats_even := by decide }

theorem P_mainnet : @P currentPresetMainnet = Preset.mainnet := rfl
theorem P_minimal : @P currentPresetMinimal = Preset.minimal := rfl

end EpochProofs.Spec

namespace EpochProofs.Spec

/-- `decide` after unfolding the generic preset to its mainnet values. -/
macro "pdecide" : tactic =>
  `(tactic| first
    | (simp only [P, Preset.ofValues] <;> decide)
    | (simp only [P, Preset.ofValues] <;> omega)
    | (simp [P, Preset.ofValues]; done))

/-- `rfl` after unfolding the generic preset to its mainnet values. -/
macro "prfl" : tactic => `(tactic| (simp only [P, Preset.ofValues] <;> rfl))

end EpochProofs.Spec
