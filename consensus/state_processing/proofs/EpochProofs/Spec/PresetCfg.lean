import EpochProofs.Spec.Types

/-!
# The preset as a parameter

The capstones were stated for `Preset.mainnet`. `PresetVar` holds every preset value where
minimal differs from mainnet. `Preset.ofVar v` takes the mainnet value for every other field.
The proofs take the preset from the class `PresetCfg`, and the facts they need about the
varying values from the class `PresetCfg.Ok`. Both presets are instances of `Preset.ofVar`
by `rfl`.
-/

namespace EpochProofs.Spec

/-- The preset values that differ between mainnet and minimal. -/
structure PresetVar where
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
def Preset.ofVar (v : PresetVar) : Preset :=
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

def PresetVar.mainnet : PresetVar :=
  ⟨32, 8192, 128000000000, 32768, 256000000000, 8192, 65536, 64, 512, 512, 256,
    #v[0, 0, 0, 0], #v[3, 0, 0, 0], 90, 64, 128, 256, 16, 16384, 8, 16384, 134217728, 262144,
    65536, 64⟩

def PresetVar.minimal : PresetVar :=
  ⟨8, 64, 64000000000, 16, 128000000000, 64, 64, 4, 32, 16, 8,
    #v[0, 0, 0, 1], #v[3, 0, 0, 1], 10, 4, 4, 64, 4, 16, 2, 16, 64, 64, 32, 2⟩

theorem Preset.mainnet_eq_ofVar : Preset.mainnet = Preset.ofVar PresetVar.mainnet := rfl
theorem Preset.minimal_eq_ofVar : Preset.minimal = Preset.ofVar PresetVar.minimal := rfl

/-- The preset that the generic proofs read. -/
class PresetCfg where
  v : PresetVar

/-- The preset of the current `PresetCfg`. -/
@[reducible] def P [c : PresetCfg] : Preset := Preset.ofVar c.v

/-- The facts about the varying values that the generic proofs use. Both presets satisfy them. -/
class PresetCfg.Ok [c : PresetCfg] : Prop where
  slots_pos : 0 < c.v.SLOTS_PER_EPOCH
  slots_gt_one : 1 < c.v.SLOTS_PER_EPOCH
  slashings_vector_pos : 0 < c.v.EPOCHS_PER_SLASHINGS_VECTOR
  slashings_vector_ge : 64 ≤ c.v.EPOCHS_PER_SLASHINGS_VECTOR
  slashings_vector_le : c.v.EPOCHS_PER_SLASHINGS_VECTOR ≤ 8192
  historical_vector_pos : 0 < c.v.EPOCHS_PER_HISTORICAL_VECTOR
  eth1_period_pos : 0 < c.v.EPOCHS_PER_ETH1_VOTING_PERIOD
  sync_size_pos : 0 < c.v.SYNC_COMMITTEE_SIZE
  sync_seats_even : (c.v.SLOTS_PER_EPOCH * c.v.SYNC_COMMITTEE_SIZE) % 2 = 0

theorem P_slots_pos [PresetCfg] [h : PresetCfg.Ok] : 0 < P.SLOTS_PER_EPOCH := h.slots_pos
theorem P_slots_gt_one [PresetCfg] [h : PresetCfg.Ok] : 1 < P.SLOTS_PER_EPOCH := h.slots_gt_one
theorem P_slashings_vector_pos [PresetCfg] [h : PresetCfg.Ok] : 0 < P.EPOCHS_PER_SLASHINGS_VECTOR :=
  h.slashings_vector_pos
theorem P_slashings_vector_ge [PresetCfg] [h : PresetCfg.Ok] : 64 ≤ P.EPOCHS_PER_SLASHINGS_VECTOR :=
  h.slashings_vector_ge
theorem P_slashings_vector_le [PresetCfg] [h : PresetCfg.Ok] : P.EPOCHS_PER_SLASHINGS_VECTOR ≤ 8192 :=
  h.slashings_vector_le
/-- The slashings vector length as a `Nat` with its bounds. -/
theorem P_slashings_vector_nat [PresetCfg] [PresetCfg.Ok] :
    ∃ V : Nat, P.EPOCHS_PER_SLASHINGS_VECTOR = V ∧ 64 ≤ V ∧ V ≤ 8192 :=
  ⟨_, rfl, P_slashings_vector_ge, P_slashings_vector_le⟩
theorem P_historical_vector_pos [PresetCfg] [h : PresetCfg.Ok] :
    0 < P.EPOCHS_PER_HISTORICAL_VECTOR := h.historical_vector_pos
theorem P_eth1_period_pos [PresetCfg] [h : PresetCfg.Ok] : 0 < P.EPOCHS_PER_ETH1_VOTING_PERIOD :=
  h.eth1_period_pos

theorem P_sync_size_pos [PresetCfg] [h : PresetCfg.Ok] : 0 < P.SYNC_COMMITTEE_SIZE :=
  h.sync_size_pos
theorem P_sync_seats_even [PresetCfg] [h : PresetCfg.Ok] :
    (P.SLOTS_PER_EPOCH * P.SYNC_COMMITTEE_SIZE) % 2 = 0 := h.sync_seats_even

@[reducible] def mainnetCfg : PresetCfg := ⟨PresetVar.mainnet⟩
@[reducible] def minimalCfg : PresetCfg := ⟨PresetVar.minimal⟩

theorem mainnetCfg_ok : @PresetCfg.Ok mainnetCfg :=
  letI := mainnetCfg
  { slots_pos := by decide, slots_gt_one := by decide, slashings_vector_pos := by decide, slashings_vector_ge := by decide,
    slashings_vector_le := by decide,
    historical_vector_pos := by decide, eth1_period_pos := by decide,
    sync_size_pos := by decide, sync_seats_even := by decide }

theorem minimalCfg_ok : @PresetCfg.Ok minimalCfg :=
  letI := minimalCfg
  { slots_pos := by decide, slots_gt_one := by decide, slashings_vector_pos := by decide, slashings_vector_ge := by decide,
    slashings_vector_le := by decide,
    historical_vector_pos := by decide, eth1_period_pos := by decide,
    sync_size_pos := by decide, sync_seats_even := by decide }

theorem P_mainnet : @P mainnetCfg = Preset.mainnet := rfl
theorem P_minimal : @P minimalCfg = Preset.minimal := rfl

end EpochProofs.Spec

namespace EpochProofs.Spec

/-- `decide` after unfolding the generic preset to its mainnet values. -/
macro "pdecide" : tactic =>
  `(tactic| first
    | (simp only [P, Preset.ofVar] <;> decide)
    | (simp only [P, Preset.ofVar] <;> omega)
    | (simp [P, Preset.ofVar]; done))

/-- `rfl` after unfolding the generic preset to its mainnet values. -/
macro "prfl" : tactic => `(tactic| (simp only [P, Preset.ofVar] <;> rfl))

end EpochProofs.Spec
