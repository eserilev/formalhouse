import EthLib.Consensus.Config
import EthLib.Consensus.Preset
import EpochProofs.EthLib.SimpSets
import EpochProofs.Spec.Fulu

/-!
# The preset of the reference and the preset of EthLib

EthLib splits the constants of the specification into a preset and a config, and keeps each as a
`UInt64`. The reference keeps them in one `Spec.Preset` (and `Spec.FuluConfig`) as natural numbers.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Consensus

/-- An EthLib preset and config, read as a preset of the reference. -/
def toSpecPreset (preset : Preset) (config : Config) : Spec.Preset :=
  { SLOTS_PER_EPOCH := preset.SLOTS_PER_EPOCH.toNat
    EFFECTIVE_BALANCE_INCREMENT := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    HYSTERESIS_QUOTIENT := preset.HYSTERESIS_QUOTIENT.toNat
    HYSTERESIS_DOWNWARD_MULTIPLIER := preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat
    HYSTERESIS_UPWARD_MULTIPLIER := preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat
    MIN_ACTIVATION_BALANCE := preset.MIN_ACTIVATION_BALANCE.toNat
    MAX_EFFECTIVE_BALANCE_ELECTRA := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    MIN_EPOCHS_TO_INACTIVITY_PENALTY := preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat
    INACTIVITY_SCORE_BIAS := config.INACTIVITY_SCORE_BIAS.toNat
    INACTIVITY_SCORE_RECOVERY_RATE := config.INACTIVITY_SCORE_RECOVERY_RATE.toNat
    EPOCHS_PER_SLASHINGS_VECTOR := preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
    PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX :=
      preset.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX.toNat
    BASE_REWARD_FACTOR := preset.BASE_REWARD_FACTOR.toNat
    INACTIVITY_PENALTY_QUOTIENT_BELLATRIX := preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat
    MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA := config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    CHURN_LIMIT_QUOTIENT_GLOAS := config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat
    EJECTION_BALANCE := config.EJECTION_BALANCE.toNat
    MAX_SEED_LOOKAHEAD := preset.MAX_SEED_LOOKAHEAD.toNat
    MIN_VALIDATOR_WITHDRAWABILITY_DELAY := config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
    MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS :=
      config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
    MAX_PENDING_DEPOSITS_PER_EPOCH := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
    SLOTS_PER_HISTORICAL_ROOT := preset.SLOTS_PER_HISTORICAL_ROOT.toNat
    EPOCHS_PER_HISTORICAL_VECTOR := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
    EPOCHS_PER_ETH1_VOTING_PERIOD := preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat
    MIN_SEED_LOOKAHEAD := preset.MIN_SEED_LOOKAHEAD.toNat
    SYNC_COMMITTEE_SIZE := preset.SYNC_COMMITTEE_SIZE.toNat
    EPOCHS_PER_SYNC_COMMITTEE_PERIOD := preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat
    PTC_SIZE := preset.PTC_SIZE.toNat
    GENESIS_FORK_VERSION := config.GENESIS_FORK_VERSION
    MAX_WITHDRAWALS_PER_PAYLOAD := preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat
    MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP := preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat
    MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP :=
      preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat
    MAX_BUILDERS_PER_WITHDRAWALS_SWEEP := preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat
    CAPELLA_FORK_VERSION := config.CAPELLA_FORK_VERSION
    SHUFFLE_ROUND_COUNT := preset.SHUFFLE_ROUND_COUNT.toNat
    MAX_COMMITTEES_PER_SLOT := preset.MAX_COMMITTEES_PER_SLOT.toNat
    TARGET_COMMITTEE_SIZE := preset.TARGET_COMMITTEE_SIZE.toNat
    MAX_VALIDATORS_PER_COMMITTEE := preset.MAX_VALIDATORS_PER_COMMITTEE.toNat
    MIN_ATTESTATION_INCLUSION_DELAY := preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat
    SHARD_COMMITTEE_PERIOD := config.SHARD_COMMITTEE_PERIOD.toNat
    MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA := preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat
    WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA := preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
    PENDING_PARTIAL_WITHDRAWALS_LIMIT := preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT.toNat
    PENDING_CONSOLIDATIONS_LIMIT := preset.PENDING_CONSOLIDATIONS_LIMIT.toNat
    CONSOLIDATION_CHURN_LIMIT_QUOTIENT := config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat
    MIN_BUILDER_WITHDRAWABILITY_DELAY := config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat }

/-- The Fulu-only values of an EthLib config, read as a Fulu config of the reference. -/
def toSpecFuluConfig (config : Config) : Spec.FuluConfig :=
  { CHURN_LIMIT_QUOTIENT := config.CHURN_LIMIT_QUOTIENT.toNat
    MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT :=
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat }

/-- On mainnet, the reference and EthLib have the same preset and config values. -/
theorem toSpecPreset_mainnet :
    toSpecPreset Preset.mainnet Config.mainnet = Spec.Preset.mainnet := by rfl

/-- On minimal, the reference and EthLib have the same preset and config values. -/
theorem toSpecPreset_minimal :
    toSpecPreset Preset.minimal Config.minimal = Spec.Preset.minimal := by rfl

/-- On mainnet, the reference and EthLib have the same Fulu config values. -/
theorem toSpecFuluConfig_mainnet :
    toSpecFuluConfig Config.mainnet = Spec.FuluConfig.mainnet := by rfl

/-- On minimal, the reference and EthLib have the same Fulu config values. -/
theorem toSpecFuluConfig_minimal :
    toSpecFuluConfig Config.minimal = Spec.FuluConfig.minimal := by rfl

/-! ## Reads of one preset value -/

section Read

variable {preset : Preset} {config : Config}

@[spec_preset] theorem toSpecPreset_SLOTS_PER_EPOCH :
    (toSpecPreset preset config).SLOTS_PER_EPOCH =
      preset.SLOTS_PER_EPOCH.toNat := rfl

@[spec_preset] theorem toSpecPreset_EFFECTIVE_BALANCE_INCREMENT :
    (toSpecPreset preset config).EFFECTIVE_BALANCE_INCREMENT =
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl

@[spec_preset] theorem toSpecPreset_HYSTERESIS_QUOTIENT :
    (toSpecPreset preset config).HYSTERESIS_QUOTIENT =
      preset.HYSTERESIS_QUOTIENT.toNat := rfl

@[spec_preset] theorem toSpecPreset_HYSTERESIS_DOWNWARD_MULTIPLIER :
    (toSpecPreset preset config).HYSTERESIS_DOWNWARD_MULTIPLIER =
      preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat := rfl

@[spec_preset] theorem toSpecPreset_HYSTERESIS_UPWARD_MULTIPLIER :
    (toSpecPreset preset config).HYSTERESIS_UPWARD_MULTIPLIER =
      preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_ACTIVATION_BALANCE :
    (toSpecPreset preset config).MIN_ACTIVATION_BALANCE =
      preset.MIN_ACTIVATION_BALANCE.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_EFFECTIVE_BALANCE_ELECTRA :
    (toSpecPreset preset config).MAX_EFFECTIVE_BALANCE_ELECTRA =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_EPOCHS_TO_INACTIVITY_PENALTY :
    (toSpecPreset preset config).MIN_EPOCHS_TO_INACTIVITY_PENALTY =
      preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY.toNat := rfl

@[spec_preset] theorem toSpecPreset_INACTIVITY_SCORE_BIAS :
    (toSpecPreset preset config).INACTIVITY_SCORE_BIAS =
      config.INACTIVITY_SCORE_BIAS.toNat := rfl

@[spec_preset] theorem toSpecPreset_INACTIVITY_SCORE_RECOVERY_RATE :
    (toSpecPreset preset config).INACTIVITY_SCORE_RECOVERY_RATE =
      config.INACTIVITY_SCORE_RECOVERY_RATE.toNat := rfl

@[spec_preset] theorem toSpecPreset_EPOCHS_PER_SLASHINGS_VECTOR :
    (toSpecPreset preset config).EPOCHS_PER_SLASHINGS_VECTOR =
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := rfl

@[spec_preset] theorem toSpecPreset_PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX :
    (toSpecPreset preset config).PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX =
      preset.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX.toNat := rfl

@[spec_preset] theorem toSpecPreset_BASE_REWARD_FACTOR :
    (toSpecPreset preset config).BASE_REWARD_FACTOR =
      preset.BASE_REWARD_FACTOR.toNat := rfl

@[spec_preset] theorem toSpecPreset_INACTIVITY_PENALTY_QUOTIENT_BELLATRIX :
    (toSpecPreset preset config).INACTIVITY_PENALTY_QUOTIENT_BELLATRIX =
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA :
    (toSpecPreset preset config).MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA =
      config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat := rfl

@[spec_preset] theorem toSpecPreset_CHURN_LIMIT_QUOTIENT_GLOAS :
    (toSpecPreset preset config).CHURN_LIMIT_QUOTIENT_GLOAS =
      config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat := rfl

@[spec_preset] theorem toSpecPreset_EJECTION_BALANCE :
    (toSpecPreset preset config).EJECTION_BALANCE =
      config.EJECTION_BALANCE.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_SEED_LOOKAHEAD :
    (toSpecPreset preset config).MAX_SEED_LOOKAHEAD =
      preset.MAX_SEED_LOOKAHEAD.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_VALIDATOR_WITHDRAWABILITY_DELAY :
    (toSpecPreset preset config).MIN_VALIDATOR_WITHDRAWABILITY_DELAY =
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS :
    (toSpecPreset preset config).MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS =
      config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_PENDING_DEPOSITS_PER_EPOCH :
    (toSpecPreset preset config).MAX_PENDING_DEPOSITS_PER_EPOCH =
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := rfl

@[spec_preset] theorem toSpecPreset_SLOTS_PER_HISTORICAL_ROOT :
    (toSpecPreset preset config).SLOTS_PER_HISTORICAL_ROOT =
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat := rfl

@[spec_preset] theorem toSpecPreset_EPOCHS_PER_HISTORICAL_VECTOR :
    (toSpecPreset preset config).EPOCHS_PER_HISTORICAL_VECTOR =
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat := rfl

@[spec_preset] theorem toSpecPreset_EPOCHS_PER_ETH1_VOTING_PERIOD :
    (toSpecPreset preset config).EPOCHS_PER_ETH1_VOTING_PERIOD =
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_SEED_LOOKAHEAD :
    (toSpecPreset preset config).MIN_SEED_LOOKAHEAD =
      preset.MIN_SEED_LOOKAHEAD.toNat := rfl

@[spec_preset] theorem toSpecPreset_SYNC_COMMITTEE_SIZE :
    (toSpecPreset preset config).SYNC_COMMITTEE_SIZE =
      preset.SYNC_COMMITTEE_SIZE.toNat := rfl

@[spec_preset] theorem toSpecPreset_EPOCHS_PER_SYNC_COMMITTEE_PERIOD :
    (toSpecPreset preset config).EPOCHS_PER_SYNC_COMMITTEE_PERIOD =
      preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := rfl

@[spec_preset] theorem toSpecPreset_PTC_SIZE :
    (toSpecPreset preset config).PTC_SIZE =
      preset.PTC_SIZE.toNat := rfl

@[spec_preset] theorem toSpecPreset_GENESIS_FORK_VERSION :
    (toSpecPreset preset config).GENESIS_FORK_VERSION =
      config.GENESIS_FORK_VERSION := rfl

@[spec_preset] theorem toSpecPreset_MAX_WITHDRAWALS_PER_PAYLOAD :
    (toSpecPreset preset config).MAX_WITHDRAWALS_PER_PAYLOAD =
      preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP :
    (toSpecPreset preset config).MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP =
      preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP :
    (toSpecPreset preset config).MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP =
      preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_BUILDERS_PER_WITHDRAWALS_SWEEP :
    (toSpecPreset preset config).MAX_BUILDERS_PER_WITHDRAWALS_SWEEP =
      preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat := rfl

@[spec_preset] theorem toSpecPreset_CAPELLA_FORK_VERSION :
    (toSpecPreset preset config).CAPELLA_FORK_VERSION =
      config.CAPELLA_FORK_VERSION := rfl

@[spec_preset] theorem toSpecPreset_SHUFFLE_ROUND_COUNT :
    (toSpecPreset preset config).SHUFFLE_ROUND_COUNT =
      preset.SHUFFLE_ROUND_COUNT.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_COMMITTEES_PER_SLOT :
    (toSpecPreset preset config).MAX_COMMITTEES_PER_SLOT =
      preset.MAX_COMMITTEES_PER_SLOT.toNat := rfl

@[spec_preset] theorem toSpecPreset_TARGET_COMMITTEE_SIZE :
    (toSpecPreset preset config).TARGET_COMMITTEE_SIZE =
      preset.TARGET_COMMITTEE_SIZE.toNat := rfl

@[spec_preset] theorem toSpecPreset_MAX_VALIDATORS_PER_COMMITTEE :
    (toSpecPreset preset config).MAX_VALIDATORS_PER_COMMITTEE =
      preset.MAX_VALIDATORS_PER_COMMITTEE.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_ATTESTATION_INCLUSION_DELAY :
    (toSpecPreset preset config).MIN_ATTESTATION_INCLUSION_DELAY =
      preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat := rfl

@[spec_preset] theorem toSpecPreset_SHARD_COMMITTEE_PERIOD :
    (toSpecPreset preset config).SHARD_COMMITTEE_PERIOD =
      config.SHARD_COMMITTEE_PERIOD.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA :
    (toSpecPreset preset config).MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA =
      preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA.toNat := rfl

@[spec_preset] theorem toSpecPreset_WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA :
    (toSpecPreset preset config).WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA =
      preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat := rfl

@[spec_preset] theorem toSpecPreset_PENDING_PARTIAL_WITHDRAWALS_LIMIT :
    (toSpecPreset preset config).PENDING_PARTIAL_WITHDRAWALS_LIMIT =
      preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT.toNat := rfl

@[spec_preset] theorem toSpecPreset_PENDING_CONSOLIDATIONS_LIMIT :
    (toSpecPreset preset config).PENDING_CONSOLIDATIONS_LIMIT =
      preset.PENDING_CONSOLIDATIONS_LIMIT.toNat := rfl

@[spec_preset] theorem toSpecPreset_CONSOLIDATION_CHURN_LIMIT_QUOTIENT :
    (toSpecPreset preset config).CONSOLIDATION_CHURN_LIMIT_QUOTIENT =
      config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat := rfl

@[spec_preset] theorem toSpecPreset_MIN_BUILDER_WITHDRAWABILITY_DELAY :
    (toSpecPreset preset config).MIN_BUILDER_WITHDRAWABILITY_DELAY =
      config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat := rfl

end Read

/-- The preset and config values that a step divides by are not zero. The reference fails on a
division by zero. EthLib divides by these values without a check. -/
structure DivisorsNonzero (preset : Preset) (config : Config) : Prop where
  slots : preset.SLOTS_PER_EPOCH ≠ 0
  historicalPeriod : preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH ≠ 0
  eth1VotingPeriod : preset.EPOCHS_PER_ETH1_VOTING_PERIOD ≠ 0
  syncCommitteePeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0
  increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0
  hysteresisQuotient : preset.HYSTERESIS_QUOTIENT ≠ 0
  churnLimitQuotient : config.CHURN_LIMIT_QUOTIENT ≠ 0
  churnLimitQuotientGloas : config.CHURN_LIMIT_QUOTIENT_GLOAS ≠ 0

theorem divisorsNonzero_mainnet : DivisorsNonzero Preset.mainnet Config.mainnet := by
  constructor <;> decide

theorem divisorsNonzero_minimal : DivisorsNonzero Preset.minimal Config.minimal := by
  constructor <;> decide

end EpochProofs.EthLib
