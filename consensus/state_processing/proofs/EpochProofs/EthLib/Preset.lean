import EthLib.Consensus.Config
import EthLib.Consensus.Preset
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

theorem slots_per_epoch_ne_zero_mainnet : Preset.mainnet.SLOTS_PER_EPOCH ≠ 0 := by decide

theorem slots_per_epoch_ne_zero_minimal : Preset.minimal.SLOTS_PER_EPOCH ≠ 0 := by decide

end EpochProofs.EthLib
