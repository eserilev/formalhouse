import EpochProofs.Etheorem.State
import EpochProofs.Spec.Epoch
import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Fulu.Transition
import EpochProofs.Sanity.FuluRegistry
import EpochProofs.Sanity.Fulu

/-!
# The assumptions about Etheorem

The bundles of the headline theorems that the step proofs of `Etheorem/` read, so this module
sits below them in the import graph, and imports no Aeneas code. `Assumptions.lean` defines the
other bundles and lists them all.

- the preset (`PresetMatchesEtheorem`): the preset `Spec.P` has Etheorem's values;
- the oracle (`GloasOracleMatchesEtheorem`): the spec `Oracle` is Etheorem's SHA-256,
  `hash_tree_root` and BLS, and SHA-256 returns 32 bytes;
- what the bridge to Etheorem needs beyond the pyspec: `GloasEtheoremDivergenceAssumptions` for
  Gloas, `FuluEtheoremBridgeConditions` for Fulu. The Fulu conditions read the Etheorem state
  before a step (`Before k e e'`), so the steps (`epochSteps`) are defined here too.

`forkproof EpochEtheorem` (`ForkReplay.lean`) writes each bundle once for both forks. The Gloas
text is the template, in `EpochProofs.Etheorem`. The Fulu copy is in `EpochProofs.Etheorem.Fulu`,
with every name part that starts with `Gloas` renamed to `Fulu`: `GloasOracleMatchesEtheorem`
becomes `Fulu.FuluOracleMatchesEtheorem`. `forkonly` holds the parts that only one fork has.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)

/-! ## The preset

`PresetMatchesEtheorem p` says that the preset `p` of the transcription holds the values of
Etheorem's preset and config that the epoch reads. It nests one structure for each group of
steps. A field `x : Const.x = p.X` says that Etheorem's constant `x` is the preset value `X`. The
other fields bound a value. `presetMatchesEtheorem_mainnet` and `_minimal` (`Etheorem/Epoch.lean`)
prove it for the two presets. -/

section Preset

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]

forkonly Gloas
open EthCLSpecs.Gloas in
/-- The Etheorem preset and config hold the values of `p`. Each field is one constant that a
helper of `Etheorem/Helpers.lean` reads. `presetAgrees_mainnet` and `presetAgrees_minimal` prove it for the two
presets. -/
structure PresetAgrees (p : Spec.Preset) : Prop where
  slotsPerEpoch : Const.slotsPerEpoch = p.SLOTS_PER_EPOCH
  effectiveBalanceIncrement : Const.effectiveBalanceIncrement = p.EFFECTIVE_BALANCE_INCREMENT
  effectiveBalanceIncrementG : Const.effectiveBalanceIncrementG.toNat = p.EFFECTIVE_BALANCE_INCREMENT
  baseRewardFactor : Const.baseRewardFactor = p.BASE_REWARD_FACTOR
  maxSeedLookahead : Const.maxSeedLookahead.toNat = p.MAX_SEED_LOOKAHEAD
  minSeedLookahead : Const.minSeedLookahead.toNat = p.MIN_SEED_LOOKAHEAD
  epochsPerHistoricalVector : Const.epochsPerHistoricalVector = p.EPOCHS_PER_HISTORICAL_VECTOR
  minPerEpochChurnLimitElectra :
    Const.minPerEpochChurnLimitElectra.toNat = p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  churnLimitQuotientGloas : Const.churnLimitQuotientGloas.toNat = p.CHURN_LIMIT_QUOTIENT_GLOAS
  maxPerEpochActivationChurnLimitGloas :
    Const.maxPerEpochActivationChurnLimitGloas.toNat = p.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
  consolidationChurnLimitQuotient :
    Const.consolidationChurnLimitQuotient.toNat = p.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
  minValidatorWithdrawabilityDelay :
    Const.minValidatorWithdrawabilityDelay.toNat = p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
  validatorRegistryLimit : Const.validatorRegistryLimit < 2 ^ 64
  genesisForkVersion : Const.genesisForkVersion = p.GENESIS_FORK_VERSION
end forkonly

forkonly Fulu
open EthCLSpecs.Fulu in
/-- The Etheorem preset and config hold the values of `p`. Each field is one constant that a
helper of `Etheorem/Helpers.lean` reads. `presetAgrees_mainnet` and `presetAgrees_minimal` prove it for the two
presets. -/
structure PresetAgrees (p : Spec.Preset) : Prop where
  slotsPerEpoch : Const.slotsPerEpoch = p.SLOTS_PER_EPOCH
  effectiveBalanceIncrement : Const.effectiveBalanceIncrement = p.EFFECTIVE_BALANCE_INCREMENT
  effectiveBalanceIncrementG : Const.effectiveBalanceIncrementG.toNat = p.EFFECTIVE_BALANCE_INCREMENT
  baseRewardFactor : Const.baseRewardFactor = p.BASE_REWARD_FACTOR
  maxSeedLookahead : Const.maxSeedLookahead.toNat = p.MAX_SEED_LOOKAHEAD
  minSeedLookahead : Const.minSeedLookahead.toNat = p.MIN_SEED_LOOKAHEAD
  epochsPerHistoricalVector : Const.epochsPerHistoricalVector = p.EPOCHS_PER_HISTORICAL_VECTOR
  minPerEpochChurnLimitElectra :
    Const.minPerEpochChurnLimitElectra.toNat = p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  minValidatorWithdrawabilityDelay :
    Const.minValidatorWithdrawabilityDelay.toNat = p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
  validatorRegistryLimit : Const.validatorRegistryLimit < 2 ^ 64
  genesisForkVersion : Const.genesisForkVersion = p.GENESIS_FORK_VERSION

open EthCLSpecs.Fulu in
/-- The Etheorem Fulu churn config holds the values of the Fulu config `f`, and `f` relates to
`p` as `fuluTab` needs. Then the Fulu churn of a total is the Gloas churn at `fuluTab`. -/
structure FuluChurnAgrees (p : Spec.Preset) (f : Spec.FuluConfig) : Prop where
  compat : Spec.FuluCompat p f
  churnLimitQuotient : Const.churnLimitQuotient.toNat = f.CHURN_LIMIT_QUOTIENT
  maxPerEpochActivationExitChurnLimit :
    Const.maxPerEpochActivationExitChurnLimit.toNat = f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
end forkonly

open EthCLSpecs.Gloas in
/-- The Etheorem preset holds the values of `p` that the tail steps read. -/
structure TailPresetAgrees (p : Spec.Preset) : Prop where
  epochsPerEth1VotingPeriod : Const.epochsPerEth1VotingPeriod = p.EPOCHS_PER_ETH1_VOTING_PERIOD
  epochsPerEth1VotingPeriodLt : Const.epochsPerEth1VotingPeriod < 2 ^ 64
  epochsPerSlashingsVector : Const.epochsPerSlashingsVector = p.EPOCHS_PER_SLASHINGS_VECTOR
  epochsPerSlashingsVectorLt : Const.epochsPerSlashingsVector < 2 ^ 64
  slotsPerHistoricalRoot : Const.slotsPerHistoricalRoot = p.SLOTS_PER_HISTORICAL_ROOT
  hysteresisQuotient : Const.hysteresisQuotient = p.HYSTERESIS_QUOTIENT
  hysteresisDownwardMultiplier :
    Const.hysteresisDownwardMultiplier = p.HYSTERESIS_DOWNWARD_MULTIPLIER
  hysteresisUpwardMultiplier : Const.hysteresisUpwardMultiplier = p.HYSTERESIS_UPWARD_MULTIPLIER
  hysteresisLt : Const.hysteresisQuotient < 2 ^ 64 ∧ Const.hysteresisDownwardMultiplier < 2 ^ 64 ∧
    Const.hysteresisUpwardMultiplier < 2 ^ 64
  maxEffectiveBalanceElectra : Const.maxEffectiveBalanceElectraG.toNat = p.MAX_EFFECTIVE_BALANCE_ELECTRA
  minActivationBalance : Const.minActivationBalance.toNat = p.MIN_ACTIVATION_BALANCE

open EthCLSpecs.Gloas in
/-- The preset values that the passes read, beyond `PresetAgrees`. -/
structure PassesPresetAgrees [EthCLSpecs.Gloas.Config] (p : Spec.Preset) : Prop
    extends PresetAgrees p where
  minEpochsToInactivityPenalty :
    Const.minEpochsToInactivityPenalty.toNat = p.MIN_EPOCHS_TO_INACTIVITY_PENALTY
  inactivityScoreBias : Const.inactivityScoreBias.toNat = p.INACTIVITY_SCORE_BIAS
  inactivityScoreRecoveryRate :
    Const.inactivityScoreRecoveryRate.toNat = p.INACTIVITY_SCORE_RECOVERY_RATE
  inactivityPenaltyQuotientBellatrix :
    Const.inactivityPenaltyQuotientBellatrix = p.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
  epochsPerSlashingsVector : Const.epochsPerSlashingsVector = p.EPOCHS_PER_SLASHINGS_VECTOR
  proportionalSlashingMultiplierBellatrix :
    Const.proportionalSlashingMultiplierBellatrix = p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX
  slotsPerHistoricalRoot : Const.slotsPerHistoricalRoot = p.SLOTS_PER_HISTORICAL_ROOT
  slotsPerEpochTwo : 2 ≤ p.SLOTS_PER_EPOCH
  epochsPerSlashingsVectorLt : p.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 63
  proportionalSlashingMultiplierLt : p.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX < 2 ^ 64
  /-- The increment and the base reward factor of mainnet and minimal. With them the base reward is
  at most `1 / 256` of the effective balance (`rewardsBaseReward_bound`), so Etheorem's product
  `base_reward * weight` fits in `uint64`. -/
  effectiveBalanceIncrementEq : p.EFFECTIVE_BALANCE_INCREMENT = 1000000000
  baseRewardFactorEq : p.BASE_REWARD_FACTOR = 64

open EthCLSpecs.Gloas in
/-- The Etheorem preset holds the registry and deposit values of `p`. They are not in
`PresetAgrees`. -/
structure QueuesPresetAgrees (p : Spec.Preset) : Prop where
  minActivationBalance : Const.minActivationBalance.toNat = p.MIN_ACTIVATION_BALANCE
  ejectionBalance : Const.ejectionBalanceG.toNat = p.EJECTION_BALANCE
  ejection_lt : p.EJECTION_BALANCE < p.MIN_ACTIVATION_BALANCE
  maxEffectiveBalanceElectra :
    Const.maxEffectiveBalanceElectraG.toNat = p.MAX_EFFECTIVE_BALANCE_ELECTRA
  maxPendingDepositsPerEpoch : Const.maxPendingDepositsPerEpoch = p.MAX_PENDING_DEPOSITS_PER_EPOCH

forkonly Gloas
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
end forkonly

forkonly Fulu
open EthCLSpecs.Fulu in
/-- The Etheorem preset holds the committee values of `p`. -/
structure CommitteePresetAgrees (p : Spec.Preset) : Prop where
  shuffleRoundCount : Const.shuffleRoundCount = p.SHUFFLE_ROUND_COUNT
  shuffleRoundCountPos : 0 < p.SHUFFLE_ROUND_COUNT
  targetCommitteeSize : Const.targetCommitteeSize = p.TARGET_COMMITTEE_SIZE
  maxCommitteesPerSlot : Const.maxCommitteesPerSlot = p.MAX_COMMITTEES_PER_SLOT
  syncCommitteeSize : Const.syncCommitteeSize = p.SYNC_COMMITTEE_SIZE
  epochsPerSyncCommitteePeriod : Const.epochsPerSyncCommitteePeriod = p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
  maxEffectiveBalanceElectra : Const.maxEffectiveBalanceElectra = p.MAX_EFFECTIVE_BALANCE_ELECTRA
end forkonly

forkonly Gloas
/-- All the preset facts the 17 steps read. -/
structure PresetMatchesEtheorem (p : Spec.Preset) : Prop where
  /-- The constants of the helpers: epochs, increments, seeds, churn, the registry limit. -/
  base : PresetAgrees p
  /-- The constants of the tail steps: eth1 votes, slashings vector, historical roots,
  hysteresis. -/
  tail : TailPresetAgrees p
  /-- The constants of the inactivity, rewards and slashings passes. -/
  passes : PassesPresetAgrees p
  /-- The constants of the registry update and the pending deposits. -/
  queues : QueuesPresetAgrees p
  /-- The constants of the shuffling and the committees. -/
  committee : CommitteePresetAgrees p
  /-- At least six slots per epoch: the builder payment window. -/
  slotsPerEpochSix : 6 ≤ p.SLOTS_PER_EPOCH
  /-- The sync committee period fits in `uint64`. -/
  epochsPerSyncCommitteePeriodLt : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64
end forkonly

forkonly Fulu
/-- All the preset and config facts the 15 Fulu steps read. -/
structure PresetMatchesEtheorem (p : Spec.Preset) (f : Spec.FuluConfig) : Prop where
  /-- The constants of the helpers. -/
  base : PresetAgrees p
  /-- The Fulu churn config. -/
  churn : FuluChurnAgrees p f
  /-- The constants of the tail steps. -/
  tail : TailPresetAgrees p
  /-- The constants of the passes. -/
  passes : PassesPresetAgrees p
  /-- The constants of the registry update and the pending deposits. -/
  queues : QueuesPresetAgrees p
  /-- The constants of the shuffling and the committees. -/
  committee : CommitteePresetAgrees p
  /-- The sync committee period fits in `uint64`. -/
  epochsPerSyncCommitteePeriodLt : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64
  /-- The sync committee is not empty. -/
  syncCommitteeSizePos : 0 < p.SYNC_COMMITTEE_SIZE
end forkonly

end Preset

/-! ## The oracle -/

section Oracle

/-- A list of roots as a `Vector` of length `n`. The list has length `n` in a reachable state.
Past the end of the list the vector holds zero roots. -/
def rootsVector (n : Nat) (roots : List Spec.Root) : Vector Spec.Root n :=
  Vector.ofFn fun i => roots.getD i.val Spec.Bytes32.zero

variable [EthCLSpecs.Gloas.Preset] [HasherTag] [CryptoBackend]

/-- `sha256(data)` in Etheorem, as a `Bytes32`. -/
def etheoremHash (data : List UInt8) : Spec.Bytes32 :=
  bytesToRoot (sha ⟨data.toArray⟩)

/-- Each `Oracle` field the epoch reads equals the Etheorem function.

`hash` is `get_seed`, the shuffle, proposer and sync committee selection, and `compute_ptc`.
`blockRoots` and `stateRoots` are `process_historical_summaries_update`. `forkData`,
`signingData`, `depositMessage` and `verify` are the deposit signature in
`apply_pending_deposit`. `aggregate` is the sync committee `aggregate_pubkey`. -/
structure OracleAgrees (o : Spec.Oracle) : Prop where
  hash : ∀ data, o.hash data = etheoremHash data
  blockRoots : ∀ roots, o.hash_tree_root_BlockRoots roots =
    htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
  stateRoots : ∀ roots, o.hash_tree_root_StateRoots roots =
    htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
  forkData : ∀ d : Spec.ForkData,
    o.hash_tree_root_ForkData d = computeForkDataRoot d.current_version d.genesis_validators_root
  signingData : ∀ d : Spec.SigningData,
    o.hash_tree_root_SigningData d = htr ({ objectRoot := d.object_root, domain := d.domain } : SigningData)
  depositMessage : ∀ m : Spec.DepositMessage,
    o.hash_tree_root_DepositMessage m =
      htr ({ pubkey := m.pubkey, withdrawalCredentials := m.withdrawal_credentials,
             amount := UInt64.ofNat m.amount } : EthCLSpecs.Gloas.DepositMessage)
  verify : ∀ pubkey root signature, o.bls_Verify pubkey root signature =
    blsVerify pubkey root signature
  aggregate : ∀ pubkeys, o.bls_AggregatePKs pubkeys = blsAggregatePubkeys pubkeys.toArray

/-- The spec `Oracle` agrees with Etheorem's functions, and SHA-256 returns 32 bytes. -/
structure GloasOracleMatchesEtheorem (o : Spec.Oracle) : Prop where
  /-- The oracle's SHA-256, `hash_tree_root` and BLS functions are Etheorem's. -/
  agrees : OracleAgrees o
  /-- SHA-256 returns 32 bytes. `sha_size_pure` proves it for the pure SHA-256. -/
  sha32 : ∀ b : ByteArray, (sha b).size = 32

end Oracle

/-! ## The Etheorem conditions -/

section Steps

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

/-- Etheorem runs the steps `l` in order from `e` and reaches `e'`. Each step starts and ends on
the uncached box. -/
inductive StepsOk : List (GloasRun Unit) → EtheoremState → EtheoremState → Prop
  | nil (e : EtheoremState) : StepsOk [] e e
  | cons {a : GloasRun Unit} {l : List (GloasRun Unit)} {e e1 e2 : EtheoremState} :
      a.run (pureState e) = .ok ((), pureState e1) → StepsOk l e1 e2 → StepsOk (a :: l) e e2

variable [EthCLSpecs.Gloas.Config] [CryptoBackend]

forkonly Gloas
/-- Etheorem's 17 epoch steps, in `processEpoch` order. -/
def epochSteps : List (GloasRun Unit) :=
  [EthCLSpecs.Gloas.processJustificationAndFinalization,
   EthCLSpecs.Gloas.processInactivityUpdates,
   EthCLSpecs.Gloas.processRewardsAndPenalties,
   EthCLSpecs.Gloas.processRegistryUpdates,
   EthCLSpecs.Gloas.processSlashings,
   EthCLSpecs.Gloas.processEth1DataReset,
   EthCLSpecs.Gloas.processPendingDeposits,
   EthCLSpecs.Gloas.processPendingConsolidations,
   EthCLSpecs.Gloas.processBuilderPendingPayments,
   EthCLSpecs.Gloas.processEffectiveBalanceUpdates,
   EthCLSpecs.Gloas.processSlashingsReset,
   EthCLSpecs.Gloas.processRandaoMixesReset,
   EthCLSpecs.Gloas.processHistoricalSummariesUpdate,
   EthCLSpecs.Gloas.processParticipationFlagUpdates,
   EthCLSpecs.Gloas.processSyncCommitteeUpdates,
   EthCLSpecs.Gloas.processProposerLookahead,
   EthCLSpecs.Gloas.processPtcWindow]
end forkonly

forkonly Fulu
/-- Etheorem's 15 Fulu epoch steps, in `processEpoch` order. -/
def epochSteps : List (FuluRun Unit) :=
  [EthCLSpecs.Fulu.processJustificationAndFinalization,
   EthCLSpecs.Fulu.processInactivityUpdates,
   EthCLSpecs.Fulu.processRewardsAndPenalties,
   EthCLSpecs.Fulu.processRegistryUpdates,
   EthCLSpecs.Fulu.processSlashings,
   EthCLSpecs.Fulu.processEth1DataReset,
   EthCLSpecs.Fulu.processPendingDeposits,
   EthCLSpecs.Fulu.processPendingConsolidations,
   EthCLSpecs.Fulu.processEffectiveBalanceUpdates,
   EthCLSpecs.Fulu.processSlashingsReset,
   EthCLSpecs.Fulu.processRandaoMixesReset,
   EthCLSpecs.Fulu.processHistoricalSummariesUpdate,
   EthCLSpecs.Fulu.processParticipationFlagUpdates,
   EthCLSpecs.Fulu.processSyncCommitteeUpdates,
   EthCLSpecs.Fulu.processProposerLookahead]
end forkonly

/-- Etheorem runs the first `k` epoch steps from `e` and reaches `e'`. -/
def Before (k : Nat) (e e' : EtheoremState) : Prop := StepsOk (epochSteps.take k) e e'

/-- The registry lists of a state have the same length. -/
def LensEq (e : EtheoremState) : Prop :=
  e.balances.val.size = e.validators.val.size ∧
    e.previousEpochParticipation.val.size = e.validators.val.size ∧
    e.currentEpochParticipation.val.size = e.validators.val.size ∧
    e.inactivityScores.val.size = e.validators.val.size

forkonly Gloas
/-- Facts about the state at the epoch start. The steps before each read do not write these
fields, so each fact still holds when its step reads it.

- `depositRoom`: Etheorem's registry limit `2^40` has room for `MAX_PENDING_DEPOSITS_PER_EPOCH`
  new validators, the most that one epoch adds. Etheorem drops a new validator past this limit
  (F10). Beta.4 has no registry limit. Lighthouse keeps the `2^40` limit.
- `builderRoom`: the builder withdrawals have room for `SLOTS_PER_EPOCH` more items under
  Etheorem's alpha.11 limit (F6). Beta.4 has no limit.

The historical summaries room is not here: beta.4 keeps the `HISTORICAL_ROOTS_LIMIT` cap, so it
is a spec condition. `process_epoch_etheorem_in` takes it as `hhist`.

These are the assumptions needed only because Etheorem diverges from the pyspec. Each is about
the Etheorem state `e`, not the oracle. -/
structure GloasEtheoremDivergenceAssumptions (e : EtheoremState) : Prop where
  /-- F10: registry room for one epoch of deposits under Etheorem's `2^40` limit. -/
  depositRoom : (toSpecState e).validators.length +
    EthCLSpecs.Gloas.Const.maxPendingDepositsPerEpoch ≤ EthCLSpecs.Gloas.Const.validatorRegistryLimit
  /-- F6: room for `SLOTS_PER_EPOCH` builder withdrawals under Etheorem's alpha.11 limit. -/
  builderRoom : (toSpecState e).builder_pending_withdrawals.length +
      EthCLSpecs.Gloas.Const.slotsPerEpoch ≤ EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit
end forkonly

forkonly Fulu
/-- The conditions of the 15 Fulu step theorems, for an epoch that starts at `e`.

State facts:
- `finalized`: the finalized epoch is below `FAR_FUTURE_EPOCH` before the registry update.
- `depositLens`, `depositRoom`: before the pending deposits, the registry lists have the same
  length, and each pending deposit has room for a new validator.
- `consolidationLens`: one balance for each validator before the pending consolidations.
- `summariesRoom`: the historical summaries list has room for one more item.

Facts about the hash values:
- `proposerFin`: each Electra proposer loop of the lookahead ends before its last pass
  (`Spec.ProposerFin`). The last pass needs `2**64 - 1` rejected candidates before it.

These are the conditions of the bridge to Etheorem's Fulu epoch. Not all are about Etheorem: F10
is Etheorem's alpha.11 registry limit, `summariesRoom` is a spec condition (beta.4 keeps the cap),
the list lengths are facts about the intermediate states, and `proposerFin` mentions the oracle,
so this bundle takes `o` where the Gloas `GloasEtheoremDivergenceAssumptions` does not. -/
structure FuluEtheoremBridgeConditions (p : Spec.Preset) (o : Spec.Oracle) (e : EtheoremState) :
    Prop where
  /-- Before the registry update, the finalized epoch is below `FAR_FUTURE_EPOCH`. -/
  finalized : ∀ e', Before 3 e e' →
    (toSpecState e').finalized_checkpoint.epoch < Spec.FAR_FUTURE_EPOCH
  /-- Before the pending deposits, the registry lists have the same length. -/
  depositLens : ∀ e', Before 6 e e' → LensEq e'
  /-- F10: before the pending deposits, Etheorem's registry limit has room for each pending
  deposit. -/
  depositRoom : ∀ e', Before 6 e e' → e'.validators.val.size + e'.pendingDeposits.val.size ≤
    EthCLSpecs.Fulu.Const.validatorRegistryLimit
  /-- Before the pending consolidations, one balance for each validator. -/
  consolidationLens : ∀ e', Before 7 e e' → e'.balances.val.size = e'.validators.val.size
  /-- Before the historical summaries update, the list has room for one more item. -/
  summariesRoom : ∀ e', Before 11 e e' →
    e'.historicalSummaries.val.size < EthCLSpecs.Fulu.Const.historicalRootsLimit
  /-- A hash-output fact: each Electra proposer loop of the lookahead ends before its last
  pass. -/
  proposerFin : ∀ e', Before 14 e e' → ∀ s, Spec.ProposerFin p o (toSpecState e')
    (Spec.get_active_validator_indices (toSpecState e')
      (EthCLSpecs.Fulu.currentEpochOf (pureState e') + EthCLSpecs.Fulu.Const.minSeedLookahead +
        1).toNat) s
end forkonly

end Steps

end forkproof
