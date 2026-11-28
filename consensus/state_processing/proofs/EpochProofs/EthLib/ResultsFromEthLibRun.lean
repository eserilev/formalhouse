import EpochProofs.Results
import EpochProofs.EthLib.ChainResults

/-!
# The main theorems, for the epoch inputs of an EthLib run

Each theorem here is a theorem of `Results.lean` about an epoch input. Here an EthLib `Run` reaches
the epoch input, in place of the block processing of the transcription. The run starts at a genesis
state, or at a state with the facts of `ChainStart`. It crosses each fork that `config` schedules.

The theorems on mainnet and minimal take the fork epochs as a parameter. The EthLib configs do not
schedule Gloas, so a genesis run with those configs does not reach a Gloas epoch input.
-/

namespace EpochProofs.Formalhouse.FromEthLibRun

open EpochProofs.EthLib EpochProofs.CacheReads
open _root_.EthLib.Consensus
  (BeaconState Config ForkedBeaconState Preset SignatureChecks processEpoch)
open Aeneas.Std (U64)
open Aeneas.Std.Result (ok)
open CacheProofs.ProgressiveBalances (LighthouseProgressiveBalancesCache)

section AnyPreset

variable [Spec.CurrentPreset] [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds]
variable {preset : Preset} {config : Config} {checks : SignatureChecks} {oracle : Spec.Oracle}
  {start : ForkedBeaconState preset}

omit [Spec.CurrentPreset.Bounds] [Spec.CurrentPreset] [Spec.CurrentPreset.Valid] in
/-- The room for deposits gives the registry limit. -/
theorem registryWithinLimit {fork : _root_.EthLib.Base.Fork} {electra : .pectra ≤ fork}
    {state : BeaconState preset fork} (roomForDeposits : RoomForDeposits electra state) :
    state.RegistryWithinLimit :=
  Nat.le_trans (Nat.le_add_right _ _) roomForDeposits

/-! ## Gloas -/

section Gloas

variable {state : BeaconState preset .glamsterdam}

omit [Spec.CurrentPreset.Bounds] in
/-- At every Gloas epoch input of a run, the cache reads give the spec values, when the cache
assumptions hold. -/
theorem gloas_cache_reads_correct
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) := by
  have invariants := run.invariants presetMatches maxEffectiveBalance (by decide)
    registryWithinLimit supply
  obtain ⟨start, startCache, hstart, hupdates⟩ := caches.progressiveBalances
  obtain ⟨built, hagree, htotal⟩ := caches.epochCache
  obtain ⟨lookup, laws, earlier, builtMap, builtLength, length, hprefix, hbuilt, hinsert⟩ :=
    caches.pubkeyCache
  rw [← activeSum_eq_active_balances] at htotal
  obtain ⟨h1, h2, h3⟩ := lighthouse_cache_reads_correct _ invariants.1.1.1.2.1
    invariants.1.1.2.2.2.2 progressiveCache (progressive_balances_correct_after_updates hstart hupdates) cachedTotal
    (epoch_cache_total_stays_correct cachedTotal.val htotal hagree)
  refine ⟨h1, h2, h3, fun pubkey => ?_⟩
  obtain ⟨result, hget, hresult⟩ := CacheProofs.get_correct_of_nodup laws
    (pubkey_cache_stays_correct laws hprefix hbuilt hinsert) invariants.1.2.1 pubkey
  rw [Spec.idxOf_pubkey_eq] at hresult
  exact ⟨result, hget, by convert hresult⟩

omit [Spec.CurrentPreset.Bounds] in
/-- Gloas, against the hand-written pyspec transcription: at every epoch input of a run, the Lean
model of Lighthouse's epoch and the transcription's give the same state, or both fail. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (Spec.process_epoch Spec.P oracle (toSpecState state)) :=
  Formalhouse.lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants oracle
    (run.invariants presetMatches maxEffectiveBalance (by decide) registryWithinLimit supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit)

/-- Gloas: at every epoch input of a run, the Lean model of Lighthouse's epoch and EthLib's
`processEpoch` give the same state, or both fail. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch config checks state)) :=
  Formalhouse.lighthouse_model_gloas_epoch_agrees_ethlib presetMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit) slotFarFromOverflow
    roomForDeposits oracleMatches

/-- Gloas: at every epoch input of a run, the Lean model of Lighthouse's epoch succeeds. EthLib's
`processEpoch` succeeds with the same state. Each cache read of the epoch gives the spec value. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  ⟨Formalhouse.lighthouse_model_gloas_epoch_eq_ethlib_of_invariants presetMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches chain.historicalSummariesBelowLimit) chain roomForDeposits
    oracleMatches,
  gloas_cache_reads_correct presetMatches maxEffectiveBalance
    (FromEthLibRun.registryWithinLimit roomForDeposits) run supply caches⟩

/-- Gloas, for the composed Rust: at an epoch input of a run, if EthLib's `processEpoch` succeeds,
the Rust returns `Ok` with the same state. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState preset .glamsterdam}
    (ethLibSucceeds : processEpoch config checks state = .ok result) :
    ∃ rustResult, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result :=
  Formalhouse.lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit) slotFarFromOverflow
    roomForDeposits oracleMatches rust ethLibSucceeds

/-- Gloas, for the composed Rust: at every epoch input of a run, the Rust returns `Ok`, and EthLib's
`processEpoch` succeeds with the same state. Each cache read of the epoch gives the spec value. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    (∃ rustResult result, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      processEpoch config checks state = .ok result ∧ rustStateToSpec rustResult = toSpecState result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) := by
  obtain ⟨⟨result, -, ethLibSucceeds⟩, reads⟩ := lighthouse_model_gloas_epoch_eq_ethlib
    presetMatches maxEffectiveBalance run supply chain roomForDeposits oracleMatches caches
  obtain ⟨rustResult, rustSucceeds, same⟩ := lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatches
    maxEffectiveBalance run supply chain.historicalSummariesBelowLimit chain.slotFarFromOverflow
    roomForDeposits oracleMatches rust ethLibSucceeds
  exact ⟨⟨rustResult, result, rustSucceeds, ethLibSucceeds, same⟩, reads⟩

end Gloas

/-! ## Fulu -/

section Fulu

variable [Spec.CurrentFuluConfig] [Spec.CurrentFuluConfig.Valid] {state : BeaconState preset .fusaka}

omit [Spec.CurrentPreset.Bounds] in
/-- Fulu, against the hand-written pyspec transcription. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState state))
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle (toSpecState state)) :=
  Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle _
    (run.invariants presetMatches maxEffectiveBalance (by decide) registryWithinLimit supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit)

omit [Spec.CurrentPreset.Bounds] in
/-- Fulu: at every epoch input of a run, the Lean model of Lighthouse's epoch and EthLib's
`processEpoch` give the same state, or both fail. The state includes the payload header, which the
epoch keeps. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch config checks state)) :=
  Formalhouse.lighthouse_model_fulu_epoch_agrees_ethlib presetMatches fuluConfigMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit) roomForDeposits oracleMatches

/-- Fulu: at every epoch input of a run, the Lean model of Lighthouse's epoch succeeds. EthLib's
`processEpoch` succeeds with the same state, and keeps the payload header. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch config checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  Formalhouse.lighthouse_model_fulu_epoch_eq_ethlib_of_invariants presetMatches fuluConfigMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches chain.historicalSummariesBelowLimit) chain roomForDeposits
    oracleMatches

/-- Fulu, for the composed Rust: at an epoch input of a run, if EthLib's `processEpoch` succeeds,
the Rust returns `Ok` with the same state. EthLib keeps the payload header. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState preset .fusaka}
    (ethLibSucceeds : processEpoch config checks state = .ok result) :
    (∃ rustResult, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  Formalhouse.lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatches fuluConfigMatches
    (run.invariants presetMatches maxEffectiveBalance (by decide)
      (registryWithinLimit roomForDeposits) supply)
    (run.atLastSlotOfEpoch presetMatches historicalSummariesBelowLimit) roomForDeposits oracleMatches
    rust ethLibSucceeds

/-- Fulu, for the composed Rust: at every epoch input of a run, the Rust returns `Ok`, and EthLib's
`processEpoch` succeeds with the same state, and keeps the payload header. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib
    (presetMatches : PresetMatchesEthLib preset config)
    (maxEffectiveBalance : MaxEffectiveBalanceIsActivationBalance preset)
    (fuluConfigMatches : toSpecFuluConfig config = Spec.FC)
    (run : RunToEpochInput config checks start state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches preset checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    ∃ rustResult result, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      processEpoch config checks state = .ok result ∧ rustStateToSpec rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  obtain ⟨result, -, ethLibSucceeds, -⟩ := lighthouse_model_fulu_epoch_eq_ethlib presetMatches
    maxEffectiveBalance fuluConfigMatches run supply chain roomForDeposits oracleMatches
  obtain ⟨⟨rustResult, rustSucceeds, same⟩, header⟩ := lighthouse_rust_fulu_epoch_of_ethlib_ok
    presetMatches maxEffectiveBalance fuluConfigMatches run supply
    chain.historicalSummariesBelowLimit roomForDeposits oracleMatches rust ethLibSucceeds
  exact ⟨rustResult, result, rustSucceeds, ethLibSucceeds, same, header⟩

end Fulu

end AnyPreset

/-! ## Mainnet and minimal -/

/-- The epoch of each fork. -/
structure ForkEpochs where
  altair : _root_.EthLib.Consensus.Epoch
  bellatrix : _root_.EthLib.Consensus.Epoch
  capella : _root_.EthLib.Consensus.Epoch
  deneb : _root_.EthLib.Consensus.Epoch
  electra : _root_.EthLib.Consensus.Epoch
  fulu : _root_.EthLib.Consensus.Epoch
  gloas : _root_.EthLib.Consensus.Epoch

/-- The config, with other fork epochs. -/
def withForkEpochs (config : Config) (forkEpochs : ForkEpochs) : Config :=
  { config with
    ALTAIR_FORK_EPOCH := forkEpochs.altair
    BELLATRIX_FORK_EPOCH := forkEpochs.bellatrix
    CAPELLA_FORK_EPOCH := forkEpochs.capella
    DENEB_FORK_EPOCH := forkEpochs.deneb
    ELECTRA_FORK_EPOCH := forkEpochs.electra
    FULU_FORK_EPOCH := forkEpochs.fulu
    GLOAS_FORK_EPOCH := forkEpochs.gloas }

/-- The preset match does not read the fork epochs. -/
theorem presetMatches_withForkEpochs [Spec.CurrentPreset] {preset : Preset} {config : Config}
    (presetMatches : PresetMatchesEthLib preset config) (forkEpochs : ForkEpochs) :
    PresetMatchesEthLib preset (withForkEpochs config forkEpochs) :=
  ⟨presetMatches.values, ⟨presetMatches.divisorsNonzero.1, presetMatches.divisorsNonzero.2,
    presetMatches.divisorsNonzero.3, presetMatches.divisorsNonzero.4,
    presetMatches.divisorsNonzero.5, presetMatches.divisorsNonzero.6,
    presetMatches.divisorsNonzero.7, presetMatches.divisorsNonzero.8⟩,
    presetMatches.committeeBounds, presetMatches.historicalRootsLimit⟩

variable {forkEpochs : ForkEpochs} {checks : SignatureChecks} {oracle : Spec.Oracle}

section Mainnet

attribute [local instance] Spec.currentPresetMainnet Spec.currentFuluConfigMainnet
local instance : @Spec.CurrentPreset.Valid Spec.currentPresetMainnet := Spec.currentPresetMainnet_ok
local instance : @Spec.CurrentPreset.Bounds Spec.currentPresetMainnet := Spec.currentPresetMainnet_bounds
local instance : Spec.CurrentFuluConfig.Valid := ⟨Spec.fuluCompat_mainnet⟩

theorem presetMatches_mainnet :
    PresetMatchesEthLib Preset.mainnet (withForkEpochs Config.mainnet forkEpochs) :=
  presetMatches_withForkEpochs presetMatchesEthLib_mainnet forkEpochs

/-- `gloas_cache_reads_correct` on mainnet. -/
theorem gloas_cache_reads_correct_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  gloas_cache_reads_correct presetMatches_mainnet
    maxEffectiveBalance_mainnet registryWithinLimit run supply caches

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (Spec.process_epoch Spec.P oracle (toSpecState state)) :=
  lighthouse_model_gloas_epoch_agrees_pyspec
    presetMatches_mainnet maxEffectiveBalance_mainnet
    registryWithinLimit run supply historicalSummariesBelowLimit oracle

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState
        (processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib
    presetMatches_mainnet maxEffectiveBalance_mainnet run supply
    historicalSummariesBelowLimit slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatches_mainnet
    maxEffectiveBalance_mainnet run supply chain roomForDeposits oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.mainnet .glamsterdam}
    (ethLibSucceeds :
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result) :
    ∃ rustResult, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatches_mainnet
    maxEffectiveBalance_mainnet run supply historicalSummariesBelowLimit slotFarFromOverflow
    roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    (∃ rustResult result, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatches_mainnet
    maxEffectiveBalance_mainnet run supply chain roomForDeposits oracleMatches caches rust

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .fusaka}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState state))
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle (toSpecState state)) :=
  lighthouse_model_fulu_epoch_agrees_pyspec
    presetMatches_mainnet maxEffectiveBalance_mainnet
    registryWithinLimit run supply historicalSummariesBelowLimit oracle

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState
        (processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib
    presetMatches_mainnet maxEffectiveBalance_mainnet
    toSpecFuluConfig_mainnet run supply historicalSummariesBelowLimit roomForDeposits
    oracleMatches

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_model_fulu_epoch_eq_ethlib presetMatches_mainnet
    maxEffectiveBalance_mainnet toSpecFuluConfig_mainnet run supply chain roomForDeposits
    oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.mainnet .fusaka}
    (ethLibSucceeds :
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result) :
    (∃ rustResult, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatches_mainnet
    maxEffectiveBalance_mainnet toSpecFuluConfig_mainnet run supply historicalSummariesBelowLimit
    roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_rust_fulu_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib_mainnet
    {start : ForkedBeaconState Preset.mainnet}
    {state : BeaconState Preset.mainnet .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.mainnet forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    ∃ rustResult result, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      processEpoch (withForkEpochs Config.mainnet forkEpochs) checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatches_mainnet
    maxEffectiveBalance_mainnet toSpecFuluConfig_mainnet run supply chain roomForDeposits
    oracleMatches rust

end Mainnet

section Minimal

attribute [local instance] Spec.currentPresetMinimal Spec.currentFuluConfigMinimal
local instance : @Spec.CurrentPreset.Valid Spec.currentPresetMinimal := Spec.currentPresetMinimal_ok
local instance : @Spec.CurrentPreset.Bounds Spec.currentPresetMinimal := Spec.currentPresetMinimal_bounds
local instance : Spec.CurrentFuluConfig.Valid := ⟨Spec.fuluCompat_minimal⟩

theorem presetMatches_minimal :
    PresetMatchesEthLib Preset.minimal (withForkEpochs Config.minimal forkEpochs) :=
  presetMatches_withForkEpochs presetMatchesEthLib_minimal forkEpochs

/-- `gloas_cache_reads_correct` on minimal. -/
theorem gloas_cache_reads_correct_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  gloas_cache_reads_correct presetMatches_minimal
    maxEffectiveBalance_minimal registryWithinLimit run supply caches

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (Spec.process_epoch Spec.P oracle (toSpecState state)) :=
  lighthouse_model_gloas_epoch_agrees_pyspec
    presetMatches_minimal maxEffectiveBalance_minimal
    registryWithinLimit run supply historicalSummariesBelowLimit oracle

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState
        (processEpoch (withForkEpochs Config.minimal forkEpochs) checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib
    presetMatches_minimal maxEffectiveBalance_minimal run supply
    historicalSummariesBelowLimit slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatches_minimal
    maxEffectiveBalance_minimal run supply chain roomForDeposits oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.minimal .glamsterdam}
    (ethLibSucceeds :
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result) :
    ∃ rustResult, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatches_minimal
    maxEffectiveBalance_minimal run supply historicalSummariesBelowLimit slotFarFromOverflow
    roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {PubkeyMap : Type} {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    (∃ rustResult result, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatches_minimal
    maxEffectiveBalance_minimal run supply chain roomForDeposits oracleMatches caches rust

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .fusaka}
    (registryWithinLimit : state.RegistryWithinLimit)
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (oracle : Spec.Oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState state))
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle (toSpecState state)) :=
  lighthouse_model_fulu_epoch_agrees_pyspec
    presetMatches_minimal maxEffectiveBalance_minimal
    registryWithinLimit run supply historicalSummariesBelowLimit oracle

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState
        (processEpoch (withForkEpochs Config.minimal forkEpochs) checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib
    presetMatches_minimal maxEffectiveBalance_minimal
    toSpecFuluConfig_minimal run supply historicalSummariesBelowLimit roomForDeposits
    oracleMatches

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_model_fulu_epoch_eq_ethlib presetMatches_minimal
    maxEffectiveBalance_minimal toSpecFuluConfig_minimal run supply chain roomForDeposits
    oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (historicalSummariesBelowLimit : (toSpecState state).historical_summaries.length <
      Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.minimal .fusaka}
    (ethLibSucceeds :
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result) :
    (∃ rustResult, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatches_minimal
    maxEffectiveBalance_minimal toSpecFuluConfig_minimal run supply historicalSummariesBelowLimit
    roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_rust_fulu_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib_minimal
    {start : ForkedBeaconState Preset.minimal}
    {state : BeaconState Preset.minimal .fusaka}
    (run : RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks start
      state)
    (supply : SupplyAtInput (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state)) :
    ∃ rustResult result, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run = ok (some rustResult) ∧
      processEpoch (withForkEpochs Config.minimal forkEpochs) checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatches_minimal
    maxEffectiveBalance_minimal toSpecFuluConfig_minimal run supply chain roomForDeposits
    oracleMatches rust

end Minimal

end EpochProofs.Formalhouse.FromEthLibRun
