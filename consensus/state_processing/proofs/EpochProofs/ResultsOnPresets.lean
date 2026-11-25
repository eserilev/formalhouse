import EpochProofs.Results

/-!
# The main theorems on mainnet and minimal
-/

namespace EpochProofs.Formalhouse

open EpochProofs.EthLib
open _root_.EthLib.Consensus (BeaconState Config Preset SignatureChecks processEpoch)
open Aeneas.Std (U64)
open Aeneas.Std.Result (ok)
open CacheProofs.ProgressiveBalances (LighthouseProgressiveBalancesCache)

variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {checks : SignatureChecks}

section Mainnet

attribute [local instance] Spec.currentPresetMainnet Spec.currentFuluConfigMainnet
local instance : @Spec.CurrentPreset.Valid Spec.currentPresetMainnet := Spec.currentPresetMainnet_ok
local instance : @Spec.CurrentPreset.Bounds Spec.currentPresetMainnet := Spec.currentPresetMainnet_bounds
local instance : Spec.CurrentFuluConfig.Valid := ⟨Spec.fuluCompat_mainnet⟩

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_mainnet {PubkeyMap : Type}
    {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.mainnet checks state = .ok result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatchesEthLib_mainnet run chain roomForDeposits
    oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_mainnet {PubkeyMap : Type}
    {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state)) :
    (∃ rustResult result, (TranslatedEpoch.translatedEpoch rustCode rustState).run =
      ok (some rustResult) ∧
      processEpoch Config.mainnet checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatchesEthLib_mainnet run chain roomForDeposits
    oracleMatches caches rust

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_mainnet
    {state : BeaconState Preset.mainnet .glamsterdam}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch Config.mainnet checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib presetMatchesEthLib_mainnet invariants atLastSlotOfEpoch
    slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_mainnet
    {state : BeaconState Preset.mainnet .glamsterdam}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state))
    {result : BeaconState Preset.mainnet .glamsterdam}
    (ethLibSucceeds : processEpoch Config.mainnet checks state = .ok result) :
    ∃ rustResult, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatchesEthLib_mainnet invariants atLastSlotOfEpoch
    slotFarFromOverflow roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (run : FuluOnlyRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.mainnet checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_model_fulu_epoch_eq_ethlib presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    run chain roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (run : FuluOnlyRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState}
    {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state)) :
    ∃ rustResult result, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run =
      ok (some rustResult)
      ∧
      processEpoch Config.mainnet checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    run chain roomForDeposits oracleMatches rust

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch Config.mainnet checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    invariants atLastSlotOfEpoch roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState}
    {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.mainnet .fusaka}
    (ethLibSucceeds : processEpoch Config.mainnet checks state = .ok result) :
    (∃ rustResult, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run =
      ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    invariants atLastSlotOfEpoch roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet {s : Spec.BeaconState}
    (hrun : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet {s : Spec.BeaconState}
    (hrun : FuluOnlyRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Mainnet

section Minimal

attribute [local instance] Spec.currentPresetMinimal Spec.currentFuluConfigMinimal
local instance : @Spec.CurrentPreset.Valid Spec.currentPresetMinimal := Spec.currentPresetMinimal_ok
local instance : @Spec.CurrentPreset.Bounds Spec.currentPresetMinimal := Spec.currentPresetMinimal_bounds
local instance : Spec.CurrentFuluConfig.Valid := ⟨Spec.fuluCompat_minimal⟩

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_minimal {PubkeyMap : Type}
    {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.minimal checks state = .ok result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatchesEthLib_minimal run chain roomForDeposits
    oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_minimal {PubkeyMap : Type}
    {progressiveCache : LighthouseProgressiveBalancesCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state)) :
    (∃ rustResult result, (TranslatedEpoch.translatedEpoch rustCode rustState).run =
      ok (some rustResult) ∧
      processEpoch Config.minimal checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    GloasCachesCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatchesEthLib_minimal run chain roomForDeposits
    oracleMatches caches rust

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_minimal
    {state : BeaconState Preset.minimal .glamsterdam}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch Config.minimal checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib presetMatchesEthLib_minimal invariants atLastSlotOfEpoch
    slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_minimal
    {state : BeaconState Preset.minimal .glamsterdam}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCode RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState} {rustState : RustState}
    (rust : GloasUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state))
    {result : BeaconState Preset.minimal .glamsterdam}
    (ethLibSucceeds : processEpoch Config.minimal checks state = .ok result) :
    ∃ rustResult, (TranslatedEpoch.translatedEpoch rustCode rustState).run = ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatchesEthLib_minimal invariants atLastSlotOfEpoch
    slotFarFromOverflow roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (run : FuluOnlyRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    ∃ result,
      Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.minimal checks state = .ok result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_model_fulu_epoch_eq_ethlib presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    run chain roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_rust_fulu_epoch_eq_ethlib_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (run : FuluOnlyRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainConditions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState}
    {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState
    (toSpecState state)) :
    ∃ rustResult result, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run =
      ok (some rustResult)
      ∧
      processEpoch Config.minimal checks state = .ok result ∧
      rustStateToSpec rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    run chain roomForDeposits oracleMatches rust

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch Config.minimal checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    invariants atLastSlotOfEpoch roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (invariants : Spec.EpochInputInvariants (toSpecState state))
    (atLastSlotOfEpoch : Spec.AtLastSlotOfEpoch (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {RustState RustError : Type}
    {rustCode : TranslatedEpoch.UntranslatedEpochCodeFulu RustState RustError}
    {rustStateToSpec : RustState → Spec.BeaconState}
    {rustState : RustState}
    (rust : FuluUntranslatedRustFacts rustCode oracle rustStateToSpec rustState (toSpecState state))
    {result : BeaconState Preset.minimal .fusaka}
    (ethLibSucceeds : processEpoch Config.minimal checks state = .ok result) :
    (∃ rustResult, (TranslatedEpoch.translatedEpochFulu rustCode rustState).run =
      ok (some rustResult) ∧
      rustStateToSpec rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    invariants atLastSlotOfEpoch roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal {s : Spec.BeaconState}
    (hrun : FuluThenGloasRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal {s : Spec.BeaconState}
    (hrun : FuluOnlyRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Minimal

end EpochProofs.Formalhouse
