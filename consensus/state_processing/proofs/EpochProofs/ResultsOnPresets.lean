import EpochProofs.Results

/-!
# The main theorems on mainnet and minimal
-/

namespace EpochProofs.Formalhouse

open EpochProofs.EthLib
open _root_.EthLib.Consensus (BeaconState Config Preset SignatureChecks processEpoch)
open Aeneas.Std (U64)
open Aeneas.Std.Result (ok)
open CacheProofs.PB (LhCache)

variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle} {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {checks : SignatureChecks}

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_mainnet {PubkeyMap : Type}
    {progressiveCache : LhCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.mainnet checks state = .ok result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatchesEthLib_mainnet run chain roomForDeposits
    oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_mainnet {PubkeyMap : Type}
    {progressiveCache : LhCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.mainnet .glamsterdam}
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    (∃ rustResult result, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch Config.mainnet checks state = .ok result ∧
      view rustResult = toSpecState result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatchesEthLib_mainnet run chain roomForDeposits
    oracleMatches caches rust

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_mainnet
    {state : BeaconState Preset.mainnet .glamsterdam}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch Config.mainnet checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib presetMatchesEthLib_mainnet invariants atEpochBoundary
    slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_mainnet
    {state : BeaconState Preset.mainnet .glamsterdam}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState Preset.mainnet .glamsterdam}
    (ethLibSucceeds : processEpoch Config.mainnet checks state = .ok result) :
    ∃ rustResult, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatchesEthLib_mainnet invariants atEpochBoundary
    slotFarFromOverflow roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
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
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    ∃ rustResult result, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch Config.mainnet checks state = .ok result ∧
      view rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    run chain roomForDeposits oracleMatches rust

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch Config.mainnet checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    invariants atEpochBoundary roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on mainnet. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_mainnet
    {state : BeaconState Preset.mainnet .fusaka}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.mainnet checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState Preset.mainnet .fusaka}
    (ethLibSucceeds : processEpoch Config.mainnet checks state = .ok result) :
    (∃ rustResult, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatchesEthLib_mainnet toSpecFuluConfig_mainnet
    invariants atEpochBoundary roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_mainnet {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on mainnet. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_mainnet {s : Spec.BeaconState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

/-- `lighthouse_model_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_eq_ethlib_minimal {PubkeyMap : Type}
    {progressiveCache : LhCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state)) :
    (∃ result, Spec.process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
      processEpoch Config.minimal checks state = .ok result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_model_gloas_epoch_eq_ethlib presetMatchesEthLib_minimal run chain roomForDeposits
    oracleMatches caches

/-- `lighthouse_rust_gloas_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_rust_gloas_epoch_eq_ethlib_minimal {PubkeyMap : Type}
    {progressiveCache : LhCache} {cachedTotal : U64}
    {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
    {pubkeyMap : PubkeyMap}
    {state : BeaconState Preset.minimal .glamsterdam}
    (run : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState state))
    (chain : GloasChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    (caches : GloasCacheAssumptions progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state))
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    (∃ rustResult result, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch Config.minimal checks state = .ok result ∧
      view rustResult = toSpecState result) ∧
    GloasCacheReadsCorrect progressiveCache cachedTotal pubkeyMapOps pubkeyMap
      (toSpecState state) :=
  lighthouse_rust_gloas_epoch_eq_ethlib presetMatchesEthLib_minimal run chain roomForDeposits
    oracleMatches caches rust

/-- `lighthouse_model_gloas_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_ethlib_minimal
    {state : BeaconState Preset.minimal .glamsterdam}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState state))
      (toSpecResult toSpecState (processEpoch Config.minimal checks state)) :=
  lighthouse_model_gloas_epoch_agrees_ethlib presetMatchesEthLib_minimal invariants atEpochBoundary
    slotFarFromOverflow roomForDeposits oracleMatches

/-- `lighthouse_rust_gloas_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_gloas_epoch_of_ethlib_ok_minimal
    {state : BeaconState Preset.minimal .glamsterdam}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (slotFarFromOverflow : (toSpecState state).slot + 8192 < 2 ^ 64)
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {rustState : σ}
    (rust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState Preset.minimal .glamsterdam}
    (ethLibSucceeds : processEpoch Config.minimal checks state = .ok result) :
    ∃ rustResult, (Compose.epoch rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result :=
  lighthouse_rust_gloas_epoch_of_ethlib_ok presetMatchesEthLib_minimal invariants atEpochBoundary
    slotFarFromOverflow roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_fulu_epoch_eq_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_eq_ethlib_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
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
    (run : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState state))
    (chain : FuluChainAssumptions oracle (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state)) :
    ∃ rustResult result, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      processEpoch Config.minimal checks state = .ok result ∧
      view rustResult = toSpecState result ∧
      result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_eq_ethlib presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    run chain roomForDeposits oracleMatches rust

/-- `lighthouse_model_fulu_epoch_agrees_ethlib` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_ethlib_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState state with
          state := ← Spec.process_epoch_lighthouse_fulu oracle (toSpecState state) })
      (toSpecResult toSpecFuluState (processEpoch Config.minimal checks state)) :=
  lighthouse_model_fulu_epoch_agrees_ethlib presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    invariants atEpochBoundary roomForDeposits oracleMatches

/-- `lighthouse_rust_fulu_epoch_of_ethlib_ok` on minimal. -/
theorem lighthouse_rust_fulu_epoch_of_ethlib_ok_minimal
    {state : BeaconState Preset.minimal .fusaka}
    (invariants : Spec.ReachableInvariants (toSpecState state))
    (atEpochBoundary : Spec.AtEpochBoundary (toSpecState state))
    (roomForDeposits : RoomForDeposits (by decide) state)
    (oracleMatches : OracleMatches Preset.minimal checks oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (rust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState state))
    {result : BeaconState Preset.minimal .fusaka}
    (ethLibSucceeds : processEpoch Config.minimal checks state = .ok result) :
    (∃ rustResult, (Compose.epochFulu rustGlue rustState).run = ok (some rustResult) ∧
      view rustResult = toSpecState result) ∧
    result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader :=
  lighthouse_rust_fulu_epoch_of_ethlib_ok presetMatchesEthLib_minimal toSpecFuluConfig_minimal
    invariants atEpochBoundary roomForDeposits oracleMatches rust ethLibSucceeds

/-- `lighthouse_model_gloas_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_minimal {s : Spec.BeaconState}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle s)
      (Spec.process_epoch Spec.P oracle s) :=
  lighthouse_model_gloas_epoch_agrees_pyspec hrun hhistBelowLimit

/-- `lighthouse_model_fulu_epoch_agrees_pyspec` on minimal. -/
theorem lighthouse_model_fulu_epoch_agrees_pyspec_minimal {s : Spec.BeaconState}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart s)
    (hhistBelowLimit : Spec.HistoricalSummariesBelowLimit s) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle s)
      (Spec.process_epoch_fulu Spec.P Spec.FC oracle s) :=
  lighthouse_model_fulu_epoch_agrees_pyspec hrun hhistBelowLimit

end Minimal

end EpochProofs.Formalhouse
