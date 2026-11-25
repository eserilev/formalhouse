import EpochProofs.Sanity.PtcIndices
import EpochProofs.Sanity.Invariants.BalanceFloor
import EpochProofs.Sanity.Invariants.LighthouseEpoch
import EpochProofs.Runs
import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Sanity.Invariants.TotalityRows
import EpochProofs.Sanity.Invariants.TotalityFulu
import EpochProofs.CacheBridge.ProgressiveBalances
import EpochProofs.CacheBridge.EpochCache
import EpochProofs.Trusted.CacheUpkeep
import EpochProofs.Compose.Epoch
import EpochProofs.Compose.Fulu
import EpochProofs.EthLib.Shuffle

/-!
# The assumptions of the main theorems

- The run, `FuluThenGloasRun` and `FuluOnlyRun` (`Runs.lean`): the state is an input of
  `process_epoch` on a chain from a start state with the facts of a genesis state. The total stake
  stays below its bounds.
- The chain, `GloasChainConditions` and `FuluChainConditions`: what the epoch needs to succeed.
- The preset, `PresetMatchesEthLib`: the preset values are those of EthLib. Proved for mainnet and
  minimal.
- The caches, `GloasCacheAssumptions`: where each cache that the Gloas epoch reads came from. The
  Fulu model reads the spec values, so the Fulu theorems take no cache facts.
- The untranslated Rust, `GloasUntranslatedRustFacts` and `FuluUntranslatedRustFacts`: what the code that Aeneas
  does not translate does.
-/

namespace EpochProofs.Formalhouse

open Aeneas Aeneas.Std Result

/-! ## The chain -/

section Chain

variable [Spec.CurrentPreset]

/-- What the Gloas epoch needs from the chain, beyond the run, to succeed. -/
structure GloasChainConditions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the three committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochBeforeCommitteeSteps Spec.P oracle state = .ok committeeInput →
      Spec.CommitteeStepPreconditions oracle committeeInput ∧
      Spec.RegistryAllowsSelection oracle committeeInput
  /-- The supply and time bounds. -/
  supplyAndTimeLimits : Spec.SupplyAndTimeLimits state
  /-- The slot is far below `2^64`. The pyspec `get_block_root` raises near `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

variable [Spec.CurrentFuluConfig]

/-- What the Fulu epoch needs from the chain, beyond the run, to succeed. -/
structure FuluChainConditions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the two committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochBeforeCommitteeStepsFulu Spec.P Spec.FC oracle state = .ok committeeInput →
      Spec.CommitteeStepPreconditionsFulu oracle committeeInput ∧
      Spec.RegistryAllowsSelection oracle committeeInput
  /-- The supply and time bounds. -/
  supplyAndTimeLimits : Spec.SupplyAndTimeLimits state
  /-- The slot is far below `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

end Chain

/-! ## The preset -/

section Preset

variable [Spec.CurrentPreset]

open EpochProofs.EthLib
open _root_.EthLib.Consensus (Config Preset)

/-- The preset of the theorems and the preset of EthLib have the same values. The other fields are
facts about these values. They hold on mainnet and minimal. -/
structure PresetMatchesEthLib (preset : Preset) (config : Config) : Prop where
  /-- The values are equal. -/
  values : toSpecPreset preset config = Spec.P
  /-- No epoch step divides by zero. -/
  divisorsNonzero : DivisorsNonzero preset config
  /-- The bounds that the committee computations use. -/
  committeeBounds : CommitteeBounds preset
  /-- Lighthouse's limit on the historical summaries is at most the spec limit. -/
  historicalRootsLimit :
    Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤ preset.HISTORICAL_ROOTS_LIMIT.toNat

end Preset

/-- Mainnet. -/
theorem presetMatchesEthLib_mainnet :
    @PresetMatchesEthLib Spec.currentPresetMainnet _root_.EthLib.Consensus.Preset.mainnet
      _root_.EthLib.Consensus.Config.mainnet :=
  letI := Spec.currentPresetMainnet
  ⟨EthLib.toSpecPreset_mainnet, EthLib.divisorsNonzero_mainnet, EthLib.committeeBounds_mainnet,
    by decide⟩

/-- Minimal. -/
theorem presetMatchesEthLib_minimal :
    @PresetMatchesEthLib Spec.currentPresetMinimal _root_.EthLib.Consensus.Preset.minimal
      _root_.EthLib.Consensus.Config.minimal :=
  letI := Spec.currentPresetMinimal
  ⟨EthLib.toSpecPreset_minimal, EthLib.divisorsNonzero_minimal, EthLib.committeeBounds_minimal,
    by decide⟩

/-! ## The caches

Where each cache that the Gloas epoch reads came from (README, "The caches"). The Fulu model
reads the spec values directly, so the Fulu theorems take no cache facts. -/

section Caches

open EpochProofs.CacheBridge

variable [Spec.CurrentPreset]

/-- What the proofs assume about the caches that the Gloas epoch reads. Lean does not check it. -/
structure GloasCacheAssumptions {PubkeyMap : Type}
    (progressiveCache : CacheProofs.ProgressiveBalances.LighthouseProgressiveBalancesCache)
    (cachedTotal : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey)
    (pubkeyMap : PubkeyMap) (state : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was correct at a state `start` of this epoch, and each write
  since then ran its cache update (`CacheUpkeep`). -/
  progressiveBalances :
    ∃ (start : CacheProofs.Spec.BeaconState)
      (startCache : CacheProofs.ProgressiveBalances.LighthouseProgressiveBalancesCache),
      CacheProofs.ProgressiveBalances.ProgressiveBalancesCacheCorrect
        Spec.P.EFFECTIVE_BALANCE_INCREMENT start startCache ∧
      CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start
        (progressiveBalancesStateOf state (state.slot / Spec.P.SLOTS_PER_EPOCH)) startCache
          progressiveCache
  /-- The epoch cache holds the total active balance of an earlier state `built`. That state has
  the same effective balances and the same active validators. -/
  epochCache : ∃ built : Spec.BeaconState,
    Spec.SameActiveBalances (state.slot / Spec.P.SLOTS_PER_EPOCH) built state ∧
    cachedTotal.val = ((built.validators.filter
      (Spec.is_active_validator · (state.slot / Spec.P.SLOTS_PER_EPOCH))).map
        (·.effective_balance)).sum
  /-- The pubkey cache was correct at an earlier state `built`. Then `update_pubkey_cache` added
  the pubkeys that came after it. The map behaves as a finite map (`BehavesAsFiniteMap`). -/
  pubkeyCache : ∃ lookup : PubkeyMap → Spec.BLSPubkey → Option Usize,
    CacheProofs.BehavesAsFiniteMap pubkeyMapOps lookup ∧
    ∃ (built : Spec.BeaconState) (builtMap : PubkeyMap) (builtLength length : Usize),
      built.validators.map (·.pubkey) <+: state.validators.map (·.pubkey) ∧
      CacheProofs.PubkeyCacheCorrect lookup builtMap builtLength (built.validators.map (·.pubkey)) ∧
      CacheProofs.insertPubkeys pubkeyMapOps builtMap builtLength
        ((state.validators.map (·.pubkey)).drop builtLength.val) = ok (some (pubkeyMap, length))

end Caches

/-! ## The untranslated Rust -/

section Glue

variable [Spec.CurrentPreset]

/-- The Rust state `rustState` holds the epoch input `s`, and the untranslated Rust does what the
proofs assume (`Compose.UntranslatedEpochFacts`). One field is a fact about the state:
`UntranslatedSinglePassFacts.depositRoom`, the new validators of the epoch fit under the `2^40`
limit of Lighthouse's validator list. -/
structure GloasUntranslatedRustFacts {RustState RustError : Type}
    (rustCode : Compose.UntranslatedEpochCode RustState RustError) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  holdsInput : rustStateToSpec rustState = s
  /-- What the proofs assume about the untranslated Rust. -/
  untranslatedCode : Compose.UntranslatedEpochFacts rustCode oracle rustStateToSpec rustState

variable [Spec.CurrentFuluConfig]

/-- The Rust state `rustState` holds the epoch input `s`, and the untranslated Rust of the Fulu
epoch does what the proofs assume (`Compose.UntranslatedEpochFactsFulu`). As for Gloas,
`UntranslatedSinglePassFacts.depositRoom` is a fact about the state. -/
structure FuluUntranslatedRustFacts {RustState RustError : Type}
    (rustCode : Compose.UntranslatedEpochCodeFulu RustState RustError) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) (rustState : RustState)
    (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  holdsInput : rustStateToSpec rustState = s
  /-- What the proofs assume about the untranslated Rust. -/
  untranslatedCode : Compose.UntranslatedEpochFactsFulu rustCode oracle rustStateToSpec rustState

end Glue

end EpochProofs.Formalhouse
