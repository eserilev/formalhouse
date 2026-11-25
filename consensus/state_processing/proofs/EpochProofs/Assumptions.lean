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

/-!
# The assumptions of the main theorems

- The run, `GloasEpochRun` and `FuluEpochRun` (`Runs.lean`): the state is an input of
  `process_epoch` on a chain from a start state with the facts of a genesis state. The total stake
  stays below its bounds.
- The chain, `GloasChainAssumptions` and `FuluChainAssumptions`: what the epoch needs to succeed.
- The caches, `GloasCacheAssumptions`: where each cache that the Gloas epoch reads came from. The
  Fulu model reads the spec values, so the Fulu theorems take no cache facts.
- The untranslated Rust, `GloasRustGlueFacts` and `FuluRustGlueFacts`: what the code that Aeneas
  does not translate does.
-/

namespace EpochProofs.Formalhouse

open Aeneas Aeneas.Std Result

/-! ## The chain -/

section Chain

variable [Spec.PresetCfg]

/-- What the Gloas epoch needs from the chain, beyond the run, to succeed. -/
structure GloasChainAssumptions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the three committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochToCommittees Spec.P oracle state = .ok committeeInput →
      Spec.CommitteeStepPreconds oracle committeeInput ∧
      Spec.SelectionStateFacts oracle committeeInput
  /-- The supply and time bounds. -/
  physicalLimits : Spec.PhysicalLimits state
  /-- The slot is far below `2^64`. The pyspec `get_block_root` raises near `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

variable [Spec.FuluCfg]

/-- What the Fulu epoch needs from the chain, beyond the run, to succeed. -/
structure FuluChainAssumptions (oracle : Spec.Oracle) (state : Spec.BeaconState) : Prop where
  /-- `committeeInput` is the state before the two committee steps. There, the pyspec does not
  raise, each selection ends, the registry is below its limit and the pubkeys are valid. -/
  committeeSteps : ∀ committeeInput,
    Spec.epochToCommitteesFulu Spec.P Spec.FC oracle state = .ok committeeInput →
      Spec.FuluCommitteeStepPreconds oracle committeeInput ∧
      Spec.SelectionStateFacts oracle committeeInput
  /-- The supply and time bounds. -/
  physicalLimits : Spec.PhysicalLimits state
  /-- The slot is far below `2^64`. -/
  slotFarFromOverflow : state.slot + 8192 < 2 ^ 64
  /-- Lighthouse's list of historical summaries has room. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit state

end Chain

/-! ## The caches

Where each cache that the Gloas epoch reads came from (README, "The caches"). The Fulu model
reads the spec values directly, so the Fulu theorems take no cache facts. -/

section Caches

open EpochProofs.CacheBridge

variable [Spec.PresetCfg]

/-- What the proofs assume about the caches that the Gloas epoch reads. Lean does not check it. -/
structure GloasCacheAssumptions {PubkeyMap : Type}
    (progressiveCache : CacheProofs.PB.LhCache) (cachedTotal : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey)
    (pubkeyMap : PubkeyMap) (state : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was correct at a state `start` of this epoch, and each write
  since then ran its cache update (`CacheUpkeep`). -/
  progressiveBalances :
    ∃ (start : CacheProofs.Spec.BeaconState) (startCache : CacheProofs.PB.LhCache),
      CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start startCache ∧
      CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start
        (pbState state (state.slot / Spec.P.SLOTS_PER_EPOCH)) startCache progressiveCache
  /-- The epoch cache holds the total active balance of an earlier state `built`. That state has
  the same effective balances and the same active validators. -/
  epochCache : ∃ built : Spec.BeaconState,
    Spec.ActiveAgree (state.slot / Spec.P.SLOTS_PER_EPOCH) built state ∧
    cachedTotal.val = ((built.validators.filter
      (Spec.is_active_validator · (state.slot / Spec.P.SLOTS_PER_EPOCH))).map
        (·.effective_balance)).sum
  /-- The pubkey cache was correct at an earlier state `built`. Then `update_pubkey_cache` added
  the pubkeys that came after it. The map behaves as a finite map (`IndexMapLaws`). -/
  pubkeyCache : ∃ lookup : PubkeyMap → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps lookup ∧
    ∃ (built : Spec.BeaconState) (builtMap : PubkeyMap) (builtLength length : Usize),
      built.validators.map (·.pubkey) <+: state.validators.map (·.pubkey) ∧
      CacheProofs.Coherent lookup builtMap builtLength (built.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps builtMap builtLength
        ((state.validators.map (·.pubkey)).drop builtLength.val) = ok (some (pubkeyMap, length))

end Caches

/-! ## The untranslated Rust -/

section Glue

variable [Spec.PresetCfg]

/-- The Rust state `st` holds the epoch input `s`, and the untranslated Rust does what the proofs
assume (`Compose.EpochLinks`). One field is a fact about the state: `SinglePassLinks.depositRoom`,
the new validators of the epoch fit under the `2^40` limit of Lighthouse's validator list. -/
structure GloasRustGlueFacts {σ E : Type} (G : Compose.EpochGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  viewEq : view st = s
  /-- What the proofs assume about the untranslated Rust. -/
  glue : Compose.EpochLinks G o view st

variable [Spec.FuluCfg]

/-- The Rust state `st` holds the epoch input `s`, and the untranslated Rust of the Fulu epoch does
what the proofs assume (`Compose.EpochLinksFulu`). As for Gloas, `SinglePassLinks.depositRoom` is a
fact about the state. -/
structure FuluRustGlueFacts {σ E : Type} (G : Compose.EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state holds the epoch input. -/
  viewEq : view st = s
  /-- What the proofs assume about the untranslated Rust. -/
  glue : Compose.EpochLinksFulu G o view st

end Glue

end EpochProofs.Formalhouse
