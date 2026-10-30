import EpochProofs.Assumptions.Etheorem
import EpochProofs.Sanity.PtcIndices
import EpochProofs.Sanity.Invariants.BalanceFloor
import EpochProofs.Sanity.Invariants.LighthouseEpoch
import EpochProofs.Sanity.Invariants.ForkUpgrade
import EpochProofs.Sanity.Invariants.FuluReachable
import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Sanity.Invariants.TotalityRows
import EpochProofs.Sanity.Invariants.TotalityFulu
import EpochProofs.CacheBridge.ProgressiveBalances
import EpochProofs.CacheBridge.EpochCache
import EpochProofs.Trusted.CacheUpkeep
import EpochProofs.Compose.Epoch
import EpochProofs.Compose.Fulu

/-!
# The assumptions of the headline theorems

Every hypothesis of the theorems in `Headline.lean` is one of the bundles below, with each field
written out. The bundles follow the groups of the README's "What is trusted".

- The preset, `Etheorem.PresetMatchesEtheorem` (`Fulu.PresetMatchesEtheorem`): the preset
  `Spec.P` has the values of Etheorem's preset that the epoch reads.
- The run, `GloasEpochRun` (`FuluEpochRun`): the state is an epoch input of a run from a start
  state with the genesis invariants, with the supply bounds of the run.
- The chain, `GloasChainAssumptions` (`FuluChainAssumptions`): the pyspec preconditions, the
  hash-output facts of the spec selections, the physical limits, and reachable-state facts not
  yet carried to the epoch (README, "Assumptions about the chain").
- Etheorem, `Etheorem.GloasEtheoremDivergenceAssumptions` (Fulu:
  `Fulu.FuluEtheoremBridgeConditions`): what the bridge to Etheorem needs beyond the pyspec.
- The oracle, `Etheorem.GloasOracleMatchesEtheorem` (`Fulu.FuluOracleMatchesEtheorem`): the spec
  `Oracle` is Etheorem's SHA-256, `hash_tree_root` and BLS, and SHA-256 returns 32 bytes.
- The caches, `GloasCacheProvenance`, and its variants `GloasCacheProvenanceUpkeep` and
  `GloasCacheProvenanceAtInput`: where each cache that the Gloas epoch reads came from.
- The Rust glue, `GloasRustGlueFacts` (`FuluRustGlueFacts`): the Rust state views as the epoch
  input, and the glue facts of the composed Rust hold.

The preset, Etheorem and oracle bundles are in `Assumptions/Etheorem.lean`. The step proofs of
`Etheorem/` read them, and they must not import the Aeneas code that the bundles here need. The
bundles here are about the transcription's state (`Spec.BeaconState`) and live in
`EpochProofs.Formalhouse`.
-/

namespace EpochProofs.Formalhouse

open Aeneas Aeneas.Std Result

/-! ## The runs -/

section Runs

variable [Spec.PresetCfg] [Spec.FuluCfg]

/-- `s` is an input of the Gloas `process_epoch` in a run that starts in Fulu, from a state with
the invariants of a genesis state, and crosses the Gloas fork (`upgrade_to_gloas`). The run
carries its supply bounds inside `run`: before each Fulu block, before each Gloas block, and
`EpochBalanceBounds` at each Gloas epoch input. The Gloas bounds are stated over the run from the
Gloas fork state, which `run` quantifies over, so they cannot be separate fields as in
`FuluEpochRun`. -/
structure GloasEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- The run, in three parts. The Fulu part: the total active balance is at most 139M ETH
  before each Fulu block (`SupplyBoundFulu`); Fulu blocks reach `fs`; the slots from `fs` reach
  `t` and `t1` at the last slot of an epoch, before the fork slot `slot`. The fork: the Fulu
  epoch gives `s2`, and `upgrade_to_gloas` at the next slot gives `g`. The Gloas part: the
  supply bounds of the Gloas run from `g` (`SupplyBound`, and `EpochBalanceBounds` at each epoch
  input, `EpochEcon`); Gloas blocks reach `gs`; the slots from `gs` reach `u` and then `s`, at
  the last slot of an epoch, before `slotG`. -/
  run : ∃ (fs t t1 : Spec.FuluState) (s2 g : Spec.BeaconState) (slot : Spec.Slot)
      (max_blobs_per_block : Spec.Epoch → Spec.Uint64) (GLOAS_FORK_EPOCH : Spec.Epoch)
      (gs u : Spec.BeaconState) (slotG : Spec.Slot),
    Spec.SupplyBoundFulu o fo c init ∧
    Spec.ReachableFulu o fo c init fs ∧ slot < 2 ^ 64 ∧ Spec.SlotReachFulu o fo fs slot t ∧
    t.state.slot < slot ∧ Spec.process_slot_fulu Spec.P o fo t = .ok t1 ∧
    (t1.state.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0 ∧
    Spec.process_epoch_fulu_m o t1.state = .ok s2 ∧
    Spec.upgrade_to_gloas Spec.P o uc
      { t1 with state := { s2 with slot := s2.slot + 1 } } = .ok g ∧
    Spec.SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH g ∧
    Spec.EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH g Spec.EpochBalanceBounds ∧
    Spec.Reachable o max_blobs_per_block GLOAS_FORK_EPOCH g gs ∧ slotG < 2 ^ 64 ∧
    Spec.SlotReachG o gs slotG u ∧ u.slot < slotG ∧
    Spec.process_slot Spec.P o u = .ok s ∧
    (s.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0

/-- `s` is an input of the Fulu `process_epoch` in a run of Fulu blocks from a state with the
invariants of a genesis state, with the supply bounds of the run. -/
structure FuluEpochRun (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  /-- The Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- The total active balance is at most 139M ETH before each block (`SupplyBoundFulu`). -/
  activeBalanceBound : Spec.SupplyBoundFulu o fo c init
  /-- `EpochBalanceBounds` at each epoch input of the run. -/
  epochBalanceBounds : Spec.EpochEconFulu o fo c init Spec.EpochBalanceBounds
  /-- The run: Fulu blocks reach `fs`, and the slots from `fs` reach `t` and then `s`, at the last
  slot of an epoch, before `slot`. -/
  run : ∃ (fs t t1 : Spec.FuluState) (slot : Spec.Slot),
    Spec.ReachableFulu o fo c init fs ∧ slot < 2 ^ 64 ∧ Spec.SlotReachFulu o fo fs slot t ∧
    t.state.slot < slot ∧ Spec.process_slot_fulu Spec.P o fo t = .ok t1 ∧
    (t1.state.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0 ∧ t1.state = s

end Runs

/-! ## The chain -/

section Chain

variable [Spec.PresetCfg]

/-- The assumptions about the chain at a Gloas epoch input (README, "Assumptions about the
chain"), beyond the run. `t` ranges over the one state that the spec epoch passes to its
committee steps (`epochToCommittees`, a function of `s`). Without the first three, the pyspec
raises. -/
structure GloasChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec precondition: a validator is active at the next epoch, a sync committee
  candidate. -/
  syncCandidate : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- Pyspec precondition (F4): an unslashed validator is active two epochs ahead, a proposer
  candidate. -/
  proposerCandidate : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []
  /-- Pyspec precondition (F12): at least `SLOTS_PER_EPOCH` validators are active two epochs
  ahead. With fewer, the first slot of that epoch has an empty PTC and `compute_ptc`
  asserts. -/
  enoughActiveForPtc : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.P.SLOTS_PER_EPOCH ≤
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)).length
  /-- Hash output: the sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
      seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- Hash output: the proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t (Spec.unslashedActive t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1
      true
  /-- Hash output: each PTC selection of the epoch two ahead ends within `2^64` passes. -/
  ptcSelectionEnds : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t → ∀ slot,
    slot / Spec.P.SLOTS_PER_EPOCH = t.slot / Spec.P.SLOTS_PER_EPOCH + 2 → ∀ l,
    Spec.ptcIndices Spec.P o t (slot / Spec.P.SLOTS_PER_EPOCH) slot = .ok l →
      ∀ seed, Spec.SelFin Spec.P o t l seed Spec.P.PTC_SIZE false
  /-- Physical limits (`PhysicalLimits`): inactivity scores below `2^22` (F5), the effective
  balance sum, funds, exit queue and validator count bounds, and the participation bound. -/
  physicalLimits : Spec.PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. The pyspec `get_block_root` raises
  above. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries, Lighthouse's list limit. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit s
  /-- Reachable-state fact not yet carried to the epoch: the SSZ vectors have their lengths. The
  Lean state holds them as lists. -/
  vectorLengths : s.VectorLengths Spec.P
  /-- Reachable-state facts not yet carried to the epoch, at `t` (`CommitteeStepFacts`): at most
  `2^40` validators, effective balances at most 2048 ETH, the lookahead and PTC window lengths,
  valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.CommitteeStepFacts o t

variable [Spec.FuluCfg]

/-- The assumptions about the chain at a Fulu epoch input, beyond the run. `t` ranges over the
one state that the spec epoch passes to its committee steps (`epochToCommitteesFulu`). Fulu has
no F4 and no F12. -/
structure FuluChainAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- Pyspec precondition: a validator is active at the next epoch, a sync committee
  candidate. -/
  syncCandidate : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1) ≠ []
  /-- Pyspec precondition: a validator is active two epochs ahead, a proposer candidate. Unlike
  Gloas F4, a slashed validator counts. -/
  proposerCandidate : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2) ≠ []
  /-- Hash output: the sync committee selection ends within `2^64` passes. -/
  syncSelectionEnds : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 1))
      seed Spec.P.SYNC_COMMITTEE_SIZE true
  /-- Hash output: the proposer selection ends within `2^64` passes. -/
  proposerSelectionEnds : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t → ∀ seed,
    Spec.SelFin Spec.P o t
      (Spec.get_active_validator_indices t (t.slot / Spec.P.SLOTS_PER_EPOCH + 2)) seed 1 true
  /-- Physical limits (F5 and the supply, funds, exit and validator count bounds). -/
  physicalLimits : Spec.PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- Physical limit: fewer than `2^24` historical summaries. -/
  historicalSummariesBelowLimit : Spec.HistoricalSummariesBelowLimit s
  /-- Reachable-state fact not yet carried: the Fulu SSZ vectors have their lengths. -/
  vectorLengths : s.FuluVectorLengths Spec.P
  /-- Reachable-state facts not yet carried, at `t` (`FuluCommitteeStepFacts`): registry size,
  effective balances, lookahead length, valid pubkeys. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.FuluCommitteeStepFacts o t

end Chain

/-! ## The caches

Where each cache that the Gloas epoch reads came from (README, "The caches"). The Fulu model
reads the spec values directly, so the Fulu theorems take no cache facts. -/

section Caches

open EpochProofs.CacheBridge

variable [Spec.PresetCfg]

/-- Where each cache that the Gloas epoch reads came from. -/
structure GloasCacheProvenance {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache (`LhCache`, the `Inner` of Lighthouse's
  `ProgressiveBalancesCache`) is coherent with the epoch input at its current epoch. -/
  progressive : CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT
    (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) progressiveCache
  /-- The epoch cache total was built at a state `b` of the same epoch that agrees with the
  epoch input on which validators are active (`ActiveAgree`): it is the active effective
  balance sum of `b`. -/
  epochCache : ∃ b : Spec.BeaconState, Spec.ActiveAgree (s.slot / Spec.P.SLOTS_PER_EPOCH) b s ∧
    totalActiveBalance.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator)
        (s.slot / Spec.P.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance))
  /-- The pubkey cache `pubkeyMap` is a cache built at an earlier state `b'`, whose pubkeys are a
  prefix of the input's, and then completed by `update_pubkey_cache` (`insertAll`), over a map
  with the `IndexMapLaws`. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize),
      b'.validators.map (·.pubkey) <+: s.validators.map (·.pubkey) ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (pubkeyMap, len))

/-- `GloasCacheProvenance` with the progressive balances cache kept up to date since a state of
the epoch, instead of coherent at the input. -/
structure GloasCacheProvenanceUpkeep {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- The progressive balances cache was coherent at a state `start` of the epoch (after a fresh
  build, or after the epoch transition), and every write since ran its cache hook (`CacheUpkeep`,
  U1 to U4 in `Trusted/CacheUpkeep.lean`). -/
  progressive : ∃ (start : CacheProofs.Spec.BeaconState) (cache0 : CacheProofs.PB.LhCache),
    CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT start cache0 ∧
    CacheUpkeep Spec.P.EFFECTIVE_BALANCE_INCREMENT start
      (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) cache0 progressiveCache
  /-- As `GloasCacheProvenance.epochCache`. -/
  epochCache : ∃ b : Spec.BeaconState, Spec.ActiveAgree (s.slot / Spec.P.SLOTS_PER_EPOCH) b s ∧
    totalActiveBalance.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (b.validators.map ecValidator)
        (s.slot / Spec.P.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance))
  /-- As `GloasCacheProvenance.pubkeyCache`. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ (b' : Spec.BeaconState) (m0 : M) (len0 len : Usize),
      b'.validators.map (·.pubkey) <+: s.validators.map (·.pubkey) ∧
      CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)) ∧
      CacheProofs.insertAll pubkeyMapOps m0 len0 ((s.validators.map (·.pubkey)).drop len0.val) =
        ok (some (pubkeyMap, len))

/-- The cache facts stated at the epoch input itself: each cache is the one built from the
input. -/
structure GloasCacheProvenanceAtInput {M : Type} (progressiveCache : CacheProofs.PB.LhCache)
    (totalActiveBalance : U64)
    (pubkeyMapOps : types.state.pubkey_index.IndexMap M Spec.BLSPubkey) (pubkeyMap : M)
    (s : Spec.BeaconState) : Prop where
  /-- As `GloasCacheProvenance.progressive`. -/
  progressive : CacheProofs.PB.Coherent Spec.P.EFFECTIVE_BALANCE_INCREMENT
    (pbState s (s.slot / Spec.P.SLOTS_PER_EPOCH)) progressiveCache
  /-- The epoch cache total is the active effective balance sum of the input. -/
  epochCache : totalActiveBalance.val = CacheProofs.EpochCache.activeSum
    (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator)
      (s.slot / Spec.P.SLOTS_PER_EPOCH))
    (s.validators.map (·.effective_balance))
  /-- The pubkey cache is coherent with the pubkeys of the input. -/
  pubkeyCache : ∃ view : M → Spec.BLSPubkey → Option Usize,
    CacheProofs.IndexMapLaws pubkeyMapOps view ∧
    ∃ len : Usize, CacheProofs.Coherent view pubkeyMap len (s.validators.map (·.pubkey))

end Caches

/-! ## The Rust glue -/

section Glue

variable [Spec.PresetCfg]

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
hold (`Compose.EpochLinks`: the contracts of `Trusted/`, the fields each wrapper borrows, the
values passed to the translated code). One field of the glue is a state fact, not a fact about
the Rust: `SinglePassLinks.depositRoom`, that the new validators of the epoch fit under the
`2^40` limit of Lighthouse's validator list. It is the Lighthouse counterpart of
`GloasEtheoremDivergenceAssumptions.depositRoom`, stated at the state after justification. -/
structure GloasRustGlueFacts {σ E : Type} (G : Compose.EpochGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state views as the epoch input. -/
  viewEq : view st = s
  /-- The glue facts. -/
  glue : Compose.EpochLinks G o view st

variable [Spec.FuluCfg]

/-- The Rust state `st` views as the epoch input `s`, and the glue facts of the composed Rust
Fulu epoch hold (`Compose.EpochLinksFulu`). As for Gloas, the glue contains one state fact,
`SinglePassLinks.depositRoom`. -/
structure FuluRustGlueFacts {σ E : Type} (G : Compose.EpochGlueFulu σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (st : σ) (s : Spec.BeaconState) : Prop where
  /-- The Rust state views as the epoch input. -/
  viewEq : view st = s
  /-- The glue facts. -/
  glue : Compose.EpochLinksFulu G o view st

end Glue

end EpochProofs.Formalhouse
