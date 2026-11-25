import EpochProofs.HeadlineSpec
import EpochProofs.Assumptions
import EpochProofs.Etheorem.Total
import EpochProofs.Etheorem.Epoch
import EpochProofs.CacheBridge.CapstoneCommittees
import EpochProofs.CacheBridge.BuildPath
import EpochProofs.CacheBridge.Upkeep
import EpochProofs.CachePubkey
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder
import EpochProofs.Sanity.RewardsAndPenalties
import EpochProofs.AgreesEtheorem.Epoch

/-!
# The headline theorems

The results of this project. Each hypothesis is a bundle of `Assumptions.lean` (the preset,
Etheorem and oracle bundles are in `Assumptions/Etheorem.lean`), and each conclusion is defined
below.

- `lighthouse_model_*`: about the Lean model of Lighthouse's epoch processing
  (`process_epoch_lighthouse`). `lighthouse_rust_*`: about the composed Aeneas translation of the
  Rust (`Compose.epoch`), given the glue facts.
- `*_eq_etheorem`: the epoch succeeds and its result equals Etheorem's `processEpoch`.
  `*_agrees_pyspec`: the epoch and this project's hand-written Lean transcription of the pyspec
  (`Spec.process_epoch`) give the same state, or both fail.

`Spec.P` is the preset (`Spec.PresetCfg`) and `Spec.FC` the Fulu config (`Spec.FuluCfg`). Every
theorem holds for any preset and config. The Etheorem ones ask that they agree with Etheorem's
(`hpreset`) and, for Gloas, that Lighthouse's `2^24` limit on `historical_summaries` is at most
Etheorem's (`hhistLimit`). `HeadlinePresets.lean` instantiates them for mainnet and minimal, where
both hold.

The run is described by `oracle` (BLS, SHA-256 and `hash_tree_root`, `Spec.Oracle`),
`fuluOracle` and `blockConfig` (the Fulu block processing parameters), `upgradeConfig` (the Gloas
fork upgrade) and `fuluStart`, the Fulu state the run starts from. `e` is an Etheorem state, and
`toSpecState e` the same state in the transcription's types. For the Rust theorems, `σ` is the
type of the Rust state, `view` maps it to the transcription's state, and `rustGlue` holds the
untranslated Rust between the translated functions (`E` is a type it uses).

Each proof calls one named lemma per step: `lighthouse_epoch_total_etheorem` (the model returns
`ok` and equals Etheorem), `lighthouse_order_epoch_etheorem_reachable_cached_ptc` (the cache
reads), `pubkey_cache_deposit_lookup` (the pubkey cache), `Compose.epoch_spec` (the composed Rust
is the model), and for Fulu `process_epoch_fulu_total`,
`lighthouse_fulu_epoch_sameResultOrBothFail` and `process_epoch_fulu_etheorem`.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.CacheBridge
open Aeneas Aeneas.Std Result
open CacheProofs.PB (LhCache lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {oracle : Spec.Oracle} {fuluOracle : Spec.FuluOracle}
  {blockConfig : Spec.FuluBlockConfig}
  {upgradeConfig : Spec.UpgradeConfig} {fuluStart : Spec.FuluState} {s : Spec.BeaconState}

/-! ## Gloas -/

section Gloas

open EpochProofs.Etheorem

variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {e : EtheoremState}

omit [Spec.FuluCfg] [Spec.FuluCfg.Ok] [Spec.PresetCfg.Bounds] in
/-- The chain bundle and the epoch input give the committee conditions at the state that the
epoch passes to the committee steps. The effective balance cap and the lookahead and PTC window
lengths there follow from the input: the cap is carried from `EBOk`, and that state is the image
of an Etheorem state, whose vectors have fixed sizes. -/
theorem GloasChainAssumptions.atCommitteeStepState (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (horacle : GloasOracleMatchesEtheorem oracle) (hin : Spec.ReachableInvariants (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (h : GloasChainAssumptions oracle (toSpecState e)) :
    Spec.AtCommitteeStepState oracle (toSpecState e) := by
  intro t ht
  have hf := h.committeeStepStateFacts t ht
  have heb := Spec.epochToCommittees_effective_balances oracle _ _ ht hin.1.1.2.2.1
  refine ⟨?_, ⟨h.syncCandidate t ht, h.proposerCandidate t ht, h.enoughActiveForPtc t ht,
    h.syncSelectionEnds t ht, h.proposerSelectionEnds t ht, h.ptcSelectionEnds t ht⟩⟩
  obtain ⟨e14, -, rfl, -⟩ := epochToCommittees_etheorem hpreset oracle horacle.agrees e hin.1.1.1
    hin.1.1.2.1 hetheorem (Nat.lt_of_lt_of_le h.historicalSummariesBelowLimit hhistLimit) ht
  have hvec := vectorLengths_toSpecState hpreset e14
  unfold Spec.BeaconState.VectorLengths at hvec
  obtain ⟨-, -, -, -, -, -, -, hpl, -, -, hptc, -⟩ := hvec
  rw [Spec.P_min_seed] at hpl hptc
  exact ⟨hf.regLen, fun v hv => (heb.1 v hv).2, hpl, hptc, hf.keys⟩

/-! ### Conclusions -/

/-- The Lean model of Lighthouse's Gloas epoch returns `ok s'`, Etheorem's Gloas `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def GloasLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremState) : Prop :=
  ∃ s', Spec.process_epoch_lighthouse o (toSpecState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s'

/-- The composed Rust Gloas epoch (`Compose.epoch`) returns `Ok st'` on the Rust state `st`,
Etheorem's Gloas `processEpoch` succeeds, and its result maps to the view of `st'`. -/
def GloasRustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlue σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EtheoremState) : Prop :=
  ∃ st', Compose.epoch G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = view st'

/-! ### Theorems -/

variable {progressiveCache : LhCache} {totalActiveBalance : U64} {PubkeyMap : Type}
  {pubkeyMapOps : types.state.pubkey_index.IndexMap PubkeyMap Spec.BLSPubkey}
  {pubkeyMap : PubkeyMap}

/-- Gloas, with each cache the one built from the epoch input: at every epoch boundary of a run
from Fulu across the Gloas fork, the Lean model of Lighthouse's epoch succeeds and equals
Etheorem's, and its cache reads give the spec values. -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_at_input
    (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenanceAtInput progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  have hin := hrun.invariants
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  -- The model returns `ok s'`.
  obtain ⟨s', hs', -⟩ := lighthouse_epoch_total_etheorem hpreset hhistLimit oracle
    horacle.agrees horacle.sha32 e hin hpre hetheorem hchain.slotFarFromOverflow
    (vectorLengths_toSpecState hpreset e) hchain.physicalLimits
    (hchain.atCommitteeStepState hpreset hhistLimit horacle hin hetheorem)
  -- Etheorem's result, and the progressive balances and epoch cache reads.
  obtain ⟨⟨he, hc1, hc2, hc3⟩, -⟩ := lighthouse_order_epoch_etheorem_reachable_cached_ptc
    hpreset hhistLimit oracle horacle.agrees horacle.sha32 e hin hpre hetheorem hs' progressiveCache
    hcaches.progressive totalActiveBalance hcaches.epochCache
  -- The pubkey cache lookup. Pubkeys are unique on a reachable state.
  obtain ⟨view, laws, len, hpk⟩ := hcaches.pubkeyCache
  exact ⟨⟨s', hs', he⟩, ⟨hc1, hc2⟩, hc3,
    fun pk => Spec.pubkey_cache_deposit_lookup laws (toSpecState e) hpk hin.1.2.1 pk⟩

/-- Gloas: at every epoch boundary of a run from Fulu across the Gloas fork, the Lean model of
Lighthouse's epoch succeeds and equals Etheorem's, and its cache reads give the spec values. The
epoch cache total and the pubkey cache were built at earlier states (`GloasCacheProvenance`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  -- Carry each cache build fact to the epoch input.
  obtain ⟨b, hagree, htotal⟩ := hcaches.epochCache
  obtain ⟨view, laws, b', m0, len0, len, hprefix, hpk0, hupd⟩ := hcaches.pubkeyCache
  exact lighthouse_model_gloas_epoch_eq_etheorem_at_input hpreset hhistLimit hrun hchain hetheorem
    horacle ⟨hcaches.progressive, epoch_cache_total_carry totalActiveBalance.val htotal hagree,
      view, laws, len, pubkey_cache_carry laws hprefix hpk0 hupd⟩

/-- `lighthouse_model_gloas_epoch_eq_etheorem` with the progressive balances cache kept up to
date since a state of the epoch (`GloasCacheProvenanceUpkeep`). -/
theorem lighthouse_model_gloas_epoch_eq_etheorem_upkeep (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenanceUpkeep progressiveCache totalActiveBalance pubkeyMapOps
      pubkeyMap (toSpecState e)) :
    GloasLighthouseModelEqualsEtheorem oracle e ∧
      GloasCacheReadsCorrect progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
        (toSpecState e) := by
  -- The upkeep keeps the cache coherent up to the epoch input.
  obtain ⟨start, cache0, hcoh0, hup⟩ := hcaches.progressive
  exact lighthouse_model_gloas_epoch_eq_etheorem hpreset hhistLimit hrun hchain hetheorem horacle
    ⟨coherent_of_upkeep hcoh0 hup, hcaches.epochCache, hcaches.pubkeyCache⟩

/-- Gloas, for the composed Rust: the same, for `Compose.epoch` on a Rust state that views as
the epoch input, given the glue facts. -/
theorem lighthouse_rust_gloas_epoch_eq_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : GloasEpochRun oracle fuluOracle blockConfig upgradeConfig fuluStart (toSpecState e))
    (hchain : GloasChainAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    (hcaches : GloasCacheProvenance progressiveCache totalActiveBalance pubkeyMapOps pubkeyMap
      (toSpecState e))
    (hrust : GloasRustGlueFacts rustGlue oracle view rustState (toSpecState e)) :
    GloasRustEqualsEtheorem rustGlue view rustState e := by
  obtain ⟨⟨s', hs', e', he', habs⟩, -⟩ := lighthouse_model_gloas_epoch_eq_etheorem hpreset
    hhistLimit hrun hchain hetheorem horacle hcaches
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  -- The composed Rust returns the model's state.
  obtain ⟨st', hep, hv⟩ := Compose.epoch_spec rustGlue oracle view rustState hrust.glue
    (by rw [hrust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hpre.2.1)
    (by rw [hrust.viewEq]; exact vectorLengths_toSpecState hpreset e) s' (by rw [hrust.viewEq]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

end Gloas

/-! ## Fulu -/

section Fulu

open EpochProofs.Etheorem.Fulu

variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {e : EtheoremState}

omit [Spec.PresetCfg.Bounds] in
/-- The Fulu chain bundle and the epoch input give the committee conditions at the state that
the epoch passes to the committee steps, as the Gloas one. -/
theorem FuluChainAssumptions.atCommitteeStepState (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    (horacle : FuluOracleMatchesEtheorem oracle) (hin : Spec.ReachableInvariants (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (h : FuluChainAssumptions oracle (toSpecState e)) :
    Spec.FuluAtCommitteeStepState oracle (toSpecState e) := by
  intro t ht
  have hf := h.committeeStepStateFacts t ht
  have heb := Spec.epochToCommitteesFulu_effective_balances oracle _ _ ht hin.1.1.2.2.1
  refine ⟨?_, ⟨h.syncCandidate t ht, h.proposerCandidate t ht, h.syncSelectionEnds t ht,
    h.proposerSelectionEnds t ht⟩⟩
  obtain ⟨e13, -, rfl⟩ := epochToCommitteesFulu_etheorem hpreset oracle horacle.agrees e
    hetheorem ht
  have hvec := fuluVectorLengths_toSpecState hpreset e13
  unfold Spec.BeaconState.FuluVectorLengths at hvec
  obtain ⟨-, -, -, -, -, -, -, hpl⟩ := hvec
  rw [Spec.P_min_seed] at hpl
  exact ⟨hf.regLen, fun v hv => (heb.1 v hv).2, hpl, hf.keys⟩

/-- The Lean model of Lighthouse's Fulu epoch returns `ok s'`, Etheorem's Fulu `processEpoch`
succeeds on the same state, and its result maps to `s'`. -/
def FuluLighthouseModelEqualsEtheorem (o : Spec.Oracle) (e : EtheoremState) : Prop :=
  ∃ s', Spec.process_epoch_lighthouse_fulu o (toSpecState e) = .ok s' ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = s'

/-- The composed Rust Fulu epoch (`Compose.epochFulu`) returns `Ok st'`, Etheorem's Fulu
`processEpoch` succeeds, and its result maps to the view of `st'`. -/
def FuluRustEqualsEtheorem {σ E : Type} (G : Compose.EpochGlueFulu σ E)
    (view : σ → Spec.BeaconState) (st : σ) (e : EtheoremState) : Prop :=
  ∃ st', Compose.epochFulu G st = ok (some st') ∧
    ∃ e', (EthCLSpecs.Fulu.processEpoch
        (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ toSpecState e' = view st'

/-- Fulu: at every epoch boundary of a Fulu run, the Lean model of Lighthouse's epoch succeeds
and equals Etheorem's. -/
theorem lighthouse_model_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState e))
    (hchain : FuluChainAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    FuluLighthouseModelEqualsEtheorem oracle e := by
  have hin := hrun.invariants
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  obtain ⟨⟨⟨hb, -, heb, -, hsup⟩, -, hcons⟩, -, -⟩ := hin
  -- The Fulu spec epoch returns `ok s'`.
  obtain ⟨s', hs'⟩ := Spec.process_epoch_fulu_total oracle (toSpecState e) hb.2.1
    hchain.slotFarFromOverflow hpre.1 (fuluVectorLengths_toSpecState hpreset e) hb.1 heb hcons
    hsup.2.2 hchain.physicalLimits
    (Spec.committeesOkFulu_of oracle _ hchain.slotFarFromOverflow
      (hchain.atCommitteeStepState hpreset horacle hrun.invariants hetheorem))
  -- The model gives the same state, and Etheorem's result maps to it.
  have hlh := (Spec.lighthouse_fulu_epoch_sameResultOrBothFail oracle (toSpecState e)
    hrun.invariants hpre s').mpr hs'
  exact ⟨s', hlh, process_epoch_fulu_etheorem hpreset oracle horacle.agrees horacle.sha32 e
    hetheorem hs'⟩

/-- Fulu, for the composed Rust. -/
theorem lighthouse_rust_fulu_epoch_eq_etheorem
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ}
    (hrun : FuluEpochRun oracle fuluOracle blockConfig fuluStart (toSpecState e))
    (hchain : FuluChainAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    (hrust : FuluRustGlueFacts rustGlue oracle view rustState (toSpecState e)) :
    FuluRustEqualsEtheorem rustGlue view rustState e := by
  obtain ⟨s', hs', e', he', habs⟩ := lighthouse_model_fulu_epoch_eq_etheorem hpreset hrun hchain
    hetheorem horacle
  have hpre := hrun.atEpochBoundary hchain.historicalSummariesBelowLimit
  have hvec := fuluVectorLengths_toSpecState hpreset e
  unfold Spec.BeaconState.FuluVectorLengths at hvec
  obtain ⟨-, -, -, -, hjb, -, -, hpl⟩ := hvec
  -- The composed Rust returns the model's state.
  obtain ⟨st', hep, hv⟩ := Compose.epochFulu_spec rustGlue oracle view rustState hrust.glue
    (by rw [hrust.viewEq]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hpre.2.1)
    (by rw [hrust.viewEq]; exact hjb) (by rw [hrust.viewEq]; exact hpl) s'
    (by rw [hrust.viewEq]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

end Fulu

end EpochProofs.Formalhouse
