import EpochProofs.AgreesEtheorem.Epoch
import EpochProofs.Compose.Epoch
import EpochProofs.Compose.Fulu

/-!
# Lighthouse and Etheorem: the same state, or both fail

The headline theorems of the equivalence. They state `SameResultOrBothFail` of the Lean model of
Lighthouse's epoch (`process_epoch_lighthouse`) and Etheorem's `processEpoch`
(`etheoremProcessEpoch`): both return `ok` with the same state, or both fail. The
`*_eq_etheorem` theorems of `Headline.lean` prove that both succeed, and so need the pyspec
preconditions. These do not.

Each hypothesis is a fact about the epoch input, not about the run that reached it:

- `hpreset`, `hhistLimit`, `horacle`: the preset and the oracle agree with Etheorem's
  (`Assumptions/Etheorem.lean`).
- `hetheorem`: what Etheorem needs beyond the pyspec, because Etheorem diverges from it
  (`GloasEtheoremDivergenceAssumptions`: alpha.11 list limits F6, F10;
  `FuluEtheoremBridgeConditions`).
- `hstate`: the state facts of `GloasEquivalenceAssumptions` (`FuluEquivalenceAssumptions`).
  `GloasEpochRun.invariants` and `GloasEpochRun.atEpochBoundary` (`Headline.lean`) prove the
  first two at every epoch input of a reachable run.

`lighthouse_rust_*_of_etheorem_ok` carry one direction to the composed Rust: when Etheorem
succeeds, the Rust returns `Ok` with the same state. The other direction needs "the Rust returns
`Ok` only when the model does", which the glue facts do not state.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open Aeneas Aeneas.Std Result

/-! ## The state facts -/

section Bundles

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok]

/-- The facts about a Gloas epoch input `s` that the equivalence needs. Each one says why. -/
structure GloasEquivalenceAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- The reachable-state invariants (`ReachableInvariants`). The model of Lighthouse and the
  transcription give the same result on them (`process_epoch_lh_full_sameResultOrBothFail'`): the
  Lighthouse order of the per-validator steps differs from the spec's, and near `2^64` it
  overflows where the spec does not (`rewards_overflow_example`). -/
  reachableInvariants : Spec.ReachableInvariants s
  /-- The last slot of an epoch, the next slot in `u64`, and fewer than `2^24` historical
  summaries, Lighthouse's list limit (`AtEpochBoundary`). Lighthouse's epoch is at an epoch
  boundary, and the transcription has no list limit. -/
  atEpochBoundary : Spec.AtEpochBoundary s
  /-- Physical limits (`PhysicalLimits`, F5). The proof takes the success of the steps before the
  committee steps from these bounds (`epochToCommittees_total`). It does not compare the failures
  of those steps one by one. -/
  physicalLimits : Spec.PhysicalLimits s
  /-- Physical limit: the slot is `8192` below `2^64`. As `physicalLimits`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- At the state `t` that the epoch passes to the committee steps: at most `2^40` validators,
  effective balances of at most 2048 ETH, valid pubkeys (`SelectionStateFacts`). The pyspec
  raises without them where Etheorem does not: `eth_aggregate_pubkeys` asserts `KeyValidate`,
  and the pyspec checks `uint64` products that Etheorem computes in `Nat`. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommittees Spec.P o s = .ok t →
    Spec.SelectionStateFacts o t

variable [Spec.FuluCfg]

/-- `GloasEquivalenceAssumptions` for a Fulu epoch input. -/
structure FuluEquivalenceAssumptions (o : Spec.Oracle) (s : Spec.BeaconState) : Prop where
  /-- As `GloasEquivalenceAssumptions.reachableInvariants`. -/
  reachableInvariants : Spec.ReachableInvariants s
  /-- As `GloasEquivalenceAssumptions.atEpochBoundary`. -/
  atEpochBoundary : Spec.AtEpochBoundary s
  /-- As `GloasEquivalenceAssumptions.physicalLimits`. -/
  physicalLimits : Spec.PhysicalLimits s
  /-- As `GloasEquivalenceAssumptions.slotFarFromOverflow`. -/
  slotFarFromOverflow : s.slot + 8192 < 2 ^ 64
  /-- As `GloasEquivalenceAssumptions.committeeStepStateFacts`, at the state that the Fulu
  epoch passes to its committee steps. -/
  committeeStepStateFacts : ∀ t, Spec.epochToCommitteesFulu Spec.P Spec.FC o s = .ok t →
    Spec.SelectionStateFacts o t

end Bundles

/-! ## Gloas -/

section Gloas

open EpochProofs.Etheorem

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {oracle : Spec.Oracle}
  {e : EtheoremState}

/-- Gloas: the Lean model of Lighthouse's epoch and Etheorem's `processEpoch` give the same
state, or both fail. No pyspec precondition. -/
theorem lighthouse_model_gloas_epoch_agrees_etheorem (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hstate : GloasEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_epoch_agrees_etheorem hpreset hhistLimit oracle horacle.agrees horacle.sha32 e
    hstate.reachableInvariants hstate.atEpochBoundary hetheorem hstate.slotFarFromOverflow
    hstate.physicalLimits hstate.committeeStepStateFacts

/-- Gloas, for the composed Rust: when Etheorem's `processEpoch` succeeds, `Compose.epoch`
returns `Ok` on a Rust state that views as the epoch input, and its state equals Etheorem's. -/
theorem lighthouse_rust_gloas_epoch_of_etheorem_ok (hpreset : PresetMatchesEtheorem Spec.P)
    (hhistLimit : Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT ≤
      EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (hstate : GloasEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : GloasEtheoremDivergenceAssumptions e)
    (horacle : GloasOracleMatchesEtheorem oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState}
    {rustState : σ} (hview : view rustState = toSpecState e)
    (hglue : Compose.EpochLinks rustGlue oracle view rustState) :
    ∀ s', etheoremProcessEpoch e = .ok s' →
      ∃ st', Compose.epoch rustGlue rustState = ok (some st') ∧ view st' = s' := by
  intro s' hs'
  have hm := ((lighthouse_model_gloas_epoch_agrees_etheorem hpreset hhistLimit hstate hetheorem
    horacle) s').mpr hs'
  rw [← hview] at hm
  exact Compose.epoch_spec rustGlue oracle view rustState hglue
    (by rw [hview]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hstate.atEpochBoundary.2.1)
    (by rw [hview]; exact vectorLengths_toSpecState hpreset e) s' hm

end Gloas

/-! ## Fulu -/

section Fulu

open EpochProofs.Etheorem.Fulu

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {oracle : Spec.Oracle}
  {e : EtheoremState}

/-- Fulu: the Lean model of Lighthouse's Fulu epoch and Etheorem's Fulu `processEpoch` give the
same state, or both fail. No pyspec precondition. `hetheorem` keeps `proposerFin`, an Etheorem
divergence: Etheorem's Fulu selects proposers with the Gloas selection, which fails one pass
before the Electra loop of the pyspec. -/
theorem lighthouse_model_fulu_epoch_agrees_etheorem
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    (hstate : FuluEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle) :
    Spec.SameResultOrBothFail (Spec.process_epoch_lighthouse_fulu oracle (toSpecState e))
      (etheoremProcessEpoch e) :=
  lighthouse_fulu_epoch_agrees_etheorem hpreset oracle horacle.agrees horacle.sha32 e hetheorem
    hstate.reachableInvariants hstate.atEpochBoundary hstate.slotFarFromOverflow
    hstate.physicalLimits hstate.committeeStepStateFacts

/-- Fulu, for the composed Rust: when Etheorem's Fulu `processEpoch` succeeds,
`Compose.epochFulu` returns `Ok`, and its state equals Etheorem's. -/
theorem lighthouse_rust_fulu_epoch_of_etheorem_ok
    (hpreset : PresetMatchesEtheorem Spec.P Spec.FC)
    (hstate : FuluEquivalenceAssumptions oracle (toSpecState e))
    (hetheorem : FuluEtheoremBridgeConditions Spec.P oracle e)
    (horacle : FuluOracleMatchesEtheorem oracle)
    {σ E : Type} {rustGlue : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState}
    {rustState : σ} (hview : view rustState = toSpecState e)
    (hglue : Compose.EpochLinksFulu rustGlue oracle view rustState) :
    ∀ s', etheoremProcessEpoch e = .ok s' →
      ∃ st', Compose.epochFulu rustGlue rustState = ok (some st') ∧ view st' = s' := by
  intro s' hs'
  have hm := ((lighthouse_model_fulu_epoch_agrees_etheorem hpreset hstate hetheorem horacle)
    s').mpr hs'
  rw [← hview] at hm
  have hvec := fuluVectorLengths_toSpecState hpreset e
  obtain ⟨-, -, -, -, hjb, -, -, hpl⟩ := hvec
  exact Compose.epochFulu_spec rustGlue oracle view rustState hglue
    (by rw [hview]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) hstate.atEpochBoundary.2.1)
    (by rw [hview]; exact hjb) (by rw [hview]; exact hpl) s' hm

end Fulu

end EpochProofs.Formalhouse
