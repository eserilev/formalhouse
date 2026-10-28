import EpochProofs.FormalhouseReadable

/-!
# The headline theorems

The results of this project, stated with the names of `FormalhouseReadable.lean`. Each holds for
any preset that agrees with Etheorem's (`hpa`, `hhr`); `HeadlinePresets.lean` instantiates them
for mainnet and minimal. `lighthouse_*` is about the Lean model of Lighthouse's epoch,
`lighthouse_*_rust` about the composed Aeneas translation of the Rust.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec
open EpochProofs.Spec (SameOk HistRoom)
open CacheProofs.PB (LhCache)
open Aeneas.Std (U64)

variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
variable {o : Spec.Oracle} {fo : Spec.FuluOracle} {c : Spec.FuluBlockConfig}
  {uc : Spec.UpgradeConfig} {init : Spec.FuluState} {s : Spec.BeaconState}

section Gloas
open EpochProofs.Etheorem
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] {e : EState}

/-- Gloas: at every epoch boundary of a run from Fulu across the Gloas fork, Lighthouse's epoch
succeeds and equals Etheorem's, and its cache reads give the spec values. -/
theorem lighthouse_gloas_epoch (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) :=
  gloas_epoch_readable hpa hhr run chain ef oracle caches

/-- Gloas, for the composed Rust: the same, for `Compose.epoch` on a Rust state that views as
the epoch input, given the glue facts. -/
theorem lighthouse_gloas_epoch_rust (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e))
    (rust : RustEpoch G o view st (absEState e)) :
    RustEqualsEtheorem G view st e :=
  gloas_epoch_rust_readable hpa hhr run chain ef oracle caches rust

end Gloas

section Fulu
open EpochProofs.Etheorem.Fulu
variable [Spec.PresetCfg.Bounds] [HasherTag] [CryptoBackend]
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] {e : EState}

/-- Fulu: at every epoch boundary of a Fulu run, Lighthouse's epoch succeeds and equals
Etheorem's. -/
theorem lighthouse_fulu_epoch (hpa : EpochPresetAgrees Spec.P Spec.FC)
    (run : FuluEpochRun o fo c init (absEState e))
    (chain : FuluChainAssumptions o (absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o) :
    LighthouseEqualsEtheoremFulu o e :=
  fulu_epoch_readable hpa run chain ef oracle

/-- Fulu, for the composed Rust. -/
theorem lighthouse_fulu_epoch_rust (hpa : EpochPresetAgrees Spec.P Spec.FC)
    {σ E : Type} {G : Compose.EpochGlueFulu σ E} {view : σ → Spec.BeaconState} {st : σ}
    (run : FuluEpochRun o fo c init (absEState e))
    (chain : FuluChainAssumptions o (absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o) (rust : RustEpochFulu G o view st (absEState e)) :
    RustEqualsEtheoremFulu G view st e :=
  fulu_epoch_rust_readable hpa run chain ef oracle rust

end Fulu

/-- Gloas, against the hand-written pyspec transcription: at every epoch boundary of a run,
Lighthouse's epoch and the spec's give the same state, or both fail. No pyspec precondition. -/
theorem lighthouse_gloas_epoch_sameOk_spec (run : GloasEpochRun o fo c uc init s)
    (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order o s) (Spec.process_epoch Spec.P o s) :=
  gloas_sameOk_of_run run hroom

/-- Fulu, against the hand-written pyspec transcription. -/
theorem lighthouse_fulu_epoch_sameOk_spec (run : FuluEpochRun o fo c init s)
    (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order_fulu o s) (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  fulu_sameOk_of_run run hroom

end EpochProofs.Formalhouse
