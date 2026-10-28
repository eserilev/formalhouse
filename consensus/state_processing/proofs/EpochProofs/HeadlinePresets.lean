import EpochProofs.Headline

/-!
# The headline theorems on mainnet and minimal

Each instantiates a theorem of `Headline.lean` with the preset, its `PresetCfg.Ok` and
`PresetCfg.Bounds` facts, the Fulu config, and the Etheorem preset with the agreement facts.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EpochProofs.Etheorem
open EpochProofs.Spec (SameOk HistRoom)
open CacheProofs.PB (LhCache)
open Aeneas.Std (U64)

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
/-- `lighthouse_gloas_epoch` on mainnet. -/
theorem lighthouse_gloas_epoch_mainnet [HasherTag] [CryptoBackend] {o fo c uc init}
    {e : EState} {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) :=
  lighthouse_gloas_epoch epochPresetAgrees_mainnet (by decide) run chain ef oracle caches

/-- `lighthouse_gloas_epoch_rust` on mainnet. -/
theorem lighthouse_gloas_epoch_rust_mainnet [HasherTag] [CryptoBackend] {o fo c uc init}
    {e : EState} {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e))
    (rust : RustEpoch G o view st (absEState e)) :
    RustEqualsEtheorem G view st e :=
  lighthouse_gloas_epoch_rust epochPresetAgrees_mainnet (by decide) run chain ef oracle caches rust
end

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
/-- `lighthouse_fulu_epoch` on mainnet. -/
theorem lighthouse_fulu_epoch_mainnet [HasherTag] [CryptoBackend] {o fo c init}
    {e : Fulu.EState} (run : FuluEpochRun o fo c init (Fulu.absEState e))
    (chain : FuluChainAssumptions o (Fulu.absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o) :
    LighthouseEqualsEtheoremFulu o e :=
  lighthouse_fulu_epoch Fulu.epochPresetAgrees_mainnet run chain ef oracle

/-- `lighthouse_fulu_epoch_rust` on mainnet. -/
theorem lighthouse_fulu_epoch_rust_mainnet [HasherTag] [CryptoBackend] {o fo c init}
    {e : Fulu.EState} {σ E : Type} {G : Compose.EpochGlueFulu σ E}
    {view : σ → Spec.BeaconState} {st : σ} (run : FuluEpochRun o fo c init (Fulu.absEState e))
    (chain : FuluChainAssumptions o (Fulu.absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o)
    (rust : RustEpochFulu G o view st (Fulu.absEState e)) :
    RustEqualsEtheoremFulu G view st e :=
  lighthouse_fulu_epoch_rust Fulu.epochPresetAgrees_mainnet run chain ef oracle rust
end

/-- `lighthouse_gloas_epoch_sameOk_spec` on mainnet. -/
theorem lighthouse_gloas_epoch_sameOk_spec_mainnet {o : Spec.Oracle} {fo : Spec.FuluOracle}
    {c : Spec.FuluBlockConfig} {uc : Spec.UpgradeConfig} {init : Spec.FuluState}
    {s : Spec.BeaconState} (run : GloasEpochRun o fo c uc init s) (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order o s) (Spec.process_epoch Spec.P o s) :=
  lighthouse_gloas_epoch_sameOk_spec run hroom

/-- `lighthouse_fulu_epoch_sameOk_spec` on mainnet. -/
theorem lighthouse_fulu_epoch_sameOk_spec_mainnet {o : Spec.Oracle} {fo : Spec.FuluOracle}
    {c : Spec.FuluBlockConfig} {init : Spec.FuluState} {s : Spec.BeaconState}
    (run : FuluEpochRun o fo c init s) (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order_fulu o s) (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  lighthouse_fulu_epoch_sameOk_spec run hroom

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
/-- `lighthouse_gloas_epoch` on minimal. -/
theorem lighthouse_gloas_epoch_minimal [HasherTag] [CryptoBackend] {o fo c uc init}
    {e : EState} {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e)) :
    LighthouseEqualsEtheorem o e ∧ GloasCacheReadsCorrect cache total inst m (absEState e) :=
  lighthouse_gloas_epoch epochPresetAgrees_minimal (by decide) run chain ef oracle caches

/-- `lighthouse_gloas_epoch_rust` on minimal. -/
theorem lighthouse_gloas_epoch_rust_minimal [HasherTag] [CryptoBackend] {o fo c uc init}
    {e : EState} {cache : LhCache} {total : U64} {M : Type} {inst} {m : M}
    {σ E : Type} {G : Compose.EpochGlue σ E} {view : σ → Spec.BeaconState} {st : σ}
    (run : GloasEpochRun o fo c uc init (absEState e))
    (chain : GloasChainAssumptions o (absEState e)) (ef : EtheoremFaithful e)
    (oracle : OracleMatchesEtheorem o)
    (caches : GloasCacheFacts cache total inst m (absEState e))
    (rust : RustEpoch G o view st (absEState e)) :
    RustEqualsEtheorem G view st e :=
  lighthouse_gloas_epoch_rust epochPresetAgrees_minimal (by decide) run chain ef oracle caches rust
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
/-- `lighthouse_fulu_epoch` on minimal. -/
theorem lighthouse_fulu_epoch_minimal [HasherTag] [CryptoBackend] {o fo c init}
    {e : Fulu.EState} (run : FuluEpochRun o fo c init (Fulu.absEState e))
    (chain : FuluChainAssumptions o (Fulu.absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o) :
    LighthouseEqualsEtheoremFulu o e :=
  lighthouse_fulu_epoch Fulu.epochPresetAgrees_minimal run chain ef oracle

/-- `lighthouse_fulu_epoch_rust` on minimal. -/
theorem lighthouse_fulu_epoch_rust_minimal [HasherTag] [CryptoBackend] {o fo c init}
    {e : Fulu.EState} {σ E : Type} {G : Compose.EpochGlueFulu σ E}
    {view : σ → Spec.BeaconState} {st : σ} (run : FuluEpochRun o fo c init (Fulu.absEState e))
    (chain : FuluChainAssumptions o (Fulu.absEState e)) (ef : EtheoremFaithfulFulu o e)
    (oracle : OracleMatchesEtheoremFulu o)
    (rust : RustEpochFulu G o view st (Fulu.absEState e)) :
    RustEqualsEtheoremFulu G view st e :=
  lighthouse_fulu_epoch_rust Fulu.epochPresetAgrees_minimal run chain ef oracle rust
end

/-- `lighthouse_gloas_epoch_sameOk_spec` on minimal. -/
theorem lighthouse_gloas_epoch_sameOk_spec_minimal {o : Spec.Oracle} {fo : Spec.FuluOracle}
    {c : Spec.FuluBlockConfig} {uc : Spec.UpgradeConfig} {init : Spec.FuluState}
    {s : Spec.BeaconState} (run : GloasEpochRun o fo c uc init s) (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order o s) (Spec.process_epoch Spec.P o s) :=
  lighthouse_gloas_epoch_sameOk_spec run hroom

/-- `lighthouse_fulu_epoch_sameOk_spec` on minimal. -/
theorem lighthouse_fulu_epoch_sameOk_spec_minimal {o : Spec.Oracle} {fo : Spec.FuluOracle}
    {c : Spec.FuluBlockConfig} {init : Spec.FuluState} {s : Spec.BeaconState}
    (run : FuluEpochRun o fo c init s) (hroom : HistRoom s) :
    SameOk (Spec.process_epoch_lh_order_fulu o s) (Spec.process_epoch_fulu Spec.P Spec.FC o s) :=
  lighthouse_fulu_epoch_sameOk_spec run hroom

end Minimal

end EpochProofs.Formalhouse
