import EpochProofs.FormalhouseFinal
import EpochProofs.Compose.Fulu

/-!
# Formalhouse: the final epoch results about the composed Rust

`formalhouse_gloas_epoch_final` and `formalhouse_fulu_epoch_final` are about the Lean model of
Lighthouse's epoch (`process_epoch_lh_order`, `process_epoch_lh_order_fulu`). The theorems here
are about `Compose.epoch` and `Compose.epochFulu`: the calls of the translated functions of
`Generated.lean`, in Lighthouse's order, joined by the untranslated glue. They add to the
hypotheses of the final theorems only the glue (`EpochGlue`) and its trusted facts
(`EpochLinks`): the contracts of `Trusted/`, which fields each wrapper borrows, the values
passed to the translated code, and N1 and the end of the proposer loops at the states where
Lighthouse shuffles.

`Compose.epoch_spec` and `Compose.epochFulu_spec` link the composition to the model, so that each
model step is the one its step theorem covers is checked by Lean.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.Etheorem EpochProofs.CacheBridge

section Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent) in
/-- `formalhouse_gloas_epoch_final` for the composed Rust: on a Rust state `st` whose view is the
epoch input, the composed Gloas epoch `Compose.epoch` returns `Ok`, and its state equals
Etheorem's `processEpoch`. -/
theorem formalhouse_gloas_epoch_rust (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e)
    (cache : LhCache)
    (hcoh : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState (absEState e)
        ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)) cache)
    (total : U64) (b : Spec.BeaconState)
    (hagree : Spec.ActiveAgree ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)
      b (absEState e))
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        (b.validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance)))
    {M : Type} {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey}
    {pview : M → Spec.BLSPubkey → Option Usize} (laws : CacheProofs.IndexMapLaws inst pview)
    (b' : Spec.BeaconState) (hpre : Spec.PkPrefix b' (absEState e))
    {m0 m : M} {len0 len : Usize}
    (hpk0 : CacheProofs.Coherent pview m0 len0 (b'.validators.map (·.pubkey)))
    (hupd : CacheProofs.insertAll inst m0 len0
      (((absEState e).validators.map (·.pubkey)).drop len0.val) = ok (some (m, len)))
    {σ E : Type} (G : Compose.EpochGlue σ E) (view : σ → Spec.BeaconState) (st : σ)
    (hst : view st = absEState e) (hL : Compose.EpochLinks G o view st) :
    ∃ st', Compose.epoch G st = ok (some st') ∧
      ∃ e', (EthCLSpecs.Gloas.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = view st' := by
  obtain ⟨s', hs', ⟨⟨⟨e', he', habs⟩, -⟩, -⟩, -⟩ := formalhouse_gloas_epoch_final hpa hhr o fo c uc
    init e hin ha cache hcoh total b hagree htotal laws b' hpre hpk0 hupd
  obtain ⟨st', hep, hv⟩ := Compose.epoch_spec G o view st hL
    (by rw [hst]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) ha.boundary.2.1) (by rw [hst]; exact ha.vectors) s'
    (by rw [hst]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

end Gloas

section Fulu

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] [Spec.FuluCfg]
  [Spec.FuluCfg.Ok]

open EpochProofs.Etheorem.Fulu

open Aeneas Aeneas.Std Result in
/-- `formalhouse_fulu_epoch_final` for the composed Rust: on a Rust state `st` whose view is the
epoch input, the composed Fulu epoch `Compose.epochFulu` returns `Ok`, and its state equals
Etheorem's Fulu `processEpoch`. -/
theorem formalhouse_fulu_epoch_rust (hpa : Fulu.EpochPresetAgrees Spec.P Spec.FC)
    (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (init : Spec.FuluState) (e : EState)
    (hin : FuluEpochInput o fo c init (absEState e)) (ha : FuluAssumptions o fo c init e)
    {σ E : Type} (G : Compose.EpochGlueFulu σ E) (view : σ → Spec.BeaconState) (st : σ)
    (hst : view st = absEState e) (hL : Compose.EpochLinksFulu G o view st) :
    ∃ st', Compose.epochFulu G st = ok (some st') ∧
      ∃ e', (EthCLSpecs.Fulu.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = view st' := by
  obtain ⟨s', hs', e', he', habs⟩ := formalhouse_fulu_epoch_final hpa o fo c init e hin ha
  have hvec := ha.vectors
  unfold Spec.BeaconState.FuluVectorLengths at hvec
  obtain ⟨-, -, -, -, hjb, -, -, hpl⟩ := hvec
  obtain ⟨st', hep, hv⟩ := Compose.epochFulu_spec G o view st hL
    (by rw [hst]; exact Nat.lt_of_le_of_lt (Nat.le_succ _) ha.boundary.2.1) (by rw [hst]; exact hjb)
    (by rw [hst]; exact hpl) s' (by rw [hst]; exact hs')
  exact ⟨st', hep, e', he', habs.trans hv.symm⟩

end Fulu

/-! ## The two presets -/

section Mainnet

attribute [local instance] Spec.mainnetCfg Spec.fuluMainnetCfg
local instance : @Spec.PresetCfg.Ok Spec.mainnetCfg := Spec.mainnetCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.mainnetCfg := Spec.mainnetCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_mainnet⟩

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
/-- `formalhouse_gloas_epoch_rust` on mainnet. -/
theorem formalhouse_gloas_epoch_rust_mainnet [HasherTag] [CryptoBackend] :
    type_of% (formalhouse_gloas_epoch_rust (hpa := epochPresetAgrees_mainnet) (hhr := by decide)) :=
  formalhouse_gloas_epoch_rust (hpa := epochPresetAgrees_mainnet) (hhr := by decide)
end

section
attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig
/-- `formalhouse_fulu_epoch_rust` on mainnet. -/
theorem formalhouse_fulu_epoch_rust_mainnet [HasherTag] [CryptoBackend] :
    type_of% (formalhouse_fulu_epoch_rust (hpa := Fulu.epochPresetAgrees_mainnet)) :=
  formalhouse_fulu_epoch_rust (hpa := Fulu.epochPresetAgrees_mainnet)
end

end Mainnet

section Minimal

attribute [local instance] Spec.minimalCfg Spec.fuluMinimalCfg
local instance : @Spec.PresetCfg.Ok Spec.minimalCfg := Spec.minimalCfg_ok
local instance : @Spec.PresetCfg.Bounds Spec.minimalCfg := Spec.minimalCfg_bounds
local instance : Spec.FuluCfg.Ok := ⟨Spec.fuluCompat_minimal⟩

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
/-- `formalhouse_gloas_epoch_rust` on minimal. -/
theorem formalhouse_gloas_epoch_rust_minimal [HasherTag] [CryptoBackend] :
    type_of% (formalhouse_gloas_epoch_rust (hpa := epochPresetAgrees_minimal) (hhr := by decide)) :=
  formalhouse_gloas_epoch_rust (hpa := epochPresetAgrees_minimal) (hhr := by decide)
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig
/-- `formalhouse_fulu_epoch_rust` on minimal. -/
theorem formalhouse_fulu_epoch_rust_minimal [HasherTag] [CryptoBackend] :
    type_of% (formalhouse_fulu_epoch_rust (hpa := Fulu.epochPresetAgrees_minimal)) :=
  formalhouse_fulu_epoch_rust (hpa := Fulu.epochPresetAgrees_minimal)
end

end Minimal

end EpochProofs.Formalhouse
