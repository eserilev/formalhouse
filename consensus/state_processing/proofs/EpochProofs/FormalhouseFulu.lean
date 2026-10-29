import EpochProofs.Etheorem.Fulu.Epoch
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder
import EpochProofs.Sanity.Invariants.TotalityFulu

/-!
# Formalhouse: the Fulu epoch of Lighthouse

`formalhouse_fulu_epoch` states, for a preset and config that agree with Etheorem's
(`EpochPresetAgrees`, proved for mainnet and minimal), at the last slot of an epoch:

1. If Lighthouse's Fulu epoch (`process_epoch_lh_order_fulu`: Lighthouse's Fulu step order, its
   genesis path and the checked Rust of each step) returns `s'`, Etheorem's Fulu `processEpoch`
   returns a state that maps to `s'`.
2. If the Fulu spec `process_epoch` returns `s'`, Lighthouse's Fulu epoch returns `s'` too.

`formalhouse_fulu_epoch_total` adds that Lighthouse's Fulu epoch returns `ok`
(`process_epoch_fulu_total`), under time and supply bounds and the Fulu pyspec preconditions.

`FuluEpochCondsAll` lists the conditions on the epoch start state. The state facts are the
invariants that reachable Gloas states keep (`EpochInputOk''`). The Lean spec has no Fulu block
processing, so for Fulu they are assumptions, not proved from genesis.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu
open EpochProofs.Etheorem.Fulu

section Generic

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]

/-- The conditions of `formalhouse_fulu_epoch` on the epoch start state `e`, by kind. -/
structure FuluEpochCondsAll (o : Spec.Oracle) (e : EState) : Prop where
  /-- The invariants that reachable Gloas states keep (`Sanity/Invariants`). For Fulu they are
  assumptions: the Lean spec has no Fulu block processing. -/
  reachable : Spec.EpochInputOk'' Spec.EpochSupply (absEState e)
  /-- The epoch boundary: the last slot of an epoch, the next slot fits in `u64`, and fewer than
  `2^24` historical summaries. -/
  boundary : Spec.TailPre (absEState e)
  /-- The conditions of the Etheorem Fulu bridge: state facts before some steps, and the
  Electra proposer loop ends before its last pass. -/
  etheorem : FuluEpochConds Spec.P o e
  /-- Oracle: the spec Oracle agrees with Etheorem's functions, and `sha` returns 32 bytes. -/
  oracle : OracleAgrees o
  sha : ∀ b : ByteArray, (sha b).size = 32

/-- The Fulu epoch of Lighthouse equals the Fulu spec and Etheorem's Fulu `processEpoch`. -/
theorem formalhouse_fulu_epoch (hpa : EpochPresetAgrees Spec.P Spec.FC) (o : Spec.Oracle)
    (e : EState) (hc : FuluEpochCondsAll o e) :
    (∀ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' →
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s') ∧
    (∀ s', Spec.process_epoch_fulu Spec.P Spec.FC o
        (absEState e) = .ok s' → Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s') := by
  have h := Spec.lighthouse_fulu_epoch_sameOk o (absEState e) hc.reachable hc.boundary
  refine ⟨fun s' hs' => ?_, fun s' hs' => (h s').mpr hs'⟩
  exact process_epoch_fulu_etheorem hpa o hc.oracle hc.sha e hc.etheorem
    ((h s').mp hs')

/-- The Fulu epoch of Lighthouse returns `ok`, and its state equals Etheorem's Fulu
`processEpoch`.

The conditions beyond `formalhouse_fulu_epoch`:
- `hslot`: the slot is at least `8192` below `2^64` (the pyspec `get_block_root` raises near
  `2^64`).
- `hvec`: the Fulu vector fields have their SSZ lengths. The Lean state holds them as lists.
- `hrb`: the time and supply bounds of `RowBounds`.
- `hcomm`: at the state that the epoch passes to the committee steps, the state facts
  (`FuluCommitteeStepFacts`) and the Fulu pyspec preconditions (`FuluCommitteeStepPreconds`: an
  active validator at the next epoch and at `current + 2`, and selections that end within `2^64`
  passes). -/
theorem formalhouse_fulu_epoch_total [Spec.PresetCfg.Bounds] (hpa : EpochPresetAgrees Spec.P Spec.FC)
    (o : Spec.Oracle) (e : EState) (hc : FuluEpochCondsAll o e)
    (hslot : (absEState e).slot + 8192 < 2 ^ 64)
    (hvec : (absEState e).FuluVectorLengths Spec.P)
    (hrb : Spec.RowBounds (absEState e))
    (hcomm : Spec.FuluAtCommitteeStepState o (absEState e)) :
    ∃ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' ∧
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s' := by
  have hin := hc.reachable
  obtain ⟨⟨⟨hb, -, heb, -, hsup⟩, -, hcons⟩, -, -⟩ := hin
  obtain ⟨s', hs'⟩ := Spec.process_epoch_fulu_total o (absEState e) hb.2.1 hslot hc.boundary.1
    hvec hb.1 heb hcons hsup.2.2 hrb (Spec.committeesOkFulu_of o _ hslot hcomm)
  have h := formalhouse_fulu_epoch hpa o e hc
  have hlh := h.2 s' hs'
  exact ⟨s', hlh, h.1 s' hlh⟩

end Generic

end EpochProofs.Formalhouse
