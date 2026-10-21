import EpochProofs.Etheorem.Fulu.Epoch
import EpochProofs.Sanity.Invariants.LighthouseFuluOrder

/-!
# Formalhouse: the Fulu epoch of Lighthouse

`formalhouse_fulu_epoch` states, on mainnet, at the last slot of an epoch:

1. If Lighthouse's Fulu epoch (`process_epoch_lh_order_fulu`: Lighthouse's Fulu step order, its
   genesis path and the checked Rust of each step) returns `s'`, Etheorem's Fulu `processEpoch`
   returns a state that maps to `s'`.
2. If the Fulu spec `process_epoch` returns `s'`, Lighthouse's Fulu epoch returns `s'` too.

It does not state that Lighthouse's Fulu epoch returns `ok`: the totality proofs
(`Totality*.lean`) cover the Gloas epoch only.

`FuluEpochCondsAll` lists the conditions on the epoch start state. The state facts are the
invariants that reachable Gloas states keep (`EpochInputOk''`). The Lean spec has no Fulu block
processing, so for Fulu they are assumptions, not proved from genesis.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu
open EpochProofs.Etheorem.Fulu

section Mainnet

attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- The conditions of `formalhouse_fulu_epoch` on the epoch start state `e`, by kind. -/
structure FuluEpochCondsAll (o : Spec.Oracle) (e : EState) : Prop where
  /-- The invariants that reachable Gloas states keep (`Sanity/Invariants`). For Fulu they are
  assumptions: the Lean spec has no Fulu block processing. -/
  reachable : Spec.EpochInputOk'' Spec.EpochSupply (absEState e)
  /-- The epoch boundary: the last slot of an epoch, the next slot fits in `u64`, and fewer than
  `2^24` historical summaries. -/
  boundary : Spec.TailPre (absEState e)
  /-- The conditions of the Etheorem Fulu bridge: state facts before some steps, the Electra
  proposer loop ends before its last pass, and Etheorem's selections return all their items
  (F3). -/
  etheorem : FuluEpochConds Spec.Preset.mainnet o e
  /-- Oracle: the spec Oracle agrees with Etheorem's functions, and `sha` returns 32 bytes. -/
  oracle : OracleAgrees o
  sha : ∀ b : ByteArray, (sha b).size = 32

/-- The Fulu epoch of Lighthouse equals the Fulu spec and Etheorem's Fulu `processEpoch`. -/
theorem formalhouse_fulu_epoch (o : Spec.Oracle) (e : EState) (hc : FuluEpochCondsAll o e) :
    (∀ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' →
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s') ∧
    (∀ s', Spec.process_epoch_fulu Spec.Preset.mainnet Spec.FuluConfig.mainnet o
        (absEState e) = .ok s' → Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s') := by
  have h := Spec.lighthouse_fulu_epoch_sameOk o (absEState e) hc.reachable hc.boundary
  refine ⟨fun s' hs' => ?_, fun s' hs' => (h s').mpr hs'⟩
  exact process_epoch_fulu_etheorem epochPresetAgrees_mainnet o hc.oracle hc.sha e hc.etheorem
    ((h s').mp hs')

end Mainnet

end EpochProofs.Formalhouse
