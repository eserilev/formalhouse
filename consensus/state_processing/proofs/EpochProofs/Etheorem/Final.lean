import EpochProofs.Etheorem.Conditions
import EpochProofs.Etheorem.LighthouseOrder

/-!
# The Lighthouse epoch equals Etheorem on reachable states

`process_epoch_lh_order` is the Lighthouse epoch model: the justification of
`justification.rs`, the single pass of `single_pass_step.rs`, the deposit, consolidation and
builder payment modules, the committee steps of `epoch_committees.rs` and the reset checks of
`tail_updates.rs`, in the order of `altair.rs` and `single_pass.rs`. The README table lists the
Rust function, glue or cache behind each step.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Mainnet

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- Lighthouse's epoch processing, in the Lighthouse order, equals Etheorem's Gloas
`processEpoch` at an epoch boundary of a reachable run, on mainnet.

- `hin`: the reachable-state invariants at the epoch boundary (`EpochInputOk''`).
- `hpre`: the epoch runs at the last slot, the next slot fits in a `u64`, and
  `historical_summaries` is below the Lighthouse limit (`TailPre`).
- `hcond`: room for the pending deposits (F10), and room in the builder withdrawals and the
  historical summaries (F6), all at the epoch start (`EpochCondsIn`).
- `hsel`: Etheorem's balance weighted selections return all their items (F3).
- `ho`, `hsha`: the oracle is Etheorem's hash and BLS functions, and SHA-256 returns 32 bytes. -/
theorem lighthouse_order_epoch_etheorem_reachable (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e))
    (hpre : Spec.TailPre (absEState e)) (hcond : EpochCondsIn e) (hsel : SelectionsFull e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_order o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' :=
  lighthouse_epoch_etheorem_reachable o ho hsha e hin hcond hsel
    ((Spec.process_epoch_lh_order_sameOk o (absEState e) hpre s').mp h)

end Mainnet

end EpochProofs.Etheorem
