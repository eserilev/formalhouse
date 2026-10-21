import EpochProofs.Etheorem.Epoch
import EpochProofs.Sanity.Invariants.LighthouseOrder

/-!
# Lighthouse in the Lighthouse order equals Etheorem

`process_epoch_lh_order` is the Lighthouse epoch with the steps after the single pass in the
order of `altair.rs` and `single_pass.rs`, and with the reset checks of `tail_updates.rs`.
`lighthouse_order_epoch_etheorem` relates it to Etheorem's Gloas `processEpoch` through
`process_epoch_lh_order_sameOk` and `lighthouse_epoch_etheorem`.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Lighthouse

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- Lighthouse's epoch processing, in the Lighthouse order, equals Etheorem's Gloas
`processEpoch` on mainnet. `hpre` holds at each epoch boundary of a reachable state, with
`historical_summaries` below the Lighthouse limit. -/
theorem lighthouse_order_epoch_etheorem (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e))
    (hpre : Spec.TailPre (absEState e)) (hc : EtheoremEpochConds e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_order o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' :=
  lighthouse_epoch_etheorem o ho hsha e hin hc
    ((Spec.process_epoch_lh_order_sameOk o (absEState e) hpre s').mp h)

end Lighthouse

end EpochProofs.Etheorem
