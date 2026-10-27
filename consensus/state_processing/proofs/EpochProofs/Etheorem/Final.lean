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

section Generic

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]

/-- Lighthouse's epoch processing, in the Lighthouse order, equals Etheorem's Gloas
`processEpoch` at an epoch boundary of a reachable run, for a preset that agrees with
Etheorem's (`hpa`).

- `hin`: the reachable-state invariants at the epoch boundary (`EpochInputOk''`).
- `hpre`: the epoch runs at the last slot, the next slot fits in a `u64`, and
  `historical_summaries` is below the Lighthouse limit (`TailPre`).
- `hcond`: room in the registry for the new validators of one epoch (F10), and room in the
  builder withdrawals (F6), both at the epoch start (`EpochCondsIn`). The historical summaries
  room comes from `hpre`.
- `hsel`: Etheorem's balance weighted selections return all their items (F3).
- `hhr`: Etheorem's `HISTORICAL_ROOTS_LIMIT` is at least Lighthouse's (both `2^24`).
- `ho`, `hsha`: the oracle is Etheorem's hash and BLS functions, and SHA-256 returns 32 bytes. -/
theorem lighthouse_order_epoch_etheorem_reachable [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e))
    (hpre : Spec.TailPre (absEState e)) (hcond : EpochCondsIn e) (hsel : SelectionsFull e)
    {s' : Spec.BeaconState} (h : Spec.process_epoch_lh_order o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' :=
  lighthouse_epoch_etheorem_reachable hpa o ho hsha e hin hcond
    (Nat.lt_of_lt_of_le hpre.2.2 hhr) hsel
    ((Spec.process_epoch_lh_order_sameOk o (absEState e) hpre s').mp h)

end Generic

end EpochProofs.Etheorem
