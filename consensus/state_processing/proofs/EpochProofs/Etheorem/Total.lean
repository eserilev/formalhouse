import EpochProofs.Etheorem.Final
import EpochProofs.Sanity.Invariants.TotalityCommittees

/-!
# Lighthouse returns `ok` and equals Etheorem

`lighthouse_order_epoch_etheorem_reachable` says: when the Lighthouse epoch model returns `ok`,
Etheorem gives the same state. `process_epoch_total` says that the spec epoch returns `ok`.
`SameOk` turns that into `ok` for the Lighthouse model. Together: on a reachable state, the
Lighthouse model returns `ok`, and its state equals Etheorem's.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

section Mainnet

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- At an epoch boundary of a reachable run on mainnet, the Lighthouse epoch model returns
`ok`, and Etheorem's Gloas `processEpoch` gives the same state.

The conditions beyond `lighthouse_order_epoch_etheorem_reachable`:
- `hslot`: the slot is at least `8192` below `2^64`. Near `2^64` the pyspec `get_block_root`
  raises on `slot + SLOTS_PER_HISTORICAL_ROOT`.
- `hvec`: the vector fields have their SSZ lengths. The Lean state holds them as lists.
- `hopen`: the steps that `Totality.lean` does not prove yet (`TotalityOpen`).
- `hcomm`: at the committee steps, the state conditions (`CommConds`) and the pyspec
  preconditions (`CommPreconds`: a sync candidate, a proposer candidate (F4), at least 32 active
  validators for the PTC, and selections that end within `2^64` passes). -/
theorem lighthouse_epoch_total_etheorem (o : Spec.Oracle) (ho : OracleAgrees o)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (absEState e))
    (hpre : Spec.TailPre (absEState e)) (hcond : EpochCondsIn e) (hsel : SelectionsFull e)
    (hslot : (absEState e).slot + 8192 < 2 ^ 64)
    (hvec : (absEState e).VectorLengths Spec.Preset.mainnet)
    (hopen : Spec.TotalityOpen o (absEState e))
    (hcomm : ∀ s, Spec.CommFrame (absEState e) s → Spec.CommConds o s ∧ Spec.CommPreconds o s) :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      ∃ e', (EthCLSpecs.Gloas.processEpoch (StateTransition := GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s' := by
  have hin' := hin
  obtain ⟨⟨⟨hb, hslot64, heb, hexit, hsup⟩, -, hcons⟩, -, hvalid⟩ := hin'
  obtain ⟨s', hs'⟩ := Spec.process_epoch_total o (absEState e) hb.2.1 hslot hpre.1 hvec hb.1
    hsup.2.1 hopen (Spec.committeesOk_of o _ hslot hcomm)
  have hfull := (Spec.process_epoch_lh_full_sameOk' o (absEState e) hb hslot64 heb hexit hsup
    hvalid hcons s').mpr hs'
  have hlh := (Spec.process_epoch_lh_order_sameOk o (absEState e) hpre s').mpr hfull
  exact ⟨s', hlh, lighthouse_order_epoch_etheorem_reachable o ho hsha e hin hpre hcond hsel hlh⟩

end Mainnet

end EpochProofs.Etheorem
