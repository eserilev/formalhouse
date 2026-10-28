import EpochProofs.FormalhouseFulu
import EpochProofs.Sanity.Invariants.FuluReachable

/-!
# Formalhouse: the Fulu epoch of Lighthouse on every reachable Fulu state

`formalhouse_fulu_epoch` and `formalhouse_fulu_epoch_total` take the reachable-state invariants
(`EpochInputOk''`) as a condition on the epoch input. `fulu_reachable_invariants` proves them for
every input of the Fulu `process_epoch` in a reachable Fulu run. So these two theorems hold on
every epoch input of a run of `state_transition_fulu` steps from a start state with the
invariants of a genesis state (`FuluStartOk`).

The run hypotheses stay as for Gloas: the supply bound before each block (`SupplyBoundFulu`) and
`EpochSupply` at each epoch input (`EpochEconFulu`). The start state is any state with the
genesis invariants. This file does not prove that a Fulu genesis state or the result of
`upgrade_to_fulu` has them.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu
open EpochProofs.Etheorem.Fulu

section Generic

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.FuluCfg] [Spec.FuluCfg.Ok]

/-- The conditions of `formalhouse_fulu_epoch` other than the reachable-state invariants. -/
structure FuluEpochCondsRun (o : Spec.Oracle) (e : EState) : Prop where
  /-- The epoch boundary: the last slot of an epoch, the next slot fits in `u64`, and fewer than
  `2^24` historical summaries. -/
  boundary : Spec.TailPre (absEState e)
  /-- The conditions of the Etheorem Fulu bridge. -/
  etheorem : FuluEpochConds Spec.P o e
  /-- Oracle: the spec Oracle agrees with Etheorem's functions, and `sha` returns 32 bytes. -/
  oracle : OracleAgrees o
  sha : ∀ b : ByteArray, (sha b).size = 32

/-- An input of the Fulu `process_epoch` in a reachable Fulu run. -/
structure FuluEpochInput (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (s : Spec.BeaconState) : Prop where
  reach : ∃ (fs t t1 : Spec.FuluState) (slot : Spec.Slot),
    Spec.ReachableFulu o fo c init fs ∧ slot < 2 ^ 64 ∧ Spec.SlotReachFulu o fo fs slot t ∧
    t.state.slot < slot ∧ Spec.process_slot_fulu Spec.P o fo t = .ok t1 ∧
    (t1.state.slot + 1) % Spec.P.SLOTS_PER_EPOCH = 0 ∧ t1.state = s

/-- On every epoch input of a reachable Fulu run, `EpochInputOk'' EpochSupply` holds. -/
theorem fuluEpochInput_ok (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (hi : Spec.FuluStartOk init.state)
    (hsupply : Spec.SupplyBoundFulu o fo c init)
    (hecon : Spec.EpochEconFulu o fo c init Spec.EpochSupply) (s : Spec.BeaconState)
    (hin : FuluEpochInput o fo c init s) : Spec.EpochInputOk'' Spec.EpochSupply s := by
  obtain ⟨fs, t, t1, slot, hr, hslot64, hreach, hlt, ht, hz, rfl⟩ := hin.reach
  exact Spec.fulu_reachable_invariants o fo c init hi hsupply _ hecon fs t t1 slot hr hslot64
    hreach hlt ht hz

/-- The Fulu epoch of Lighthouse equals the Fulu spec and Etheorem's Fulu `processEpoch`, on
every epoch input of a reachable Fulu run. -/
theorem formalhouse_fulu_epoch_reachable (hpa : EpochPresetAgrees Spec.P Spec.FC) (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (init : Spec.FuluState) (hi : Spec.FuluStartOk init.state)
    (hsupply : Spec.SupplyBoundFulu o fo c init)
    (hecon : Spec.EpochEconFulu o fo c init Spec.EpochSupply) (e : EState)
    (hin : FuluEpochInput o fo c init (absEState e)) (hc : FuluEpochCondsRun o e) :
    (∀ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' →
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s') ∧
    (∀ s', Spec.process_epoch_fulu Spec.P Spec.FC o
        (absEState e) = .ok s' → Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s') :=
  formalhouse_fulu_epoch hpa o e
    ⟨fuluEpochInput_ok o fo c init hi hsupply hecon _ hin, hc.boundary, hc.etheorem, hc.oracle,
      hc.sha⟩

/-- The Fulu epoch of Lighthouse returns `ok`, and its state equals Etheorem's Fulu
`processEpoch`, on every epoch input of a reachable Fulu run. The other conditions are those of
`formalhouse_fulu_epoch_total`: the slot bound, the SSZ vector lengths, the time and supply bounds
(`RowBounds`) and the committee conditions. -/
theorem formalhouse_fulu_epoch_total_reachable [Spec.PresetCfg.Bounds]
    (hpa : EpochPresetAgrees Spec.P Spec.FC) (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (init : Spec.FuluState) (hi : Spec.FuluStartOk init.state)
    (hsupply : Spec.SupplyBoundFulu o fo c init)
    (hecon : Spec.EpochEconFulu o fo c init Spec.EpochSupply) (e : EState)
    (hin : FuluEpochInput o fo c init (absEState e)) (hc : FuluEpochCondsRun o e)
    (hslot : (absEState e).slot + 8192 < 2 ^ 64)
    (hvec : (absEState e).FuluVectorLengths Spec.P)
    (hrb : Spec.RowBounds (absEState e))
    (hcomm : Spec.CommAtFulu o (absEState e)) :
    ∃ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' ∧
      ∃ e', (EthCLSpecs.Fulu.processEpoch (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s' :=
  formalhouse_fulu_epoch_total hpa o e
    ⟨fuluEpochInput_ok o fo c init hi hsupply hecon _ hin, hc.boundary, hc.etheorem, hc.oracle,
      hc.sha⟩ hslot hvec hrb hcomm

end Generic

end EpochProofs.Formalhouse
