import EthLib.Consensus.Proofs.Transition.EpochJustification
import EpochProofs.EthLib.Accessors
import EpochProofs.Spec.JustificationFinalization

/-!
# `process_justification_and_finalization`: the reference and EthLib agree

`justification_gloas` and `justification_fulu` are the main theorems. Both come from one proof for
all forks from Altair.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- The reference state after some writes of this step. -/
def withCheckpoints (s : BeaconState preset fork) (bits : List Bool)
    (currentJustified finalized : Checkpoint) : Spec.BeaconState :=
  { toSpecState s with
    justification_bits := bits
    previous_justified_checkpoint := toSpecCheckpoint s.currentJustifiedCheckpoint
    current_justified_checkpoint := toSpecCheckpoint currentJustified
    finalized_checkpoint := toSpecCheckpoint finalized }

/-- One of the four finalization rules. -/
theorem finalizes_same (s : BeaconState preset fork) (bits : List Bool)
    (currentJustified finalized source : Checkpoint) (justified specJustified : Bool)
    (hjustified : specJustified = justified) (gap currentEpoch : UInt64) :
    SameOutcome
      (fun applies state => state =
        withCheckpoints s bits currentJustified (if applies then source else finalized))
      (finalizes justified source.epoch gap currentEpoch)
      (if specJustified then do
        if (← Spec.uint64Add (toSpecCheckpoint source).epoch gap.toNat) == currentEpoch.toNat then
          pure (withCheckpoints s bits currentJustified source)
        else pure (withCheckpoints s bits currentJustified finalized)
      else pure (withCheckpoints s bits currentJustified finalized)) := by
  subst hjustified
  unfold finalizes
  cases specJustified
  · exact .returned rfl
  · simp only [ite_true]
    refine .bind (addChecked_same source.epoch gap).liftArith.liftAccessor ?_
    rintro sum _ rfl -
    by_cases h : sum = currentEpoch
    · simp only [h, beq_self_eq_true, ite_true]
      exact .returned rfl
    · have h' : ¬sum.toNat = currentEpoch.toNat := fun h' => h (UInt64.toNat_inj.mp h')
      simp only [beq_iff_eq, h', ite_false]
      exact .returned (by simp [h])

/-- The justification of one epoch. EthLib gives the new checkpoint. The reference writes the
checkpoint and one justification bit. -/
theorem justifyCheckpoint_same (s : BeaconState preset fork) (bits : List Bool)
    (currentJustified finalized : Checkpoint) (weight threshold epoch : UInt64) (bit : Nat)
    (hbit : bit < bits.length) :
    SameOutcome
      (fun checkpoint state => state =
        withCheckpoints s (if threshold ≤ weight then bits.set bit true else bits) checkpoint
          finalized)
      (justifyCheckpoint s (decide (threshold ≤ weight)) epoch currentJustified)
      (if weight.toNat ≥ threshold.toNat then do
        let root ← Spec.get_block_root (toSpecPreset preset config)
          (withCheckpoints s bits currentJustified finalized) epoch.toNat
        let newBits ← Spec.listSet bits bit true
        pure { withCheckpoints s bits currentJustified finalized with
          current_justified_checkpoint := { epoch := epoch.toNat, root := root }
          justification_bits := newBits }
      else pure (withCheckpoints s bits currentJustified finalized)) := by
  unfold justifyCheckpoint
  by_cases h : threshold ≤ weight
  · have h' := UInt64.le_iff_toNat_le.mp h
    simp only [h, decide_true, ite_true, ge_iff_le, h']
    refine .bind (y := Spec.get_block_root _ (toSpecState s) _)
      (get_block_root_same s epoch).liftAccessor ?_
    rintro root _ rfl -
    simp only [Spec.listSet, hbit, ite_true]
    exact .returned rfl
  · have h' : ¬threshold.toNat ≤ weight.toNat := fun h' => h (UInt64.le_iff_toNat_le.mpr h')
    simp only [h, decide_false, Bool.false_eq_true, ite_false, ge_iff_le, h']
    exact .returned rfl

/-- The justification bits of a state, oldest last. -/
theorem justificationBits_toList (bits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat) :
    bits.bits.toList = [bits.bits[0], bits.bits[1], bits.bits[2], bits.bits[3]] := by
  obtain ⟨⟨⟨l⟩, hl⟩⟩ := bits
  match l, hl with
  | [_, _, _, _], _ => rfl

/-- The justification bits that EthLib writes. -/
theorem newBits_eq (bits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat) (previous current : Bool) :
    let newBits := ((shiftJustificationBits bits).set 1
      (previous || (shiftJustificationBits bits)[1]) (by decide)).set 0 current (by decide)
    newBits[0] = current ∧ newBits[1] = (previous || bits.bits[0]) ∧
      newBits[2] = bits.bits[1] ∧ newBits[3] = bits.bits[2] := by
  simp [shiftJustificationBits]

theorem weigh_justification_and_finalization_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset fork) (total previousTarget currentTarget : UInt64) :
    SameOutcome (fun a b => b = toSpecState a)
      (weighJustificationAndFinalization s total previousTarget currentTarget)
      (Spec.weigh_justification_and_finalization (toSpecPreset preset config) (toSpecState s)
        total.toNat previousTarget.toNat currentTarget.toNat) := by
  unfold weighJustificationAndFinalization Spec.weigh_justification_and_finalization
  rw [get_previous_epoch_eq hslots, get_current_epoch_eq hslots]
  simp only [bind_ok]
  generalize hb : s.justificationBits.bits = oldBits
  have hold : (toSpecState s).justification_bits =
      [oldBits[0], oldBits[1], oldBits[2], oldBits[3]] := by
    rw [← hb]
    exact justificationBits_toList _
  have hshift : Spec.listSet ((toSpecState s).justification_bits.take 1 ++
      (toSpecState s).justification_bits.take (Spec.JUSTIFICATION_BITS_LENGTH - 1)) 0 false =
      .ok [false, oldBits[0], oldBits[1], oldBits[2]] := by
    rw [hold]
    rfl
  simp only [hshift, bind_ok, bind_assoc]
  refine .bind (mulChecked_same previousTarget 3).liftArith.liftAccessor ?_
  rintro previousWeight _ rfl -
  refine .bind (mulChecked_same total 2).liftArith.liftAccessor ?_
  rintro threshold _ rfl hthreshold
  obtain ⟨_, hthreshold, rfl⟩ :=
    (mulChecked_same total 2).liftArith.liftAccessor.returns hthreshold
  refine .bind (justifyCheckpoint_same s [false, oldBits[0], oldBits[1], oldBits[2]]
    s.currentJustifiedCheckpoint s.finalizedCheckpoint previousWeight threshold
    (getPreviousEpoch s) 1 (by simp)) ?_
  rintro justified _ rfl -
  refine .bind (mulChecked_same currentTarget 3).liftArith.liftAccessor ?_
  rintro currentWeight _ rfl -
  have hthreshold' : Spec.uint64Mul total.toNat 2 = .ok threshold.toNat := hthreshold
  rw [hthreshold']
  simp only [bind_ok]
  refine .bind (justifyCheckpoint_same s _ justified s.finalizedCheckpoint currentWeight threshold
    (getCurrentEpoch s) 0 (by split <;> simp)) ?_
  rintro justified' _ rfl -
  have hlist : (if threshold ≤ currentWeight then
        (if threshold ≤ previousWeight then
          [false, oldBits[0], oldBits[1], oldBits[2]].set 1 true
        else [false, oldBits[0], oldBits[1], oldBits[2]]).set 0 true
      else if threshold ≤ previousWeight then
        [false, oldBits[0], oldBits[1], oldBits[2]].set 1 true
      else [false, oldBits[0], oldBits[1], oldBits[2]]) =
      [decide (threshold ≤ currentWeight), decide (threshold ≤ previousWeight) || oldBits[0],
        oldBits[1], oldBits[2]] := by
    by_cases h : threshold ≤ currentWeight <;> by_cases h' : threshold ≤ previousWeight <;>
      simp [h, h']
  rw [hlist]
  obtain ⟨hbit0, hbit1, hbit2, hbit3⟩ := newBits_eq s.justificationBits
    (decide (threshold ≤ previousWeight)) (decide (threshold ≤ currentWeight))
  have hbits := justificationBits_toList ⟨((shiftJustificationBits s.justificationBits).set 1
    (decide (threshold ≤ previousWeight) || (shiftJustificationBits s.justificationBits)[1])
    (by decide)).set 0 (decide (threshold ≤ currentWeight)) (by decide)⟩
  simp only [hbit0, hbit1, hbit2, hbit3, hb] at hbits ⊢
  generalize decide (threshold ≤ currentWeight) = bit0 at hbits ⊢
  generalize (decide (threshold ≤ previousWeight) || oldBits[0]) = bit1 at hbits ⊢
  have extract14 : ∀ a b c d : Bool, ([a, b, c, d].extract 1 4).all id = (b && c && d) := by decide
  have extract13 : ∀ a b c d : Bool, ([a, b, c, d].extract 1 3).all id = (b && c) := by decide
  have extract03 : ∀ a b c d : Bool, ([a, b, c, d].extract 0 3).all id = (a && b && c) := by decide
  have extract02 : ∀ a b c d : Bool, ([a, b, c, d].extract 0 2).all id = (a && b) := by decide
  refine .bind (finalizes_same s _ justified' _ s.previousJustifiedCheckpoint _ _
    (extract14 bit0 bit1 oldBits[1] oldBits[2]) 3 _) ?_
  rintro byOldPrevious3 _ rfl -
  refine .bind (finalizes_same s _ justified' _ s.previousJustifiedCheckpoint _ _
    (extract13 bit0 bit1 oldBits[1] oldBits[2]) 2 _) ?_
  rintro byOldPrevious2 _ rfl -
  refine .bind (finalizes_same s _ justified' _ s.currentJustifiedCheckpoint _ _
    (extract03 bit0 bit1 oldBits[1] oldBits[2]) 2 _) ?_
  rintro byOldCurrent2 _ rfl -
  refine .bind_pure (finalizes_same s _ justified' _ s.currentJustifiedCheckpoint _ _
    (extract02 bit0 bit1 oldBits[1] oldBits[2]) 1 _) ?_
  rintro byOldCurrent1 _ rfl
  simp only [withCheckpoints, toSpecState, hbits]
  cases byOldPrevious3 <;> cases byOldPrevious2 <;> cases byOldCurrent2 <;>
    cases byOldCurrent1 <;> rfl

theorem justification_same (altair : .altair ≤ fork) (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome (fun a b => b = toSpecState a) (processJustificationAndFinalization s)
      (Spec.process_justification_and_finalization (toSpecPreset preset config)
        (toSpecState s)) := by
  unfold processJustificationAndFinalization Spec.process_justification_and_finalization
  rw [dite_eq_left altair, processJustificationAndFinalizationAltair, get_current_epoch_eq hslots,
    get_previous_epoch_eq hslots]
  simp only [bind_ok]
  refine .ite UInt64.le_iff_toNat_le (fun _ => .pure rfl) (fun _ => ?_)
  refine .bind (get_unslashed_participating_indices_same hslots altair hregistry
    TIMELY_TARGET_FLAG_INDEX (by decide) _).liftAccessor fun previous _ hprevious _ => ?_
  refine .bind (get_unslashed_participating_indices_same hslots altair hregistry
    TIMELY_TARGET_FLAG_INDEX (by decide) _).liftAccessor fun current _ hcurrent _ => ?_
  refine .bind (get_total_active_balance_same hslots hregistry).liftAccessor ?_
  rintro total _ rfl -
  refine .bind (get_total_balance_same hprevious).liftAccessor ?_
  rintro previousTarget _ rfl -
  refine .bind (get_total_balance_same hcurrent).liftAccessor ?_
  rintro currentTarget _ rfl -
  exact weigh_justification_and_finalization_same hslots s total previousTarget currentTarget

/-- Gloas: the reference and EthLib return the same state, or both fail. The registry limit is the
spec limit `VALIDATOR_REGISTRY_LIMIT`, which the Gloas type of the registry does not hold. -/
theorem justification_gloas (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset .glamsterdam) (hregistry : s.RegistryWithinLimit) :
    Spec.SameResultOrBothFail
      (Spec.process_justification_and_finalization (toSpecPreset preset config) (toSpecState s))
      (toSpecResult toSpecState (processJustificationAndFinalization s)) :=
  (justification_same (by decide) hslots hregistry).sameResultOrBothFail

/-- Justification does not write the payload header of Fulu. -/
theorem justification_keeps_payload_header {s s' : BeaconState preset fork}
    (h : processJustificationAndFinalization s = .ok s') :
    s'.latestExecutionPayloadHeader = s.latestExecutionPayloadHeader :=
  congrArg (·.latestExecutionPayloadHeader) (processJustificationAndFinalization_eq h)

/-- Fulu: the reference and EthLib return the same state, or both fail. -/
theorem justification_fulu (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset .fusaka) :
    Spec.SameResultOrBothFail
      (do
        pure { toSpecFuluState s with
          state := ← Spec.process_justification_and_finalization (toSpecPreset preset config)
            (toSpecFuluState s).state })
      (toSpecResult toSpecFuluState (processJustificationAndFinalization s)) := by
  have h := justification_same (config := config) (by decide) hslots (registryWithinLimit_of_fulu s)
  apply SameOutcome.sameResultOrBothFail
  rw [← bind_pure (processJustificationAndFinalization s)]
  refine .bind h ?_
  rintro s' _ rfl hs'
  refine .pure ?_
  rw [toSpecFuluState, toSpecFuluState, justification_keeps_payload_header hs']

end EpochProofs.EthLib
