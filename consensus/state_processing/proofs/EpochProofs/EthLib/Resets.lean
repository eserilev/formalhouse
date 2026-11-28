import EthLib.Consensus.Transition.EpochParticipation
import EthLib.Consensus.Transition.EpochUpdates
import EpochProofs.EthLib.Accessors
import EpochProofs.Spec.EpochRest

/-!
# The reset and rotation steps: the reference and EthLib agree

The eth1 data reset, the slashings reset, the RANDAO mixes reset and the participation flag
updates. No step needs a bound on the registry.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem eth1_data_reset_same (hdiv : DivisorsNonzero preset config) (beforeHeze : fork < .hegota)
    (s : BeaconState preset fork) :
    SameOutcome SameState (processEth1DataReset beforeHeze s)
      (Spec.process_eth1_data_reset (toSpecPreset preset config) (toSpecState s)) := by
  unfold processEth1DataReset Spec.process_eth1_data_reset
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  simp only [toSpecPreset, uint64Mod_eq hdiv.eth1VotingPeriod, bind_ok, beq_iff_eq]
  refine .ite (by rw [← UInt64.toNat_inj]; rfl) (fun _ => .returned ?_) (fun _ => .returned rfl)
  rw [SameState, toSpecState_with_eth1_data_votes s beforeHeze]
  rfl

theorem slashings_reset_same (hdiv : DivisorsNonzero preset config)
    (s : BeaconState preset fork) :
    SameOutcome SameState (processSlashingsReset s)
      (Spec.process_slashings_reset (toSpecPreset preset config) (toSpecState s)) := by
  unfold processSlashingsReset Spec.process_slashings_reset
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  rw [← bind_assoc]
  refine .bind (writeCircularRooted_same UInt64.toNat s.slashings next 0).liftAccessor ?_
  rintro slashings _ rfl -
  exact .returned rfl

theorem randao_mixes_reset_same (hdiv : DivisorsNonzero preset config)
    (s : BeaconState preset fork) :
    SameOutcome SameState (processRandaoMixesReset s)
      (Spec.process_randao_mixes_reset (toSpecPreset preset config) (toSpecState s)) := by
  unfold processRandaoMixesReset Spec.process_randao_mixes_reset
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  refine .bind (readCircular_same s.randaoMixes.elements (getCurrentEpoch s)).liftAccessor ?_
  rintro _ mix rfl -
  rw [← bind_assoc]
  have hwrite := writeCircularRooted_same id s.randaoMixes next mix
  rw [List.map_id] at hwrite
  refine .bind hwrite.liftAccessor ?_
  rintro mixes _ rfl -
  exact .returned (by simp [SameState, toSpecState])

theorem participation_flag_updates_eq (altair : .altair ≤ fork) (s : BeaconState preset fork) :
    Spec.process_participation_flag_updates (toSpecState s) =
      toSpecState (processParticipationFlagUpdates s altair) := by
  unfold Spec.process_participation_flag_updates processParticipationFlagUpdates
  simp [toSpecState, fieldOr, altair, readList]

end EpochProofs.EthLib
