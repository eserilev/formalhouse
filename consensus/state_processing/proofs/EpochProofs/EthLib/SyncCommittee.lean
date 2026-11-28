import EthLib.Consensus.Transition.EpochParticipation
import EpochProofs.EthLib.FuluSelection
import EpochProofs.Spec.EpochCommittees

/-!
# `process_sync_committee_updates`: the reference and EthLib agree

Gloas and Fulu differ in the reference loop that selects the members. EthLib has one loop.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- The committee of the selected members. `specIndices` is the selection of the reference. -/
theorem sync_committee_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (s : BeaconState preset fork)
    {specIndices : Spec.SpecM (List Nat)}
    (hindices : SameOutcome (fun a b => b = a.toList.map UInt64.toNat)
      (getNextSyncCommitteeIndices s) specIndices) :
    SameOutcome (fun a b => b = toSpecSyncCommittee (Rooted.of a)) (getNextSyncCommittee s)
      (do
        let indices ← specIndices
        let pubkeys ← indices.mapM fun index => do
          pure (← Spec.listGet (toSpecState s).validators index).pubkey
        let aggregate_pubkey ← Spec.eth_aggregate_pubkeys o pubkeys
        pure { pubkeys, aggregate_pubkey }) := by
  unfold getNextSyncCommittee
  refine .bind hindices ?_
  rintro indices _ rfl -
  refine .bind (SameOutcome.vectorMapM UInt64.toNat id indices fun index _ => by
    refine .bind (getValidator_same s index) ?_
    rintro v _ rfl -
    exact .returned rfl) ?_
  rintro pubkeys _ rfl -
  rw [List.map_id]
  have haggregate := eth_aggregate_pubkeys_same ho pubkeys.toList
  have harray : pubkeys.toList.toArray = pubkeys.toArray := by simp [Vector.toList]
  rw [harray] at haggregate
  refine .bind haggregate ?_
  rintro key _ rfl -
  exact .returned rfl

theorem sync_committee_updates_same (hdiv : DivisorsNonzero preset config)
    (altair : .altair ≤ fork) (s : BeaconState preset fork)
    {specCommittee : Spec.BeaconState → Spec.SpecM Spec.SyncCommittee}
    (hcommittee : ∀ st : BeaconState preset fork, st.validators = s.validators →
      SameOutcome (fun a b => b = toSpecSyncCommittee (Rooted.of a)) (getNextSyncCommittee st)
        (specCommittee (toSpecState st))) :
    SameOutcome SameState (processSyncCommitteeUpdates s altair)
      (do
        let next_epoch ← Spec.uint64Add
          (← Spec.get_current_epoch (toSpecPreset preset config) (toSpecState s)) 1
        if (← Spec.uint64Mod next_epoch
            (toSpecPreset preset config).EPOCHS_PER_SYNC_COMMITTEE_PERIOD) == 0 then
          let state := { toSpecState s with
            current_sync_committee := (toSpecState s).next_sync_committee }
          pure { state with next_sync_committee := ← specCommittee state }
        else
          pure (toSpecState s)) := by
  unfold processSyncCommitteeUpdates
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  simp only [spec_preset, uint64Mod_eq hdiv.syncCommitteePeriod, bind_ok, beq_iff_eq]
  refine .ite (by rw [← UInt64.toNat_inj]; rfl) (fun _ => ?_) (fun _ => .returned rfl)
  have hcurrent := (toSpecState_with_current_sync_committee s altair
    (s.nextSyncCommittee altair)).trans
    (congrArg (fun committee => { toSpecState s with current_sync_committee := committee })
      (toSpecState_next_sync_committee s altair).symm)
  have hnext (state : Spec.BeaconState)
      (hstate : toSpecState { s with currentSyncCommittee := fun _ => s.nextSyncCommittee altair } =
        state) :
      SameOutcome SameState
        (do
          let drawn := Rooted.of (← liftAccessor (getNextSyncCommittee
            { s with currentSyncCommittee := fun _ => s.nextSyncCommittee altair }))
          return { s with
            currentSyncCommittee := fun _ => s.nextSyncCommittee altair
            nextSyncCommittee := fun _ => drawn })
        (do pure { state with next_sync_committee := ← specCommittee state }) := by
    subst hstate
    refine .bind (hcommittee { s with
      currentSyncCommittee := fun _ => s.nextSyncCommittee altair } rfl).liftAccessor ?_
    rintro committee _ rfl -
    refine .returned ?_
    rw [SameState, ← toSpecState_with_next_sync_committee _ altair]
  exact hnext _ hcurrent

theorem sync_committee_updates_gloas (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (altair : .altair ≤ fork) (electra : .pectra ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processSyncCommitteeUpdates s altair)
      (Spec.process_sync_committee_updates (toSpecPreset preset config) o (toSpecState s)) :=
  sync_committee_updates_same hdiv altair s
    (specCommittee := Spec.get_next_sync_committee (toSpecPreset preset config) o)
    fun st hvalidators => sync_committee_same ho st
      (sync_committee_indices_same hdiv.slots hbounds ho electra
        (by rwa [BeaconState.RegistryWithinLimit, hvalidators]))

theorem sync_committee_updates_fulu (hdiv : DivisorsNonzero preset config)
    (hbounds : CommitteeBounds preset) {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (altair : .altair ≤ fork) (electra : .pectra ≤ fork)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameState (processSyncCommitteeUpdates s altair)
      (Spec.process_sync_committee_updates_fulu (toSpecPreset preset config) o (toSpecState s)) :=
  sync_committee_updates_same hdiv altair s
    (specCommittee := Spec.get_next_sync_committee_fulu (toSpecPreset preset config) o)
    fun st hvalidators => sync_committee_same ho st
      (fulu_sync_committee_indices_same hdiv.slots hbounds ho electra
        (by rwa [BeaconState.RegistryWithinLimit, hvalidators]))

end EpochProofs.EthLib
