import EpochProofs.Spec.EpochCommittees

/-!
# `compute_ptc` with the committee indices as one step

`ptcIndices` is the loop of `compute_ptc` that joins the beacon committees of a slot.
`compute_ptc_eq` splits `compute_ptc` into the seed, `ptcIndices` and the selection.
Lighthouse reads the committees from its committee cache.
-/

namespace EpochProofs.Spec

/-- The beacon committees of `slot`, joined in order. -/
def ptcIndices (p : Preset) (o : Oracle) (state : BeaconState) (epoch : Epoch) (slot : Slot) :
    SpecM (List ValidatorIndex) := do
  let mut indices : List ValidatorIndex := []
  let committees_per_slot ← get_committee_count_per_slot p state epoch
  for i in List.range committees_per_slot do
    let committee ← get_beacon_committee p o state slot i
    indices := indices ++ committee
  pure indices

theorem compute_ptc_eq (p : Preset) (o : Oracle) (state : BeaconState) (slot : Slot) :
    compute_ptc p o state slot = (do
      let epoch ← compute_epoch_at_slot p slot
      let s ← get_seed p o state epoch DOMAIN_PTC_ATTESTER
      let indices ← ptcIndices p o state epoch slot
      compute_balance_weighted_selection p o state indices
        (o.hash (s.toList ++ uint_to_bytes 8 slot)) p.PTC_SIZE false) := by
  simp only [compute_ptc, ptcIndices, bind_assoc, pure_bind]
end EpochProofs.Spec
