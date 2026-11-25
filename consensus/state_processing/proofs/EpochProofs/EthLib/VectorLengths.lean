import EpochProofs.EthLib.Preset
import EpochProofs.EthLib.State
import EpochProofs.Sanity.Invariants.TotalityFulu

/-!
# The vector fields of an EthLib state have their SSZ lengths

The type of an EthLib vector fixes its length. The reference keeps the vectors as lists.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config}

/-- A Fulu EthLib state, read as a reference state, has the SSZ vector lengths of Fulu. -/
theorem fuluVectorLengths_toSpecState {fork : _root_.EthLib.Base.Fork} (fulu : .fusaka ≤ fork)
    (state : BeaconState preset fork) :
    (toSpecState state).FuluVectorLengths (toSpecPreset preset config) := by
  have altair : _root_.EthLib.Base.Fork.altair ≤ fork := Nat.le_trans (by decide) fulu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [toSpecState_block_roots, spec_preset]
  · simp [toSpecState_state_roots, spec_preset]
  · simp [toSpecState_randao_mixes, spec_preset]
  · simp [toSpecState_slashings, spec_preset]
  · simp only [toSpecState_justification_bits, Vector.length_toList]
    rfl
  · simp [toSpecState_current_sync_committee _ altair, toSpecSyncCommittee, spec_preset]
  · simp [toSpecState_next_sync_committee _ altair, toSpecSyncCommittee, spec_preset]
  · simp [toSpecState_proposer_lookahead _ fulu, spec_preset]

/-- A Gloas EthLib state, read as a reference state, has the SSZ vector lengths of Gloas. -/
theorem vectorLengths_toSpecState (state : BeaconState preset .glamsterdam) :
    (toSpecState state).VectorLengths (toSpecPreset preset config) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    fuluVectorLengths_toSpecState (config := config) (by decide) state
  have gloas : _root_.EthLib.Base.Fork.glamsterdam ≤ .glamsterdam := by decide
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_, ?_⟩
  · have hread : (toSpecState state).execution_payload_availability =
        (state.executionPayloadAvailability gloas).bits.toList := by
      simp [toSpecState, fieldOr, gloas]
    simp [hread, spec_preset]
  · simp [toSpecState_builder_pending_payments _ gloas, spec_preset]
  · simp [toSpecState_ptc_window _ gloas, spec_preset]
  · simp only [toSpecState_ptc_window _ gloas, List.mem_map]
    rintro _ ⟨committee, -, rfl⟩
    simp [spec_preset]

end EpochProofs.EthLib
