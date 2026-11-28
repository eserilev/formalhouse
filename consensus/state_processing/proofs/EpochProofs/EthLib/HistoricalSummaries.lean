import EthLib.Consensus.Transition.EpochUpdates
import EpochProofs.EthLib.Oracle

/-!
# `process_historical_summaries_update`: the reference and EthLib agree

`hroom` names a difference. `historical_summaries` is a list with the limit
`HISTORICAL_ROOTS_LIMIT`. If the list is full, EthLib fails, and the reference appends.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem historical_summaries_update_same (hdiv : DivisorsNonzero preset config)
    {checks : SignatureChecks} {o : Spec.Oracle} (ho : OracleMatches preset checks o)
    (capella : .shapella ≤ fork) (s : BeaconState preset fork)
    (hroom : (s.historicalSummaries capella).data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    SameOutcome SameState (processHistoricalSummariesUpdate s capella)
      (Spec.process_historical_summaries_update (toSpecPreset preset config) o
        (toSpecState s)) := by
  unfold processHistoricalSummariesUpdate Spec.process_historical_summaries_update
  rw [get_current_epoch_eq hdiv.slots]
  simp only [bind_ok, spec_preset]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  simp only [uint64Div_eq hdiv.slots, uint64Mod_eq hdiv.historicalPeriod, bind_ok, beq_iff_eq]
  refine .ite (by rw [← UInt64.toNat_inj]; rfl) (fun _ => ?_) (fun _ => .returned rfl)
  simp only [ho.blockRoots s.blockRoots, ho.stateRoots s.stateRoots, liftSsz, Except.mapError,
    bind_ok, hroom, dite_true]
  refine .returned ?_
  simp only [SameState, toSpecState_with_historical_summaries s capella,
    toSpecState_historical_summaries s capella, readList, Array.toList_push, List.map_append]
  rfl

end EpochProofs.EthLib
