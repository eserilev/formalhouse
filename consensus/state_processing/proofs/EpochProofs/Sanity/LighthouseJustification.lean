import EpochProofs.Spec.JustificationLighthouse
import EpochProofs.Sanity.Rows

namespace EpochProofs.Spec

/-- `get_block_root` reads only `slot` and `block_roots`. -/
def rootAt (p : Preset) (slot : Slot) (block_roots : List Root) (epoch : Epoch) : SpecM Root := do
  let start ← compute_start_slot_at_epoch p epoch
  if !(start < slot) then
    throw .assertionFailed
  if !(slot ≤ (← uint64Add start p.SLOTS_PER_HISTORICAL_ROOT)) then
    throw .assertionFailed
  listGet block_roots (start % p.SLOTS_PER_HISTORICAL_ROOT)

/-- Splits the goals on `t` where `t` occurs. -/
local macro "split_on " t:term : tactic =>
  `(tactic| all_goals (try (by_cases h : $t <;> simp [h, pure, Except.pure])))

theorem get_block_root_eq_rootAt (p : Preset) (s : BeaconState) (epoch : Epoch) :
    get_block_root p s epoch = rootAt p s.slot s.block_roots epoch := rfl

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- With four justification bits, the Lighthouse model of
`weigh_justification_and_finalization` has the same `ok` results as the spec. Lighthouse runs
the arithmetic before it reads the block roots, so the two can fail at different steps. -/
theorem lhWeigh_sameResultOrBothFail (p : Preset) (s : BeaconState) (tab x y : Gwei)
    (hlen : s.justification_bits.length = JUSTIFICATION_BITS_LENGTH) :
    SameResultOrBothFail (lhWeighJustificationAndFinalization p s tab x y)
      (weigh_justification_and_finalization p s tab x y) := by
  obtain ⟨a, b, c, d, hbits⟩ : ∃ a b c d, s.justification_bits = [a, b, c, d] := by
    match h : s.justification_bits, hlen with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  intro v
  simp only [lhWeighJustificationAndFinalization, weigh_justification_and_finalization,
    lhWeighJustification, lhFinalizeStep, hbits, listGet, JUSTIFICATION_BITS_LENGTH, listSet,
    get_block_root_eq_rootAt]
  cases get_previous_epoch p s <;> cases get_current_epoch p s <;>
    cases uint64Mul tab 2 <;> cases uint64Mul x 3 <;> cases uint64Mul y 3 <;>
    simp only [bind, Except.bind, pure, Except.pure]
  all_goals (try simp)
  · rename_i pe ce thr px cx
    by_cases hjp : thr ≤ px <;> cases rootAt p s.slot s.block_roots pe <;> simp [hjp]
  · rename_i pe ce thr px cx
    by_cases hjp : thr ≤ px <;> by_cases hjc : thr ≤ cx <;> cases a <;> cases b <;> cases c <;>
      simp [hjp, hjc]
    all_goals (try (cases rootAt p s.slot s.block_roots pe <;> simp))
    all_goals (try (cases rootAt p s.slot s.block_roots ce <;> simp))
    all_goals simp only [uint64Add, pure, Except.pure]
    split_on s.previous_justified_checkpoint.epoch + 3 < UINT64_SIZE
    split_on s.previous_justified_checkpoint.epoch + 3 = ce
    split_on s.previous_justified_checkpoint.epoch + 2 < UINT64_SIZE
    split_on s.previous_justified_checkpoint.epoch + 2 = ce
    split_on s.current_justified_checkpoint.epoch + 2 < UINT64_SIZE
    split_on s.current_justified_checkpoint.epoch + 2 = ce
    split_on s.current_justified_checkpoint.epoch + 1 < UINT64_SIZE
    split_on s.current_justified_checkpoint.epoch + 1 = ce

/-- The Lighthouse model of `process_justification_and_finalization` has the same `ok` results
as the spec. -/
theorem lhJustificationAndFinalization_sameResultOrBothFail (p : Preset) (s : BeaconState) :
    SameResultOrBothFail (lhJustificationAndFinalization p s) (process_justification_and_finalization p s) := by
  unfold lhJustificationAndFinalization
  split
  · exact SameResultOrBothFail.refl _
  rename_i hlen
  have hlen : s.justification_bits.length = JUSTIFICATION_BITS_LENGTH := Decidable.of_not_not hlen
  unfold process_justification_and_finalization
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  split
  · exact SameResultOrBothFail.refl _
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun _ _ => ?_)
  exact lhWeigh_sameResultOrBothFail p s _ _ _ hlen

end EpochProofs.Spec
