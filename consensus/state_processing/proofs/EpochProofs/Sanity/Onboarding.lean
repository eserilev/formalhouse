import EpochProofs.Sanity.Invariants.ForkUpgrade

/-!
# Closed forms for builder onboarding at the Gloas fork

While every builder has `withdrawable_epoch = FAR_FUTURE_EPOCH` and the current epoch is below
it, `get_index_for_new_builder` returns the registry length, so `add_builder_to_registry`
appends. Onboarding at the fork starts from an empty registry and adds only such builders.
-/

namespace EpochProofs.Spec

theorem forIn_all_yield {β : Type} (l : List Nat) (init : β)
    (body : Nat → β → SpecM (ForInStep β)) (P : Nat → Prop) (hl : ∀ i ∈ l, P i)
    (h : ∀ i, P i → body i init = .ok (.yield init)) :
    forIn l init body = .ok init := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, h x (hl x (List.mem_cons_self ..))]
    exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))

theorem get_index_for_new_builder_far (p : Preset) (state : BeaconState) (ce : Nat)
    (hce : get_current_epoch p state = .ok ce) (hlt : ce < FAR_FUTURE_EPOCH)
    (hall : ∀ b ∈ state.builders, b.withdrawable_epoch = FAR_FUTURE_EPOCH) :
    get_index_for_new_builder p state = .ok state.builders.length := by
  unfold get_index_for_new_builder
  simp only [hce]
  rw [forIn_all_yield _ _ _ (fun i => i < state.builders.length)
    (fun i hi => List.mem_range.mp hi)]
  · rfl
  · intro i hi
    have hb := hall _ (List.getElem_mem hi)
    have hn : ¬ state.builders[i].withdrawable_epoch ≤ ce := by
      rw [hb]; exact Nat.not_le.mpr hlt
    simp [listGet, List.getElem?_eq_getElem hi, hn, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

theorem add_builder_to_registry_far (p : Preset) (state : BeaconState) (ce : Nat)
    (hce : get_current_epoch p state = .ok ce) (hlt : ce < FAR_FUTURE_EPOCH)
    (hall : ∀ b ∈ state.builders, b.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (hspe : p.SLOTS_PER_EPOCH ≠ 0) (pubkey : BLSPubkey) (version : UInt8)
    (address : ExecutionAddress) (amount : Gwei) (slot : Slot) :
    add_builder_to_registry p state pubkey version address amount slot =
      .ok { state with builders := state.builders ++ [{
        pubkey, version, execution_address := address, balance := amount,
        deposit_epoch := slot / p.SLOTS_PER_EPOCH, withdrawable_epoch := FAR_FUTURE_EPOCH }] } := by
  unfold add_builder_to_registry
  rw [get_index_for_new_builder_far p state ce hce hlt hall]
  simp [compute_epoch_at_slot, uint64Div, hspe, set_or_append_list, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

end EpochProofs.Spec
