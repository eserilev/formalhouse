import EpochProofs.Etheorem.Helpers
import EpochProofs.Sanity.PendingConsolidations

/-!
# The reference `process_pending_consolidations` equals Etheorem's

The main theorem is `process_pending_consolidations_etheorem`. Etheorem runs the queue with a
fuel loop, `pcLoop`. `pcLoop_fuel` proves that this loop does the same moves as the
reference `stepLoop` (`Spec.process_pending_consolidations_eq`). The fuel is the queue length
plus one, so the loop never runs out of fuel.

The theorem needs one condition: the state has one balance for each validator. A reachable
state has this property.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

/-- The loop body of Etheorem's `pcLoop`. -/
def pcStep (cons : Array EthCLSpecs.Gloas.PendingConsolidation) (nextEpoch : UInt64) (npc : Nat) :
    GloasRun (Step Nat Nat) :=
  if npc ≥ cons.size then pure (Step.done npc)
  else do
    let state ← get
    let pc := cons[npc]!
    let src ← sszGetIdx state.view.validators pc.sourceIndex.toNat
    if src.slashed = true then pure (Step.next (npc + 1))
    else if src.withdrawableEpoch > nextEpoch then pure (Step.done npc)
    else do
      let srcBal ← sszGetIdx state.view.balances pc.sourceIndex.toNat
      let amt := umin srcBal src.effectiveBalance
      let state ← EthCLSpecs.Gloas.decreaseBalance state pc.sourceIndex amt
      set (← EthCLSpecs.Gloas.increaseBalance state pc.targetIndex amt)
      pure (Step.next (npc + 1))

/-- Etheorem's `pcLoop` is a fuel loop over `pcStep`. -/
theorem pcLoop_eq (cons : Array EthCLSpecs.Gloas.PendingConsolidation) (ne : UInt64) :
    EthCLSpecs.Gloas.pcLoop (StateTransition := GloasRun) cons ne =
      fuelLoop (cons.size + 1) 0 cons.size (pcStep cons ne) := rfl


/-- One step of the queue. Our step and Etheorem's step move the same balance, and they stop
at the same consolidation. -/
theorem pcStep_ok (cons : Array EthCLSpecs.Gloas.PendingConsolidation) (ne : UInt64) (e : EState)
    (k : Nat) (hk : k < cons.size) (hlen : e.balances.val.size = e.validators.val.size)
    {r : (List Nat × Nat) × Bool}
    (h : Spec.consolidationStep ((e.validators.toList.map absValidator).map Spec.globalLocal)
        ne.toNat (e.balances.toList.map UInt64.toNat, k)
        ((absPendingConsolidation cons[k]!).source_index,
          (absPendingConsolidation cons[k]!).target_index) = .ok r) :
    r.1.2 = (if r.2 then k else k + 1) ∧
    ∃ B : SSZList UInt64 EthCLSpecs.Gloas.Const.validatorRegistryLimit,
      (pcStep cons ne k).run (pureState e) =
        .ok ((if r.2 then Step.done k else Step.next (k + 1)), pureState { e with balances := B }) ∧
      B.toList.map UInt64.toNat = r.1.1 ∧ B.val.size = e.balances.val.size := by
  generalize hpc : cons[k]! = pc at h
  have hnk : ¬ k ≥ cons.size := by omega
  unfold pcStep
  rw [if_neg hnk, hpc]
  simp only [absPendingConsolidation] at h
  unfold Spec.consolidationStep at h
  simp only [Spec.localExists_global, List.length_map] at h
  have hVs : e.validators.toList.length = e.validators.val.size := by simp
  rw [hVs] at h
  have hrun_get : ∀ s, (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
  simp only [run_bind, hrun_get, except_bind_ok, view_uncachedBox]
  by_cases hsrc : pc.sourceIndex.toNat < e.validators.val.size
  case neg =>
    simp [hsrc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  have hsome : e.validators.val[pc.sourceIndex.toNat]? = some e.validators.val[pc.sourceIndex.toNat]! := by
    simp [hsrc]
  rw [run_sszGetIdx_some _ _ _ hsome, except_bind_ok]
  have hgetV : Spec.listGet (List.map Spec.globalLocal (List.map absValidator e.validators.toList))
      pc.sourceIndex.toNat = .ok (Spec.globalLocal (absValidator e.validators.val[pc.sourceIndex.toNat]!)) := by
    simp [Spec.listGet, hsrc, pure, Except.pure]
  have hsrcT : decide (pc.sourceIndex.toNat < e.validators.val.size) = true := by simp [hsrc]
  simp only [hsrcT, Bool.not_true, Bool.false_eq_true, if_false, hgetV, pure, Except.pure, bind,
    Except.bind] at h
  dsimp only
  generalize hv : e.validators.val[pc.sourceIndex.toNat]! = v at h ⊢
  by_cases hsl : v.slashed = true
  · simp only [Spec.globalLocal, absValidator, hsl, if_true, Except.ok.injEq] at h
    subst h
    simp only [hsl, if_true]
    exact ⟨rfl, e.balances, rfl, rfl, rfl⟩
  have hsl' : v.slashed = false := by simpa using hsl
  simp only [Spec.globalLocal, absValidator, hsl', Bool.false_eq_true, if_false] at h
  simp only [hsl', Bool.false_eq_true, if_false]
  by_cases hwe : v.withdrawableEpoch > ne
  · have hwe' : ne.toNat < v.withdrawableEpoch.toNat := UInt64.lt_iff_toNat_lt.mp hwe
    simp only [hwe', if_true, Except.ok.injEq] at h
    subst h
    simp only [hwe, if_true]
    exact ⟨by simp, e.balances, rfl, rfl, rfl⟩
  have hwe' : ¬ ne.toNat < v.withdrawableEpoch.toNat := fun h' => hwe (UInt64.lt_iff_toNat_lt.mpr h')
  simp only [hwe', if_false] at h
  simp only [hwe, if_false]
  have hsrcB : pc.sourceIndex.toNat < e.balances.val.size := by omega
  have hbsome : e.balances.val[pc.sourceIndex.toNat]? = some e.balances.val[pc.sourceIndex.toNat]! := by
    simp [hsrcB]
  have hgetB : Spec.listGet (List.map UInt64.toNat e.balances.toList) pc.sourceIndex.toNat =
      .ok (e.balances.val[pc.sourceIndex.toNat]!).toNat := by
    simp [Spec.listGet, hsrcB, pure, Except.pure]
  rw [hgetB] at h
  simp only [run_bind, run_sszGetIdx_some _ _ _ hbsome, except_bind_ok]
  generalize hb : e.balances.val[pc.sourceIndex.toNat]! = b at h ⊢
  have hamt : min b.toNat v.effectiveBalance.toNat = (umin b v.effectiveBalance).toNat :=
    (umin_toNat _ _).symm
  dsimp only at h
  rw [hamt] at h
  generalize hd : Spec.decrease_balance (List.map UInt64.toNat e.balances.toList)
      pc.sourceIndex.toNat (umin b v.effectiveBalance).toNat = d at h
  cases d with
  | error err => cases h
  | ok bs1 =>
  obtain ⟨hdrun, hbs1⟩ := decrease_balance_etheorem e e pc.sourceIndex _ hd
  rw [hdrun, except_bind_ok]
  dsimp only at h
  by_cases htgt : pc.targetIndex.toNat < e.validators.val.size
  case neg =>
    simp [htgt, throw, throwThe, MonadExceptOf.throw] at h
  simp only [htgt, decide_true, Bool.not_true, Bool.false_eq_true, if_false] at h
  generalize hi : Spec.increase_balance bs1 pc.targetIndex.toNat (umin b v.effectiveBalance).toNat = ib at h
  cases ib with
  | error err => cases h
  | ok bs2 =>
  simp only [Except.ok.injEq] at h
  subst h
  rw [hbs1] at hi
  generalize hnb : e.balances.set! pc.sourceIndex.toNat
    (if umin b v.effectiveBalance > e.balances.val[pc.sourceIndex.toNat]! then 0
     else e.balances.val[pc.sourceIndex.toNat]! - umin b v.effectiveBalance) = nb at hi ⊢
  generalize he1 : ({ e with balances := nb } : EState) = e1 at hi
  obtain ⟨hirun, hbs2⟩ := increase_balance_etheorem e1 e pc.targetIndex _ (by
    rw [← he1]; exact hi)
  rw [hirun, except_bind_ok]
  subst he1
  refine ⟨by simp, _, rfl, ?_, ?_⟩
  · rw [hbs2]
  · rw [← hnb]; simp

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
/-- One turn of a fuel loop. -/
theorem fuelLoop_succ_run {σ β α : Type} (n : Nat) (init : β) (ex : α)
    (step : β → StateT σ (Except StateTransitionError) (Step β α)) (s : σ) :
    (fuelLoop (n + 1) init ex step).run s =
      ((step init).run s >>= fun p => match p.1 with
        | .done a => .ok (a, p.2)
        | .next b => (fuelLoop n b ex step).run p.2) := by
  show (do match ← step init with
      | .done a => return a
      | .next b => fuelLoop n b ex step : StateT σ (Except StateTransitionError) α).run s = _
  rw [run_bind]
  congr 1
  funext p
  rcases p with ⟨a | b, s'⟩ <;> rfl

/-- The pair a consolidation step reads. -/
def consPair (c : EthCLSpecs.Gloas.PendingConsolidation) : Nat × Nat :=
  ((absPendingConsolidation c).source_index, (absPendingConsolidation c).target_index)

/-- From position `k` with `j` items left, `pcLoop` stops where our loop stops and writes the same
balances. -/
theorem pcLoop_fuel (cons : Array EthCLSpecs.Gloas.PendingConsolidation) (ne : UInt64) :
    ∀ (j k : Nat) (e : EState) {r : (List Nat × Nat) × Bool}, k + j = cons.size →
      e.balances.val.size = e.validators.val.size →
      Spec.stepLoop (Spec.consolidationStep ((e.validators.toList.map absValidator).map
          Spec.globalLocal) ne.toNat) (e.balances.toList.map UInt64.toNat, k)
          ((cons.toList.drop k).map consPair) = .ok r →
      ∃ B : SSZList UInt64 EthCLSpecs.Gloas.Const.validatorRegistryLimit,
        (fuelLoop (j + 1) k cons.size (pcStep cons ne)).run (pureState e) =
          .ok (r.1.2, pureState { e with balances := B }) ∧
        B.toList.map UInt64.toNat = r.1.1 ∧ B.val.size = e.balances.val.size := by
  intro j
  induction j with
  | zero =>
    intro k e r hk hlen h
    have hdrop : cons.toList.drop k = [] := by simp; omega
    rw [hdrop] at h
    simp only [List.map_nil, Spec.stepLoop, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨e.balances, ?_, rfl, rfl⟩
    rw [fuelLoop_succ_run]
    have hge : k ≥ cons.size := by omega
    simp only [pcStep, if_pos hge]
    rfl
  | succ j ih =>
    intro k e r hk hlen h
    have hlt : k < cons.size := by omega
    have hdrop : cons.toList.drop k = cons[k]! :: cons.toList.drop (k + 1) := by
      have hlt' : k < cons.toList.length := by simpa using hlt
      rw [List.drop_eq_getElem_cons hlt', getElem!_pos cons k hlt, Array.getElem_toList]
    rw [hdrop, List.map_cons, Spec.stepLoop] at h
    obtain ⟨r1, hr1, h⟩ := Spec.specM_bind_ok h
    obtain ⟨hcnt, B1, hrun1, hB1, hsz1⟩ := pcStep_ok cons ne e k hlt hlen hr1
    rw [fuelLoop_succ_run, hrun1, except_bind_ok]
    obtain ⟨⟨bal1, cnt1⟩, b1⟩ := r1
    dsimp only at hcnt hB1 h ⊢
    cases b1 with
    | true =>
      simp only [if_true, pure, Except.pure, Except.ok.injEq] at h hcnt ⊢
      subst h
      exact ⟨B1, by rw [hcnt], hB1, hsz1⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h hcnt ⊢
      have hlen1 : B1.val.size = e.validators.val.size := by omega
      rw [← hB1, hcnt] at h
      obtain ⟨B, hrun, hB, hsz⟩ := ih (k + 1) { e with balances := B1 } (by omega) hlen1 h
      exact ⟨B, hrun, hB, by rw [hsz, hsz1]⟩

section Main
variable [EthCLSpecs.Gloas.Config] {p : Spec.Preset} (hp : PresetAgrees p)
include hp

/-- The reference `process_pending_consolidations` equals Etheorem's.

If the reference succeeds, Etheorem succeeds and the two results agree through `absEState`.
`hlen`: the state has one balance for each validator. -/
theorem process_pending_consolidations_etheorem (e : EState) {s' : Spec.BeaconState}
    (hlen : e.balances.val.size = e.validators.val.size)
    (h : Spec.process_pending_consolidations p (absEState e) = .ok s') :
    ∃ e' : EState,
      (EthCLSpecs.Gloas.processPendingConsolidations (StateTransition := GloasRun)).run
          (pureState e) = .ok ((), pureState e') ∧ s' = absEState e' := by
  rw [Spec.process_pending_consolidations_eq p _ (by simpa using hlen)] at h
  rw [get_current_epoch_eq hp] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  next ne hne =>
  have hne' := uint64Add_ok (a := EthCLSpecs.Gloas.currentEpochOf (pureState e)) (b := 1)
    (by simpa using hne)
  split at h
  · cases h
  next r hr =>
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [← hne'] at hr
  have hcons : (absEState e).pending_consolidations.map
      (fun c => (c.source_index, c.target_index)) =
      (e.pendingConsolidations.toArray.toList.drop 0).map consPair := by
    simp [consPair, absPendingConsolidation, SSZList.toArray, SSZList.toList]
  rw [hcons] at hr
  obtain ⟨B, hrun, hB, -⟩ := pcLoop_fuel e.pendingConsolidations.toArray
    (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) e.pendingConsolidations.toArray.size 0 e
    (by simp) hlen hr
  refine ⟨{ e with
    balances := B
    pendingConsolidations := sszDrop e.pendingConsolidations r.1.2 }, ?_, ?_⟩
  · have hrun_get : ∀ s, (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
    unfold EthCLSpecs.Gloas.processPendingConsolidations
    simp only [run_bind, hrun_get, except_bind_ok, view_uncachedBox]
    rw [pcLoop_eq, hrun, except_bind_ok]
    rfl
  · rw [← hB]
    simp [absEState, sszDrop, SSZList.toList, List.map_drop]
    rw [List.take_of_length_le (by simp)]

end Main

end EpochProofs.Etheorem
