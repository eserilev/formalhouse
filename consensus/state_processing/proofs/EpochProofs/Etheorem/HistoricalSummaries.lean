import EpochProofs.Etheorem.Resets
import EpochProofs.Etheorem.Oracle

/-!
# `process_historical_summaries_update` equals Etheorem's

The main theorem is `historical_summaries_update_etheorem`. The reference takes
`hash_tree_root` from the `Oracle`. `OracleAgrees o` says that it equals Etheorem's `htr`.

Etheorem pins alpha.11, where `historical_summaries` has the limit `HISTORICAL_ROOTS_LIMIT`.
Past the limit Etheorem's `SSZList.push` drops the new summary. In beta.4 the list has no limit.
So the theorem assumes that the list is below the limit (finding F6).
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

/-- The summary that Etheorem appends. -/
def etheoremSummary (e : EtheoremState) : EthCLSpecs.Gloas.HistoricalSummary :=
  { blockSummaryRoot := htr e.blockRoots, stateSummaryRoot := htr e.stateRoots }

theorem processHistoricalSummariesUpdate_run (e : EtheoremState) :
    (EthCLSpecs.Gloas.processHistoricalSummariesUpdate (StateTransition := GloasRun)).run
        (pureState e) =
      .ok ((), pureState (if (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1) %
          UInt64.ofNat (EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot /
            EthCLSpecs.Gloas.Const.slotsPerEpoch) = 0
        then { e with historicalSummaries := e.historicalSummaries.push (etheoremSummary e) }
        else e)) := by
  unfold EthCLSpecs.Gloas.processHistoricalSummariesUpdate EthCLSpecs.Gloas.getCurrentEpoch
  by_cases h : (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1) %
      UInt64.ofNat (EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot /
        EthCLSpecs.Gloas.Const.slotsPerEpoch) = 0
  · rw [if_pos h]
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.pure, Except.bind, view_uncachedBox, h]
    rfl
  · rw [if_neg h]
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.pure, Except.bind, view_uncachedBox, h]

omit [EthCLSpecs.Gloas.Preset] [HasherTag] in
/-- `SSZList.push` below the limit appends. -/
theorem sszList_push_toList {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α)
    (h : xs.val.size < cap) : (xs.push x).toList = xs.toList ++ [x] := by
  simp [SSZList.push, h, SSZList.toList]

variable [EthCLSpecs.Gloas.Config] [CryptoBackend]

/-- `process_historical_summaries_update` equals Etheorem's.

`hcap`: the list is below Etheorem's alpha.11 limit `HISTORICAL_ROOTS_LIMIT` (F6). -/
theorem historical_summaries_update_etheorem {p : Spec.Preset} (hp : PresetAgrees p)
    (ht : TailPresetAgrees p) {o : Spec.Oracle} (ho : OracleAgrees o) (e : EtheoremState)
    (hcap : e.historicalSummaries.val.size < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {s' : Spec.BeaconState}
    (h : Spec.process_historical_summaries_update p o (toSpecState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processHistoricalSummariesUpdate (StateTransition := GloasRun)).run
        (pureState e) = .ok ((), pureState e') ∧ toSpecState e' = s' := by
  refine ⟨_, processHistoricalSummariesUpdate_run e, ?_⟩
  have hlt := EthCLSpecs.Gloas.Const.slotsPerHistoricalRootLt
  have hper : (UInt64.ofNat (EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot /
      EthCLSpecs.Gloas.Const.slotsPerEpoch)).toNat =
      p.SLOTS_PER_HISTORICAL_ROOT / p.SLOTS_PER_EPOCH := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt),
      ht.slotsPerHistoricalRoot, hp.slotsPerEpoch]
  unfold Spec.process_historical_summaries_update at h
  rw [get_current_epoch_eq hp, currentEpochOf_pureState] at h
  simp only [bind, Except.bind] at h
  generalize hc : EthCLSpecs.Gloas.computeEpochAtSlot e.slot = c at h ⊢
  cases hadd : Spec.uint64Add c.toNat 1 with
  | error err => rw [hadd] at h; cases h
  | ok n =>
    rw [hadd] at h
    simp only at h
    have hn : (c + 1).toNat = n := uint64Add_ok (a := c) (b := 1) (by simpa using hadd)
    cases hdiv : Spec.uint64Div p.SLOTS_PER_HISTORICAL_ROOT p.SLOTS_PER_EPOCH with
    | error err => rw [hdiv] at h; cases h
    | ok per =>
      rw [hdiv] at h
      simp only at h
      have hper' : per = p.SLOTS_PER_HISTORICAL_ROOT / p.SLOTS_PER_EPOCH := by
        unfold Spec.uint64Div at hdiv
        split at hdiv
        · cases hdiv
        · simp only [pure, Except.pure, Except.ok.injEq] at hdiv; exact hdiv.symm
      cases hmod : Spec.uint64Mod n per with
      | error err => rw [hmod] at h; cases h
      | ok r =>
        rw [hmod] at h
        have hr : ((c + 1) % UInt64.ofNat (EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot /
            EthCLSpecs.Gloas.Const.slotsPerEpoch)).toNat = r := by
          apply uint64Mod_ok
          rw [hn, hper, ← hper']
          exact hmod
        simp only [pure, Except.pure] at h
        by_cases h0 : r = 0
        · rw [if_pos (by rw [uint64_eq_zero_iff, hr, h0])]
          simp only [h0, beq_self_eq_true, if_true, Except.ok.injEq] at h
          rw [← h, toSpecState_set_historicalSummaries, sszList_push_toList _ _ hcap, List.map_append]
          simp only [toSpecState_historical_summaries, toSpecState_block_roots, toSpecState_state_roots,
            ho.blockRoots, ho.stateRoots, rootsVector_toList]
          rfl
        · rw [if_neg (by rw [uint64_eq_zero_iff, hr]; exact h0)]
          simp only [beq_iff_eq, h0, if_false, Except.ok.injEq] at h
          exact h

end forkproof

