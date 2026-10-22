import EpochProofs.Sanity.Invariants.LighthouseOrderTail
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluEpoch

/-!
# The order of the Fulu steps after the effective balance update

The Fulu spec runs the slashings reset, the randao reset, the historical summaries update, the
participation rotation, the sync committee update and then the proposer lookahead. Lighthouse
runs the Fulu proposer lookahead inside `process_epoch_single_pass`, before these steps and
before the eth1 reset (`single_pass.rs`, `altair.rs`).

`specOrderFulu_lhOrderFulu` shows that the two orders give the same `ok` results. It is the
Fulu version of `specOrder_lhOrder`: the Fulu lookahead reads the same fields as the Gloas
lookahead (`plFuluNew_congr`), so each swap of `LighthouseOrderTail.lean` carries over.
-/

namespace EpochProofs.Spec

/-! ## The Fulu proposer lookahead as a computed value and a write -/

/-- The new `proposer_lookahead` that `process_proposer_lookahead_fulu` writes. -/
def plFuluNew [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM (List ValidatorIndex) := do
  let last_epoch_start ← uint64Sub s.proposer_lookahead.length P.SLOTS_PER_EPOCH
  let st := setPL s (s.proposer_lookahead.drop P.SLOTS_PER_EPOCH ++
    s.proposer_lookahead.drop last_epoch_start)
  let last_epoch_proposers ← get_beacon_proposer_indices_fulu P o st
    (← uint64Add (← uint64Add (s.slot / P.SLOTS_PER_EPOCH)
      P.MIN_SEED_LOOKAHEAD) 1)
  pure (st.proposer_lookahead.take last_epoch_start ++ last_epoch_proposers)

theorem process_proposer_lookahead_fulu_eq [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    process_proposer_lookahead_fulu P o s = (fun l => setPL s l) <$> plFuluNew o s := by
  unfold process_proposer_lookahead_fulu plFuluNew setPL
  simp only [get_current_epoch_mainnet, ok_bind']
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

/-- The Fulu `get_beacon_proposer_indices` reads `validators` and the proposer seed of
`epoch`. -/
theorem get_beacon_proposer_indices_fulu_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    {epoch : Epoch} (hv : s1.validators = s2.validators)
    (hseed : get_seed p o s1 epoch DOMAIN_BEACON_PROPOSER =
      get_seed p o s2 epoch DOMAIN_BEACON_PROPOSER) :
    get_beacon_proposer_indices_fulu p o s1 epoch = get_beacon_proposer_indices_fulu p o s2 epoch := by
  simp only [get_beacon_proposer_indices_fulu, compute_proposer_indices_fulu,
    compute_proposer_index, get_active_validator_indices_congr hv, hseed, hv]

/-- `plFuluNew` reads `proposer_lookahead`, `slot`, `validators` and the proposer seed two epochs
ahead. -/
theorem plFuluNew_congr [PresetCfg] (o : Oracle) (s1 s2 : BeaconState)
    (hpl : s1.proposer_lookahead = s2.proposer_lookahead) (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators)
    (hseed : get_seed P o s1 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1)
        DOMAIN_BEACON_PROPOSER =
      get_seed P o s2 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1)
        DOMAIN_BEACON_PROPOSER) :
    plFuluNew o s1 = plFuluNew o s2 := by
  have hg : ∀ l, get_beacon_proposer_indices_fulu P o (setPL s1 l)
      (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1) =
    get_beacon_proposer_indices_fulu P o (setPL s2 l)
      (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1) := fun l =>
    get_beacon_proposer_indices_fulu_congr hv
      ((congrFun (congrFun (get_seed_congr (s1 := setPL s1 l) (s2 := s1) rfl) _) _).trans
        (hseed.trans (congrFun (congrFun (get_seed_congr (s1 := s2) (s2 := setPL s2 l) rfl) _) _)))
  unfold plFuluNew
  rw [hpl, hs]
  have hmsl : P.MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [hmsl]
  generalize get_beacon_proposer_indices_fulu P o = F at hg ⊢
  cases uint64Sub s2.proposer_lookahead.length P.SLOTS_PER_EPOCH with
  | error e => simp only [error_bind']
  | ok les =>
    simp only [ok_bind']
    by_cases h1 : s2.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64
    · simp only [uint64Add_of_lt _ _ h1, ok_bind']
      by_cases h2 : s2.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64
      · simp only [uint64Add_of_lt _ _ h2, ok_bind', hg]
        rfl
      · simp only [uint64Add_of_ge _ _ h2, error_bind']
    · simp only [uint64Add_of_ge _ _ h1, error_bind']

theorem plFuluNew_set [PresetCfg] (o : Oracle) (s t : BeaconState)
    (hpl : t.proposer_lookahead = s.proposer_lookahead) (hs : t.slot = s.slot)
    (hv : t.validators = s.validators) (hr : t.randao_mixes = s.randao_mixes) :
    plFuluNew o t = plFuluNew o s :=
  plFuluNew_congr o t s hpl hs hv (by rw [get_seed_congr hr])

/-! ## The swaps with the Fulu proposer lookahead -/

theorem eth1_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    SameOk (process_eth1_data_reset P s >>= process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>= process_eth1_data_reset P) :=
  swap_shapes _ _ eth1Cond (fun b t => if b then { t with eth1_data_votes := [] } else t)
    (plFuluNew o) (fun w t => setPL t w) s eth1_eq (process_proposer_lookahead_fulu_eq o)
    (fun b _ => by cases b <;> rfl)
    (fun _ _ => eth1Cond_slot rfl) (fun b _ => by cases b <;> rfl)

theorem slashings_reset_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    SameOk (process_slashings_reset P s >>= process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>= process_slashings_reset P) :=
  swap_shapes _ _ srNew (fun v t => { t with slashings := v }) (plFuluNew o)
    (fun w t => setPL t w) s process_slashings_reset_eq (process_proposer_lookahead_fulu_eq o)
    (fun _ _ => plFuluNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem randao_reset_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) (hroom : SlotRoom s) :
    SameOk (process_randao_mixes_reset P s >>=
        process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>=
        process_randao_mixes_reset P) :=
  swap_shapes _ _ rrNew (fun v t => { t with randao_mixes := v }) (plFuluNew o)
    (fun w t => setPL t w) s process_randao_mixes_reset_eq (process_proposer_lookahead_fulu_eq o)
    (fun v hv => plFuluNew_congr o _ s rfl rfl rfl (rrNew_seed o s v hroom hv _))
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem historical_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    SameOk (process_historical_summaries_update P o s >>=
        process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>=
        process_historical_summaries_update P o) :=
  swap_shapes _ _ (hsNew o) (fun v t => { t with historical_summaries := v })
    (plFuluNew o) (fun w t => setPL t w) s (process_historical_summaries_update_eq o)
    (process_proposer_lookahead_fulu_eq o)
    (fun _ _ => plFuluNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem participation_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    SameOk (pfStep s >>= process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>= pfStep) :=
  swap_shapes _ _ pfNew (fun v t => setPF t v) (plFuluNew o) (fun w t => setPL t w) s
    pfStep_eq (process_proposer_lookahead_fulu_eq o)
    (fun _ _ => plFuluNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem sync_swaps_fulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    SameOk (process_sync_committee_updates P o s >>=
        process_proposer_lookahead_fulu P o)
      (process_proposer_lookahead_fulu P o s >>=
        process_sync_committee_updates P o) :=
  swap_shapes _ _ (scNew o) (fun v t => setSC t v) (plFuluNew o) (fun w t => setPL t w) s
    (process_sync_committee_updates_eq o) (process_proposer_lookahead_fulu_eq o)
    (fun _ _ => plFuluNew_set o s _ rfl rfl rfl rfl)
    (fun _ _ => scNew_congr o _ s rfl rfl rfl rfl rfl) (fun _ _ => rfl)

/-! ## The two Fulu orders -/

/-- The Fulu spec order of the steps after the effective balance update, with the eth1 reset
first. -/
def specOrderFulu [PresetCfg] (o : Oracle) : List (BeaconState → SpecM BeaconState) :=
  [process_eth1_data_reset P, process_slashings_reset P,
    process_randao_mixes_reset P, process_historical_summaries_update P o,
    pfStep, process_sync_committee_updates P o,
    process_proposer_lookahead_fulu P o]

/-- The Lighthouse Fulu order: the proposer lookahead first. -/
def lhOrderFulu [PresetCfg] (o : Oracle) : List (BeaconState → SpecM BeaconState) :=
  [process_proposer_lookahead_fulu P o,
    process_eth1_data_reset P, process_slashings_reset P,
    process_randao_mixes_reset P, process_historical_summaries_update P o,
    pfStep, process_sync_committee_updates P o]

/-- The two Fulu orders give the same `ok` results. -/
theorem specOrderFulu_lhOrderFulu [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) (hroom : SlotRoom s) :
    SameOk (runSteps (specOrderFulu o) s) (runSteps (lhOrderFulu o) s) := by
  let e1 := process_eth1_data_reset P
  let sr := process_slashings_reset P
  let rr := process_randao_mixes_reset P
  let hs := process_historical_summaries_update P o
  let sc := process_sync_committee_updates P o
  let pl := process_proposer_lookahead_fulu P o
  have k1 : StepKeeps SlotRoom e1 := slotRoom_keeps_eth1
  have k2 : StepKeeps SlotRoom sr := slotRoom_keeps_sr
  have k3 : StepKeeps SlotRoom rr := slotRoom_keeps_rr
  have k4 : StepKeeps SlotRoom hs := slotRoom_keeps_hs o
  have k5 : StepKeeps SlotRoom pfStep := slotRoom_keeps_pf
  have keep : ∀ (l : List (BeaconState → SpecM BeaconState)),
      (∀ f ∈ l, f = e1 ∨ f = sr ∨ f = rr ∨ f = hs ∨ f = pfStep) →
      ∀ f ∈ l, StepKeeps SlotRoom f := by
    intro l hl f hf
    rcases hl f hf with rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr, hs, pfStep] [] sc pl
    (keep _ (by simp)) (fun t _ => sync_swaps_fulu o t) s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr, hs] [sc] pfStep pl
    (keep _ (by simp)) (fun t _ => participation_swaps_fulu o t) s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr] [pfStep, sc] hs pl
    (keep _ (by simp)) (fun t _ => historical_swaps_fulu o t) s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr] [hs, pfStep, sc] rr pl
    (keep _ (by simp)) (fun t ht => randao_reset_swaps_fulu o t ht) s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1] [rr, hs, pfStep, sc] sr pl
    (keep _ (by simp)) (fun t _ => slashings_reset_swaps_fulu o t) s hroom) ?_
  exact runSteps_swap SlotRoom [] [sr, rr, hs, pfStep, sc] e1 pl
    (keep _ (by simp)) (fun t _ => eth1_swaps_fulu o t) s hroom

end EpochProofs.Spec
