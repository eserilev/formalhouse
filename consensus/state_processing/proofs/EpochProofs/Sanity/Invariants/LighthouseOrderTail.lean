import EpochProofs.Sanity.Invariants.LighthouseOrderSwaps

/-!
# The order of the steps after the builder payments

The spec runs the eth1 reset, then (after the deposits, consolidations and payments) the
slashings reset, the randao reset, the historical summaries update, the participation rotation,
the sync committee update, the proposer lookahead and the PTC window. Lighthouse runs the
proposer lookahead and the PTC window first, then the eth1 reset and the other steps.

`runSteps` runs a list of steps. `runSteps_swap` swaps two neighbours. Each step here keeps the
slot, so the conditions of the swaps hold at every position.
-/

namespace EpochProofs.Spec

/-! ## Running a list of steps -/

/-- Run the steps in order. -/
def runSteps : List (BeaconState → SpecM BeaconState) → BeaconState → SpecM BeaconState
  | [], s => pure s
  | f :: fs, s => f s >>= runSteps fs

/-- A step keeps `P`. -/
def StepKeeps (P : BeaconState → Prop) (f : BeaconState → SpecM BeaconState) : Prop :=
  ∀ s t, P s → f s = .ok t → P t

theorem runSteps_append (pre post : List (BeaconState → SpecM BeaconState)) (s : BeaconState) :
    runSteps (pre ++ post) s = runSteps pre s >>= runSteps post := by
  induction pre generalizing s with
  | nil => rfl
  | cons f fs ih =>
    show (f s >>= runSteps (fs ++ post)) = (f s >>= runSteps fs) >>= runSteps post
    rw [bind_assoc]
    congr 1
    funext t
    exact ih t

/-- `runSteps` keeps `P` when each step keeps it. -/
theorem runSteps_keeps (P : BeaconState → Prop) :
    ∀ (fs : List (BeaconState → SpecM BeaconState)), (∀ f ∈ fs, StepKeeps P f) →
      ∀ s t, P s → runSteps fs s = .ok t → P t
  | [], _, s, t, hs, h => by cases h; exact hs
  | f :: fs, hk, s, t, hs, h => by
    simp only [runSteps] at h
    cases hf : f s with
    | error e => rw [hf] at h; cases h
    | ok u =>
      rw [hf] at h
      exact runSteps_keeps P fs (fun g hg => hk g (by simp [hg])) u t
        (hk f (by simp) s u hs hf) h

/-- Two neighbours swap when they swap on every state with `P`, and the steps before them keep
`P`. -/
theorem runSteps_swap (P : BeaconState → Prop) (pre post : List (BeaconState → SpecM BeaconState))
    (f g : BeaconState → SpecM BeaconState) (hpre : ∀ h ∈ pre, StepKeeps P h)
    (hfg : ∀ s, P s → SameOk (f s >>= g) (g s >>= f)) (s : BeaconState) (hs : P s) :
    SameOk (runSteps (pre ++ f :: g :: post) s) (runSteps (pre ++ g :: f :: post) s) := by
  rw [runSteps_append, runSteps_append]
  refine SameOk.bind (SameOk.refl _) (fun u hu => ?_)
  have hPu := runSteps_keeps P pre hpre s u hs hu
  show SameOk (f u >>= fun v => g v >>= runSteps post) (g u >>= fun v => f v >>= runSteps post)
  exact sameOk_swap_cont (hfg u hPu) (runSteps post)

/-! ## The steps as computed values and writes -/

/-- The new `slashings` of the slashings reset. -/
def srNew (s : BeaconState) : SpecM (List Gwei) := do
  let next_epoch ← uint64Add (← get_current_epoch Preset.mainnet s) 1
  listSet s.slashings (← uint64Mod next_epoch Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR) 0

theorem process_slashings_reset_eq (s : BeaconState) :
    process_slashings_reset Preset.mainnet s =
      (fun v => { s with slashings := v }) <$> srNew s := by
  unfold process_slashings_reset srNew
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

/-- The new `randao_mixes` of the randao reset. -/
def rrNew (s : BeaconState) : SpecM (List Bytes32) := do
  let current_epoch ← get_current_epoch Preset.mainnet s
  let next_epoch ← uint64Add current_epoch 1
  let mix ← get_randao_mix Preset.mainnet s current_epoch
  listSet s.randao_mixes (← uint64Mod next_epoch Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR) mix

theorem process_randao_mixes_reset_eq (s : BeaconState) :
    process_randao_mixes_reset Preset.mainnet s =
      (fun v => { s with randao_mixes := v }) <$> rrNew s := by
  unfold process_randao_mixes_reset rrNew
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

/-- The new `historical_summaries` of the historical summaries update. -/
def hsNew (o : Oracle) (s : BeaconState) : SpecM (List HistoricalSummary) := do
  let next_epoch ← uint64Add (← get_current_epoch Preset.mainnet s) 1
  if (← uint64Mod next_epoch
      (← uint64Div Preset.mainnet.SLOTS_PER_HISTORICAL_ROOT Preset.mainnet.SLOTS_PER_EPOCH)) == 0
  then
    let historical_summary : HistoricalSummary := {
      block_summary_root := o.hash_tree_root_BlockRoots s.block_roots
      state_summary_root := o.hash_tree_root_StateRoots s.state_roots }
    pure (s.historical_summaries ++ [historical_summary])
  else
    pure s.historical_summaries

theorem process_historical_summaries_update_eq (o : Oracle) (s : BeaconState) :
    process_historical_summaries_update Preset.mainnet o s =
      (fun v => { s with historical_summaries := v }) <$> hsNew o s := by
  unfold process_historical_summaries_update hsNew
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

/-- The participation rotation as a step. -/
def pfStep (s : BeaconState) : SpecM BeaconState := pure (process_participation_flag_updates s)

/-- `s` with new participation lists. -/
def setPF (s : BeaconState) (v : List ParticipationFlags × List ParticipationFlags) :
    BeaconState :=
  { s with previous_epoch_participation := v.fst, current_epoch_participation := v.snd }

/-- `s` with new sync committees. -/
def setSC (s : BeaconState) (v : SyncCommittee × SyncCommittee) : BeaconState :=
  { s with current_sync_committee := v.fst, next_sync_committee := v.snd }

/-- The new participation lists of the rotation. -/
def pfNew (s : BeaconState) : SpecM (List ParticipationFlags × List ParticipationFlags) :=
  pure (s.current_epoch_participation, List.replicate s.validators.length 0)

theorem pfStep_eq (s : BeaconState) :
    pfStep s = (fun v => setPF s v) <$> pfNew s := rfl

/-- The new sync committees of the sync committee update. -/
def scNew (o : Oracle) (s : BeaconState) : SpecM (SyncCommittee × SyncCommittee) := do
  let next_epoch ← uint64Add (← get_current_epoch Preset.mainnet s) 1
  if (← uint64Mod next_epoch Preset.mainnet.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) == 0 then
    let next ← get_next_sync_committee Preset.mainnet o
      { s with current_sync_committee := s.next_sync_committee }
    pure (s.next_sync_committee, next)
  else
    pure (s.current_sync_committee, s.next_sync_committee)

theorem process_sync_committee_updates_eq (o : Oracle) (s : BeaconState) :
    process_sync_committee_updates Preset.mainnet o s =
      (fun v => setSC s v) <$> scNew o s := by
  unfold process_sync_committee_updates scNew setSC
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

/-! ## What the steps read -/

theorem scNew_congr (o : Oracle) (s1 s2 : BeaconState) (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes)
    (hn : s1.next_sync_committee = s2.next_sync_committee)
    (hc : s1.current_sync_committee = s2.current_sync_committee) :
    scNew o s1 = scNew o s2 := by
  have h := get_next_sync_committee_congr (p := Preset.mainnet) (o := o)
    (s1 := { s1 with current_sync_committee := s1.next_sync_committee })
    (s2 := { s2 with current_sync_committee := s2.next_sync_committee }) hs hv hr
  unfold scNew
  rw [h, hn, hc]
  simp only [get_current_epoch_mainnet, hs]

/-- The randao reset writes the mix of the next epoch. The seeds two epochs ahead read the mix of
the current epoch, so they do not change. -/
theorem rrNew_seed (o : Oracle) (s : BeaconState) (v : List Bytes32)
    (hfit : s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 65538 < 2 ^ 64)
    (hv : rrNew s = .ok v) (d : DomainType) :
    get_seed Preset.mainnet o { s with randao_mixes := v }
        (s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 + 1) d =
      get_seed Preset.mainnet o s (s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 + 1) d := by
  have hspe : Preset.mainnet.SLOTS_PER_EPOCH = 32 := rfl
  have hehv : Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR = 65536 := rfl
  have hmsl : Preset.mainnet.MIN_SEED_LOOKAHEAD = 1 := rfl
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot / Preset.mainnet.SLOTS_PER_EPOCH = n := ⟨_, rfl⟩
  rw [hn] at hfit ⊢
  have hf : @LT.lt Nat _ (n + 65538) (2 ^ 64) := hfit
  have h1 : n + 1 < 2 ^ 64 := by omega
  unfold rrNew at hv
  simp only [get_current_epoch_mainnet, hn, ok_bind', uint64Add_of_lt _ _ h1, get_randao_mix,
    uint64Mod, hehv, show (65536 : Nat) ≠ 0 by decide, if_false, pure, Except.pure] at hv
  cases hmix : listGet s.randao_mixes (n % 65536) with
  | error e => rw [hmix] at hv; cases hv
  | ok mix =>
    rw [hmix, ok_bind'] at hv
    unfold listSet at hv
    split at hv
    · cases hv
      unfold get_seed get_randao_mix
      have h2 : n + 1 + 1 + 65536 < 2 ^ 64 := by omega
      simp only [hehv, hmsl, uint64Add_of_lt _ _ h2, ok_bind']
      have h3 : 1 ≤ n + 1 + 1 + 65536 := by omega
      have h4 : 1 ≤ n + 1 + 1 + 65536 - 1 := by omega
      simp only [uint64Sub, h3, h4, if_true, pure, Except.pure, ok_bind', uint64Mod,
        show (65536 : Nat) ≠ 0 by decide, if_false]
      have hidx : (n + 1 + 1 + 65536 - 1 - 1) % 65536 ≠ (n + 1) % 65536 := by omega
      simp only [listGet, List.getElem?_set_ne (Ne.symm hidx)]
    · cases hv

/-! ## The swaps with the proposer lookahead and the PTC window -/

/-- The slot fits with room for the seed lookups two epochs ahead. -/
def SlotRoom (s : BeaconState) : Prop :=
  s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 65538 < 2 ^ 64

theorem plNew_set (o : Oracle) (s t : BeaconState) (hpl : t.proposer_lookahead = s.proposer_lookahead)
    (hs : t.slot = s.slot) (hv : t.validators = s.validators)
    (hr : t.randao_mixes = s.randao_mixes) : plNew o t = plNew o s :=
  plNew_congr o t s hpl hs hv (by rw [get_seed_congr hr])

theorem ptcNew_set (o : Oracle) (s t : BeaconState) (hptc : t.ptc_window = s.ptc_window)
    (hs : t.slot = s.slot) (hv : t.validators = s.validators)
    (hr : t.randao_mixes = s.randao_mixes) : ptcNew o t = ptcNew o s :=
  ptcNew_congr o t s hptc hs hv (fun d => by rw [get_seed_congr hr])

/-- A step `X` swaps with the proposer lookahead and with the PTC window. -/
structure SwapsWithCommittees (o : Oracle) (X : BeaconState → SpecM BeaconState) : Prop where
  pl : ∀ s, SlotRoom s → SameOk (X s >>= process_proposer_lookahead Preset.mainnet o)
    (process_proposer_lookahead Preset.mainnet o s >>= X)
  ptc : ∀ s, SlotRoom s → SameOk (X s >>= process_ptc_window Preset.mainnet o)
    (process_ptc_window Preset.mainnet o s >>= X)

theorem eth1_swaps (o : Oracle) : SwapsWithCommittees o (process_eth1_data_reset Preset.mainnet) where
  pl s _ := swap_shapes _ _ eth1Cond (fun b t => if b then { t with eth1_data_votes := [] } else t)
    (plNew o) (fun w t => setPL t w) s eth1_eq (process_proposer_lookahead_eq o)
    (fun b _ => by cases b <;> rfl)
    (fun _ _ => eth1Cond_slot rfl) (fun b _ => by cases b <;> rfl)
  ptc s _ := swap_shapes _ _ eth1Cond (fun b t => if b then { t with eth1_data_votes := [] } else t)
    (ptcNew o) (fun w t => setPTC t w) s eth1_eq (process_ptc_window_eq o)
    (fun b _ => by cases b <;> rfl)
    (fun _ _ => eth1Cond_slot rfl) (fun b _ => by cases b <;> rfl)

theorem slashings_reset_swaps (o : Oracle) :
    SwapsWithCommittees o (process_slashings_reset Preset.mainnet) where
  pl s _ := swap_shapes _ _ srNew (fun v t => { t with slashings := v }) (plNew o)
    (fun w t => setPL t w) s process_slashings_reset_eq (process_proposer_lookahead_eq o)
    (fun _ _ => plNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  ptc s _ := swap_shapes _ _ srNew (fun v t => { t with slashings := v }) (ptcNew o)
    (fun w t => setPTC t w) s process_slashings_reset_eq (process_ptc_window_eq o)
    (fun _ _ => ptcNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem randao_reset_swaps (o : Oracle) :
    SwapsWithCommittees o (process_randao_mixes_reset Preset.mainnet) where
  pl s hroom := swap_shapes _ _ rrNew (fun v t => { t with randao_mixes := v }) (plNew o)
    (fun w t => setPL t w) s process_randao_mixes_reset_eq (process_proposer_lookahead_eq o)
    (fun v hv => plNew_congr o _ s rfl rfl rfl (rrNew_seed o s v hroom hv _))
    (fun _ _ => rfl) (fun _ _ => rfl)
  ptc s hroom := swap_shapes _ _ rrNew (fun v t => { t with randao_mixes := v }) (ptcNew o)
    (fun w t => setPTC t w) s process_randao_mixes_reset_eq (process_ptc_window_eq o)
    (fun v hv => ptcNew_congr o _ s rfl rfl rfl (rrNew_seed o s v hroom hv))
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem historical_swaps (o : Oracle) :
    SwapsWithCommittees o (process_historical_summaries_update Preset.mainnet o) where
  pl s _ := swap_shapes _ _ (hsNew o) (fun v t => { t with historical_summaries := v })
    (plNew o) (fun w t => setPL t w) s (process_historical_summaries_update_eq o)
    (process_proposer_lookahead_eq o)
    (fun _ _ => plNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  ptc s _ := swap_shapes _ _ (hsNew o) (fun v t => { t with historical_summaries := v })
    (ptcNew o) (fun w t => setPTC t w) s (process_historical_summaries_update_eq o)
    (process_ptc_window_eq o)
    (fun _ _ => ptcNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem participation_swaps (o : Oracle) : SwapsWithCommittees o pfStep where
  pl s _ := swap_shapes _ _ pfNew (fun v t => setPF t v) (plNew o) (fun w t => setPL t w) s
    pfStep_eq (process_proposer_lookahead_eq o)
    (fun _ _ => plNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  ptc s _ := swap_shapes _ _ pfNew (fun v t => setPF t v) (ptcNew o) (fun w t => setPTC t w) s
    pfStep_eq (process_ptc_window_eq o)
    (fun _ _ => ptcNew_set o s _ rfl rfl rfl rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem sync_swaps (o : Oracle) :
    SwapsWithCommittees o (process_sync_committee_updates Preset.mainnet o) where
  pl s _ := swap_shapes _ _ (scNew o) (fun v t => setSC t v) (plNew o) (fun w t => setPL t w) s
    (process_sync_committee_updates_eq o) (process_proposer_lookahead_eq o)
    (fun _ _ => plNew_set o s _ rfl rfl rfl rfl)
    (fun _ _ => scNew_congr o _ s rfl rfl rfl rfl rfl) (fun _ _ => rfl)
  ptc s _ := swap_shapes _ _ (scNew o) (fun v t => setSC t v) (ptcNew o) (fun w t => setPTC t w)
    s (process_sync_committee_updates_eq o) (process_ptc_window_eq o)
    (fun _ _ => ptcNew_set o s _ rfl rfl rfl rfl)
    (fun _ _ => scNew_congr o _ s rfl rfl rfl rfl rfl) (fun _ _ => rfl)

/-! ## The two orders -/

theorem map_ok_inv {α : Type} {f : α → BeaconState} {x : SpecM α} {t : BeaconState}
    (h : f <$> x = .ok t) : ∃ v, x = .ok v ∧ t = f v := by
  cases x with
  | error e => cases h
  | ok v => cases h; exact ⟨v, rfl, rfl⟩

/-- A step that only writes values keeps every condition on the fields it does not write. -/
theorem keeps_of_shape {α : Type} (P : BeaconState → Prop) (X : BeaconState → SpecM BeaconState)
    (xNew : BeaconState → SpecM α) (G : α → BeaconState → BeaconState)
    (hX : ∀ t, X t = (fun v => G v t) <$> xNew t) (hG : ∀ v t, P t → P (G v t)) :
    StepKeeps P X := by
  intro s t hs h
  rw [hX] at h
  obtain ⟨v, -, rfl⟩ := map_ok_inv h
  exact hG v s hs

theorem slotRoom_keeps_eth1 : StepKeeps SlotRoom (process_eth1_data_reset Preset.mainnet) :=
  keeps_of_shape _ _ _ _ eth1_eq (fun b t h => by cases b <;> exact h)

theorem slotRoom_keeps_sr : StepKeeps SlotRoom (process_slashings_reset Preset.mainnet) :=
  keeps_of_shape _ _ _ _ process_slashings_reset_eq (fun _ _ h => h)

theorem slotRoom_keeps_rr : StepKeeps SlotRoom (process_randao_mixes_reset Preset.mainnet) :=
  keeps_of_shape _ _ _ _ process_randao_mixes_reset_eq (fun _ _ h => h)

theorem slotRoom_keeps_hs (o : Oracle) :
    StepKeeps SlotRoom (process_historical_summaries_update Preset.mainnet o) :=
  keeps_of_shape _ _ _ _ (process_historical_summaries_update_eq o) (fun _ _ h => h)

theorem slotRoom_keeps_pf : StepKeeps SlotRoom pfStep :=
  keeps_of_shape _ _ _ _ pfStep_eq (fun _ _ h => h)

theorem slotRoom_keeps_sc (o : Oracle) :
    StepKeeps SlotRoom (process_sync_committee_updates Preset.mainnet o) :=
  keeps_of_shape _ _ _ _ (process_sync_committee_updates_eq o) (fun _ _ h => h)

theorem slotRoom_keeps_pl (o : Oracle) :
    StepKeeps SlotRoom (process_proposer_lookahead Preset.mainnet o) :=
  keeps_of_shape _ _ _ _ (process_proposer_lookahead_eq o) (fun _ _ h => h)

theorem slotRoom_keeps_ptc (o : Oracle) :
    StepKeeps SlotRoom (process_ptc_window Preset.mainnet o) :=
  keeps_of_shape _ _ _ _ (process_ptc_window_eq o) (fun _ _ h => h)

/-- The spec order of the steps after the builder payments, with the eth1 reset first. -/
def specOrder (o : Oracle) : List (BeaconState → SpecM BeaconState) :=
  [process_eth1_data_reset Preset.mainnet, process_slashings_reset Preset.mainnet,
    process_randao_mixes_reset Preset.mainnet, process_historical_summaries_update Preset.mainnet o,
    pfStep, process_sync_committee_updates Preset.mainnet o,
    process_proposer_lookahead Preset.mainnet o, process_ptc_window Preset.mainnet o]

/-- The Lighthouse order: the proposer lookahead and the PTC window first. -/
def lhOrder (o : Oracle) : List (BeaconState → SpecM BeaconState) :=
  [process_proposer_lookahead Preset.mainnet o, process_ptc_window Preset.mainnet o,
    process_eth1_data_reset Preset.mainnet, process_slashings_reset Preset.mainnet,
    process_randao_mixes_reset Preset.mainnet, process_historical_summaries_update Preset.mainnet o,
    pfStep, process_sync_committee_updates Preset.mainnet o]

/-- The two orders give the same `ok` results. -/
theorem specOrder_lhOrder (o : Oracle) (s : BeaconState) (hroom : SlotRoom s) :
    SameOk (runSteps (specOrder o) s) (runSteps (lhOrder o) s) := by
  let e1 := process_eth1_data_reset Preset.mainnet
  let sr := process_slashings_reset Preset.mainnet
  let rr := process_randao_mixes_reset Preset.mainnet
  let hs := process_historical_summaries_update Preset.mainnet o
  let sc := process_sync_committee_updates Preset.mainnet o
  let pl := process_proposer_lookahead Preset.mainnet o
  let ptc := process_ptc_window Preset.mainnet o
  have k1 : StepKeeps SlotRoom e1 := slotRoom_keeps_eth1
  have k2 : StepKeeps SlotRoom sr := slotRoom_keeps_sr
  have k3 : StepKeeps SlotRoom rr := slotRoom_keeps_rr
  have k4 : StepKeeps SlotRoom hs := slotRoom_keeps_hs o
  have k5 : StepKeeps SlotRoom pfStep := slotRoom_keeps_pf
  have k7 : StepKeeps SlotRoom pl := slotRoom_keeps_pl o
  have keep : ∀ (l : List (BeaconState → SpecM BeaconState)),
      (∀ f ∈ l, f = e1 ∨ f = sr ∨ f = rr ∨ f = hs ∨ f = pfStep ∨ f = pl) →
      ∀ f ∈ l, StepKeeps SlotRoom f := by
    intro l hl f hf
    rcases hl f hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  -- Move the proposer lookahead to the front.
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr, hs, pfStep] [ptc] sc pl
    (keep _ (by simp)) (sync_swaps o).pl s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr, hs] [sc, ptc] pfStep pl
    (keep _ (by simp)) (participation_swaps o).pl s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr, rr] [pfStep, sc, ptc] hs pl
    (keep _ (by simp)) (historical_swaps o).pl s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1, sr] [hs, pfStep, sc, ptc] rr pl
    (keep _ (by simp)) (randao_reset_swaps o).pl s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [e1] [rr, hs, pfStep, sc, ptc] sr pl
    (keep _ (by simp)) (slashings_reset_swaps o).pl s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [] [sr, rr, hs, pfStep, sc, ptc] e1 pl
    (keep _ (by simp)) (eth1_swaps o).pl s hroom) ?_
  -- Move the PTC window to the second place.
  refine SameOk.trans (runSteps_swap SlotRoom [pl, e1, sr, rr, hs, pfStep] [] sc ptc
    (keep _ (by simp)) (sync_swaps o).ptc s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [pl, e1, sr, rr, hs] [sc] pfStep ptc
    (keep _ (by simp)) (participation_swaps o).ptc s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [pl, e1, sr, rr] [pfStep, sc] hs ptc
    (keep _ (by simp)) (historical_swaps o).ptc s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [pl, e1, sr] [hs, pfStep, sc] rr ptc
    (keep _ (by simp)) (randao_reset_swaps o).ptc s hroom) ?_
  refine SameOk.trans (runSteps_swap SlotRoom [pl, e1] [rr, hs, pfStep, sc] sr ptc
    (keep _ (by simp)) (slashings_reset_swaps o).ptc s hroom) ?_
  exact runSteps_swap SlotRoom [pl] [sr, rr, hs, pfStep, sc] e1 ptc
    (keep _ (by simp)) (eth1_swaps o).ptc s hroom

end EpochProofs.Spec
