import EpochProofs.Equiv.TailUpdates
import EpochProofs.Equiv.EpochCommittees
import EpochProofs.Sanity.Invariants.LighthouseOrder

/-!
# The epoch tail, composed from the translated functions

`tail` is the end of `altair.rs` `process_epoch`: the eth1, slashings and RANDAO resets
(`resets.rs`), the historical summaries update, the participation rotation and the sync
committee update. The checks and indices are the translated functions of `tail_updates.rs`, and
the next sync committee indices are the translated `next_sync_committee_indices`. The reads and
the writes are untranslated glue (`TailGlue`), each with the fact that links it to the spec
(`TailLinks`). `tail_spec` shows that `tail` returns the state of the model `lhTailOrder`.
-/

namespace EpochProofs.Spec

/-- The steps of `lhRestOrder` after the PTC window. -/
def lhTailOrder [PresetCfg] (o : Oracle) (t : BeaconState) : SpecM BeaconState := do
  let t ← lhEth1DataReset t
  let t ← lhSlashingsReset t
  let t ← lhRandaoMixesReset t
  let t ← lhHistoricalSummariesUpdate o t
  let t := process_participation_flag_updates t
  process_sync_committee_updates P o t

/-- The steps of `lhTailOrder` before the sync committee update. -/
def lhResets [PresetCfg] (o : Oracle) (t : BeaconState) : SpecM BeaconState := do
  let t ← lhEth1DataReset t
  let t ← lhSlashingsReset t
  let t ← lhRandaoMixesReset t
  let t ← lhHistoricalSummariesUpdate o t
  pure (process_participation_flag_updates t)

theorem lhTailOrder_eq [PresetCfg] (o : Oracle) (t : BeaconState) :
    lhTailOrder o t = lhResets o t >>= process_sync_committee_updates P o := by
  simp only [lhTailOrder, lhResets, bind_assoc, pure_bind]

theorem lhRestOrder_eq [PresetCfg] (o : Oracle) (t : BeaconState) :
    lhRestOrder o t = (do
      let t ← process_proposer_lookahead P o t
      let t ← process_ptc_window P o t
      lhTailOrder o t) := rfl

/-- The sync committee of `indices`, as `sync_committee_from_indices` builds it. -/
def syncCommitteeOf (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex) :
    SpecM SyncCommittee := do
  let pubkeys ← indices.mapM fun index => do pure (← listGet s.validators index).pubkey
  let aggregate_pubkey ← eth_aggregate_pubkeys o pubkeys
  pure { pubkeys, aggregate_pubkey }

/-- The check of `process_sync_committee_updates`. -/
def syncDue (p : Preset) (s : BeaconState) : SpecM Bool := do
  let next_epoch ← uint64Add (← get_current_epoch p s) 1
  pure ((← uint64Mod next_epoch p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) == 0)

theorem process_sync_committee_updates_split (p : Preset) (o : Oracle) (s : BeaconState) :
    process_sync_committee_updates p o s = (do
      if ← syncDue p s then
        let s := { s with current_sync_committee := s.next_sync_committee }
        let indices ← get_next_sync_committee_indices p o s
        pure { s with next_sync_committee := ← syncCommitteeOf o s indices }
      else pure s) := by
  unfold process_sync_committee_updates syncDue get_next_sync_committee syncCommitteeOf
  simp only [bind_assoc, pure_bind]

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- A translated call that agrees with an `ok` spec result returns `Ok`. -/
theorem absResult_ok {α β : Type} {f : α → β} {r : core.result.Result α safe_arith.ArithError}
    {x : β} (h : absResult f r = .ok x) : ∃ v, r = .Ok v ∧ f v = x := by
  cases r with
  | Ok v => exact ⟨v, rfl, Except.ok.inj h⟩
  | Err e => cases h

/-- The untranslated Rust of the end of `altair.rs` `process_epoch`. -/
structure TailGlue (σ : Type) where
  /-- `process_eth1_data_reset`: the slot, `SlotsPerEth1VotingPeriod`, the votes reset. -/
  slot : σ → U64
  eth1Period : U64
  clearVotes : σ → σ
  /-- `process_slashings_reset` and `process_randao_mixes_reset`: the current epoch, the vector
  lengths, the writes. `none`: an index out of bounds. -/
  currentEpoch : σ → U64
  slashingsLength : U64
  resetSlashing : σ → U64 → Option σ
  mixesLength : U64
  copyMix : σ → U64 → U64 → Option σ
  /-- `process_historical_summaries_update`: `state.next_epoch()?`, the constants, the push. -/
  nextEpoch : σ → Option U64
  slotsPerHistoricalRoot : U64
  slotsPerEpoch : U64
  pushSummary : σ → Option σ
  /-- `rotate_participation_flags`. -/
  rotate : σ → σ
  /-- `process_sync_committee_updates`: the check, the write of the current committee, the reads
  for `next_sync_committee_indices`, and `sync_committee_from_indices` with its write. -/
  syncDue : σ → Option Bool
  writeCurrentSync : σ → Option σ
  H : Type
  hash : ShuffleHashInst H
  effectiveBalances : EBInst σ
  syncIndices : σ → Slice Usize
  syncDomain : Array U8 4#usize
  syncEpoch : σ → U64
  syncMix : σ → Array U8 32#usize
  syncSize : Usize
  syncConstants : σ → LhSelectionConstants
  writeNextSync : σ → alloc.vec.Vec Usize → Option σ

variable {σ : Type}

/-- The resets, the historical summaries update and the participation rotation, as the calls of
the translated functions joined by the glue `G`. `none`: the Rust returns an error. -/
def resets (G : TailGlue σ) (st : σ) : Result (Option σ) := do
  let r ← per_epoch_processing.tail_updates.eth1_data_votes_reset_due (G.slot st) G.eth1Period
  match r with
  | .Err _ => ok none
  | .Ok due =>
  let st := if due then G.clearVotes st else st
  let r ← per_epoch_processing.tail_updates.slashings_reset_index (G.currentEpoch st)
    G.slashingsLength
  match r with
  | .Err _ => ok none
  | .Ok none => ok none
  | .Ok (some i) =>
  match G.resetSlashing st i with
  | none => ok none
  | some st =>
  let r ← per_epoch_processing.tail_updates.randao_mixes_reset_indices (G.currentEpoch st)
    G.mixesLength
  match r with
  | .Err _ => ok none
  | .Ok none => ok none
  | .Ok (some (source, target)) =>
  match G.copyMix st source target with
  | none => ok none
  | some st =>
  match G.nextEpoch st with
  | none => ok none
  | some next =>
  let r ← per_epoch_processing.tail_updates.historical_summary_due next G.slotsPerHistoricalRoot
    G.slotsPerEpoch
  match r with
  | .Err _ => ok none
  | .Ok due =>
  match (if due then G.pushSummary st else some st) with
  | none => ok none
  | some st => ok (some (G.rotate st))

/-- `process_sync_committee_updates`, as the call of the translated
`next_sync_committee_indices` joined by the glue `G`. -/
def syncUpdate (G : TailGlue σ) (st : σ) : Result (Option σ) := do
  match G.syncDue st with
  | none => ok none
  | some false => ok (some st)
  | some true =>
  match G.writeCurrentSync st with
  | none => ok none
  | some st =>
  let r ← per_epoch_processing.epoch_committees.next_sync_committee_indices G.hash
    G.effectiveBalances st (G.syncIndices st) G.syncDomain (G.syncEpoch st) (G.syncMix st)
    G.syncSize (G.syncConstants st)
  match r with
  | .Err _ => ok none
  | .Ok indices => ok (G.writeNextSync st indices)

/-- The end of `process_epoch`. `none`: the Rust returns an error. -/
def tail (G : TailGlue σ) (st : σ) : Result (Option σ) := do
  let r ← resets G st
  match r with
  | none => ok none
  | some st5 => syncUpdate G st5

/-- N1 at the sync committee update: the active validators of the next epoch fit in the
shuffle. -/
def SyncN1 (G : TailGlue σ) (st : σ) : Prop :=
  ∀ st', G.writeCurrentSync st = some st' → (G.syncIndices st').val.length ≤ 2 ^ 24

variable [Spec.PresetCfg]

/-- The trusted facts about the glue `G`. Each read reads the state it is given and each write
writes the spec value, so each fact holds for every state `t`. -/
structure TailLinks (G : TailGlue σ) (o : Spec.Oracle) (view : σ → Spec.BeaconState) : Prop where
  slot : ∀ t, (G.slot t).val = (view t).slot
  eth1Period : G.eth1Period.val = Spec.LH_SLOTS_PER_ETH1_VOTING_PERIOD
  clearVotes : ∀ t, view (G.clearVotes t) = { view t with eth1_data_votes := [] }
  currentEpoch : ∀ t, (G.currentEpoch t).val = (view t).slot / Spec.P.SLOTS_PER_EPOCH
  slashingsLength : G.slashingsLength.val = Spec.P.EPOCHS_PER_SLASHINGS_VECTOR
  resetSlashing : ∀ t i l, Spec.listSet (view t).slashings i.val 0 = .ok l →
    ∃ t', G.resetSlashing t i = some t' ∧ view t' = { view t with slashings := l }
  mixesLength : G.mixesLength.val = Spec.P.EPOCHS_PER_HISTORICAL_VECTOR
  copyMix : ∀ t source target mix l, Spec.listGet (view t).randao_mixes source.val = .ok mix →
    Spec.listSet (view t).randao_mixes target.val mix = .ok l →
    ∃ t', G.copyMix t source target = some t' ∧ view t' = { view t with randao_mixes := l }
  /-- L1. -/
  nextEpoch : ∀ t n, Spec.uint64Add ((view t).slot / Spec.P.SLOTS_PER_EPOCH) 1 = .ok n →
    ∃ v, G.nextEpoch t = some v ∧ v.val = n
  slotsPerHistoricalRoot : G.slotsPerHistoricalRoot.val = Spec.P.SLOTS_PER_HISTORICAL_ROOT
  slotsPerEpoch : G.slotsPerEpoch.val = Spec.P.SLOTS_PER_EPOCH
  /-- The push succeeds below the Lighthouse limit, and `HistoricalSummary::new` hashes the
  roots as `hash_tree_root` does. -/
  pushSummary : ∀ t, (view t).historical_summaries.length < Spec.LH_HISTORICAL_ROOTS_LIMIT →
    ∃ t', G.pushSummary t = some t' ∧ view t' = { view t with
      historical_summaries := (view t).historical_summaries ++
        [{ block_summary_root := o.hash_tree_root_BlockRoots (view t).block_roots
           state_summary_root := o.hash_tree_root_StateRoots (view t).state_roots }] }
  rotate : ∀ t, view (G.rotate t) = Spec.process_participation_flag_updates (view t)
  syncDue : ∀ t b, Spec.syncDue Spec.P (view t) = .ok b → G.syncDue t = some b
  writeCurrentSync : ∀ t, ∃ t', G.writeCurrentSync t = some t' ∧
    view t' = { view t with current_sync_committee := (view t).next_sync_committee }
  hash : HashLink G.hash o
  effectiveBalances : ∀ t, EBLink G.effectiveBalances t
    ((view t).validators.map (·.effective_balance))
  syncIndices : ∀ t, (G.syncIndices t).val.map (·.val) =
    Spec.get_active_validator_indices (view t) (G.syncEpoch t).val
  syncDomain : u8s G.syncDomain.val = Spec.DOMAIN_SYNC_COMMITTEE.toList
  syncEpoch : ∀ t ce, Spec.get_current_epoch Spec.P (view t) = .ok ce →
    (G.syncEpoch t).val = ce + 1
  syncMix : ∀ t, SeedMixLink Spec.P (view t) (G.syncEpoch t).val (G.syncMix t)
  syncSize : G.syncSize.val = Spec.P.SYNC_COMMITTEE_SIZE
  syncConstants : ∀ t, SelectionConstantsMatch Spec.P (G.syncConstants t)
  /-- `sync_committee_from_indices` collects the pubkeys and aggregates them with BLS. -/
  writeNextSync : ∀ t v c, Spec.syncCommitteeOf o (view t) (v.val.map (·.val)) = .ok c →
    ∃ t', G.writeNextSync t v = some t' ∧ view t' = { view t with next_sync_committee := c }
  usize64 : Usize.max = U64.max

/-- The composed resets return the state of the model `lhResets`. -/
theorem resets_spec [Spec.PresetCfg.Ok] (G : TailGlue σ) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (hL : TailLinks G o view) (st : σ) (t5 : Spec.BeaconState)
    (h : Spec.lhResets o (view st) = .ok t5) :
    ∃ st5, resets G st = ok (some st5) ∧ view st5 = t5 := by
  unfold Spec.lhResets at h
  obtain ⟨t1, h1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t2, h2, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t3, h3, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t4, h4, h⟩ := Spec.specM_bind_ok h
  unfold resets
  -- The eth1 reset.
  unfold Spec.lhEth1DataReset at h1
  obtain ⟨due, hdue, h1⟩ := Spec.specM_bind_ok h1
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (eth1_data_votes_reset_due_equiv (G.slot st) G.eth1Period)
  rw [hL.slot, hL.eth1Period, hdue] at he
  obtain ⟨due', rfl, hd⟩ := absResult_ok he
  simp only [id] at hd
  subst hd
  rw [hr]
  simp only [bind_tc_ok]
  obtain ⟨st1, hst1, hv1⟩ : ∃ st1, (if due' then G.clearVotes st else st) = st1 ∧ view st1 = t1 := by
    refine ⟨_, rfl, ?_⟩
    cases due' with
    | true => simp only [if_true] at h1 ⊢; cases h1; rw [hL.clearVotes]
    | false => simp only [Bool.false_eq_true, if_false] at h1 ⊢; cases h1; rfl
  rw [hst1]
  -- The slashings reset.
  unfold Spec.lhSlashingsReset at h2
  obtain ⟨oi, hoi, h2⟩ := Spec.specM_bind_ok h2
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (slashings_reset_index_equiv (G.currentEpoch st1) G.slashingsLength)
  rw [hL.currentEpoch, hL.slashingsLength, hv1, hoi] at he
  obtain ⟨oi', rfl, hd⟩ := absResult_ok he
  rw [hr]
  simp only [bind_tc_ok]
  cases oi with
  | none => cases h2
  | some i =>
  obtain ⟨i', rfl⟩ : ∃ i', oi' = some i' := by
    cases oi' with
    | none => cases hd
    | some i' => exact ⟨i', rfl⟩
  simp only [Option.map, Option.some.injEq] at hd
  subst hd
  obtain ⟨l, hl, h2⟩ := Spec.specM_bind_ok h2
  rw [← hv1] at hl
  obtain ⟨st2, hw2, hv2⟩ := hL.resetSlashing st1 i' l hl
  simp only [hw2]
  have hv2' : view st2 = t2 := by rw [hv2, hv1]; cases h2; rfl
  -- The randao reset.
  unfold Spec.lhRandaoMixesReset at h3
  obtain ⟨op, hop, h3⟩ := Spec.specM_bind_ok h3
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (randao_mixes_reset_indices_equiv (G.currentEpoch st2) G.mixesLength)
  rw [hL.currentEpoch, hL.mixesLength, hv2', hop] at he
  obtain ⟨op', rfl, hd⟩ := absResult_ok he
  rw [hr]
  simp only [bind_tc_ok]
  cases op with
  | none => cases h3
  | some p =>
  obtain ⟨⟨src, tgt⟩, rfl⟩ : ∃ q, op' = some q := by
    cases op' with
    | none => cases hd
    | some q => exact ⟨q, rfl⟩
  simp only [Option.map, Option.some.injEq] at hd
  subst hd
  simp only at h3
  obtain ⟨mix, hmix, h3⟩ := Spec.specM_bind_ok h3
  obtain ⟨l, hl, h3⟩ := Spec.specM_bind_ok h3
  rw [← hv2'] at hmix hl
  obtain ⟨st3, hw3, hv3⟩ := hL.copyMix st2 src tgt mix l hmix hl
  simp only [hw3]
  have hv3' : view st3 = t3 := by rw [hv3, hv2']; cases h3; rfl
  -- The historical summaries update.
  unfold Spec.lhHistoricalSummariesUpdate at h4
  obtain ⟨ne, hne, h4⟩ := Spec.specM_bind_ok h4
  rw [← hv3'] at hne
  obtain ⟨ne', hne', hnev⟩ := hL.nextEpoch st3 ne hne
  rw [hne']
  simp only
  obtain ⟨due, hdue, h4⟩ := Spec.specM_bind_ok h4
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (historical_summary_due_equiv ne' G.slotsPerHistoricalRoot G.slotsPerEpoch)
  rw [hnev, hL.slotsPerHistoricalRoot, hL.slotsPerEpoch, hdue] at he
  obtain ⟨due', rfl, hd⟩ := absResult_ok he
  simp only [id] at hd
  subst hd
  rw [hr]
  simp only [bind_tc_ok]
  obtain ⟨st4, hst4, hv4⟩ : ∃ st4, (if due' then G.pushSummary st3 else some st3) = some st4 ∧
      view st4 = t4 := by
    cases due' with
    | true =>
      simp only [if_true] at h4 ⊢
      split at h4
      · rename_i hlt
        rw [← hv3'] at hlt
        obtain ⟨st4, hp, hv⟩ := hL.pushSummary st3 hlt
        refine ⟨st4, hp, ?_⟩
        rw [hv, hv3']
        cases h4
        rfl
      · cases h4
    | false =>
      simp only [Bool.false_eq_true, if_false] at h4 ⊢
      cases h4
      exact ⟨st3, rfl, hv3'⟩
  rw [hst4]
  simp only
  -- The participation rotation.
  refine ⟨G.rotate st4, rfl, ?_⟩
  rw [hL.rotate, hv4]
  cases h
  rfl

/-- The composed sync committee update returns the state of `process_sync_committee_updates`. -/
theorem syncUpdate_spec (G : TailGlue σ) (o : Spec.Oracle) (view : σ → Spec.BeaconState)
    (hL : TailLinks G o view) (st5 : σ) (hn1 : SyncN1 G st5) (T : Spec.BeaconState)
    (h : Spec.process_sync_committee_updates Spec.P o (view st5) = .ok T) :
    ∃ st', syncUpdate G st5 = ok (some st') ∧ view st' = T := by
  rw [Spec.process_sync_committee_updates_split] at h
  obtain ⟨b, hb, h⟩ := Spec.specM_bind_ok h
  unfold syncUpdate
  rw [hL.syncDue st5 b hb]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    cases h
    exact ⟨st5, rfl, rfl⟩
  | true =>
  simp only [if_true] at h
  obtain ⟨st6, hw6, hv6⟩ := hL.writeCurrentSync st5
  simp only [hw6]
  rw [← hv6] at h
  obtain ⟨idx, hidx, h⟩ := Spec.specM_bind_ok h
  obtain ⟨c, hc, h⟩ := Spec.specM_bind_ok h
  have hsync := next_sync_committee_indices_spec G.hash G.effectiveBalances st6 Spec.P o hL.hash
    (view st6) (hL.effectiveBalances st6) (G.syncIndices st6) G.syncDomain hL.syncDomain
    (G.syncEpoch st6) (hL.syncEpoch st6) (hL.syncIndices st6) (G.syncMix st6) (hL.syncMix st6)
    G.syncSize hL.syncSize (G.syncConstants st6) (hL.syncConstants st6) (hn1 st6 hw6)
    hL.usize64 idx hidx
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hsync
  rw [hr]
  simp only [bind_tc_ok]
  rw [← hv] at hc
  obtain ⟨st7, hw7, hv7⟩ := hL.writeNextSync st6 v c hc
  refine ⟨st7, by rw [hw7], ?_⟩
  rw [hv7, hv6]
  cases h
  rfl

/-- The composed tail returns the state of the model: when `lhTailOrder` returns `ok`, the Rust
returns `Ok` with that state. -/
theorem tail_spec [Spec.PresetCfg.Ok] (G : TailGlue σ) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) (hL : TailLinks G o view) (st : σ)
    (hn1 : ∀ st5, resets G st = ok (some st5) → SyncN1 G st5) (T : Spec.BeaconState)
    (h : Spec.lhTailOrder o (view st) = .ok T) :
    ∃ st', tail G st = ok (some st') ∧ view st' = T := by
  rw [Spec.lhTailOrder_eq] at h
  obtain ⟨t5, h5, h⟩ := Spec.specM_bind_ok h
  obtain ⟨st5, hr, hv5⟩ := resets_spec G o view hL st t5 h5
  obtain ⟨st', hs, hv'⟩ := syncUpdate_spec G o view hL st5 (hn1 st5 hr) T (by rw [hv5]; exact h)
  refine ⟨st', ?_, hv'⟩
  unfold tail
  rw [hr]
  simp only [bind_tc_ok]
  exact hs

end EpochProofs.Compose
