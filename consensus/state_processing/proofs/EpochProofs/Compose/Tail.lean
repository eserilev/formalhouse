import EpochProofs.AeneasCompat
import EpochProofs.Equiv.TailUpdates
import EpochProofs.Equiv.EpochCommittees
import EpochProofs.Sanity.Invariants.LighthouseOrder

/-!
# The epoch tail, composed from the translated functions

`tail` is the end of `altair.rs` `process_epoch`: the eth1, slashings and RANDAO resets
(`resets.rs`), the historical summaries update, the participation rotation and the sync
committee update. The checks and indices are the translated functions of `tail_updates.rs`, and
the next sync committee indices are the translated `next_sync_committee_indices`. The reads and
the writes are untranslated code (`UntranslatedEndOfEpoch`), each with the fact that links it to
the spec (`UntranslatedEndOfEpochFacts`). `translatedEndOfEpoch_matches_model` shows that `tail`
returns the state of the model `lighthouseStepsAfterPtcWindow`.
-/

namespace EpochProofs.Spec

/-- The steps of `lighthouseStepsAfterPayments` after the PTC window. -/
def lighthouseStepsAfterPtcWindow [CurrentPreset] (oracle : Oracle)
    (t : BeaconState) : SpecM BeaconState := do
  let t ← lighthouseEth1DataReset t
  let t ← lighthouseSlashingsReset t
  let t ← lighthouseRandaoMixesReset t
  let t ← lighthouseHistoricalSummariesUpdate oracle t
  let t := process_participation_flag_updates t
  process_sync_committee_updates P oracle t

/-- The steps of `lighthouseStepsAfterPtcWindow` before the sync committee update. -/
def lighthouseResets [CurrentPreset] (oracle : Oracle) (t : BeaconState) : SpecM BeaconState := do
  let t ← lighthouseEth1DataReset t
  let t ← lighthouseSlashingsReset t
  let t ← lighthouseRandaoMixesReset t
  let t ← lighthouseHistoricalSummariesUpdate oracle t
  pure (process_participation_flag_updates t)

theorem lighthouseStepsAfterPtcWindow_eq [CurrentPreset] (oracle : Oracle) (t : BeaconState) :
    lighthouseStepsAfterPtcWindow oracle t = lighthouseResets oracle t >>=
      process_sync_committee_updates P oracle := by
  simp only [lighthouseStepsAfterPtcWindow, lighthouseResets, bind_assoc, pure_bind]

theorem lighthouseStepsAfterPayments_eq [CurrentPreset] (oracle : Oracle) (t : BeaconState) :
    lighthouseStepsAfterPayments oracle t = (do
      let t ← process_proposer_lookahead P oracle t
      let t ← process_ptc_window P oracle t
      lighthouseStepsAfterPtcWindow oracle t) := rfl

/-- The sync committee of `indices`, as `sync_committee_from_indices` builds it. -/
def syncCommitteeOf (oracle : Oracle) (s : BeaconState) (indices : List ValidatorIndex) :
    SpecM SyncCommittee := do
  let pubkeys ← indices.mapM fun index => do pure (← listGet s.validators index).pubkey
  let aggregate_pubkey ← eth_aggregate_pubkeys oracle pubkeys
  pure { pubkeys, aggregate_pubkey }

/-- The check of `process_sync_committee_updates`. -/
def syncDue (p : Preset) (s : BeaconState) : SpecM Bool := do
  let next_epoch ← uint64Add (← get_current_epoch p s) 1
  pure ((← uint64Mod next_epoch p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD) == 0)

theorem process_sync_committee_updates_split (p : Preset) (oracle : Oracle) (s : BeaconState) :
    process_sync_committee_updates p oracle s = (do
      if ← syncDue p s then
        let s := { s with current_sync_committee := s.next_sync_committee }
        let indices ← get_next_sync_committee_indices p oracle s
        pure { s with next_sync_committee := ← syncCommitteeOf oracle s indices }
      else pure s) := by
  unfold process_sync_committee_updates syncDue get_next_sync_committee syncCommitteeOf
  simp only [bind_assoc, pure_bind]

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- A translated call that agrees with an `ok` spec result returns `Ok`. -/
theorem resultToSpec_ok {α β : Type} {f : α → β} {r : core.result.Result α safe_arith.ArithError}
    {x : β} (h : resultToSpec f r = .ok x) : ∃ v, r = .Ok v ∧ f v = x := by
  cases r with
  | Ok v => exact ⟨v, rfl, Except.ok.inj h⟩
  | Err e => cases h

/-- The untranslated Rust of the end of `altair.rs` `process_epoch`. -/
structure UntranslatedEndOfEpoch (RustState : Type) where
  /-- `process_eth1_data_reset`: the slot, `SlotsPerEth1VotingPeriod`, the votes reset. -/
  slot : RustState → U64
  eth1VotingPeriod : U64
  clearVotes : RustState → RustState
  /-- `process_slashings_reset` and `process_randao_mixes_reset`: the current epoch, the vector
  lengths, the writes. `none`: an index out of bounds. -/
  currentEpoch : RustState → U64
  slashingsLength : U64
  resetSlashing : RustState → U64 → Option RustState
  mixesLength : U64
  copyMix : RustState → U64 → U64 → Option RustState
  /-- `process_historical_summaries_update`: `state.next_epoch()?`, the constants, the push. -/
  nextEpoch : RustState → Option U64
  slotsPerHistoricalRoot : U64
  slotsPerEpoch : U64
  pushSummary : RustState → Option RustState
  /-- `rotate_participation_flags`. -/
  rotateParticipation : RustState → RustState
  /-- `process_sync_committee_updates`: the check, the write of the current committee, the reads
  for `next_sync_committee_indices`, and `sync_committee_from_indices` with its write. -/
  syncDue : RustState → Option Bool
  writeCurrentSync : RustState → Option RustState
  Hash : Type
  hash : ShuffleHashInst Hash
  effectiveBalances : EffectiveBalanceSource RustState
  syncIndices : RustState → Slice Usize
  syncDomain : Array U8 4#usize
  syncEpoch : RustState → U64
  syncMix : RustState → Array U8 32#usize
  syncSize : Usize
  syncConstants : RustState → LighthouseSelectionConstants
  writeNextSync : RustState → alloc.vec.Vec Usize → Option RustState

variable {RustState : Type}

/-- The resets, the historical summaries update and the participation rotation, as the calls of
the translated functions joined by the untranslated code. `none`: the Rust returns an error. -/
def translatedResets (code : UntranslatedEndOfEpoch RustState)
    (rustState : RustState) : Result (Option RustState) := do
  let r ← per_epoch_processing.tail_updates.eth1_data_votes_reset_due (code.slot rustState)
    code.eth1VotingPeriod
  match r with
  | .Err _ => ok none
  | .Ok due =>
  let rustState := if due then code.clearVotes rustState else rustState
  let r ← per_epoch_processing.tail_updates.slashings_reset_index (code.currentEpoch rustState)
    code.slashingsLength
  match r with
  | .Err _ => ok none
  | .Ok none => ok none
  | .Ok (some i) =>
  match code.resetSlashing rustState i with
  | none => ok none
  | some rustState =>
  let r ← per_epoch_processing.tail_updates.randao_mixes_reset_indices (code.currentEpoch rustState)
    code.mixesLength
  match r with
  | .Err _ => ok none
  | .Ok none => ok none
  | .Ok (some (source, target)) =>
  match code.copyMix rustState source target with
  | none => ok none
  | some rustState =>
  match code.nextEpoch rustState with
  | none => ok none
  | some next =>
  let r ← per_epoch_processing.tail_updates.historical_summary_due next code.slotsPerHistoricalRoot
    code.slotsPerEpoch
  match r with
  | .Err _ => ok none
  | .Ok due =>
  match (if due then code.pushSummary rustState else some rustState) with
  | none => ok none
  | some rustState => ok (some (code.rotateParticipation rustState))

/-- `process_sync_committee_updates`, as the call of the translated
`next_sync_committee_indices` joined by the untranslated code. -/
def translatedSyncCommitteeUpdate (code : UntranslatedEndOfEpoch RustState)
    (rustState : RustState) : Result (Option RustState) := do
  match code.syncDue rustState with
  | none => ok none
  | some false => ok (some rustState)
  | some true =>
  match code.writeCurrentSync rustState with
  | none => ok none
  | some rustState =>
  let r ← per_epoch_processing.epoch_committees.next_sync_committee_indices code.hash
    code.effectiveBalances rustState (code.syncIndices rustState) code.syncDomain
      (code.syncEpoch rustState) (code.syncMix rustState)
    code.syncSize (code.syncConstants rustState)
  match r with
  | .Err _ => ok none
  | .Ok indices => ok (code.writeNextSync rustState indices)

/-- The end of `process_epoch`. `none`: the Rust returns an error. -/
def translatedEndOfEpoch (code : UntranslatedEndOfEpoch RustState)
    (rustState : RustState) : Result (Option RustState) := do
  let r ← translatedResets code rustState
  match r with
  | none => ok none
  | some rustState5 => translatedSyncCommitteeUpdate code rustState5

/-- At the sync committee update, at most `2^24` active validators of the next epoch enter the
shuffle. -/
def SyncN1 (code : UntranslatedEndOfEpoch RustState) (rustState : RustState) : Prop :=
  ∀ rustState', code.writeCurrentSync rustState = some rustState' →
    (code.syncIndices rustState').val.length ≤ 2 ^ 24

variable [Spec.CurrentPreset]

/-- The trusted facts about the untranslated code. Each read reads the state it is given and
each write writes the spec value, so each fact holds for every state `t`. -/
structure UntranslatedEndOfEpochFacts (code : UntranslatedEndOfEpoch RustState)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState) : Prop where
  /-- The slot, the epoch and the vector lengths are the spec values. -/
  slot : ∀ t, (code.slot t).val = (rustStateToSpec t).slot
  eth1VotingPeriod : code.eth1VotingPeriod.val = Spec.LIGHTHOUSE_SLOTS_PER_ETH1_VOTING_PERIOD
  /-- The eth1 votes reset. -/
  clearVotes : ∀ t, rustStateToSpec (code.clearVotes t) =
    { rustStateToSpec t with eth1_data_votes := [] }
  currentEpoch : ∀ t, (code.currentEpoch t).val = (rustStateToSpec t).slot / Spec.P.SLOTS_PER_EPOCH
  slashingsLength : code.slashingsLength.val = Spec.P.EPOCHS_PER_SLASHINGS_VECTOR
  /-- The slashings reset writes one entry. -/
  resetSlashing : ∀ t i l, Spec.listSet (rustStateToSpec t).slashings i.val 0 = .ok l →
    ∃ t', code.resetSlashing t i = some t' ∧ rustStateToSpec t' =
      { rustStateToSpec t with slashings := l }
  mixesLength : code.mixesLength.val = Spec.P.EPOCHS_PER_HISTORICAL_VECTOR
  /-- The RANDAO reset copies one mix. -/
  copyMix : ∀ t source target mix l, Spec.listGet (rustStateToSpec t).randao_mixes source.val =
    .ok mix →
    Spec.listSet (rustStateToSpec t).randao_mixes target.val mix = .ok l →
    ∃ t', code.copyMix t source target = some t' ∧ rustStateToSpec t' =
      { rustStateToSpec t with randao_mixes := l }
  /-- `state.next_epoch()` is the spec next epoch. -/
  nextEpoch : ∀ t n, Spec.uint64Add ((rustStateToSpec t).slot / Spec.P.SLOTS_PER_EPOCH) 1 = .ok n →
    ∃ v, code.nextEpoch t = some v ∧ v.val = n
  slotsPerHistoricalRoot : code.slotsPerHistoricalRoot.val = Spec.P.SLOTS_PER_HISTORICAL_ROOT
  slotsPerEpoch : code.slotsPerEpoch.val = Spec.P.SLOTS_PER_EPOCH
  /-- The push succeeds below the Lighthouse limit, and `HistoricalSummary::new` hashes the
  roots as `hash_tree_root` does. -/
  pushSummary : ∀ t, (rustStateToSpec t).historical_summaries.length <
    Spec.LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT →
    ∃ t', code.pushSummary t = some t' ∧ rustStateToSpec t' = { rustStateToSpec t with
      historical_summaries := (rustStateToSpec t).historical_summaries ++
        [{ block_summary_root := oracle.hash_tree_root_BlockRoots (rustStateToSpec t).block_roots
           state_summary_root := oracle.hash_tree_root_StateRoots (rustStateToSpec t).state_roots }]
             }
  /-- The participation rotation is the spec step. -/
  rotateParticipation : ∀ t, rustStateToSpec (code.rotateParticipation t) =
    Spec.process_participation_flag_updates (rustStateToSpec t)
  /-- The check of the sync committee period. -/
  syncDue : ∀ t b, Spec.syncDue Spec.P (rustStateToSpec t) = .ok b → code.syncDue t = some b
  /-- The next sync committee becomes the current one. -/
  writeCurrentSync : ∀ t, ∃ t', code.writeCurrentSync t = some t' ∧
    rustStateToSpec t' = { rustStateToSpec t with current_sync_committee :=
      (rustStateToSpec t).next_sync_committee }
  hash : HashMatches code.hash oracle
  effectiveBalances : ∀ t, EffectiveBalancesMatch code.effectiveBalances t
    ((rustStateToSpec t).validators.map (·.effective_balance))
  /-- The candidates are the active validators of the next epoch. -/
  syncIndices : ∀ t, (code.syncIndices t).val.map (·.val) =
    Spec.get_active_validator_indices (rustStateToSpec t) (code.syncEpoch t).val
  syncDomain : byteValues code.syncDomain.val = Spec.DOMAIN_SYNC_COMMITTEE.toList
  syncEpoch : ∀ t current, Spec.get_current_epoch Spec.P (rustStateToSpec t) = .ok current →
    (code.syncEpoch t).val = current + 1
  syncMix : ∀ t, SeedMixMatches Spec.P (rustStateToSpec t) (code.syncEpoch t).val (code.syncMix t)
  syncSize : code.syncSize.val = Spec.P.SYNC_COMMITTEE_SIZE
  syncConstants : ∀ t, SelectionConstantsMatch Spec.P (code.syncConstants t)
  /-- `sync_committee_from_indices` collects the pubkeys and aggregates them with BLS. -/
  writeNextSync : ∀ t v c, Spec.syncCommitteeOf oracle (rustStateToSpec t) (v.val.map (·.val)) =
    .ok c →
    ∃ t', code.writeNextSync t v = some t' ∧ rustStateToSpec t' =
      { rustStateToSpec t with next_sync_committee := c }
  usize64 : Usize.max = U64.max

/-- The composed resets return the state of the model `lighthouseResets`. -/
theorem translatedResets_matches_model [Spec.CurrentPreset.Valid]
    (code : UntranslatedEndOfEpoch RustState) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedEndOfEpochFacts code oracle rustStateToSpec) (rustState : RustState)
    (t5 : Spec.BeaconState)
    (h : Spec.lighthouseResets oracle (rustStateToSpec rustState) = .ok t5) :
    ∃ rustState5, translatedResets code rustState = ok (some rustState5) ∧
      rustStateToSpec rustState5 = t5 := by
  unfold Spec.lighthouseResets at h
  obtain ⟨t1, h1, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t2, h2, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t3, h3, h⟩ := Spec.specM_bind_ok h
  obtain ⟨t4, h4, h⟩ := Spec.specM_bind_ok h
  unfold translatedResets
  -- The eth1 reset.
  unfold Spec.lighthouseEth1DataReset at h1
  obtain ⟨due, hdue, h1⟩ := Spec.specM_bind_ok h1
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (eth1_data_votes_reset_due_equiv (code.slot rustState) code.eth1VotingPeriod)
  rw [hL.slot, hL.eth1VotingPeriod, hdue] at he
  obtain ⟨due', rfl, hd⟩ := resultToSpec_ok he
  simp only [id] at hd
  subst hd
  rw [hr]
  simp only [bind_tc_ok]
  obtain ⟨rustState1, hst1, hv1⟩ : ∃ rustState1,
    (if due' then code.clearVotes rustState else rustState) = rustState1 ∧
    rustStateToSpec rustState1 = t1 := by
    refine ⟨_, rfl, ?_⟩
    cases due' with
    | true => simp only [if_true] at h1 ⊢; cases h1; rw [hL.clearVotes]
    | false => simp only [Bool.false_eq_true, if_false] at h1 ⊢; cases h1; rfl
  rw [hst1]
  -- The slashings reset.
  unfold Spec.lighthouseSlashingsReset at h2
  obtain ⟨oi, hoi, h2⟩ := Spec.specM_bind_ok h2
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (slashings_reset_index_equiv (code.currentEpoch rustState1) code.slashingsLength)
  rw [hL.currentEpoch, hL.slashingsLength, hv1, hoi] at he
  obtain ⟨oi', rfl, hd⟩ := resultToSpec_ok he
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
  obtain ⟨rustState2, hw2, hv2⟩ := hL.resetSlashing rustState1 i' l hl
  simp only [hw2]
  have hv2' : rustStateToSpec rustState2 = t2 := by rw [hv2, hv1]; cases h2; rfl
  -- The randao reset.
  unfold Spec.lighthouseRandaoMixesReset at h3
  obtain ⟨op, hop, h3⟩ := Spec.specM_bind_ok h3
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (randao_mixes_reset_indices_equiv (code.currentEpoch rustState2) code.mixesLength)
  rw [hL.currentEpoch, hL.mixesLength, hv2', hop] at he
  obtain ⟨op', rfl, hd⟩ := resultToSpec_ok he
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
  obtain ⟨rustState3, hw3, hv3⟩ := hL.copyMix rustState2 src tgt mix l hmix hl
  simp only [hw3]
  have hv3' : rustStateToSpec rustState3 = t3 := by rw [hv3, hv2']; cases h3; rfl
  -- The historical summaries update.
  unfold Spec.lighthouseHistoricalSummariesUpdate at h4
  obtain ⟨ne, hne, h4⟩ := Spec.specM_bind_ok h4
  rw [← hv3'] at hne
  obtain ⟨ne', hne', hnev⟩ := hL.nextEpoch rustState3 ne hne
  rw [hne']
  simp only
  obtain ⟨due, hdue, h4⟩ := Spec.specM_bind_ok h4
  obtain ⟨r, hr, he⟩ := spec_imp_exists
    (historical_summary_due_equiv ne' code.slotsPerHistoricalRoot code.slotsPerEpoch)
  rw [hnev, hL.slotsPerHistoricalRoot, hL.slotsPerEpoch, hdue] at he
  obtain ⟨due', rfl, hd⟩ := resultToSpec_ok he
  simp only [id] at hd
  subst hd
  rw [hr]
  simp only [bind_tc_ok]
  obtain ⟨rustState4, hst4, hv4⟩ : ∃ rustState4,
    (if due' then code.pushSummary rustState3 else some rustState3) = some rustState4 ∧
      rustStateToSpec rustState4 = t4 := by
    cases due' with
    | true =>
      simp only [if_true] at h4 ⊢
      split at h4
      · rename_i hlt
        rw [← hv3'] at hlt
        obtain ⟨rustState4, hp, hv⟩ := hL.pushSummary rustState3 hlt
        refine ⟨rustState4, hp, ?_⟩
        rw [hv, hv3']
        cases h4
        rfl
      · cases h4
    | false =>
      simp only [Bool.false_eq_true, if_false] at h4 ⊢
      cases h4
      exact ⟨rustState3, rfl, hv3'⟩
  rw [hst4]
  simp only
  -- The participation rotation.
  refine ⟨code.rotateParticipation rustState4, rfl, ?_⟩
  rw [hL.rotateParticipation, hv4]
  cases h
  rfl

/-- The composed sync committee update returns the state of `process_sync_committee_updates`. -/
theorem translatedSyncCommitteeUpdate_matches_model (code : UntranslatedEndOfEpoch RustState)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedEndOfEpochFacts code oracle rustStateToSpec) (rustState5 : RustState)
    (hn1 : SyncN1 code rustState5) (T : Spec.BeaconState)
    (h : Spec.process_sync_committee_updates Spec.P oracle (rustStateToSpec rustState5) = .ok T) :
    ∃ rustState', translatedSyncCommitteeUpdate code rustState5 = ok (some rustState') ∧
      rustStateToSpec rustState' = T := by
  rw [Spec.process_sync_committee_updates_split] at h
  obtain ⟨b, hb, h⟩ := Spec.specM_bind_ok h
  unfold translatedSyncCommitteeUpdate
  rw [hL.syncDue rustState5 b hb]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    cases h
    exact ⟨rustState5, rfl, rfl⟩
  | true =>
  simp only [if_true] at h
  obtain ⟨rustState6, hw6, hv6⟩ := hL.writeCurrentSync rustState5
  simp only [hw6]
  rw [← hv6] at h
  obtain ⟨idx, hidx, h⟩ := Spec.specM_bind_ok h
  obtain ⟨c, hc, h⟩ := Spec.specM_bind_ok h
  have hsync := next_sync_committee_indices_spec code.hash code.effectiveBalances rustState6 Spec.P
    oracle hL.hash
    (rustStateToSpec rustState6) (hL.effectiveBalances rustState6) (code.syncIndices rustState6)
      code.syncDomain hL.syncDomain
    (code.syncEpoch rustState6) (hL.syncEpoch rustState6) (hL.syncIndices rustState6)
      (code.syncMix rustState6) (hL.syncMix rustState6)
    code.syncSize hL.syncSize (code.syncConstants rustState6) (hL.syncConstants rustState6)
      (hn1 rustState6 hw6)
    hL.usize64 idx hidx
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hsync
  rw [hr]
  simp only [bind_tc_ok]
  rw [← hv] at hc
  obtain ⟨rustState7, hw7, hv7⟩ := hL.writeNextSync rustState6 v c hc
  refine ⟨rustState7, by rw [hw7], ?_⟩
  rw [hv7, hv6]
  cases h
  rfl

/-- The composed tail returns the state of the model: when `lighthouseStepsAfterPtcWindow` returns
`ok`, the Rust returns `Ok` with that state. -/
theorem translatedEndOfEpoch_matches_model [Spec.CurrentPreset.Valid]
    (code : UntranslatedEndOfEpoch RustState) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedEndOfEpochFacts code oracle rustStateToSpec) (rustState : RustState)
    (hn1 : ∀ rustState5, translatedResets code rustState = ok (some rustState5) →
    SyncN1 code rustState5) (T : Spec.BeaconState)
    (h : Spec.lighthouseStepsAfterPtcWindow oracle (rustStateToSpec rustState) = .ok T) :
    ∃ rustState', translatedEndOfEpoch code rustState = ok (some rustState') ∧
      rustStateToSpec rustState' = T := by
  rw [Spec.lighthouseStepsAfterPtcWindow_eq] at h
  obtain ⟨t5, h5, h⟩ := Spec.specM_bind_ok h
  obtain ⟨rustState5, hr, hv5⟩ :=
    translatedResets_matches_model code oracle rustStateToSpec hL rustState t5 h5
  obtain ⟨rustState', hs, hv'⟩ :=
    translatedSyncCommitteeUpdate_matches_model code oracle rustStateToSpec hL rustState5
    (hn1 rustState5 hr) T (by rw [hv5]; exact h)
  refine ⟨rustState', ?_, hv'⟩
  unfold translatedEndOfEpoch
  rw [hr]
  simp only [bind_tc_ok]
  exact hs

end EpochProofs.Compose
