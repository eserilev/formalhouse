import EpochProofs.Etheorem.Shuffle

/-!
# Sync committee, proposer lookahead and PTC window updates equal Etheorem's

`process_sync_committee_updates`, `process_proposer_lookahead` and `process_ptc_window` each
take a balance weighted selection. Etheorem stops a selection after `10^7` passes (F3). pyspec
loops until it has `size` items. So each theorem assumes that Etheorem's selections are full:
`SyncSelectionFull`, `ProposerSelectionsFull` and `PtcSelectionsFull`.

`hsha` says that `sha` returns 32 bytes. `sha_size_pure` proves it for the pure SHA-256.

The reference raises in two cases where Etheorem does not. `compute_balance_weighted_selection`
asserts `total > 0`, and `eth_aggregate_pubkeys` asserts `KeyValidate`. Each theorem assumes that
the reference succeeds, so these cases do not occur.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

/-- The pure SHA-256 returns 32 bytes. -/
theorem sha_size_pure (b : ByteArray) : (@sha pureHasherTag b).size = 32 :=
  LeanSha256.hash_size_eq_32 b

theorem filterAuxM_ok {ε α : Type} (f : α → Except ε Bool) (g : α → Bool) :
    ∀ (l acc : List α) {r : List α}, (∀ a ∈ l, ∀ b, f a = .ok b → b = g a) →
      List.filterAuxM f l acc = .ok r → r = (l.filter g).reverse ++ acc := by
  intro l
  induction l with
  | nil =>
    intro acc r _ h
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at h
    simp [h]
  | cons a l ih =>
    intro acc r hf h
    simp only [List.filterAuxM, except_bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    rw [hf a (by simp) b hb] at h
    rw [ih _ (fun a ha b hb => hf a (by simp [ha]) b hb) h]
    cases hg : g a <;> simp [hg]

theorem filterM_ok {ε α : Type} (f : α → Except ε Bool) (g : α → Bool) (l : List α) {r : List α}
    (hf : ∀ a ∈ l, ∀ b, f a = .ok b → b = g a) (h : l.filterM f = .ok r) : r = l.filter g := by
  simp only [List.filterM, except_bind_eq_ok, except_pure_eq_ok] at h
  obtain ⟨acc, hacc, rfl⟩ := h
  rw [filterAuxM_ok f g l [] hf hacc]
  simp


variable [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config]

/-! ## Proposers -/

/-- The candidates of `get_beacon_proposer_indices` in Etheorem: active and not slashed. -/
def proposerCandidates (e : EState) (epoch : UInt64) : Array UInt64 :=
  (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).filter
    (fun vi => !(e.validators[vi.toNat]!).slashed)

/-- The seed of slot `i` of `epoch` in `compute_proposer_indices`, as Etheorem computes it. -/
def proposerSlotSeed (e : EState) (epoch : UInt64) (i : Nat) : ByteArray :=
  sha (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) epoch
      EthCLSpecs.Gloas.Const.domainBeaconProposer) ++
    uint64ToBytes (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i))

/-- Each proposer selection of `epoch` in Etheorem returns one proposer. -/
def ProposerSelectionsFull (e : EState) (epoch : UInt64) : Prop :=
  ∀ i < EthCLSpecs.Gloas.Const.slotsPerEpoch,
    1 ≤ (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) (proposerCandidates e epoch)
      (proposerSlotSeed e epoch i) 1 true).size

section Proposers

variable {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem get_beacon_proposer_indices_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (epoch : UInt64)
    (hfull : ProposerSelectionsFull e epoch) {r : List Nat}
    (h : Spec.get_beacon_proposer_indices p o (absEState e) epoch.toNat = .ok r) :
    r = (EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e) epoch).toList.map
      UInt64.toNat := by
  unfold Spec.get_beacon_proposer_indices at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨cands, hcands, seed, hseed, h⟩ := h
  rw [get_active_validator_indices_eq hp] at hcands
  have hcands' := filterM_ok _ (fun idx => !(e.validators.val[idx]!).slashed) _ ?hf hcands
  case hf =>
    intro v _ b hb
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨val, hval, rfl⟩ := hb
    simp only [absEState_validators] at hval
    obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator v hval
    rfl
  have hc2 : cands = (proposerCandidates e epoch).toList.map UInt64.toNat := by
    rw [hcands', List.filter_map]
    simp [proposerCandidates, sszList_getElem!_val, Function.comp_def]
  subst hc2
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Gloas.Const.domainBeaconProposer rfl hseed
  subst hseed'
  unfold Spec.compute_proposer_indices at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨start, hstart, seeds, hseeds, h⟩ := h
  have hstart' := compute_start_slot_at_epoch_ok hp epoch hstart
  subst hstart'
  have hslt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  have hseeds' := mapM_ok_map _ (fun i => bytesToRoot (proposerSlotSeed e epoch i)) _ ?hf2 hseeds
  case hf2 =>
    intro i hi b hb
    simp only [List.mem_range] at hi
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hi64 : i < 2 ^ 64 := by rw [← hp.slotsPerEpoch] at hi; omega
    have hx' : x = (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat := by
      rw [← UInt64.toNat_ofNat_of_lt' (n := i) hi64] at hx
      exact (uint64Add_ok hx).symm
    subst hx'
    have hba : toBA ((EthCLSpecs.Gloas.getSeed (pureState e) epoch
        EthCLSpecs.Gloas.Const.domainBeaconProposer).toList ++ Spec.uint_to_bytes 8
          (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat) =
        vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) epoch
          EthCLSpecs.Gloas.Const.domainBeaconProposer) ++
        uint64ToBytes (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i) := by
      apply ba_eq_of_toList
      rw [toBA_data, append_data_toList, vecToBytes_toList, uint_to_bytes_8]
    rw [hash_eq o ho, hba]
    unfold proposerSlotSeed
    rfl
  subst hseeds'
  have hr := mapM_ok_map _ (fun sd => ((EthCLSpecs.Gloas.computeBalanceWeightedSelection
      (pureState e) (proposerCandidates e epoch) (vecToBytes sd) 1 true)[0]!).toNat) _ ?hf3 h
  case hf3 =>
    intro sd hsd v hv
    simp only [List.mem_map, List.mem_range] at hsd
    obtain ⟨i, hi, rfl⟩ := hsd
    simp only [except_bind_eq_ok] at hv
    obtain ⟨sel, hsel, hv⟩ := hv
    have hfi := hfull i (by rw [hp.slotsPerEpoch]; exact hi)
    rw [← vecToBytes_bytesToRoot (proposerSlotSeed e epoch i) (hsha _)] at hfi
    rw [compute_balance_weighted_selection_ok p o ho hc e _ _ 1 true hfi hsel] at hv
    obtain ⟨-, rfl⟩ := listGet_ok hv
    rw [map_toNat_getElem!_all]
  subst hr
  unfold EthCLSpecs.Gloas.getBeaconProposerIndices EthCLSpecs.Gloas.computeProposerIndices
  simp only [List.map_map, Array.toList_map, Array.toList_range, view_uncachedBox, hp.slotsPerEpoch]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, vecToBytes_bytesToRoot _ (hsha _), proposerSlotSeed,
    proposerCandidates, sszList_getElem!_val]
  rfl


/-- The new proposer lookahead in Etheorem. -/
def newLookahead (e : EState) : Vector UInt64 (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  Vector.ofFn fun i =>
    if i.val < EthCLSpecs.Gloas.Const.slotsPerEpoch then
      vget e.proposerLookahead (i.val + EthCLSpecs.Gloas.Const.slotsPerEpoch)
    else (EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead + 1))[
        i.val - EthCLSpecs.Gloas.Const.slotsPerEpoch]!

omit [EthCLSpecs.Gloas.Config] hp hc in
theorem processProposerLookahead_run (e : EState) :
    (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState { e with proposerLookahead := newLookahead e }) := rfl

/-- `process_proposer_lookahead` equals Etheorem's when Etheorem's proposer selections are
full. -/
theorem process_proposer_lookahead_etheorem (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hsha : ∀ b : ByteArray, (sha b).size = 32)
    (e : EState)
    (hfull : ProposerSelectionsFull e (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
      EthCLSpecs.Gloas.Const.minSeedLookahead + 1))
    {s' : Spec.BeaconState} (h : Spec.process_proposer_lookahead p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  refine ⟨_, processProposerLookahead_run e, ?_⟩
  unfold Spec.process_proposer_lookahead at h
  have hge : ∀ l, Spec.get_current_epoch p { absEState e with proposer_lookahead := l } =
      Spec.get_current_epoch p (absEState e) := fun _ => rfl
  have hgb : ∀ l ep, Spec.get_beacon_proposer_indices p o
      { absEState e with proposer_lookahead := l } ep =
      Spec.get_beacon_proposer_indices p o (absEState e) ep := fun _ _ => rfl
  simp only [hge, hgb, except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨les, hles, ep1, hep1, ep2, hep2, P, hP, props, hprops, hfin⟩ := h
  rw [except_pure_eq_ok] at hfin
  subst hfin
  rw [Except.ok.injEq] at hep1
  subst hep1
  rw [← hp.minSeedLookahead] at hep2
  have hep2' := uint64Add_ok hep2
  subst hep2'
  have hP' := uint64Add_ok (b := 1) hP
  subst hP'
  have hprops' := get_beacon_proposer_indices_ok hp hc o ho hsha e _ hfull hprops
  subst hprops'
  obtain ⟨hles', -⟩ := uint64Sub_eq hles
  subst hles'
  rw [absEState_set_proposerLookahead]
  have hsize : (EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead +
        1)).size = EthCLSpecs.Gloas.Const.slotsPerEpoch := by
    simp [EthCLSpecs.Gloas.getBeaconProposerIndices, EthCLSpecs.Gloas.computeProposerIndices]
  have hlist : (newLookahead e).toList.map UInt64.toNat =
      List.take ((absEState e).proposer_lookahead.length - p.SLOTS_PER_EPOCH)
        (List.drop p.SLOTS_PER_EPOCH (absEState e).proposer_lookahead ++
          List.drop ((absEState e).proposer_lookahead.length - p.SLOTS_PER_EPOCH)
            (absEState e).proposer_lookahead) ++
      List.map UInt64.toNat (EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
        (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead +
          1)).toList := by
    simp only [absEState_proposer_lookahead, List.length_map, Vector.length_toList,
      ← hp.slotsPerEpoch]
    have h2 : 2 * EthCLSpecs.Gloas.Const.slotsPerEpoch - EthCLSpecs.Gloas.Const.slotsPerEpoch =
        EthCLSpecs.Gloas.Const.slotsPerEpoch := by omega
    rw [h2, List.take_append_of_le_length (by simp; omega)]
    rw [List.take_of_length_le (by simp; omega)]
    apply List.ext_getElem
    · simp [newLookahead, hsize]; omega
    · intro i h1 h2'
      simp only [newLookahead, List.getElem_map, Vector.getElem_toList, Vector.getElem_ofFn]
      split
      · rename_i hi
        rw [List.getElem_append_left (by simp; omega)]
        simp [vget, getElem!_pos e.proposerLookahead.toArray (i + EthCLSpecs.Gloas.Const.slotsPerEpoch)
          (by simp; omega), Nat.add_comm]
      · rename_i hi
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_drop, List.length_map, Vector.length_toList, List.getElem_map,
          Array.getElem_toList]
        have hk : i - (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch -
            EthCLSpecs.Gloas.Const.slotsPerEpoch) = i - EthCLSpecs.Gloas.Const.slotsPerEpoch := by
          omega
        simp only [hk]
        rw [getElem!_pos _ _ (by simp at h1; omega)]
  rw [hlist]
end Proposers

/-! ## Selection size -/

omit [EthCLSpecs.Gloas.Config] in
/-- Etheorem's selection never holds more than `size` items. -/
theorem cbwsAux_size_le (indices effBals : Array Nat) (perm : Array UInt64) (seed : ByteArray)
    (total size : Nat) (shuffle : Bool) :
    ∀ (fuel i : Nat) (rb : ByteArray) (sel : Array UInt64), sel.size ≤ size →
      (EthCLSpecs.Gloas.cbwsAux indices effBals perm seed total size shuffle fuel i rb sel).size
        ≤ size := by
  intro fuel
  induction fuel with
  | zero => intro i rb sel h; simpa [EthCLSpecs.Gloas.cbwsAux] using h
  | succ f ih =>
    intro i rb sel h
    unfold EthCLSpecs.Gloas.cbwsAux
    split
    · exact h
    · rename_i hlt
      apply ih
      have hite : ∀ (c : Prop) [Decidable c] (x : UInt64),
          (if c then sel.push x else sel).size ≤ sel.size + 1 := by
        intro c _ x; split <;> simp
      exact Nat.le_trans (hite _ _) (by omega)

omit [EthCLSpecs.Gloas.Config] in
theorem computeBalanceWeightedSelection_size_le (e : EState) (indices : Array UInt64)
    (seed : ByteArray) (size : Nat) (shuffle : Bool) :
    (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) indices seed size shuffle).size
      ≤ size :=
  cbwsAux_size_le _ _ _ _ _ _ _ _ _ _ _ (by simp)

/-! ## Sync committee -/

/-- The selection of the next sync committee in Etheorem returns `SYNC_COMMITTEE_SIZE` items. -/
def SyncSelectionFull (e : EState) : Prop :=
  EthCLSpecs.Gloas.Const.syncCommitteeSize ≤
    (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e)
        (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1))
      (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e)
        (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1)
        EthCLSpecs.Gloas.Const.domainSyncCommittee))
      EthCLSpecs.Gloas.Const.syncCommitteeSize true).size

section Sync

variable [CryptoBackend] {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem get_next_sync_committee_ok (o : Spec.Oracle) (hoa : OracleAgrees o) (e : EState)
    (hfull : SyncSelectionFull e) {c : Spec.SyncCommittee}
    (h : Spec.get_next_sync_committee p o (absEState e) = .ok c) :
    c = absSyncCommittee (EthCLSpecs.Gloas.getNextSyncCommittee (pureState e)) := by
  unfold Spec.get_next_sync_committee Spec.get_next_sync_committee_indices at h
  simp only [except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨sel, ⟨ep, hep, ep1, hep1, seed, hseed, hsel⟩, pks, hpks, agg, hagg, hc'⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hep1' := uint64Add_ok (b := 1) hep1
  subst hep1'
  have hseed' := get_seed_ok hp o hoa.hash e _ _ EthCLSpecs.Gloas.Const.domainSyncCommittee rfl
    hseed
  subst hseed'
  rw [get_active_validator_indices_eq hp, ← hc.syncCommitteeSize] at hsel
  have hsel' := compute_balance_weighted_selection_ok p o hoa.hash hc e _ _ _ true hfull hsel
  subst hsel'
  have hpks' := mapM_ok_map _ (fun idx => ((e.validators[idx]?).getD default).pubkey) _ ?hf hpks
  case hf =>
    intro idx _ b hb
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨val, hval, rfl⟩ := hb
    simp only [absEState_validators] at hval
    obtain ⟨hlt, rfl⟩ := listGet_map_ok e.validators.val absValidator idx hval
    rw [getElem?_pos e.validators idx hlt, getElem!_pos e.validators.val idx hlt]
    rfl
  subst hpks'
  unfold Spec.eth_aggregate_pubkeys at hagg
  simp only [] at hagg
  split at hagg
  · exact absurd hagg throw_bind_ne_ok
  simp only [pure_bind] at hagg
  split at hagg
  · exact absurd hagg throw_bind_ne_ok
  simp only [except_pure_eq_ok] at hagg
  subst hagg
  rw [except_pure_eq_ok] at hc'
  subst hc'
  have hsz := Nat.le_antisymm (computeBalanceWeightedSelection_size_le e _ _ _ true) hfull
  have hpk : (List.map (fun idx => ((e.validators[idx]?).getD default).pubkey)
      (List.map UInt64.toNat (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
        (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e)
          (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1))
        (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e)
          (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1)
          EthCLSpecs.Gloas.Const.domainSyncCommittee))
        EthCLSpecs.Gloas.Const.syncCommitteeSize true).toList)) =
      (EthCLSpecs.Gloas.getNextSyncCommittee (pureState e)).pubkeys.toList := by
    unfold EthCLSpecs.Gloas.getNextSyncCommittee
    simp only [view_uncachedBox, vecToBytes] at hsz ⊢
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toList,
        Vector.getElem_ofFn]
      rw [getElem!_pos _ i (by simpa using h1)]
  unfold absSyncCommittee
  rw [hoa.aggregate, hpk]
  rfl


omit [EthCLSpecs.Gloas.Config] hp hc in
theorem processSyncCommitteeUpdates_run (e : EState) :
    (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run
        (pureState e) =
      .ok ((), pureState (if (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
          UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0 then
        { e with currentSyncCommittee := e.nextSyncCommittee,
                 nextSyncCommittee := EthCLSpecs.Gloas.getNextSyncCommittee (pureState e) }
        else e)) := by
  unfold EthCLSpecs.Gloas.processSyncCommitteeUpdates
  have hget : ∀ s : EthCLSpecs.Gloas.State,
      (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  cases hz : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0)
  · simp only [Bool.false_eq_true, if_false]
    rfl
  · simp only [if_true]
    rfl

/-- `process_sync_committee_updates` equals Etheorem's when Etheorem's sync committee selection
is full. -/
theorem process_sync_committee_updates_etheorem (o : Spec.Oracle) (hoa : OracleAgrees o)
    (hperiod : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64) (e : EState)
    (hfull : SyncSelectionFull e) {s' : Spec.BeaconState}
    (h : Spec.process_sync_committee_updates p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  refine ⟨_, processSyncCommitteeUpdates_run e, ?_⟩
  unfold Spec.process_sync_committee_updates at h
  simp only [except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨ep, hep, ep1, hep1, m, hm, h⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hep1' := uint64Add_ok (b := 1) hep1
  subst hep1'
  obtain ⟨hm', -⟩ := uint64Mod_eq hm
  subst hm'
  have hcond : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0) =
      ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1).toNat %
        p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD == 0) := by
    rw [hc.epochsPerSyncCommitteePeriod]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hperiod]
    simp
  rw [hcond]
  split at h
  · rename_i hz
    rw [if_pos hz]
    have hgn : Spec.get_next_sync_committee p o { absEState e with
        current_sync_committee := (absEState e).next_sync_committee } =
        Spec.get_next_sync_committee p o (absEState e) := rfl
    simp only [hgn, except_bind_eq_ok, except_pure_eq_ok] at h
    obtain ⟨c, hcn, rfl⟩ := h
    rw [get_next_sync_committee_ok hp hc o hoa e hfull hcn, absEState_set_syncCommittees]
    rfl
  · rename_i hz
    rw [if_neg hz]
    rw [except_pure_eq_ok] at h
    exact h
end Sync

/-! ## PTC window -/

/-- The PTC candidates of `slot` in Etheorem: the beacon committees of the slot, in order. -/
def ptcCandidates (e : EState) (slot : UInt64) : Array UInt64 :=
  (Array.range (EthCLSpecs.Gloas.getCommitteeCountPerSlot (pureState e)
      (EthCLSpecs.Gloas.computeEpochAtSlot slot))).foldl
    (fun acc i => acc ++ EthCLSpecs.Gloas.getBeaconCommittee (pureState e) slot i) #[]

/-- The PTC seed of `slot` in Etheorem. -/
def ptcSeed (e : EState) (slot : UInt64) : ByteArray :=
  sha (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) (EthCLSpecs.Gloas.computeEpochAtSlot slot)
    EthCLSpecs.Gloas.Const.domainPtcAttester) ++ uint64ToBytes slot)

/-- The PTC selection of `slot` in Etheorem returns `PTC_SIZE` items. -/
def PtcSelectionFull (e : EState) (slot : UInt64) : Prop :=
  EthCLSpecs.Gloas.Const.ptcSize ≤
    (EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) (ptcCandidates e slot)
      (ptcSeed e slot) EthCLSpecs.Gloas.Const.ptcSize false).size

section Ptc

variable {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem compute_ptc_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (slot : UInt64)
    (hfull : PtcSelectionFull e slot) {r : List Nat}
    (h : Spec.compute_ptc p o (absEState e) slot.toNat = .ok r) :
    r = (EthCLSpecs.Gloas.computePtc (pureState e) slot).toList.map UInt64.toNat := by
  unfold Spec.compute_ptc at h
  rw [compute_epoch_at_slot_eq hp] at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨ep, hep, seed, hseed, cps, hcps, cands, hcands, h⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Gloas.Const.domainPtcAttester rfl hseed
  subst hseed'
  have hcps' := get_committee_count_per_slot_ok hp hc e _ hcps
  subst hcps'
  have key := forIn_ok_rel (fun L (A : Array UInt64) => L = A.toList.map UInt64.toNat)
    (fun A i => A ++ EthCLSpecs.Gloas.getBeaconCommittee (pureState e) slot i) _ ?hf _ [] #[]
    cands rfl hcands
  case hf =>
    intro i L A res hLA hb
    simp only [except_bind_eq_ok, pure_bind, except_pure_eq_ok] at hb
    obtain ⟨com, hcom, rfl⟩ := hb
    refine ⟨_, rfl, ?_⟩
    rw [hLA, get_beacon_committee_ok hp o ho hc e slot i hcom]
    simp
  have hcands' : cands = (ptcCandidates e slot).toList.map UInt64.toNat := by
    rw [key, ptcCandidates, ← Array.foldl_toList, Array.toList_range]
  subst hcands'
  have hseed2 : o.hash ((EthCLSpecs.Gloas.getSeed (pureState e) (EthCLSpecs.Gloas.computeEpochAtSlot slot)
      EthCLSpecs.Gloas.Const.domainPtcAttester).toList ++ Spec.uint_to_bytes 8 slot.toNat) =
      bytesToRoot (ptcSeed e slot) := by
    have hba : toBA ((EthCLSpecs.Gloas.getSeed (pureState e)
        (EthCLSpecs.Gloas.computeEpochAtSlot slot) EthCLSpecs.Gloas.Const.domainPtcAttester).toList ++
          Spec.uint_to_bytes 8 slot.toNat) =
        vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) (EthCLSpecs.Gloas.computeEpochAtSlot slot)
          EthCLSpecs.Gloas.Const.domainPtcAttester) ++ uint64ToBytes slot := by
      apply ba_eq_of_toList
      rw [toBA_data, append_data_toList, vecToBytes_toList, uint_to_bytes_8]
    rw [hash_eq o ho, hba]
    rfl
  rw [hseed2, ← hc.ptcSize] at h
  have hfull' := hfull
  unfold PtcSelectionFull at hfull'
  rw [← vecToBytes_bytesToRoot (ptcSeed e slot) (hsha _)] at hfull'
  rw [compute_balance_weighted_selection_ok p o ho hc e _ _ _ false hfull' h,
    vecToBytes_bytesToRoot (ptcSeed e slot) (hsha _)]
  have hsz := Nat.le_antisymm (computeBalanceWeightedSelection_size_le e _ _ _ false) hfull
  unfold EthCLSpecs.Gloas.computePtc
  apply List.ext_getElem
  · simp [hsz]
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toList, Vector.getElem_ofFn]
    rw [getElem!_pos _ i (by simpa [ptcCandidates, ptcSeed, vecToBytes] using h1)]
    rfl


/-- The first slot of the epoch that `process_ptc_window` fills, in Etheorem. -/
def ptcStartSlot (e : EState) : UInt64 :=
  EthCLSpecs.Gloas.computeStartSlotAtEpoch (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
    EthCLSpecs.Gloas.Const.minSeedLookahead + 1)

/-- Each PTC selection of the epoch that `process_ptc_window` fills is full in Etheorem. -/
def PtcSelectionsFull (e : EState) : Prop :=
  ∀ i < EthCLSpecs.Gloas.Const.slotsPerEpoch, PtcSelectionFull e (ptcStartSlot e + UInt64.ofNat i)

/-- The new PTC window in Etheorem. -/
def newPtcWindow (e : EState) :
    Vector (Vector UInt64 EthCLSpecs.Gloas.Const.ptcSize) (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  shiftWindow e.ptcWindow EthCLSpecs.Gloas.Const.slotsPerEpoch
    (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch)
    (fun k => ((Array.range EthCLSpecs.Gloas.Const.slotsPerEpoch).map
      (fun i => EthCLSpecs.Gloas.computePtc (pureState e) (ptcStartSlot e + UInt64.ofNat i)))[k]!)

omit [EthCLSpecs.Gloas.Config] hp hc in
theorem processPtcWindow_run (e : EState) :
    (EthCLSpecs.Gloas.processPtcWindow (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState { e with ptcWindow := newPtcWindow e }) := rfl

/-- `process_ptc_window` equals Etheorem's when Etheorem's PTC selections are full. -/
theorem process_ptc_window_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (hfull : PtcSelectionsFull e)
    {s' : Spec.BeaconState} (h : Spec.process_ptc_window p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processPtcWindow (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  refine ⟨_, processPtcWindow_run e, ?_⟩
  unfold Spec.process_ptc_window at h
  have hge : ∀ l, Spec.get_current_epoch p { absEState e with ptc_window := l } =
      Spec.get_current_epoch p (absEState e) := fun _ => rfl
  have hcp : ∀ l slot, Spec.compute_ptc p o { absEState e with ptc_window := l } slot =
      Spec.compute_ptc p o (absEState e) slot := fun _ _ => rfl
  simp only [hge, hcp, except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨se, hse, ep1, hep1, ep2, hep2, ep3, hep3, st, hst, en, hen, ptcs, hptcs, fs, hfs,
    hfin⟩ := h
  rw [except_pure_eq_ok] at hfin
  subst hfin
  rw [Except.ok.injEq] at hep1
  subst hep1
  rw [← hp.minSeedLookahead] at hep2
  have hep2' := uint64Add_ok hep2
  subst hep2'
  have hep3' := uint64Add_ok (b := 1) hep3
  subst hep3'
  have hst' := compute_start_slot_at_epoch_ok hp _ hst
  subst hst'
  obtain ⟨hen', hen64⟩ := uint64Add_eq hen
  subst hen'
  obtain ⟨hse', -⟩ := uint64Sub_eq hse
  subst hse'
  obtain ⟨hfs', -⟩ := uint64Sub_eq hfs
  subst hfs'
  have hslt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  have hptcs' := mapM_ok_map _ (fun slot => (EthCLSpecs.Gloas.computePtc (pureState e)
      (UInt64.ofNat slot)).toList.map UInt64.toNat) _ ?hf hptcs
  case hf =>
    intro slot hslot r hr
    simp only [List.mem_range'_1] at hslot
    obtain ⟨hs1, hs2⟩ := hslot
    have hs1' : (ptcStartSlot e).toNat ≤ slot := hs1
    have hs2' : slot < (ptcStartSlot e).toNat + ((ptcStartSlot e).toNat + p.SLOTS_PER_EPOCH -
        (ptcStartSlot e).toNat) := hs2
    have hen' : (ptcStartSlot e).toNat + p.SLOTS_PER_EPOCH < 2 ^ 64 := hen64
    have hs64 : slot < 2 ^ 64 := by omega
    rw [← UInt64.toNat_ofNat_of_lt' (n := slot) hs64] at hr
    refine compute_ptc_ok hp hc o ho hsha e _ ?_ hr
    have hi : slot - (ptcStartSlot e).toNat < EthCLSpecs.Gloas.Const.slotsPerEpoch := by
      rw [hp.slotsPerEpoch]; omega
    have := hfull _ hi
    have heq : ptcStartSlot e + UInt64.ofNat (slot - (ptcStartSlot e).toNat) =
        UInt64.ofNat slot := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
        UInt64.toNat_ofNat_of_lt' hs64]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [heq] at this
    exact this
  subst hptcs'
  rw [absEState_set_ptcWindow]
  refine congrArg (fun l => { absEState e with ptc_window := l }) ?_
  simp only [absEState_ptc_window, List.length_map, Vector.length_toList, ← hp.slotsPerEpoch]
  have hen' : (ptcStartSlot e).toNat + EthCLSpecs.Gloas.Const.slotsPerEpoch < 2 ^ 64 := by
    rw [hp.slotsPerEpoch]; exact hen64
  unfold ptcStartSlot at hen'
  have h3 : 3 * EthCLSpecs.Gloas.Const.slotsPerEpoch - EthCLSpecs.Gloas.Const.slotsPerEpoch =
      2 * EthCLSpecs.Gloas.Const.slotsPerEpoch := by omega
  rw [h3, Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega)]
  apply List.ext_getElem
  · simp [newPtcWindow]; omega
  · intro j h1 h2
    simp only [newPtcWindow, shiftWindow, List.getElem_map, Vector.getElem_toList,
      Vector.getElem_ofFn]
    split
    · rename_i hj
      rw [List.getElem_append_left (by simp; omega)]
      simp [vget, getElem!_pos e.ptcWindow.toArray (j + EthCLSpecs.Gloas.Const.slotsPerEpoch)
        (by simp; omega), Nat.add_comm]
    · rename_i hj
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_drop, List.length_map, Vector.length_toList, List.getElem_map,
        List.getElem_range']
      have hk : j - (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch -
          EthCLSpecs.Gloas.Const.slotsPerEpoch) = j - 2 * EthCLSpecs.Gloas.Const.slotsPerEpoch := by
        omega
      simp only [hk]
      rw [getElem!_pos _ _ (by simp at h1 ⊢; omega)]
      simp only [Array.getElem_map, Array.getElem_range, ptcStartSlot]
      congr 3
      apply UInt64.toNat_inj.mp
      simp at h1
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
end Ptc
end EpochProofs.Etheorem

namespace EpochProofs.Etheorem

section
attribute [local instance] EthCLSpecs.Gloas.mainnet
theorem committeePresetAgrees_mainnet : CommitteePresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
end

section
attribute [local instance] EthCLSpecs.Gloas.minimal
theorem committeePresetAgrees_minimal : CommitteePresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
end

end EpochProofs.Etheorem
