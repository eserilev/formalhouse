import EpochProofs.Etheorem.Fulu.Shuffle
import EpochProofs.Sanity.FuluEpoch
import EpochProofs.Sanity.Fulu

/-!
# Fulu sync committee and proposer lookahead updates equal Etheorem's

Fulu has no PTC window. Its proposer lookahead takes every active validator, slashed or not, and
its proposer and sync committee selections are the Electra loops. Etheorem's Fulu writes both
selections as the Gloas balance weighted selection.

- The Electra sync committee loop gives the same `ok` results as the selection
  (`process_sync_committee_updates_fulu_sameOk`).
- The Electra proposer loop returns what the selection returns if it ends before its last pass
  (`ProposerFin`, `compute_proposer_indices_fulu_ok`). The last pass needs `2**64 - 1` rejected
  candidates before it.

Etheorem's selection counts passes with the spec's `uint64` counter and returns only once it has
`size` items, as pyspec does. So when the reference returns, Etheorem returns the same items.

`hsha` says that `sha` returns 32 bytes. `sha_size_pure` proves it for the pure SHA-256.

The reference raises in one case where Etheorem does not: `eth_aggregate_pubkeys` asserts
`KeyValidate`. Each theorem assumes that the reference succeeds, so this case does not occur.
-/

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu

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


variable [EthCLSpecs.Fulu.Preset] [HasherTag] [EthCLSpecs.Fulu.Config]

/-! ## Proposers -/

/-- The candidates of the Fulu `get_beacon_proposer_indices` in Etheorem: every active
validator. -/
def proposerCandidates (e : EState) (epoch : UInt64) : Array UInt64 :=
  EthCLSpecs.Fulu.getActiveValidatorIndices (pureState e) epoch

/-- The seed of slot `i` of `epoch` in `compute_proposer_indices`, as Etheorem computes it. -/
def proposerSlotSeed (e : EState) (epoch : UInt64) (i : Nat) : ByteArray :=
  sha (vecToBytes (EthCLSpecs.Fulu.getSeed (pureState e) epoch
      EthCLSpecs.Fulu.Const.domainBeaconProposer) ++
    uint64ToBytes (EthCLSpecs.Fulu.computeStartSlotAtEpoch epoch + UInt64.ofNat i))

section Proposers

variable {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

/-- The Fulu `get_beacon_proposer_indices` equals Etheorem's when the Electra loops end before
their last pass. -/
theorem get_beacon_proposer_indices_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (epoch : UInt64)
    (hfin : ∀ s, Spec.ProposerFin p o (absEState e)
      (Spec.get_active_validator_indices (absEState e) epoch.toNat) s)
    {r : List Nat}
    (h : Spec.get_beacon_proposer_indices_fulu p o (absEState e) epoch.toNat = .ok r) :
    ∃ props, EthCLSpecs.Fulu.getBeaconProposerIndices (pureState e) epoch = .ok props ∧
      r = props.toList.map UInt64.toNat := by
  unfold Spec.get_beacon_proposer_indices_fulu at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨seed, hseed, h⟩ := h
  have h := Spec.compute_proposer_indices_fulu_ok p o (absEState e) _ seed _
    (fun x hx => Spec.active_validator_index_lt _ _ x hx) hfin r h
  have hc2 : Spec.get_active_validator_indices (absEState e) epoch.toNat =
      (proposerCandidates e epoch).toList.map UInt64.toNat := by
    rw [get_active_validator_indices_eq hp]
    rfl
  rw [hc2] at h
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Fulu.Const.domainBeaconProposer rfl hseed
  subst hseed'
  unfold Spec.compute_proposer_indices at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨start, hstart, seeds, hseeds, h⟩ := h
  have hstart' := compute_start_slot_at_epoch_ok hp epoch hstart
  subst hstart'
  have hslt := EthCLSpecs.Fulu.Const.slotsPerEpochLt
  have hseeds' := mapM_ok_map _ (fun i => bytesToRoot (proposerSlotSeed e epoch i)) _ ?hf2 hseeds
  case hf2 =>
    intro i hi b hb
    simp only [List.mem_range] at hi
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hi64 : i < 2 ^ 64 := by rw [← hp.slotsPerEpoch] at hi; omega
    have hx' : x = (EthCLSpecs.Fulu.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat := by
      rw [← UInt64.toNat_ofNat_of_lt' (n := i) hi64] at hx
      exact (uint64Add_ok hx).symm
    subst hx'
    have hba : toBA ((EthCLSpecs.Fulu.getSeed (pureState e) epoch
        EthCLSpecs.Fulu.Const.domainBeaconProposer).toList ++ Spec.uint_to_bytes 8
          (EthCLSpecs.Fulu.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat) =
        vecToBytes (EthCLSpecs.Fulu.getSeed (pureState e) epoch
          EthCLSpecs.Fulu.Const.domainBeaconProposer) ++
        uint64ToBytes (EthCLSpecs.Fulu.computeStartSlotAtEpoch epoch + UInt64.ofNat i) := by
      apply ba_eq_of_toList
      rw [toBA_data, append_data_toList, vecToBytes_toList, uint_to_bytes_8]
    rw [hash_eq o ho, hba]
    unfold proposerSlotSeed
    rfl
  subst hseeds'
  -- The Etheorem step of slot `i`: select one proposer with the seed of slot `i`.
  obtain ⟨cs, hcs, rfl⟩ := mapM_ok_rel _ (fun i => do
      let sel ← EthCLSpecs.Fulu.computeBalanceWeightedSelection (pureState e)
        (proposerCandidates e epoch) (proposerSlotSeed e epoch i) 1 true
      return sel[0]!) UInt64.toNat (fun i => bytesToRoot (proposerSlotSeed e epoch i)) _
    (by
      intro i _ v hv
      simp only [except_bind_eq_ok] at hv
      obtain ⟨sel, hsel, hv⟩ := hv
      obtain ⟨res, hres, rfl⟩ := compute_balance_weighted_selection_ok p o ho hc e _ _ 1 true hsel
      rw [vecToBytes_bytesToRoot (proposerSlotSeed e epoch i) (hsha _)] at hres
      refine ⟨res[0]!, by rw [hres]; rfl, ?_⟩
      obtain ⟨-, rfl⟩ := listGet_ok hv
      rw [map_toNat_getElem!_all]) h
  refine ⟨cs.toArray, ?_, by simp⟩
  unfold EthCLSpecs.Fulu.getBeaconProposerIndices EthCLSpecs.Fulu.computeProposerIndices
  rw [Array.mapM_eq_mapM_toList, Array.toList_range, hp.slotsPerEpoch]
  exact congrArg (fun x => List.toArray <$> x) hcs


/-- The new proposer lookahead in Etheorem, from the new proposers `props`. -/
def newLookahead (e : EState) (props : Array UInt64) :
    Vector UInt64 (2 * EthCLSpecs.Fulu.Const.slotsPerEpoch) :=
  Vector.ofFn fun i =>
    if i.val < EthCLSpecs.Fulu.Const.slotsPerEpoch then
      vget e.proposerLookahead (i.val + EthCLSpecs.Fulu.Const.slotsPerEpoch)
    else props[i.val - EthCLSpecs.Fulu.Const.slotsPerEpoch]!

omit [EthCLSpecs.Fulu.Config] hp hc in
theorem processProposerLookahead_run (e : EState) (props : Array UInt64)
    (hprops : EthCLSpecs.Fulu.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Fulu.currentEpochOf (pureState e) + EthCLSpecs.Fulu.Const.minSeedLookahead + 1)
      = .ok props) :
    (EthCLSpecs.Fulu.processProposerLookahead (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState { e with proposerLookahead := newLookahead e props }) := by
  unfold EthCLSpecs.Fulu.processProposerLookahead
  rw [run_bind]
  rw [show (get : FuluRun EthCLSpecs.Fulu.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok]
  simp only []
  rw [run_bind, run_liftErr_of_ok _ _ (by rw [hprops]; rfl), except_bind_ok]
  rfl

/-- `process_proposer_lookahead` equals Etheorem's. -/
theorem process_proposer_lookahead_etheorem (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hsha : ∀ b : ByteArray, (sha b).size = 32)
    (e : EState)
    (hfin : ∀ s, Spec.ProposerFin p o (absEState e)
      (Spec.get_active_validator_indices (absEState e)
        (EthCLSpecs.Fulu.currentEpochOf (pureState e) + EthCLSpecs.Fulu.Const.minSeedLookahead +
          1).toNat) s)
    {s' : Spec.BeaconState} (h : Spec.process_proposer_lookahead_fulu p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.processProposerLookahead (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  unfold Spec.process_proposer_lookahead_fulu at h
  have hge : ∀ l, Spec.get_current_epoch p { absEState e with proposer_lookahead := l } =
      Spec.get_current_epoch p (absEState e) := fun _ => rfl
  have hgb : ∀ l ep, Spec.get_beacon_proposer_indices_fulu p o
      { absEState e with proposer_lookahead := l } ep =
      Spec.get_beacon_proposer_indices_fulu p o (absEState e) ep := fun _ _ => rfl
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
  obtain ⟨props, hpe, rfl⟩ := get_beacon_proposer_indices_ok hp hc o ho hsha e _ hfin hprops
  refine ⟨_, processProposerLookahead_run e props hpe, ?_⟩
  obtain ⟨hles', -⟩ := uint64Sub_eq hles
  subst hles'
  rw [absEState_set_proposerLookahead]
  have hsize : props.size = EthCLSpecs.Fulu.Const.slotsPerEpoch := by
    unfold EthCLSpecs.Fulu.getBeaconProposerIndices EthCLSpecs.Fulu.computeProposerIndices at hpe
    rw [Array.mapM_eq_mapM_toList] at hpe
    simp only [except_map_eq_ok] at hpe
    obtain ⟨l, hl, rfl⟩ := hpe
    simpa using mapM_length_eq hl
  have hlist : (newLookahead e props).toList.map UInt64.toNat =
      List.take ((absEState e).proposer_lookahead.length - p.SLOTS_PER_EPOCH)
        (List.drop p.SLOTS_PER_EPOCH (absEState e).proposer_lookahead ++
          List.drop ((absEState e).proposer_lookahead.length - p.SLOTS_PER_EPOCH)
            (absEState e).proposer_lookahead) ++
      List.map UInt64.toNat props.toList := by
    simp only [absEState_proposer_lookahead, List.length_map, Vector.length_toList,
      ← hp.slotsPerEpoch]
    have h2 : 2 * EthCLSpecs.Fulu.Const.slotsPerEpoch - EthCLSpecs.Fulu.Const.slotsPerEpoch =
        EthCLSpecs.Fulu.Const.slotsPerEpoch := by omega
    rw [h2, List.take_append_of_le_length (by simp; omega)]
    rw [List.take_of_length_le (by simp; omega)]
    apply List.ext_getElem
    · simp [newLookahead, hsize]; omega
    · intro i h1 h2'
      simp only [newLookahead, List.getElem_map, Vector.getElem_toList, Vector.getElem_ofFn]
      split
      · rename_i hi
        rw [List.getElem_append_left (by simp; omega)]
        simp [vget, getElem!_pos e.proposerLookahead.toArray (i + EthCLSpecs.Fulu.Const.slotsPerEpoch)
          (by simp; omega), Nat.add_comm]
      · rename_i hi
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_drop, List.length_map, Vector.length_toList, List.getElem_map,
          Array.getElem_toList]
        have hk : i - (2 * EthCLSpecs.Fulu.Const.slotsPerEpoch -
            EthCLSpecs.Fulu.Const.slotsPerEpoch) = i - EthCLSpecs.Fulu.Const.slotsPerEpoch := by
          omega
        simp only [hk]
        rw [getElem!_pos _ _ (by simp at h1; omega)]
  rw [hlist]
end Proposers

/-! ## Sync committee -/

section Sync

variable [CryptoBackend] {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem get_next_sync_committee_ok (o : Spec.Oracle) (hoa : OracleAgrees o) (e : EState)
    {c : Spec.SyncCommittee}
    (h : Spec.get_next_sync_committee p o (absEState e) = .ok c) :
    ∃ c', EthCLSpecs.Fulu.getNextSyncCommittee (pureState e) = .ok c' ∧
      c = absSyncCommittee c' := by
  unfold Spec.get_next_sync_committee Spec.get_next_sync_committee_indices at h
  simp only [except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨sel, ⟨ep, hep, ep1, hep1, seed, hseed, hsel⟩, pks, hpks, agg, hagg, hc'⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hep1' := uint64Add_ok (b := 1) hep1
  subst hep1'
  have hseed' := get_seed_ok hp o hoa.hash e _ _ EthCLSpecs.Fulu.Const.domainSyncCommittee rfl
    hseed
  subst hseed'
  rw [get_active_validator_indices_eq hp, ← hc.syncCommitteeSize] at hsel
  obtain ⟨res, hres, rfl⟩ := compute_balance_weighted_selection_ok p o hoa.hash hc e _ _ _ true hsel
  have hsz := computeBalanceWeightedSelection_ok_size e _ _ _ true hres
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
  unfold EthCLSpecs.Fulu.getNextSyncCommittee
  simp only [view_uncachedBox]
  simp only [vecToBytes] at hres
  rw [hres, except_bind_ok]
  refine ⟨_, rfl, ?_⟩
  have hpk : (List.map (fun idx => ((e.validators[idx]?).getD default).pubkey)
      (List.map UInt64.toNat res.toList)) =
      (Vector.ofFn fun i : Fin EthCLSpecs.Fulu.Const.syncCommitteeSize =>
        ((e.validators[(res[i.val]!).toNat]?).getD default).pubkey).toList := by
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toList,
        Vector.getElem_ofFn]
      rw [getElem!_pos _ i (by simpa using h1)]
  unfold absSyncCommittee
  rw [hoa.aggregate, hpk]
  rfl


omit [EthCLSpecs.Fulu.Config] hp hc in
/-- Etheorem's `processSyncCommitteeUpdates` at a period boundary, when the next sync committee
is `c'`. -/
theorem processSyncCommitteeUpdates_run_update (e : EState) (c' : EthCLSpecs.Fulu.SyncCommittee)
    (hz : ((EthCLSpecs.Fulu.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSyncCommitteePeriod == 0) = true)
    (hc' : EthCLSpecs.Fulu.getNextSyncCommittee (pureState e) = .ok c') :
    (EthCLSpecs.Fulu.processSyncCommitteeUpdates (StateTransition := FuluRun)).run
        (pureState e) =
      .ok ((), pureState { e with currentSyncCommittee := e.nextSyncCommittee,
                                  nextSyncCommittee := c' }) := by
  unfold EthCLSpecs.Fulu.processSyncCommitteeUpdates
  have hget : ∀ s : EthCLSpecs.Fulu.State,
      (get : FuluRun EthCLSpecs.Fulu.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  simp only [hz, if_true]
  rw [run_bind, run_liftErr_of_ok _ _ (by rw [hc']; rfl), except_bind_ok]
  rfl

omit [EthCLSpecs.Fulu.Config] hp hc in
/-- Etheorem's `processSyncCommitteeUpdates` away from a period boundary leaves the state. -/
theorem processSyncCommitteeUpdates_run_skip (e : EState)
    (hz : ((EthCLSpecs.Fulu.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSyncCommitteePeriod == 0) = false) :
    (EthCLSpecs.Fulu.processSyncCommitteeUpdates (StateTransition := FuluRun)).run
        (pureState e) = .ok ((), pureState e) := by
  unfold EthCLSpecs.Fulu.processSyncCommitteeUpdates
  have hget : ∀ s : EthCLSpecs.Fulu.State,
      (get : FuluRun EthCLSpecs.Fulu.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  simp only [hz, Bool.false_eq_true, if_false]
  rfl

/-- `process_sync_committee_updates` equals Etheorem's. -/
theorem process_sync_committee_updates_etheorem (o : Spec.Oracle) (hoa : OracleAgrees o)
    (hperiod : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64) (e : EState)
    {s' : Spec.BeaconState}
    (h : Spec.process_sync_committee_updates p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.processSyncCommitteeUpdates (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
  unfold Spec.process_sync_committee_updates at h
  simp only [except_bind_eq_ok, get_current_epoch_eq hp] at h
  obtain ⟨ep, hep, ep1, hep1, m, hm, h⟩ := h
  rw [Except.ok.injEq] at hep
  subst hep
  have hep1' := uint64Add_ok (b := 1) hep1
  subst hep1'
  obtain ⟨hm', -⟩ := uint64Mod_eq hm
  subst hm'
  have hcond : ((EthCLSpecs.Fulu.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Fulu.Const.epochsPerSyncCommitteePeriod == 0) =
      ((EthCLSpecs.Fulu.currentEpochOf (pureState e) + 1).toNat %
        p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD == 0) := by
    rw [hc.epochsPerSyncCommitteePeriod]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hperiod]
    simp
  split at h
  · rename_i hz
    have hgn : Spec.get_next_sync_committee p o { absEState e with
        current_sync_committee := (absEState e).next_sync_committee } =
        Spec.get_next_sync_committee p o (absEState e) := rfl
    simp only [hgn, except_bind_eq_ok, except_pure_eq_ok] at h
    obtain ⟨c, hcn, rfl⟩ := h
    obtain ⟨c', hc', rfl⟩ := get_next_sync_committee_ok hp hc o hoa e hcn
    refine ⟨_, processSyncCommitteeUpdates_run_update e c' (by rw [hcond]; exact hz) hc', ?_⟩
    rw [absEState_set_syncCommittees]
    rfl
  · rename_i hz
    rw [except_pure_eq_ok] at h
    refine ⟨e, processSyncCommitteeUpdates_run_skip e
      (by rw [hcond]; exact Bool.eq_false_iff.mpr hz), h⟩
/-- The Fulu `process_sync_committee_updates`, with the Electra loop, equals Etheorem's. -/
theorem process_sync_committee_updates_fulu_etheorem (o : Spec.Oracle) (hoa : OracleAgrees o)
    (hperiod : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64) (hsize : 0 < p.SYNC_COMMITTEE_SIZE)
    (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_sync_committee_updates_fulu p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.processSyncCommitteeUpdates (StateTransition := FuluRun)).run
        (pureState e) = .ok ((), pureState e') ∧ absEState e' = s' :=
  process_sync_committee_updates_etheorem hp hc o hoa hperiod e
    ((Spec.process_sync_committee_updates_fulu_sameOk p o (absEState e) hsize s').mp h)
end Sync

end EpochProofs.Etheorem.Fulu

namespace EpochProofs.Etheorem.Fulu

section
attribute [local instance] EthCLSpecs.Fulu.mainnet
theorem committeePresetAgrees_mainnet : CommitteePresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
end

section
attribute [local instance] EthCLSpecs.Fulu.minimal
theorem committeePresetAgrees_minimal : CommitteePresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
end

end EpochProofs.Etheorem.Fulu
