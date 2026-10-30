import EpochProofs.Etheorem.Shuffle
import EpochProofs.Sanity.FuluEpoch
import EpochProofs.Sanity.Fulu

/-!
# Sync committee, proposer lookahead and PTC window updates equal Etheorem's

`process_sync_committee_updates`, `process_proposer_lookahead` and `process_ptc_window` each
take a balance weighted selection. Etheorem's selection counts passes with the spec's `uint64`
counter and returns only once it has `size` items, as pyspec does. So when the reference
returns, Etheorem returns the same items (`compute_balance_weighted_selection_ok`), and each
selection has `size` items (`computeBalanceWeightedSelection_ok_size`).

`hsha` says that `sha` returns 32 bytes. `sha_size_pure` proves it for the pure SHA-256.

The reference raises in one case where Etheorem does not: `eth_aggregate_pubkeys` asserts
`KeyValidate`. Each theorem assumes that the reference succeeds, so this case does not occur.

Fulu has no PTC window. Its proposer lookahead takes every active validator, slashed or not, and
its proposer and sync committee selections are the Electra loops. Etheorem's Fulu writes both
selections as the balance weighted selection.
- The Electra sync committee loop gives the same `ok` results as the selection
  (`process_sync_committee_updates_fulu_sameOk`).
- The Electra proposer loop returns what the selection returns if it ends before its last pass
  (`ProposerFin`, `compute_proposer_indices_fulu_ok`). The last pass needs `2**64 - 1` rejected
  candidates before it.

Each proof here holds for Gloas and for Fulu. `forkproof EpochEtheorem` (see `Forks.lean`)
elaborates the shared text once per fork, and `forkonly` holds the parts that differ.
-/

forkproof EpochEtheorem

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

forkonly Gloas
/-- The candidates of `get_beacon_proposer_indices` in Etheorem: active and not slashed. -/
def proposerCandidates (e : EState) (epoch : UInt64) : Array UInt64 :=
  (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e) epoch).filter
    (fun vi => !(e.validators[vi.toNat]!).slashed)
end forkonly

forkonly Fulu
/-- The candidates of the Fulu `get_beacon_proposer_indices` in Etheorem: every active
validator. -/
def proposerCandidates (e : EState) (epoch : UInt64) : Array UInt64 :=
  EthCLSpecs.Fulu.getActiveValidatorIndices (pureState e) epoch
end forkonly

/-- The seed of slot `i` of `epoch` in `compute_proposer_indices`, as Etheorem computes it. -/
def proposerSlotSeed (e : EState) (epoch : UInt64) (i : Nat) : ByteArray :=
  sha (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) epoch
      EthCLSpecs.Gloas.Const.domainBeaconProposer) ++
    uint64ToBytes (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i))

section Proposers

variable {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

forkonly Gloas
theorem get_beacon_proposer_indices_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (epoch : UInt64) {r : List Nat}
    (h : Spec.get_beacon_proposer_indices p o (absEState e) epoch.toNat = .ok r) :
    ∃ props, EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e) epoch = .ok props ∧
      r = props.toList.map UInt64.toNat := by
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
  -- The Etheorem step of slot `i`: select one proposer with the seed of slot `i`.
  obtain ⟨cs, hcs, rfl⟩ := mapM_ok_rel _ (fun i => do
      let sel ← EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
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
  unfold EthCLSpecs.Gloas.getBeaconProposerIndices EthCLSpecs.Gloas.computeProposerIndices
  simp only [view_uncachedBox]
  rw [Array.mapM_eq_mapM_toList, Array.toList_range, hp.slotsPerEpoch]
  exact congrArg (fun x => List.toArray <$> x) hcs
end forkonly

forkonly Fulu
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
end forkonly

/-- The new proposer lookahead in Etheorem, from the new proposers `props`. -/
def newLookahead (e : EState) (props : Array UInt64) :
    Vector UInt64 (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  Vector.ofFn fun i =>
    if i.val < EthCLSpecs.Gloas.Const.slotsPerEpoch then
      vget e.proposerLookahead (i.val + EthCLSpecs.Gloas.Const.slotsPerEpoch)
    else props[i.val - EthCLSpecs.Gloas.Const.slotsPerEpoch]!

omit [EthCLSpecs.Gloas.Config] hp hc in
theorem processProposerLookahead_run (e : EState) (props : Array UInt64)
    (hprops : EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead + 1)
      = .ok props) :
    (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState { e with proposerLookahead := newLookahead e props }) := by
  unfold EthCLSpecs.Gloas.processProposerLookahead
  rw [run_bind]
  rw [show (get : GloasRun EthCLSpecs.Gloas.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok]
  simp only []
  rw [run_bind, run_liftErr_of_ok _ _ (by rw [hprops]; rfl), except_bind_ok]
  rfl

forkonly Gloas
/-- `process_proposer_lookahead` equals Etheorem's. -/
theorem process_proposer_lookahead_etheorem (o : Spec.Oracle)
    (ho : ∀ d, o.hash d = etheoremHash d) (hsha : ∀ b : ByteArray, (sha b).size = 32)
    (e : EState)
    {s' : Spec.BeaconState} (h : Spec.process_proposer_lookahead p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
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
  obtain ⟨props, hpe, rfl⟩ := get_beacon_proposer_indices_ok hp hc o ho hsha e _ hprops
  refine ⟨_, processProposerLookahead_run e props hpe, ?_⟩
  obtain ⟨hles', -⟩ := uint64Sub_eq hles
  subst hles'
  rw [absEState_set_proposerLookahead]
  have hsize : props.size = EthCLSpecs.Gloas.Const.slotsPerEpoch := by
    unfold EthCLSpecs.Gloas.getBeaconProposerIndices EthCLSpecs.Gloas.computeProposerIndices at hpe
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
end forkonly

forkonly Fulu
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
end forkonly

/-! ## Sync committee -/

section Sync

variable [CryptoBackend] {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem get_next_sync_committee_ok (o : Spec.Oracle) (hoa : OracleAgrees o) (e : EState)
    {c : Spec.SyncCommittee}
    (h : Spec.get_next_sync_committee p o (absEState e) = .ok c) :
    ∃ c', EthCLSpecs.Gloas.getNextSyncCommittee (pureState e) = .ok c' ∧
      c = absSyncCommittee c' := by
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
  unfold EthCLSpecs.Gloas.getNextSyncCommittee
  simp only [view_uncachedBox]
  simp only [vecToBytes] at hres
  rw [hres, except_bind_ok]
  refine ⟨_, rfl, ?_⟩
  have hpk : (List.map (fun idx => ((e.validators[idx]?).getD default).pubkey)
      (List.map UInt64.toNat res.toList)) =
      (Vector.ofFn fun i : Fin EthCLSpecs.Gloas.Const.syncCommitteeSize =>
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

omit [EthCLSpecs.Gloas.Config] hp hc in
/-- Etheorem's `processSyncCommitteeUpdates` at a period boundary, when the next sync committee
is `c'`. -/
theorem processSyncCommitteeUpdates_run_update (e : EState) (c' : EthCLSpecs.Gloas.SyncCommittee)
    (hz : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0) = true)
    (hc' : EthCLSpecs.Gloas.getNextSyncCommittee (pureState e) = .ok c') :
    (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run
        (pureState e) =
      .ok ((), pureState { e with currentSyncCommittee := e.nextSyncCommittee,
                                  nextSyncCommittee := c' }) := by
  unfold EthCLSpecs.Gloas.processSyncCommitteeUpdates
  have hget : ∀ s : EthCLSpecs.Gloas.State,
      (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  simp only [hz, if_true]
  rw [run_bind, run_liftErr_of_ok _ _ (by rw [hc']; rfl), except_bind_ok]
  rfl

omit [EthCLSpecs.Gloas.Config] hp hc in
/-- Etheorem's `processSyncCommitteeUpdates` away from a period boundary leaves the state. -/
theorem processSyncCommitteeUpdates_run_skip (e : EState)
    (hz : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0) = false) :
    (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run
        (pureState e) = .ok ((), pureState e) := by
  unfold EthCLSpecs.Gloas.processSyncCommitteeUpdates
  have hget : ∀ s : EthCLSpecs.Gloas.State,
      (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  simp only [hz, Bool.false_eq_true, if_false]
  rfl

forkonly Gloas
/-- `process_sync_committee_updates` equals Etheorem's. -/
theorem process_sync_committee_updates_etheorem (o : Spec.Oracle) (hoa : OracleAgrees o)
    (hperiod : p.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64) (e : EState)
    {s' : Spec.BeaconState}
    (h : Spec.process_sync_committee_updates p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run (pureState e) =
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
  have hcond : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0) =
      ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1).toNat %
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

section Ptc

variable {p : Spec.Preset} (hp : PresetAgrees p) (hc : CommitteePresetAgrees p)
include hp hc

theorem compute_ptc_ok (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState) (slot : UInt64) {r : List Nat}
    (h : Spec.compute_ptc p o (absEState e) slot.toNat = .ok r) :
    ∃ v, EthCLSpecs.Gloas.computePtc (pureState e) slot = .ok v ∧
      r = v.toList.map UInt64.toNat := by
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
  obtain ⟨res, hres, rfl⟩ := compute_balance_weighted_selection_ok p o ho hc e _ _ _ false h
  rw [vecToBytes_bytesToRoot (ptcSeed e slot) (hsha _)] at hres
  have hsz := computeBalanceWeightedSelection_ok_size e _ _ _ false hres
  refine ⟨Vector.ofFn fun i : Fin EthCLSpecs.Gloas.Const.ptcSize => res[i.val]!, ?_, ?_⟩
  · unfold EthCLSpecs.Gloas.computePtc
    show (do
      let sel ← EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
        (ptcCandidates e slot) (ptcSeed e slot) EthCLSpecs.Gloas.Const.ptcSize false
      return Vector.ofFn fun i : Fin EthCLSpecs.Gloas.Const.ptcSize => sel[i.val]!) = _
    rw [hres]
    rfl
  · apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toList, Vector.getElem_ofFn]
      rw [getElem!_pos _ i (by simpa using h1)]

/-- The first slot of the epoch that `process_ptc_window` fills, in Etheorem. -/
def ptcStartSlot (e : EState) : UInt64 :=
  EthCLSpecs.Gloas.computeStartSlotAtEpoch (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
    EthCLSpecs.Gloas.Const.minSeedLookahead + 1)

/-- The new PTC window in Etheorem, from the PTCs `fresh` of the epoch that it fills. -/
def newPtcWindow (e : EState) (fresh : Array (Vector UInt64 EthCLSpecs.Gloas.Const.ptcSize)) :
    Vector (Vector UInt64 EthCLSpecs.Gloas.Const.ptcSize) (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  shiftWindow e.ptcWindow EthCLSpecs.Gloas.Const.slotsPerEpoch
    (2 * EthCLSpecs.Gloas.Const.slotsPerEpoch) (fun k => fresh[k]!)

omit [EthCLSpecs.Gloas.Config] hp hc in
theorem processPtcWindow_run (e : EState) (fresh : Array (Vector UInt64 EthCLSpecs.Gloas.Const.ptcSize))
    (hfresh : (Array.range EthCLSpecs.Gloas.Const.slotsPerEpoch).mapM
      (fun i => EthCLSpecs.Gloas.computePtc (pureState e) (ptcStartSlot e + UInt64.ofNat i)) =
        .ok fresh) :
    (EthCLSpecs.Gloas.processPtcWindow (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState { e with ptcWindow := newPtcWindow e fresh }) := by
  unfold EthCLSpecs.Gloas.processPtcWindow
  rw [run_bind]
  rw [show (get : GloasRun EthCLSpecs.Gloas.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok]
  simp only []
  have hfresh' : (Array.range EthCLSpecs.Gloas.Const.slotsPerEpoch).mapM
      (fun i => EthCLSpecs.Gloas.computePtc (pureState e)
        (EthCLSpecs.Gloas.computeStartSlotAtEpoch (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
          EthCLSpecs.Gloas.Const.minSeedLookahead + 1) + UInt64.ofNat i)) = .ok fresh := hfresh
  rw [run_bind, run_liftErr_of_ok _ _ (congrArg (Except.mapError ErrorConv.conv) hfresh'),
    except_bind_ok]
  rfl

/-- `process_ptc_window` equals Etheorem's. -/
theorem process_ptc_window_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EState)
    {s' : Spec.BeaconState} (h : Spec.process_ptc_window p o (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processPtcWindow (StateTransition := GloasRun)).run (pureState e) =
      .ok ((), pureState e') ∧ absEState e' = s' := by
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
  rw [Nat.add_sub_cancel_left, List.range'_eq_map_range] at hptcs
  have hen' : (ptcStartSlot e).toNat + p.SLOTS_PER_EPOCH < 2 ^ 64 := hen64
  -- The Etheorem step of slot `i` of the epoch: the PTC of `ptcStartSlot e + i`.
  obtain ⟨cs, hcs, rfl⟩ := mapM_ok_rel (fun slot => Spec.compute_ptc p o (absEState e) slot)
    (fun i => EthCLSpecs.Gloas.computePtc (pureState e) (ptcStartSlot e + UInt64.ofNat i))
    (fun v => v.toList.map UInt64.toNat) _ _
    (by
      intro i hi r hr
      simp only [List.mem_range] at hi
      have heq : (ptcStartSlot e + UInt64.ofNat i).toNat = (ptcStartSlot e).toNat + i := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
          Nat.mod_eq_of_lt (by first | omega | (simp only [UInt64.size]; omega))]
      have hr' : Spec.compute_ptc p o (absEState e) (ptcStartSlot e + UInt64.ofNat i).toNat =
          .ok r := by rw [heq]; exact hr
      exact compute_ptc_ok hp hc o ho hsha e _ hr') hptcs
  have hlen : cs.length = EthCLSpecs.Gloas.Const.slotsPerEpoch := by
    rw [mapM_length_eq hcs, List.length_range, hp.slotsPerEpoch]
  have hfresh : (Array.range EthCLSpecs.Gloas.Const.slotsPerEpoch).mapM
      (fun i => EthCLSpecs.Gloas.computePtc (pureState e) (ptcStartSlot e + UInt64.ofNat i)) =
        .ok cs.toArray := by
    rw [Array.mapM_eq_mapM_toList, Array.toList_range, hp.slotsPerEpoch, hcs]
    rfl
  refine ⟨_, processPtcWindow_run e cs.toArray hfresh, ?_⟩
  rw [absEState_set_ptcWindow]
  refine congrArg (fun l => { absEState e with ptc_window := l }) ?_
  simp only [absEState_ptc_window, List.length_map, Vector.length_toList, ← hp.slotsPerEpoch]
  have hen' : (ptcStartSlot e).toNat + EthCLSpecs.Gloas.Const.slotsPerEpoch < 2 ^ 64 := by
    rw [hp.slotsPerEpoch]; exact hen64
  unfold ptcStartSlot at hen'
  have h3 : 3 * EthCLSpecs.Gloas.Const.slotsPerEpoch - EthCLSpecs.Gloas.Const.slotsPerEpoch =
      2 * EthCLSpecs.Gloas.Const.slotsPerEpoch := by omega
  rw [h3]
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
      simp only [List.length_drop, List.length_map, Vector.length_toList, List.getElem_map]
      have hk : j - (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch -
          EthCLSpecs.Gloas.Const.slotsPerEpoch) = j - 2 * EthCLSpecs.Gloas.Const.slotsPerEpoch := by
        omega
      simp only [hk]
      rw [getElem!_pos _ _ (by simp at h1 ⊢; omega)]
      simp
end Ptc
end forkonly

forkonly Fulu
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
end forkonly

end forkproof

forkproof EpochEtheorem

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

end forkproof

