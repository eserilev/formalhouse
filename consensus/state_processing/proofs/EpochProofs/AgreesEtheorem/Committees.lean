import EpochProofs.AgreesEtheorem.Selection

/-!
# When an Etheorem committee step succeeds, the reference step succeeds

`Etheorem/Committees.lean` goes from the reference to Etheorem: if the reference committee step
returns `s'`, Etheorem's step returns a state that maps to `s'`. This file goes the other way, for
the steps that run a balance weighted selection: the sync committee update, the proposer
lookahead and (Gloas) the PTC window.

Each proof reads the selections out of Etheorem's successful run, turns each into `SelOk` with
`selOk_of_etheorem`, and closes with the `_total_of_sel` theorem of
`AgreesEtheorem/CommitteesTotal.lean`. No pyspec precondition is assumed: an empty candidate set
or a selection that runs past `2**64` passes makes Etheorem fail, as it makes the reference fail.

The state facts (`SelFacts`) stay. Etheorem does not fail where the reference fails on them:
`eth_aggregate_pubkeys` asserts `KeyValidate` on each key and Etheorem aggregates without the
check, and the reference checks the `uint64` products that Etheorem computes in `Nat`. They hold
on reachable states. The proposer lookahead and PTC window lengths hold on every Etheorem state
(`lookahead_length`, `ptc_window_length`).

Each proof here holds for Gloas and for Fulu. `forkproof EpochEtheorem` (see
`Etheorem/Forks.lean`) elaborates the shared text once per fork.
-/

forkproof EpochEtheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] [CryptoBackend]
variable [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds]

section Converse

variable (hp : PresetAgrees Spec.P) (hc : CommitteePresetAgrees Spec.P)
include hp hc

omit [Spec.PresetCfg.Bounds] [CryptoBackend] hc in
/-- Etheorem's current epoch is the reference's. -/
theorem currentEpochOf_toNat (e : EtheoremState) :
    (EthCLSpecs.Gloas.currentEpochOf (pureState e)).toNat =
      (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH := by
  have h1 := get_current_epoch_eq hp e
  rw [Spec.tot_current_epoch] at h1
  exact (Except.ok.inj h1).symm

omit [EthCLSpecs.Gloas.Config] [CryptoBackend] [Spec.PresetCfg.Ok] hp in
/-- `selOk_of_etheorem` for a selection over the validators active at `epoch`, with the bounds
read from `SelFacts`. -/
theorem selOk_active_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (e : EtheoremState) (hf : Spec.SelFacts o (toSpecState e)) (epoch : UInt64) (seed : Spec.Bytes32)
    (size : Nat) (shuffle : Bool) (cands : Array UInt64)
    (hcands : cands.toList.map UInt64.toNat ⊆
      Spec.get_active_validator_indices (toSpecState e) epoch.toNat)
    (hlen : cands.size ≤ 2 ^ 40) {res : Array UInt64}
    (h : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e) cands (vecToBytes seed)
      size shuffle = .ok res) :
    Spec.SelOk Spec.P o (toSpecState e) (cands.toList.map UInt64.toNat) seed size shuffle :=
  selOk_of_etheorem Spec.P o ho hc e cands seed size shuffle
    (fun j hj => Spec.active_lt _ _ j (hcands hj))
    (by rw [Spec.P_maxeb]; exact hf.ebMax) hlen Spec.P_shuffle_le
    (by rw [Spec.P_maxeb]; decide) h

/-- When Etheorem's sync committee update succeeds, the reference update succeeds, and keeps the
fields that the next committee steps read. -/
theorem sync_committee_updates_of_etheorem (o : Spec.Oracle) (hoa : OracleAgrees o)
    (hperiod : Spec.P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD < 2 ^ 64) (e : EtheoremState)
    (hf : Spec.SelFacts o (toSpecState e)) {r : Unit × EthCLSpecs.Gloas.State}
    (h : (EthCLSpecs.Gloas.processSyncCommitteeUpdates (StateTransition := GloasRun)).run
      (pureState e) = .ok r) :
    Spec.OkWith (Spec.process_sync_committee_updates Spec.P o (toSpecState e)) (fun s' =>
      s'.slot = (toSpecState e).slot ∧ s'.validators = (toSpecState e).validators ∧
        s'.randao_mixes = (toSpecState e).randao_mixes ∧
        s'.proposer_lookahead = (toSpecState e).proposer_lookahead ∧
        s'.ptc_window = (toSpecState e).ptc_window) := by
  apply Spec.process_sync_committee_updates_total_of_sel o _ hf.slot hf.randao hf.keys
  intro hz seed hseed
  have hcur := currentEpochOf_toNat hp e
  have ha1 : (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Spec.P_ep_bound hf.slot 1 (by decide))
  have hcur1 : (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1).toNat =
      (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 1 := by
    rw [UInt64.toNat_add, hcur, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (by show _ < 18446744073709551616; omega)
  have hz' : ((EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerSyncCommitteePeriod == 0) = true := by
    rw [hc.epochsPerSyncCommitteePeriod]
    apply beq_iff_eq.mpr
    rw [← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' hperiod, hcur1]
    simpa using hz
  unfold EthCLSpecs.Gloas.processSyncCommitteeUpdates at h
  rw [run_bind, show (get : GloasRun EthCLSpecs.Gloas.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok] at h
  simp only [hz', if_true] at h
  cases hn : EthCLSpecs.Gloas.getNextSyncCommittee (pureState e) with
  | error err =>
    rw [run_bind, run_liftErr_of_error _ _ (by rw [hn]; rfl), except_bind_error] at h
    cases h
  | ok c' =>
  unfold EthCLSpecs.Gloas.getNextSyncCommittee at hn
  simp only [view_uncachedBox] at hn
  cases hcb : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e)
        (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1))
      (vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e)
        (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1)
        EthCLSpecs.Gloas.Const.domainSyncCommittee))
      EthCLSpecs.Gloas.Const.syncCommitteeSize true with
  | error err =>
    simp only [vecToBytes] at hcb
    rw [hcb, except_bind_error] at hn
    cases hn
  | ok res =>
  rw [← hcur1] at hseed ⊢
  have hseed' := get_seed_ok hp o hoa.hash e _ _ EthCLSpecs.Gloas.Const.domainSyncCommittee rfl
    hseed
  subst hseed'
  rw [get_active_validator_indices_eq hp]
  rw [hc.syncCommitteeSize] at hcb
  have hlen : (EthCLSpecs.Gloas.getActiveValidatorIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1)).size ≤ 2 ^ 40 := by
    have h1 := Spec.active_len_le (toSpecState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + 1).toNat
    rw [get_active_validator_indices_eq hp] at h1
    simp only [List.length_map, Array.length_toList] at h1
    exact h1.trans hf.regLen
  exact selOk_active_of_etheorem hc o hoa.hash e hf _ _ _ true _
    (by rw [get_active_validator_indices_eq hp]; exact List.Subset.refl _) hlen hcb

omit [HasherTag] [CryptoBackend] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] hc in
/-- The proposer lookahead of an Etheorem state has `2 * SLOTS_PER_EPOCH` items. -/
theorem lookahead_length (e : EtheoremState) :
    (toSpecState e).proposer_lookahead.length = 2 * Spec.P.SLOTS_PER_EPOCH := by
  simp [toSpecState_proposer_lookahead, hp.slotsPerEpoch]

omit [EthCLSpecs.Gloas.Preset] [HasherTag] [EthCLSpecs.Gloas.Config] [CryptoBackend]
  [Spec.PresetCfg] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] hp hc in
/-- Each item of a successful `mapM` is a successful call. -/
theorem mapM_ok_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ∀ a ∈ l, ∃ y, f a = .ok y := by
  intro l
  induction l with
  | nil => intro _ _ a ha; cases ha
  | cons x xs ih =>
    intro ys h a ha
    rw [List.mapM_cons, except_bind_eq_ok] at h
    obtain ⟨y, hy, h⟩ := h
    rw [except_bind_eq_ok] at h
    obtain ⟨zs, hzs, -⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, hy⟩
    · exact ih hzs a ha

omit [CryptoBackend] [Spec.PresetCfg.Ok] in
/-- When Etheorem's `get_beacon_proposer_indices` of `epoch` succeeds, each reference proposer
selection of `epoch` returns (`ProposerSelOk`), over Etheorem's candidates. -/
theorem proposerSelOk_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState) (hf : Spec.SelFacts o (toSpecState e))
    (epoch : UInt64)
    (hcands : (proposerCandidates e epoch).toList.map UInt64.toNat ⊆
      Spec.get_active_validator_indices (toSpecState e) epoch.toNat)
    (hlen : (proposerCandidates e epoch).size ≤ 2 ^ 40)
    (hstart : epoch.toNat * Spec.P.SLOTS_PER_EPOCH + Spec.P.SLOTS_PER_EPOCH < 2 ^ 64)
    {props : Array UInt64}
    (h : EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e) epoch = .ok props) :
    Spec.ProposerSelOk o (toSpecState e) epoch.toNat
      ((proposerCandidates e epoch).toList.map UInt64.toNat) := by
  intro seed hseed i hi
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Gloas.Const.domainBeaconProposer rfl hseed
  subst hseed'
  unfold EthCLSpecs.Gloas.getBeaconProposerIndices EthCLSpecs.Gloas.computeProposerIndices at h
  simp only [view_uncachedBox] at h
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at h
  simp only [except_map_eq_ok] at h
  obtain ⟨l, hl, -⟩ := h
  have hi' : i < EthCLSpecs.Gloas.Const.slotsPerEpoch := by rw [hp.slotsPerEpoch]; exact hi
  obtain ⟨y, hy⟩ := mapM_ok_mem hl i (List.mem_range.mpr hi')
  cases hcb : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (proposerCandidates e epoch) (proposerSlotSeed e epoch i) 1 true with
  | error err =>
    simp only [proposerSlotSeed, proposerCandidates, vecToBytes] at hcb
    rw [hcb, except_bind_error] at hy
    cases hy
  | ok sel =>
  have hst : (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch).toNat =
      epoch.toNat * Spec.P.SLOTS_PER_EPOCH :=
    compute_start_slot_at_epoch_ok hp epoch (by
      unfold Spec.compute_start_slot_at_epoch; exact Spec.tot_mul (by omega))
  have hsi : (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat =
      epoch.toNat * Spec.P.SLOTS_PER_EPOCH + i := by
    rw [UInt64.toNat_add, hst, UInt64.toNat_ofNat_of_lt' (by show i < 18446744073709551616; omega)]
    exact Nat.mod_eq_of_lt (by show _ < 18446744073709551616; omega)
  have hseedEq : o.hash ((EthCLSpecs.Gloas.getSeed (pureState e) epoch
      EthCLSpecs.Gloas.Const.domainBeaconProposer).toList ++
        Spec.uint_to_bytes 8 (epoch.toNat * Spec.P.SLOTS_PER_EPOCH + i)) =
      bytesToRoot (proposerSlotSeed e epoch i) := by
    have hba : toBA ((EthCLSpecs.Gloas.getSeed (pureState e) epoch
        EthCLSpecs.Gloas.Const.domainBeaconProposer).toList ++ Spec.uint_to_bytes 8
          (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i).toNat) =
        vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) epoch
          EthCLSpecs.Gloas.Const.domainBeaconProposer) ++
        uint64ToBytes (EthCLSpecs.Gloas.computeStartSlotAtEpoch epoch + UInt64.ofNat i) := by
      apply ba_eq_of_toList
      rw [toBA_data, append_data_toList, vecToBytes_toList, uint_to_bytes_8]
    rw [← hsi, hash_eq o ho, hba]
    rfl
  rw [hseedEq]
  have hcb' : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (proposerCandidates e epoch) (vecToBytes (bytesToRoot (proposerSlotSeed e epoch i))) 1 true =
      .ok sel := by
    rw [vecToBytes_bytesToRoot (proposerSlotSeed e epoch i) (hsha _)]; exact hcb
  exact selOk_active_of_etheorem hc o ho e hf epoch (bytesToRoot (proposerSlotSeed e epoch i)) 1
    true (proposerCandidates e epoch) hcands hlen hcb'

omit [EthCLSpecs.Gloas.Config] [CryptoBackend] [Spec.PresetCfg] [Spec.PresetCfg.Ok]
  [Spec.PresetCfg.Bounds] hp hc in
/-- When Etheorem's proposer lookahead succeeds, its proposer computation succeeds. -/
theorem props_of_lookahead_run (e : EtheoremState) {r : Unit × EthCLSpecs.Gloas.State}
    (h : (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run
      (pureState e) = .ok r) :
    ∃ props, EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead +
        1) = .ok props := by
  unfold EthCLSpecs.Gloas.processProposerLookahead at h
  rw [run_bind, show (get : GloasRun EthCLSpecs.Gloas.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok] at h
  simp only [] at h
  cases hq : EthCLSpecs.Gloas.getBeaconProposerIndices (pureState e)
      (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead +
        1) with
  | error err =>
    rw [run_bind, run_liftErr_of_error _ _ (by rw [hq]; rfl), except_bind_error] at h
    cases h
  | ok props => exact ⟨props, rfl⟩

omit [CryptoBackend] [Spec.PresetCfg.Bounds] hc in
/-- The epoch whose proposers the lookahead computes, `current + MIN_SEED_LOOKAHEAD + 1`, is
`current + 2` in the reference. -/
theorem lookahead_epoch_toNat (e : EtheoremState) (hslot : (toSpecState e).slot + 8192 < 2 ^ 64) :
    (EthCLSpecs.Gloas.currentEpochOf (pureState e) + EthCLSpecs.Gloas.Const.minSeedLookahead +
      1).toNat = (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 2 := by
  have hcur := currentEpochOf_toNat hp e
  have hm : EthCLSpecs.Gloas.Const.minSeedLookahead.toNat = 1 := by
    rw [hp.minSeedLookahead, Spec.P_min_seed]
  have h2 : (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Spec.P_ep_bound hslot 2 (by decide))
  have h1 : (toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_succ _) h2
  rw [UInt64.toNat_add, UInt64.toNat_add, hcur, hm, UInt64.toNat_one, Nat.mod_eq_of_lt h1]
  exact Nat.mod_eq_of_lt h2

forkonly Gloas
omit [CryptoBackend] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] hc in
/-- The reference proposer candidates are Etheorem's: active and not slashed. -/
theorem unslashedActive_eq (e : EtheoremState) (ep : UInt64) :
    Spec.unslashedActive (toSpecState e) ep.toNat =
      (proposerCandidates e ep).toList.map UInt64.toNat := by
  have hfil : (Spec.get_active_validator_indices (toSpecState e) ep.toNat).filterM
      (fun index => do pure !(← Spec.listGet (toSpecState e).validators index).slashed :
        Nat → Spec.SpecM Bool) = .ok (Spec.unslashedActive (toSpecState e) ep.toNat) := by
    apply Spec.tot_filterM
    intro j hj
    have hjl := Spec.active_lt _ _ j hj
    simp only [Spec.tot_get hjl, Spec.tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  rw [get_active_validator_indices_eq hp] at hfil
  have h2 := filterM_ok _ (fun idx => !(e.validators.val[idx]!).slashed) _ ?hf hfil
  case hf =>
    intro v _ b hb
    simp only [except_bind_eq_ok, except_pure_eq_ok] at hb
    obtain ⟨val, hval, rfl⟩ := hb
    simp only [toSpecState_validators] at hval
    obtain ⟨-, rfl⟩ := listGet_map_ok e.validators.val absValidator v hval
    rfl
  rw [h2, List.filter_map]
  simp [proposerCandidates, sszList_getElem!_val, Function.comp_def]

omit [CryptoBackend] in
/-- When Etheorem's proposer lookahead succeeds, the reference lookahead succeeds, and keeps the
fields that the PTC window reads. -/
theorem proposer_lookahead_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hf : Spec.SelFacts o (toSpecState e)) {r : Unit × EthCLSpecs.Gloas.State}
    (h : (EthCLSpecs.Gloas.processProposerLookahead (StateTransition := GloasRun)).run
      (pureState e) = .ok r) :
    Spec.OkWith (Spec.process_proposer_lookahead Spec.P o (toSpecState e)) (fun s' =>
      s'.slot = (toSpecState e).slot ∧ s'.validators = (toSpecState e).validators ∧
        s'.randao_mixes = (toSpecState e).randao_mixes ∧
        s'.ptc_window = (toSpecState e).ptc_window) := by
  obtain ⟨props, hprops⟩ := props_of_lookahead_run e h
  have hep := lookahead_epoch_toNat hp e hf.slot
  apply Spec.process_proposer_lookahead_total_of_sel o _ hf.slot hf.randao (lookahead_length hp e)
  rw [← hep, unslashedActive_eq hp]
  have hlen : (proposerCandidates e (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
      EthCLSpecs.Gloas.Const.minSeedLookahead + 1)).size ≤ 2 ^ 40 := by
    have h2 : (Spec.unslashedActive (toSpecState e) (EthCLSpecs.Gloas.currentEpochOf (pureState e) +
        EthCLSpecs.Gloas.Const.minSeedLookahead + 1).toNat).length ≤
        (toSpecState e).validators.length :=
      (List.length_filter_le _ _).trans (Spec.active_len_le _ _)
    rw [unslashedActive_eq hp] at h2
    simp only [List.length_map, Array.length_toList] at h2
    exact h2.trans hf.regLen
  exact proposerSelOk_of_etheorem hp hc o ho hsha e hf _
    (by
      rw [← unslashedActive_eq hp]
      exact fun x hx => List.mem_of_mem_filter hx)
    hlen (by rw [hep]; exact Spec.P_ep_start_bound hf.slot 2 (by decide)) hprops
end forkonly

forkonly Fulu
omit [CryptoBackend] in
/-- When Etheorem's proposer lookahead succeeds, the reference Fulu lookahead succeeds. -/
theorem proposer_lookahead_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hf : Spec.SelFacts o (toSpecState e)) {r : Unit × EthCLSpecs.Fulu.State}
    (h : (EthCLSpecs.Fulu.processProposerLookahead (StateTransition := FuluRun)).run
      (pureState e) = .ok r) :
    ∃ s', Spec.process_proposer_lookahead_fulu Spec.P o (toSpecState e) = .ok s' := by
  obtain ⟨props, hprops⟩ := props_of_lookahead_run e h
  have hep := lookahead_epoch_toNat hp e hf.slot
  apply Spec.process_proposer_lookahead_fulu_total_of_sel o _ hf.slot hf.randao (lookahead_length hp e)
  rw [← hep, get_active_validator_indices_eq hp]
  have hlen : (proposerCandidates e (EthCLSpecs.Fulu.currentEpochOf (pureState e) +
      EthCLSpecs.Fulu.Const.minSeedLookahead + 1)).size ≤ 2 ^ 40 := by
    have h1 := Spec.active_len_le (toSpecState e)
      (EthCLSpecs.Fulu.currentEpochOf (pureState e) + EthCLSpecs.Fulu.Const.minSeedLookahead +
        1).toNat
    rw [get_active_validator_indices_eq hp] at h1
    simp only [List.length_map, Array.length_toList] at h1
    exact h1.trans hf.regLen
  exact proposerSelOk_of_etheorem hp hc o ho hsha e hf _
    (by rw [get_active_validator_indices_eq hp]; exact List.Subset.refl _)
    hlen (by rw [hep]; exact Spec.P_ep_start_bound hf.slot 2 (by decide)) hprops
end forkonly

forkonly Gloas
omit [HasherTag] [CryptoBackend] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] hc in
/-- The PTC window of an Etheorem state has `3 * SLOTS_PER_EPOCH` items. -/
theorem ptc_window_length (e : EtheoremState) :
    (toSpecState e).ptc_window.length = 3 * Spec.P.SLOTS_PER_EPOCH := by
  simp [toSpecState_ptc_window, hp.slotsPerEpoch]

omit [CryptoBackend] [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] in
/-- The reference `ptcIndices` of `slot` are Etheorem's PTC candidates. -/
theorem ptcIndices_eq_candidates (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (e : EtheoremState) (slot : UInt64) {l : List Nat}
    (h : Spec.ptcIndices Spec.P o (toSpecState e) (EthCLSpecs.Gloas.computeEpochAtSlot slot).toNat
      slot.toNat = .ok l) :
    l = (ptcCandidates e slot).toList.map UInt64.toNat := by
  unfold Spec.ptcIndices at h
  simp only [except_bind_eq_ok] at h
  obtain ⟨cps, hcps, cands, hcands, h⟩ := h
  rw [except_pure_eq_ok] at h
  subst h
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
  rw [key, ptcCandidates, ← Array.foldl_toList, Array.toList_range]

omit [CryptoBackend] in
/-- When Etheorem's `compute_ptc` of `slot` succeeds, the reference PTC selection of `slot`
returns (`PtcSelOk`). -/
theorem ptcSelOk_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hf : Spec.SelFacts o (toSpecState e)) (slot : UInt64)
    (hslot : slot.toNat / Spec.P.SLOTS_PER_EPOCH + Spec.P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    {v : Vector UInt64 EthCLSpecs.Gloas.Const.ptcSize}
    (h : EthCLSpecs.Gloas.computePtc (pureState e) slot = .ok v) :
    Spec.PtcSelOk o (toSpecState e) slot.toNat := by
  intro seed hseed l hl
  have hep : (EthCLSpecs.Gloas.computeEpochAtSlot slot).toNat =
      slot.toNat / Spec.P.SLOTS_PER_EPOCH := by
    have h1 := compute_epoch_at_slot_eq hp slot
    unfold Spec.compute_epoch_at_slot at h1
    rw [Spec.tot_div Spec.P_slots_ne] at h1
    exact (Except.ok.inj h1).symm
  have hn := (Spec.active_len_le (toSpecState e) (slot.toNat / Spec.P.SLOTS_PER_EPOCH)).trans
    hf.regLen
  obtain ⟨l2, hl2, hlen2, hmem2⟩ := Spec.ptcIndices_total o (toSpecState e) slot.toNat hslot
    hf.randao hn
  rw [hl2] at hl
  cases hl
  rw [← hep] at hseed hl2
  have hseed' := get_seed_ok hp o ho e _ _ EthCLSpecs.Gloas.Const.domainPtcAttester rfl hseed
  subst hseed'
  have hl' := ptcIndices_eq_candidates hp hc o ho e slot hl2
  have hseed2 : o.hash ((EthCLSpecs.Gloas.getSeed (pureState e)
      (EthCLSpecs.Gloas.computeEpochAtSlot slot) EthCLSpecs.Gloas.Const.domainPtcAttester).toList ++
        Spec.uint_to_bytes 8 slot.toNat) = bytesToRoot (ptcSeed e slot) := by
    have hba : toBA ((EthCLSpecs.Gloas.getSeed (pureState e)
        (EthCLSpecs.Gloas.computeEpochAtSlot slot) EthCLSpecs.Gloas.Const.domainPtcAttester).toList ++
          Spec.uint_to_bytes 8 slot.toNat) =
        vecToBytes (EthCLSpecs.Gloas.getSeed (pureState e) (EthCLSpecs.Gloas.computeEpochAtSlot slot)
          EthCLSpecs.Gloas.Const.domainPtcAttester) ++ uint64ToBytes slot := by
      apply ba_eq_of_toList
      rw [toBA_data, append_data_toList, vecToBytes_toList, uint_to_bytes_8]
    rw [hash_eq o ho, hba]
    rfl
  have h' : (do
      let sel ← EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
        (ptcCandidates e slot) (ptcSeed e slot) EthCLSpecs.Gloas.Const.ptcSize false
      return Vector.ofFn fun i : Fin EthCLSpecs.Gloas.Const.ptcSize => sel[i.val]!) =
      Except.ok v := by
    unfold EthCLSpecs.Gloas.computePtc at h
    exact h
  cases hcb : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (ptcCandidates e slot) (ptcSeed e slot) EthCLSpecs.Gloas.Const.ptcSize false with
  | error err => rw [hcb, except_bind_error] at h'; cases h'
  | ok sel =>
  have hcb' : EthCLSpecs.Gloas.computeBalanceWeightedSelection (pureState e)
      (ptcCandidates e slot) (vecToBytes (bytesToRoot (ptcSeed e slot))) Spec.P.PTC_SIZE false =
      .ok sel := by
    rw [vecToBytes_bytesToRoot (ptcSeed e slot) (hsha _), ← hc.ptcSize]; exact hcb
  rw [hseed2, hl']
  have hk : slot.toNat % Spec.P.SLOTS_PER_EPOCH < Spec.P.SLOTS_PER_EPOCH :=
    Nat.mod_lt _ Spec.P_slots_pos
  refine selOk_of_etheorem Spec.P o ho hc e _ _ _ false ?_
    (by rw [Spec.P_maxeb]; exact hf.ebMax) ?_ Spec.P_shuffle_le (by rw [Spec.P_maxeb]; decide)
    hcb'
  · rw [← hl']
    intro j hj
    exact Spec.active_lt _ _ j (hmem2 j hj)
  · have h3 := Spec.ptc_len_le
      (Spec.get_active_validator_indices (toSpecState e) (slot.toNat / Spec.P.SLOTS_PER_EPOCH)).length
      _ _ Spec.P_slots_pos hk
    rw [← hlen2, hl'] at h3
    simp only [List.length_map, Array.length_toList] at h3
    exact h3.trans hn

omit [CryptoBackend] in
/-- When Etheorem's PTC window step succeeds, the reference step succeeds. -/
theorem ptc_window_of_etheorem (o : Spec.Oracle) (ho : ∀ d, o.hash d = etheoremHash d)
    (hsha : ∀ b : ByteArray, (sha b).size = 32) (e : EtheoremState)
    (hf : Spec.SelFacts o (toSpecState e)) {r : Unit × EthCLSpecs.Gloas.State}
    (h : (EthCLSpecs.Gloas.processPtcWindow (StateTransition := GloasRun)).run (pureState e) =
      .ok r) :
    Spec.OkWith (Spec.process_ptc_window Spec.P o (toSpecState e)) (fun _ => True) := by
  apply Spec.process_ptc_window_total_of_sel o _ hf.slot hf.randao hf.regLen (ptc_window_length hp e)
  intro slot hslotE
  unfold EthCLSpecs.Gloas.processPtcWindow at h
  rw [run_bind, show (get : GloasRun EthCLSpecs.Gloas.State).run (pureState e) =
    .ok (pureState e, pureState e) from rfl, except_bind_ok] at h
  simp only [] at h
  cases hm : (Array.range EthCLSpecs.Gloas.Const.slotsPerEpoch).mapM
      (fun i => EthCLSpecs.Gloas.computePtc (pureState e) (ptcStartSlot e + UInt64.ofNat i)) with
  | error err =>
    rw [run_bind, run_liftErr_of_error _ _ (by rw [ptcStartSlot] at hm; rw [hm]; rfl),
      except_bind_error] at h
    cases h
  | ok fresh =>
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hm
  simp only [except_map_eq_ok] at hm
  obtain ⟨cs, hcs, -⟩ := hm
  have hS := Spec.P_slots_pos
  have hj : slot % Spec.P.SLOTS_PER_EPOCH < EthCLSpecs.Gloas.Const.slotsPerEpoch := by
    rw [hp.slotsPerEpoch]; exact Nat.mod_lt _ hS
  obtain ⟨v, hv⟩ := mapM_ok_mem hcs _ (List.mem_range.mpr hj)
  have hep := lookahead_epoch_toNat hp e hf.slot
  have hst := Spec.P_ep_start_bound hf.slot 2 (by decide)
  have hstartN : (ptcStartSlot e).toNat =
      ((toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 2) * Spec.P.SLOTS_PER_EPOCH := by
    unfold ptcStartSlot
    apply compute_start_slot_at_epoch_ok hp
    rw [hep]
    unfold Spec.compute_start_slot_at_epoch
    exact Spec.tot_mul (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hst)
  have hslotU : (ptcStartSlot e + UInt64.ofNat (slot % Spec.P.SLOTS_PER_EPOCH)).toNat = slot := by
    have hdm := Nat.div_add_mod slot Spec.P.SLOTS_PER_EPOCH
    rw [hslotE] at hdm
    have hmS := Nat.mod_lt slot hS
    have hlt : ((toSpecState e).slot / Spec.P.SLOTS_PER_EPOCH + 2) * Spec.P.SLOTS_PER_EPOCH +
        slot % Spec.P.SLOTS_PER_EPOCH < 2 ^ 64 :=
      Nat.lt_trans (Nat.add_lt_add_left hmS _) hst
    rw [UInt64.toNat_add, hstartN, UInt64.toNat_ofNat_of_lt'
      (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt, Nat.mul_comm]
    exact hdm
  have h1 := ptcSelOk_of_etheorem hp hc o ho hsha e hf _
    (by rw [hslotU, hslotE]; exact Spec.P_ep_bound hf.slot 2 (by decide)) hv
  rw [hslotU] at h1
  exact h1
end forkonly

end Converse

end forkproof
