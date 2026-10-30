import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Sanity.Invariants.TotalityFulu

/-!
# The committee steps succeed when their selections do

`TotalityCommittees.lean` and `TotalityFulu.lean` prove that the committee steps succeed from the
pyspec preconditions (`CommitteeStepPreconds`: a candidate for each selection, at least
`SLOTS_PER_EPOCH` active validators for the PTC, and selections that end within `2^64` passes).
Each precondition is there for one reason: so that each balance weighted selection that the step
runs returns.

The theorems here take that directly. `SelOk` says that one selection returns at least `size`
items, all of them candidates. Each theorem asks `SelOk` only for the selections that the step
runs, with the seeds that it computes. With that and the state facts (`CommFacts`), the step
succeeds. `AgreesEtheorem/Committees.lean` proves the `SelOk` facts from a successful Etheorem
step (`selOk_of_etheorem`), so the pyspec preconditions are not needed there.

The proofs are those of `TotalityCommittees.lean` with `compute_balance_weighted_selection_total`
replaced by the `SelOk` hypothesis.
-/

namespace EpochProofs.Spec

/-- The reference selection over `indices` returns at least `size` items, each one of
`indices`. -/
def SelOk (p : Preset) (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffle : Bool) : Prop :=
  ∃ r, compute_balance_weighted_selection p o s indices seed size shuffle = .ok r ∧
    size ≤ r.length ∧ ∀ x ∈ r, x ∈ indices

/-- `SelOk` reads the state only through its validators. -/
theorem SelOk.congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) {indices : List ValidatorIndex} {seed : Bytes32}
    {size : Nat} {shuffle : Bool} (h : SelOk p o s2 indices seed size shuffle) :
    SelOk p o s1 indices seed size shuffle := by
  obtain ⟨r, hr, h1, h2⟩ := h
  refine ⟨r, ?_, h1, h2⟩
  unfold compute_balance_weighted_selection at hr ⊢
  rw [hv]
  exact hr

/-- The state facts that the committee steps read and Etheorem does not check. The reference
raises without them where Etheorem does not: `eth_aggregate_pubkeys` asserts `KeyValidate` on
each key, and the reference checks the `uint64` products and the shuffle arithmetic that Etheorem
computes in `Nat`. Each holds on reachable states: the slot is far from `2^64`, the RANDAO vector
has its SSZ length, the registry limit is `2^40`, the effective balance is at most
`MAX_EFFECTIVE_BALANCE_ELECTRA` (`EBOk`), and a deposit adds a validator only after its signature
checks. `CommFacts` without the two vector lengths, which hold on every Etheorem state. -/
structure SelFacts [PresetCfg] (o : Oracle) (s : BeaconState) : Prop where
  slot : s.slot + 8192 < 2 ^ 64
  randao : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR
  regLen : s.validators.length ≤ 2 ^ 40
  ebMax : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000
  keys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true

/-- The part of `SelFacts` that the epoch steps before the committee steps do not give: the
registry limit `2^40`, effective balances of at most `MAX_EFFECTIVE_BALANCE_ELECTRA` (2048 ETH),
and valid public keys. Each is an invariant of reachable states that this project does not yet
carry to the committee steps. -/
structure SelectionStateFacts (o : Oracle) (s : BeaconState) : Prop where
  regLen : s.validators.length ≤ 2 ^ 40
  ebMax : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000
  keys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true

/-- `SelFacts` at the state `s` that the epoch passes to the committee steps, from the epoch
input `t`: the slot and RANDAO length come from `CommFrame`. -/
theorem SelFacts.of_frame [PresetCfg] {o : Oracle} {t s : BeaconState} (hfr : CommFrame t s)
    (hslot : t.slot + 8192 < 2 ^ 64) (h : SelectionStateFacts o s) : SelFacts o s :=
  ⟨hfr.slot ▸ hslot, hfr.randao, h.regLen, h.ebMax, h.keys⟩

/-- `SelFacts` reads the slot, the RANDAO mixes and the validators. -/
theorem SelFacts.congr [PresetCfg] {o : Oracle} {s1 s2 : BeaconState} (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes)
    (h : SelFacts o s2) : SelFacts o s1 :=
  ⟨hs ▸ h.slot, hr ▸ h.randao, hv ▸ h.regLen, hv ▸ h.ebMax, hv ▸ h.keys⟩

variable [PresetCfg] [PresetCfg.Ok] [PresetCfg.Bounds]

/-! ## Sync committee -/

/-- The sync committee selection at `s`: the selection over the validators active at the next
epoch, with the sync committee seed of that epoch. -/
def SyncSelOk (o : Oracle) (s : BeaconState) : Prop :=
  ∀ seed, get_seed P o s (s.slot / P.SLOTS_PER_EPOCH + 1) DOMAIN_SYNC_COMMITTEE = .ok seed →
    SelOk P o s (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 1)) seed
      P.SYNC_COMMITTEE_SIZE true

omit [PresetCfg.Ok] [PresetCfg.Bounds] in
theorem SyncSelOk.congr {o : Oracle} {s1 s2 : BeaconState} (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes)
    (h : SyncSelOk o s2) : SyncSelOk o s1 := by
  intro seed hseed
  rw [get_seed_congr hr, hs] at hseed
  rw [get_active_validator_indices_congr hv, hs]
  exact SelOk.congr hv (h seed hseed)

omit [PresetCfg.Bounds] in
/-- `get_next_sync_committee_total` with the sync committee selection as a hypothesis. -/
theorem get_next_sync_committee_total_of_sel (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hkeys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true)
    (hsel : SyncSelOk o s) :
    ∃ c, get_next_sync_committee P o s = .ok c := by
  have he : s.slot / P.SLOTS_PER_EPOCH + 1 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 :=
    P_ep_bound hslot 1 (by decide)
  obtain ⟨seed, hseed⟩ := get_seed_total o s (s.slot / P.SLOTS_PER_EPOCH + 1)
    DOMAIN_SYNC_COMMITTEE he hr
  have hsz := P_sync_pos (h := inferInstance)
  obtain ⟨r, hr1, hr2, hr3⟩ := hsel seed hseed
  have hrl : ∀ j ∈ r, j < s.validators.length := fun j hj => active_lt s _ j (hr3 j hj)
  have hpk : r.mapM (fun index => do pure (← listGet s.validators index).pubkey :
      ValidatorIndex → SpecM BLSPubkey) =
      .ok (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero) := by
    apply tot_mapM
    intro j hj
    have hjl := hrl j hj
    simp only [tot_get hjl, tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  have hagg : eth_aggregate_pubkeys o
      (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero) =
      .ok (o.bls_AggregatePKs
        (r.map fun j => (s.validators[j]?.map (·.pubkey)).getD BLSPubkey.zero)) := by
    unfold eth_aggregate_pubkeys
    rw [if_neg (by rw [List.length_map]; exact fun h => h (by omega))]
    rw [if_neg (by
      simp only [List.all_eq_true, List.mem_map, Bool.not_eq_true, not_forall, not_exists]
      intro x ⟨j, hj, hx⟩
      subst hx
      have hjl := hrl j hj
      simp only [List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some]
      rw [hkeys _ (List.getElem_mem hjl)]
      simp)]
    rfl
  unfold get_next_sync_committee get_next_sync_committee_indices
  rw [tot_current_epoch, tot_bind_ok, tot_add (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) he),
    tot_bind_ok, hseed, tot_bind_ok]
  simp only [hr1, tot_bind_ok, hpk, hagg]
  exact ⟨_, rfl⟩

/-- `process_sync_committee_updates_total` with the sync committee selection as a hypothesis,
asked only at a sync committee period boundary, where the step selects. -/
theorem process_sync_committee_updates_total_of_sel (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hkeys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true)
    (hsel : (s.slot / P.SLOTS_PER_EPOCH + 1) % P.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      SyncSelOk o s) :
    OkWith (process_sync_committee_updates P o s) (fun s' =>
      s'.slot = s.slot ∧ s'.validators = s.validators ∧ s'.randao_mixes = s.randao_mixes ∧
        s'.proposer_lookahead = s.proposer_lookahead ∧ s'.ptc_window = s.ptc_window) := by
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  unfold process_sync_committee_updates
  rw [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_bind_ok,
    tot_mod P_sync_period_ne, tot_bind_ok]
  split
  · rename_i hz
    obtain ⟨c, hc⟩ := get_next_sync_committee_total_of_sel o
      { s with current_sync_committee := s.next_sync_committee } hslot hr hkeys
      (SyncSelOk.congr rfl rfl rfl (hsel (by simpa using hz)))
    dsimp only
    rw [hc, tot_bind_ok]
    exact OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact OkWith.pure ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Proposers -/

/-- The proposer selections of epoch `e` over the candidates `indices`: one selection of one
item for each slot of the epoch, with the slot's seed. -/
def ProposerSelOk (o : Oracle) (s : BeaconState) (e : Nat) (indices : List ValidatorIndex) :
    Prop :=
  ∀ seed, get_seed P o s e DOMAIN_BEACON_PROPOSER = .ok seed → ∀ i < P.SLOTS_PER_EPOCH,
    SelOk P o s indices (o.hash (seed.toList ++ uint_to_bytes 8 (e * P.SLOTS_PER_EPOCH + i))) 1
      true

omit [PresetCfg.Ok] [PresetCfg.Bounds] in
theorem ProposerSelOk.congr {o : Oracle} {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) (hr : s1.randao_mixes = s2.randao_mixes) {e : Nat}
    {indices : List ValidatorIndex} (h : ProposerSelOk o s2 e indices) :
    ProposerSelOk o s1 e indices := by
  intro seed hseed i hi
  rw [get_seed_congr hr] at hseed
  exact SelOk.congr hv (h seed hseed i hi)

omit [PresetCfg.Ok] [PresetCfg.Bounds] in
/-- `compute_proposer_indices` succeeds when each of its selections does. -/
theorem compute_proposer_indices_total_of_sel (o : Oracle) (s : BeaconState) (e : Nat)
    (seed : Bytes32) (indices : List ValidatorIndex)
    (hstart : e * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64)
    (hsel : ∀ i < P.SLOTS_PER_EPOCH,
      SelOk P o s indices (o.hash (seed.toList ++ uint_to_bytes 8 (e * P.SLOTS_PER_EPOCH + i))) 1
        true) :
    ∃ r, compute_proposer_indices P o s e seed indices = .ok r := by
  unfold compute_proposer_indices compute_start_slot_at_epoch
  rw [tot_mul (show e * P.SLOTS_PER_EPOCH < 2 ^ 64 by omega), tot_bind_ok]
  have hseeds := tot_mapM (fun i => do
      pure (o.hash (seed.toList ++ uint_to_bytes 8 (← uint64Add (e * P.SLOTS_PER_EPOCH) i))) :
        Nat → SpecM Bytes32)
    (fun i => o.hash (seed.toList ++ uint_to_bytes 8 (e * P.SLOTS_PER_EPOCH + i)))
    (List.range P.SLOTS_PER_EPOCH) (by
      intro i hi
      rw [List.mem_range] at hi
      rw [tot_add (show e * P.SLOTS_PER_EPOCH + i < 2 ^ 64 by omega), tot_bind_ok]
      rfl)
  rw [hseeds, tot_bind_ok]
  apply tot_mapM_ex
  intro sd hsd
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsd
  obtain ⟨r, hr1, hr2, -⟩ := hsel i (List.mem_range.mp hi)
  rw [hr1, tot_bind_ok, tot_get (show 0 < r.length by omega)]
  exact ⟨_, rfl⟩

omit [PresetCfg.Bounds] in
/-- `get_beacon_proposer_indices_total` with the proposer selections as a hypothesis. -/
theorem get_beacon_proposer_indices_total_of_sel (o : Oracle) (s : BeaconState) (e : Nat)
    (he : e + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hstart : e * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hsel : ProposerSelOk o s e (unslashedActive s e)) :
    ∃ r, get_beacon_proposer_indices P o s e = .ok r := by
  have hfil : (get_active_validator_indices s e).filterM (fun index => do
      pure !(← listGet s.validators index).slashed : ValidatorIndex → SpecM Bool) =
      .ok (unslashedActive s e) := by
    apply tot_filterM
    intro j hj
    have hjl := active_lt s e j hj
    simp only [tot_get hjl, tot_bind_ok, List.getElem?_eq_getElem hjl, Option.map_some,
      Option.getD_some]
    rfl
  obtain ⟨seed, hseed⟩ := get_seed_total o s e DOMAIN_BEACON_PROPOSER he hr
  obtain ⟨r, hr1⟩ := compute_proposer_indices_total_of_sel o s e seed _ hstart (hsel seed hseed)
  unfold get_beacon_proposer_indices
  rw [hfil, tot_bind_ok, hseed, tot_bind_ok]
  exact ⟨r, hr1⟩

/-- `process_proposer_lookahead_total` with the proposer selections as a hypothesis. -/
theorem process_proposer_lookahead_total_of_sel (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hlen : s.proposer_lookahead.length = 2 * P.SLOTS_PER_EPOCH)
    (hsel : ProposerSelOk o s (s.slot / P.SLOTS_PER_EPOCH + 2)
      (unslashedActive s (s.slot / P.SLOTS_PER_EPOCH + 2))) :
    OkWith (process_proposer_lookahead P o s) (fun s' =>
      s'.slot = s.slot ∧ s'.validators = s.validators ∧ s'.randao_mixes = s.randao_mixes ∧
        s'.ptc_window = s.ptc_window) := by
  have he : s.slot / P.SLOTS_PER_EPOCH + 2 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 :=
    P_ep_bound hslot 2 (by decide)
  obtain ⟨r, hr1⟩ := get_beacon_proposer_indices_total_of_sel o
    { s with proposer_lookahead := s.proposer_lookahead.drop P.SLOTS_PER_EPOCH ++
      s.proposer_lookahead.drop (2 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) }
    (s.slot / P.SLOTS_PER_EPOCH + 2) he (P_ep_start_bound hslot 2 (by decide)) hr
    (ProposerSelOk.congr rfl rfl hsel)
  unfold process_proposer_lookahead
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.proposer_lookahead.length by omega), tot_bind_ok]
  rw [hlen]
  dsimp only
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
    rw [Nat.add_assoc], hr1, tot_bind_ok]
  exact OkWith.pure ⟨rfl, rfl, rfl, rfl⟩

omit [PresetCfg.Bounds] in
/-- `get_beacon_proposer_indices_fulu_total` with the proposer selections as a hypothesis. The
Fulu candidates are all active validators. -/
theorem get_beacon_proposer_indices_fulu_total_of_sel (o : Oracle) (s : BeaconState) (e : Nat)
    (he : e + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hstart : e * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hsel : ProposerSelOk o s e (get_active_validator_indices s e)) :
    ∃ r, get_beacon_proposer_indices_fulu P o s e = .ok r := by
  obtain ⟨seed, hseed⟩ := get_seed_total o s e DOMAIN_BEACON_PROPOSER he hr
  have hin : ∀ j ∈ get_active_validator_indices s e, j < s.validators.length :=
    fun j hj => active_lt s e j hj
  obtain ⟨r, hr1⟩ := compute_proposer_indices_total_of_sel o s e seed _ hstart (hsel seed hseed)
  unfold get_beacon_proposer_indices_fulu
  rw [hseed, tot_bind_ok]
  exact ⟨r, compute_proposer_indices_ok_fulu P o s e seed _ hin r hr1⟩

/-- `process_proposer_lookahead_fulu_total` with the proposer selections as a hypothesis. -/
theorem process_proposer_lookahead_fulu_total_of_sel (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hlen : s.proposer_lookahead.length = 2 * P.SLOTS_PER_EPOCH)
    (hsel : ProposerSelOk o s (s.slot / P.SLOTS_PER_EPOCH + 2)
      (get_active_validator_indices s (s.slot / P.SLOTS_PER_EPOCH + 2))) :
    ∃ s', process_proposer_lookahead_fulu P o s = .ok s' := by
  have he : s.slot / P.SLOTS_PER_EPOCH + 2 + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64 :=
    P_ep_bound hslot 2 (by decide)
  obtain ⟨r, hr1⟩ := get_beacon_proposer_indices_fulu_total_of_sel o
    { s with proposer_lookahead := s.proposer_lookahead.drop P.SLOTS_PER_EPOCH ++
      s.proposer_lookahead.drop (2 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) }
    (s.slot / P.SLOTS_PER_EPOCH + 2) he (P_ep_start_bound hslot 2 (by decide)) hr
    (ProposerSelOk.congr rfl rfl hsel)
  unfold process_proposer_lookahead_fulu
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.proposer_lookahead.length by omega), tot_bind_ok]
  rw [hlen]
  dsimp only
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
    rw [Nat.add_assoc], hr1, tot_bind_ok]
  exact ⟨_, rfl⟩

/-! ## PTC window -/

/-- The PTC selection of `slot`: the selection over the slot's beacon committees, joined, with
the PTC seed of the slot. -/
def PtcSelOk (o : Oracle) (s : BeaconState) (slot : Nat) : Prop :=
  ∀ seed, get_seed P o s (slot / P.SLOTS_PER_EPOCH) DOMAIN_PTC_ATTESTER = .ok seed → ∀ l,
    ptcIndices P o s (slot / P.SLOTS_PER_EPOCH) slot = .ok l →
      SelOk P o s l (o.hash (seed.toList ++ uint_to_bytes 8 slot)) P.PTC_SIZE false

omit [PresetCfg.Ok] [PresetCfg.Bounds] in
theorem PtcSelOk.congr {o : Oracle} {s1 s2 : BeaconState} (hv : s1.validators = s2.validators)
    (hr : s1.randao_mixes = s2.randao_mixes) {slot : Nat} (h : PtcSelOk o s2 slot) :
    PtcSelOk o s1 slot := by
  intro seed hseed l hl
  rw [get_seed_congr hr] at hseed
  rw [ptcIndices_congr o hv hr] at hl
  exact SelOk.congr hv (h seed hseed l hl)

/-- `compute_ptc_total` with the PTC selection as a hypothesis. -/
theorem compute_ptc_total_of_sel (o : Oracle) (s : BeaconState) (slot : Nat)
    (hslot : slot / P.SLOTS_PER_EPOCH + P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64)
    (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hn40 : s.validators.length ≤ 2 ^ 40) (hsel : PtcSelOk o s slot) :
    ∃ r, compute_ptc P o s slot = .ok r := by
  have hn := (active_len_le s (slot / P.SLOTS_PER_EPOCH)).trans hn40
  obtain ⟨seed, hseed⟩ := get_seed_total o s (slot / P.SLOTS_PER_EPOCH) DOMAIN_PTC_ATTESTER
    hslot hr
  obtain ⟨l, hl1, -, -⟩ := ptcIndices_total o s slot hslot hr hn
  obtain ⟨r, hr1, -, -⟩ := hsel seed hseed l hl1
  refine ⟨r, ?_⟩
  rw [compute_ptc_eq]
  unfold compute_epoch_at_slot
  rw [tot_div P_slots_ne, tot_bind_ok]
  rw [hseed, tot_bind_ok, hl1, tot_bind_ok]
  exact hr1

/-- `process_ptc_window_total` with the PTC selections of the epoch that it fills as a
hypothesis. Without F12 (at least `SLOTS_PER_EPOCH` active validators), the first of these
selections has no candidate, so the hypothesis fails there, as the pyspec does. -/
theorem process_ptc_window_total_of_sel (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = P.EPOCHS_PER_HISTORICAL_VECTOR)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (hlen : s.ptc_window.length = 3 * P.SLOTS_PER_EPOCH)
    (hsel : ∀ slot, slot / P.SLOTS_PER_EPOCH = s.slot / P.SLOTS_PER_EPOCH + 2 →
      PtcSelOk o s slot) :
    OkWith (process_ptc_window P o s) (fun _ => True) := by
  have ha1 : s.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 1 (by decide))
  have ha2 : s.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (P_ep_bound hslot 2 (by decide))
  have hst := P_ep_start_bound hslot 2 (by decide)
  unfold process_ptc_window compute_start_slot_at_epoch
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h1, tot_sub (show P.SLOTS_PER_EPOCH ≤ s.ptc_window.length by omega), tot_bind_ok, hlen]
  dsimp only
  simp only [tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / P.SLOTS_PER_EPOCH + 1 + 1 = s.slot / P.SLOTS_PER_EPOCH + 2 by
      rw [Nat.add_assoc],
    tot_mul (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hst), tot_bind_ok,
    tot_add hst, tot_bind_ok, Nat.add_sub_cancel_left]
  obtain ⟨ptcs, hptcs⟩ := tot_mapM_ex (fun slot =>
      compute_ptc P o
        { s with ptc_window := List.drop P.SLOTS_PER_EPOCH s.ptc_window ++
          List.drop (3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH) s.ptc_window } slot)
    (List.range' ((s.slot / P.SLOTS_PER_EPOCH + 2) * P.SLOTS_PER_EPOCH) P.SLOTS_PER_EPOCH) (by
      intro slot hslot'
      rw [List.mem_range'] at hslot'
      obtain ⟨j, hj, rfl⟩ := hslot'
      rw [Nat.one_mul]
      have hdiv := slot_div_window (a := s.slot / P.SLOTS_PER_EPOCH + 2) P_slots_pos hj
      exact compute_ptc_total_of_sel o _ _ (by rw [hdiv]; exact P_ep_bound hslot 2 (by decide))
        hr hreg (PtcSelOk.congr rfl rfl (hsel _ hdiv)))
  rw [hptcs, tot_bind_ok]
  simp only [List.length_append, List.length_drop, hlen]
  rw [tot_sub (show P.SLOTS_PER_EPOCH ≤ 3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH +
    (3 * P.SLOTS_PER_EPOCH - (3 * P.SLOTS_PER_EPOCH - P.SLOTS_PER_EPOCH)) by omega), tot_bind_ok]
  exact OkWith.pure trivial

end EpochProofs.Spec
