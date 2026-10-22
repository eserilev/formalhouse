import EpochProofs.Sanity.Invariants.TotalityCommittees
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluCfg
import EpochProofs.Sanity.Invariants.TotalityRows
import EpochProofs.Sanity.Invariants.LighthouseFulu

/-!
# Totality of the Fulu epoch

`process_epoch_fulu_total` shows that the Fulu spec `process_epoch` returns `ok` on mainnet, from
the same state facts as the Gloas `process_epoch_total_rows`. Most steps are the Gloas steps.
The differences:

- The registry update and the pending deposits run at the churn total `fuluTabM tab`
  (`MidCore`, `DepCore` with `g = fuluTabM`).
- No builder payments and no PTC window.
- The sync committee update is the Electra loop. It gives the same `ok` results as the Gloas
  selection (`process_sync_committee_updates_fulu_sameOk`).
- The proposer lookahead draws from every active validator, with no slashed filter, and runs the
  Electra loop. A Gloas selection that returns gives the same proposers
  (`compute_proposer_indices_ok_fulu`).

The pyspec preconditions of the Fulu committee steps are weaker than the Gloas ones
(`FuluCommPreconds`): some validator is active at `current + 2`, slashed or not, and the PTC
needs nothing, because Fulu has no PTC. So Fulu has no counterpart of F12: a Fulu chain with
fewer than `SLOTS_PER_EPOCH` active validators does not halt at the epoch boundary.
-/

namespace EpochProofs.Spec

/-! ## Vector lengths -/

/-- The SSZ vector lengths of the Fulu `BeaconState`: `VectorLengths` without the Gloas fields
(execution payload availability, builder pending payments, PTC window). -/
def BeaconState.FuluVectorLengths (p : Preset) (state : BeaconState) : Prop :=
  state.block_roots.length = p.SLOTS_PER_HISTORICAL_ROOT ∧
  state.state_roots.length = p.SLOTS_PER_HISTORICAL_ROOT ∧
  state.randao_mixes.length = p.EPOCHS_PER_HISTORICAL_VECTOR ∧
  state.slashings.length = p.EPOCHS_PER_SLASHINGS_VECTOR ∧
  state.justification_bits.length = JUSTIFICATION_BITS_LENGTH ∧
  state.current_sync_committee.pubkeys.length = p.SYNC_COMMITTEE_SIZE ∧
  state.next_sync_committee.pubkeys.length = p.SYNC_COMMITTEE_SIZE ∧
  state.proposer_lookahead.length = (p.MIN_SEED_LOOKAHEAD + 1) * p.SLOTS_PER_EPOCH

/-! ## Churn total -/

theorem fuluTabM_lt [PresetCfg] [FuluCfg] (x : Gwei) (hx : x < 2 ^ 57) : fuluTabM x < 2 ^ 60 := by
  unfold fuluTabM fuluTab
  have h : @LE.le Nat _ (min (x / 2) (FC.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT *
      P.CHURN_LIMIT_QUOTIENT_GLOAS)) (x / 2) := Nat.min_le_left _ _
  have hx' : @LT.lt Nat _ x (2 ^ 57) := hx
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (Nat.div_le_self _ _))
    (Nat.lt_trans hx' (by decide))

/-! ## The four per-validator steps -/

/-- The Fulu inactivity, rewards, registry and slashings steps succeed after justification and
finalization. -/
def MidOkFulu (t : BeaconState) : Prop :=
  ∀ s1, JFShape t s1 → s1.finalized_checkpoint.epoch ≤ t.slot / 32 →
    (t.slot / 32 ≠ 0 → s1.finalized_checkpoint.epoch + 1 ≤ t.slot / 32) →
    OkWith (specFourStepsFulu s1) (fun s => TailFrame t s ∧ DepFrame t s)

theorem midOkFulu_of_rowBounds [PresetCfg] [PresetCfg.Ok] (t : BeaconState) (hrows : RowsOk t)
    (hslot : t.slot + 8192 < 2 ^ 64) (heb : EBOk P t)
    (hrl : t.randao_mixes.length = 65536) (hsll : t.slashings.length = 8192)
    (hcons : ConsolidationsInRange t) (hsl : t.slashings.sum * 3 < 2 ^ 64) (hrb : RowBounds t) :
    MidOkFulu t := by
  intro s1 hshape hfin0 hfin
  have hcore := midCore_of_rowBounds fuluTabM fuluTabM_lt t hrows hslot heb hrl hsll hcons hsl
    hrb s1 hshape hfin0 hfin
  obtain ⟨cp1, cp2, cp3, bits, hs1⟩ := hshape
  have hrows1 : RowsOk s1 := by rw [hs1]; exact hrows
  have hslot1 : s1.slot = t.slot := by rw [hs1]
  have hteb1 : totalEffectiveBalance s1 = totalEffectiveBalance t := by rw [hs1]; rfl
  have hslot' : @LT.lt Nat _ (t.slot + 8192) (2 ^ 64) := hslot
  have hcur : get_current_epoch P s1 = .ok (t.slot / 32) := by
    rw [← hslot1]; exact tot_current_epoch s1
  obtain ⟨tab, htab, -, -⟩ := get_total_active_balance_bounds P s1
    (t.slot / 32) hcur (by rw [hteb1]; exact Nat.lt_trans hrb.supply (by decide))
  have hact := compute_activation_exit_epoch_of_lt P (t.slot / 32)
    (by show @LT.lt Nat _ (t.slot / 32 + 1 + 4) (2 ^ 64); omega)
  have hfar : t.slot / 32 < FAR_FUTURE_EPOCH := by
    show @LT.lt Nat _ (t.slot / 32) (2 ^ 64 - 1); omega
  have hsame := specFourStepsFulu_sameOk s1 tab htab hrows1 (t.slot / 32) _ hcur hact hfar
  obtain ⟨v, hv, hp⟩ := hcore tab htab
  exact ⟨v, (hsame v).mpr hv, hp⟩

/-! ## The committee steps -/

theorem compute_proposer_indices_total [PresetCfg] (o : Oracle) (s : BeaconState) (e : Nat) (seed : Bytes32)
    (indices : List ValidatorIndex) (hstart : e * 32 + 32 < 2 ^ 64) (hne : indices ≠ [])
    (hin : ∀ j ∈ indices, j < s.validators.length)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hlen : indices.length ≤ 2 ^ 40)
    (hsel : ∀ sd, SelFin P o s indices sd 1 true) :
    ∃ r, compute_proposer_indices P o s e seed indices = .ok r := by
  unfold compute_proposer_indices compute_start_slot_at_epoch
  have h32 : (P).SLOTS_PER_EPOCH = 32 := rfl
  rw [h32, tot_mul (show e * 32 < 2 ^ 64 by omega), tot_bind_ok]
  obtain ⟨seeds, hseeds⟩ := tot_mapM_ex (fun i => do
      pure (o.hash (seed.toList ++ uint_to_bytes 8 (← uint64Add (e * 32) i))) : Nat → SpecM Bytes32)
    (List.range 32) (by
      intro i hi
      rw [List.mem_range] at hi
      rw [tot_add (show e * 32 + i < 2 ^ 64 by omega), tot_bind_ok]
      exact ⟨_, rfl⟩)
  rw [hseeds, tot_bind_ok]
  apply tot_mapM_ex
  intro sd _
  obtain ⟨r, hr1, hr2, -⟩ := compute_balance_weighted_selection_total P o s
    indices sd 1 true hne hin heb hlen (by decide) (by decide) (hsel sd)
  rw [hr1, tot_bind_ok, tot_get (show 0 < r.length by omega)]
  exact ⟨_, rfl⟩

theorem get_beacon_proposer_indices_fulu_total [PresetCfg] (o : Oracle) (s : BeaconState) (e : Nat)
    (he : e + 65536 < 2 ^ 64) (hstart : e * 32 + 32 < 2 ^ 64)
    (hr : s.randao_mixes.length = 65536)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hne : get_active_validator_indices s e ≠ [])
    (hsel : ∀ seed, SelFin P o s (get_active_validator_indices s e) seed 1 true) :
    ∃ r, get_beacon_proposer_indices_fulu P o s e = .ok r := by
  obtain ⟨seed, hseed⟩ := get_seed_total o s e DOMAIN_BEACON_PROPOSER he hr
  have hin : ∀ j ∈ get_active_validator_indices s e, j < s.validators.length :=
    fun j hj => active_lt s e j hj
  obtain ⟨r, hr1⟩ := compute_proposer_indices_total o s e seed _ hstart hne hin heb
    ((active_len_le s e).trans hreg) hsel
  unfold get_beacon_proposer_indices_fulu
  rw [hseed, tot_bind_ok]
  exact ⟨r, compute_proposer_indices_ok_fulu P o s e seed _ hin r hr1⟩

theorem process_proposer_lookahead_fulu_total [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState)
    (hslot : s.slot + 8192 < 2 ^ 64) (hr : s.randao_mixes.length = 65536)
    (hreg : s.validators.length ≤ 2 ^ 40)
    (heb : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000)
    (hlen : s.proposer_lookahead.length = 64)
    (hne : get_active_validator_indices s (s.slot / 32 + 2) ≠ [])
    (hsel : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / 32 + 2))
      seed 1 true) :
    ∃ s', process_proposer_lookahead_fulu P o s = .ok s' := by
  have he : s.slot / 32 + 2 + 65536 < 2 ^ 64 := ep_bound hslot 2 (by decide)
  obtain ⟨r, hr1⟩ := get_beacon_proposer_indices_fulu_total o
    { s with proposer_lookahead := s.proposer_lookahead.drop 32 ++ s.proposer_lookahead.drop 32 }
    (s.slot / 32 + 2) he (ep_start_bound hslot 2 (by decide)) hr hreg heb hne hsel
  unfold process_proposer_lookahead_fulu
  have h32 : (P).SLOTS_PER_EPOCH = 32 := rfl
  have h1 : (P).MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [h32, h1, tot_sub (show 32 ≤ s.proposer_lookahead.length by omega), tot_bind_ok]
  rw [hlen]
  dsimp only
  have ha1 : s.slot / 32 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (ep_bound hslot 1 (by decide))
  have ha2 : s.slot / 32 + 1 + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (ep_bound hslot 2 (by decide))
  simp only [Nat.reduceSub, tot_current_epoch, tot_bind_ok, tot_add ha1, tot_add ha2]
  rw [show s.slot / 32 + 1 + 1 = s.slot / 32 + 2 by rw [Nat.add_assoc], hr1, tot_bind_ok]
  exact ⟨_, rfl⟩

/-- State facts that the two Fulu committee steps read beyond `CommFrame`. They are the Gloas
`CommConds` without the PTC window length. -/
structure FuluCommConds (o : Oracle) (s : BeaconState) : Prop where
  regLen : s.validators.length ≤ 2 ^ 40
  ebMax : ∀ v ∈ s.validators, v.effective_balance ≤ 2048000000000
  lookahead : s.proposer_lookahead.length = 64
  keys : ∀ v ∈ s.validators, o.bls_KeyValidate v.pubkey = true

/-- Preconditions of the Fulu pyspec itself. Without them the pyspec raises.

- `syncActive`: some validator is active at the next epoch (`i % active_validator_count` divides
  by zero otherwise).
- `proposers`: some validator is active at `current + 2` (`compute_proposer_index` asserts
  `len(indices) > 0`). Unlike Gloas F4, a slashed active validator counts.
- `selSync`, `selProp` (like F3): each selection accepts its candidates within `2^64` passes.
  This depends on the hash values. A candidate with effective balance `0` still passes when its
  random value is `0`, so the loop ends with probability 1. -/
structure FuluCommPreconds (o : Oracle) (s : BeaconState) : Prop where
  syncActive : get_active_validator_indices s (s.slot / 32 + 1) ≠ []
  proposers : get_active_validator_indices s (s.slot / 32 + 2) ≠ []
  selSync : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / 32 + 1))
    seed 512 true
  selProp : ∀ seed, SelFin P o s (get_active_validator_indices s (s.slot / 32 + 2))
    seed 1 true

/-- The Fulu sync committee update and proposer lookahead succeed on every state with the facts
that the earlier steps keep. -/
def CommitteesOkFulu [PresetCfg] (o : Oracle) (t : BeaconState) : Prop :=
  ∀ s, CommFrame t s → OkWith (do
      let s ← process_sync_committee_updates_fulu P o s
      process_proposer_lookahead_fulu P o s) (fun _ => True)

theorem committeesOkFulu_of [PresetCfg] [PresetCfg.Ok] (o : Oracle) (t : BeaconState) (hslot : t.slot + 8192 < 2 ^ 64)
    (h : ∀ s, CommFrame t s → FuluCommConds o s ∧ FuluCommPreconds o s) :
    CommitteesOkFulu o t := by
  intro s hf
  obtain ⟨hc, hp⟩ := h s hf
  have hs : s.slot + 8192 < 2 ^ 64 := hf.slot ▸ hslot
  obtain ⟨s1, h1, e1s, e1v, e1r, e1l, -⟩ := process_sync_committee_updates_total o s hs hf.randao
    hc.regLen hc.ebMax hc.keys hp.syncActive hp.selSync
  have h1f := ((process_sync_committee_updates_fulu_sameOk P o s (by decide)) s1).mpr
    h1
  rw [h1f, tot_bind_ok]
  have hsel1 : ∀ seed, SelFin P o s1
      (get_active_validator_indices s1 (s1.slot / 32 + 2)) seed 1 true := by
    intro seed
    simp only [SelFin, ebsOf_congr e1v, get_active_validator_indices_congr e1v, e1s]
    exact hp.selProp seed
  obtain ⟨s2, h2⟩ := process_proposer_lookahead_fulu_total o s1 (e1s ▸ hs) (e1r ▸ hf.randao)
    (e1v ▸ hc.regLen) (e1v ▸ hc.ebMax) (e1l ▸ hc.lookahead)
    (by rw [get_active_validator_indices_congr e1v, e1s]; exact hp.proposers) hsel1
  exact ⟨s2, h2, trivial⟩

/-! ## The whole Fulu epoch -/

/-- The Fulu spec `process_epoch` succeeds on mainnet at the last slot of an epoch, from the
reachable-state facts at its input, `RowBounds`, and the Fulu committee steps. -/
theorem process_epoch_fulu_total [PresetCfg] [PresetCfg.Ok] [FuluCfg] (o : Oracle) (t : BeaconState) (hrows : RowsOk t)
    (hslot : t.slot + 8192 < 2 ^ 64) (hlast : (t.slot + 1) % 32 = 0)
    (hvec : t.FuluVectorLengths P) (hffg : FfgInvariant P t)
    (heb : EBOk P t) (hcons : ConsolidationsInRange t)
    (hsl : t.slashings.sum * 3 < 2 ^ 64) (hrb : RowBounds t) (hcomm : CommitteesOkFulu o t) :
    ∃ s', process_epoch_fulu P FC o t = .ok s' := by
  have hsup : totalEffectiveBalance t < 2 ^ 60 := Nat.lt_trans hrb.supply (by decide)
  have hmid := midOkFulu_of_rowBounds t hrows hslot heb hvec.2.2.1 hvec.2.2.2.1 hcons hsl hrb
  have hdep := depCore_of_rowBounds fuluTabM o t hslot hrb
  have hslot64 : t.slot < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hslot
  obtain ⟨hbr, -, -, -, hbits, -⟩ := hvec
  have hcp := tot_cp hffg.1.2 hffg.2 hslot64
  rw [process_epoch_fulu_parts]
  obtain ⟨s1, h1, -⟩ := process_justification_and_finalization_total t hrows hslot hlast hbr hbits
    hcp hsup
  rw [h1, tot_bind_ok]
  have hfin : t.slot / 32 ≠ 0 → s1.finalized_checkpoint.epoch + 1 ≤ t.slot / 32 := fun hne =>
    process_justification_and_finalization_finalized _ t s1 _ (tot_current_epoch t)
      (by simpa [GENESIS_EPOCH] using hne) hffg h1
  have hfin0 : s1.finalized_checkpoint.epoch ≤ t.slot / 32 := by
    rcases process_justification_and_finalization_step _ t s1 h1 with rfl | ⟨h2, -⟩
    · exact hffg.finalized_le
    · have h2' : 2 ≤ t.slot / 32 := h2
      exact Nat.le_of_succ_le (hfin (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide) h2')))
  obtain ⟨s5, h5, f5, d5⟩ := hmid s1 (process_justification_and_finalization_shape _ t s1 h1)
    hfin0 hfin
  rw [h5, tot_bind_ok]
  unfold epochRestFulu
  -- eth1 data reset
  obtain ⟨s6, h6, e6⟩ := process_eth1_data_reset_total s5 (f5.slot ▸ hslot64)
  have f6 : TailFrame t s6 ∧ DepFrame t s6 := by
    rcases e6 with rfl | rfl
    · exact ⟨f5, d5⟩
    · exact ⟨⟨f5.slot, f5.rows, f5.randao, f5.slashings, f5.cons, f5.bsum, f5.ebs, f5.teb⟩,
        ⟨d5.pend, d5.dbtc, d5.vlen, d5.bsum, d5.teb, d5.fin⟩⟩
  rw [h6, tot_bind_ok]
  -- pending deposits, at the Fulu churn total
  obtain ⟨tab6, ht6, -⟩ := tot_tab_lt s6 f6.1.teb
  rw [ht6, tot_bind_ok]
  obtain ⟨s7, h7, f7⟩ := hdep s6 tab6 f6.1 f6.2 ht6
  rw [h7, tot_bind_ok]
  -- pending consolidations
  obtain ⟨s8, h8, B, k, rfl, hBl, hBs⟩ := process_pending_consolidations_total s7 f7.rows
    (f7.slot ▸ hslot64) f7.cons (Nat.lt_trans f7.bsum (by decide))
  rw [h8, tot_bind_ok]
  have f8 : TailFrame t { s7 with balances := B, pending_consolidations := s7.pending_consolidations.drop k } :=
    ⟨f7.slot, ⟨hBl, f7.rows.2.1, f7.rows.2.2.1, f7.rows.2.2.2⟩, f7.randao, f7.slashings,
      fun c hc => f7.cons c (List.mem_of_mem_drop hc), Nat.lt_of_le_of_lt hBs f7.bsum, f7.ebs,
      f7.teb⟩
  generalize hs8 : ({ s7 with balances := B, pending_consolidations := s7.pending_consolidations.drop k } : BeaconState) = s8 at f8 ⊢
  -- effective balance updates (Fulu has no builder payments)
  obtain ⟨s10, h10, vs, hvs, e10⟩ := process_effective_balance_updates_total s8 f8.rows
    (fun b hb => Nat.lt_of_le_of_lt (tot_mem_le_sum hb) (Nat.lt_trans f8.bsum (by decide)))
    (fun v hv => Nat.lt_trans (f8.ebs v hv) (by decide))
  rw [h10, tot_bind_ok]
  have r10 : RowsOk s10 := by subst e10; exact tot_rowsOk_validators f8.rows vs hvs
  have k10 : s10.slot = t.slot ∧ s10.slashings.length = 8192 ∧
      s10.randao_mixes.length = 65536 := by subst e10; exact ⟨f8.slot, f8.slashings, f8.randao⟩
  -- slashings reset
  obtain ⟨s11, h11, i11, a11, e11⟩ := process_slashings_reset_total s10 (k10.1 ▸ hslot64) k10.2.1
  rw [h11, tot_bind_ok]
  have k11 : RowsOk s11 ∧ s11.slot = t.slot ∧ s11.randao_mixes.length = 65536 := by
    subst e11; exact ⟨r10, k10.1, k10.2.2⟩
  -- RANDAO mixes reset
  obtain ⟨s12, h12, i12, a12, e12⟩ := process_randao_mixes_reset_total s11 (k11.2.1 ▸ hslot64)
    k11.2.2
  rw [h12, tot_bind_ok]
  have k12 : RowsOk s12 ∧ s12.slot = t.slot ∧ s12.randao_mixes.length = 65536 := by
    subst e12; exact ⟨k11.1, k11.2.1, by simp [k11.2.2]⟩
  -- historical summaries
  obtain ⟨s13, h13, l13, e13⟩ := process_historical_summaries_update_total o s12
    (k12.2.1 ▸ hslot64)
  rw [h13, tot_bind_ok]
  have k13 : RowsOk s13 ∧ s13.slot = t.slot ∧ s13.randao_mixes.length = 65536 := by
    subst e13; exact k12
  -- participation flags, then the committee steps
  obtain ⟨s', hs', -⟩ := hcomm (process_participation_flag_updates s13)
    ⟨k13.2.1, ⟨k13.1.1, k13.1.2.1, k13.1.2.2.2, by simp [process_participation_flag_updates]⟩,
      k13.2.2⟩
  exact ⟨s', hs'⟩

end EpochProofs.Spec
