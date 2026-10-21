import EpochProofs.Equiv.EpochCommittees
import EpochProofs.Sanity.Fulu

/-!
# Lighthouse Fulu epoch steps equal the reference

Lighthouse runs the Fulu steps through the same translated functions as the Gloas steps, with
the Fulu constants and the Fulu candidates:

- `exit_churn_limit_capped`: `registry_update::exit_churn_limit` returns the activation churn of
  any preset. `exit_churn_limit_fulu` and `activation_churn_limit_fulu` take the Fulu constants:
  the result is `get_activation_exit_churn_limit`. `activation_churn_limit_gloas` takes the Gloas
  constants of the pending deposits glue: the result is `get_activation_churn_limit`.
- `next_proposer_lookahead_spec_fulu`: `epoch_committees::next_proposer_lookahead` on all the
  active validators returns Fulu `process_proposer_lookahead`, if each Electra proposer loop
  ends before its last pass (`ProposerFin`).
- `next_sync_committee_indices_spec_fulu`: `epoch_committees::next_sync_committee_indices`
  returns the Electra `get_next_sync_committee_indices`.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- `exit_churn_limit` returns `get_activation_churn_limit` of the preset whose quotient and
cap are the Lighthouse constants. -/
theorem exit_churn_limit_capped (p : Spec.Preset) (total_active_balance : U64)
    (c : LhRegistryConstants)
    (hmin : c.min_per_epoch_churn_limit.val = p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (hq : c.churn_limit_quotient.val = p.CHURN_LIMIT_QUOTIENT_GLOAS)
    (hinc : c.effective_balance_increment.val = p.EFFECTIVE_BALANCE_INCREMENT)
    (hcap : c.exit_churn_cap.val = p.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS) :
    per_epoch_processing.registry_update.exit_churn_limit total_active_balance c ⦃ r =>
      absResult (·.val) r = Spec.get_activation_churn_limit p total_active_balance.val ⦄ := by
  unfold per_epoch_processing.registry_update.exit_churn_limit
  apply exists_imp_spec
  obtain ⟨r1, hr1, h1⟩ := spec_imp_exists (safe_div_spec total_active_balance c.churn_limit_quotient)
  rw [hr1]
  cases r1 with
  | Err e =>
    obtain ⟨rfl, hz⟩ := h1.2 e rfl
    rw [hq] at hz
    refine ⟨_, rfl, ?_⟩
    simp [Spec.get_activation_churn_limit, Spec.uint64Div, hz, absResult, absArithError,
      except_error_bind, throw, throwThe, MonadExceptOf.throw]
  | Ok q =>
  obtain ⟨hqv, hnz⟩ := h1.1 q rfl
  rw [hq] at hqv hnz
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  have hmax := core.cmp.impls.OrdU64.max_val c.min_per_epoch_churn_limit q
  simp only [core.cmp.max, core.cmp.OrdU64, liftFun2, bind_tc_ok]
  obtain ⟨r2, hr2, h2⟩ := spec_imp_exists (safe_rem_spec
    (core.cmp.impls.OrdU64.max c.min_per_epoch_churn_limit q) c.effective_balance_increment)
  rw [hr2]
  cases r2 with
  | Err e =>
    obtain ⟨rfl, hz⟩ := h2.2 e rfl
    rw [hinc] at hz
    refine ⟨_, rfl, ?_⟩
    simp [Spec.get_activation_churn_limit, Spec.uint64Div, Spec.uint64Mod, hnz, ← hqv, hz,
      absResult, absArithError, except_ok_bind, except_error_bind, throw, throwThe,
      MonadExceptOf.throw, Pure.pure, Except.pure, core.convert.FromSame.from]
  | Ok m =>
  obtain ⟨hm, hmnz⟩ := h2.1 m rfl
  rw [hinc] at hm hmnz
  simp only [bind_tc_ok]
  obtain ⟨r3, hr3, h3⟩ := spec_imp_exists (safe_sub_spec
    (core.cmp.impls.OrdU64.max c.min_per_epoch_churn_limit q) m)
  rw [hr3]
  cases r3 with
  | Err e =>
    obtain ⟨_, hlt⟩ := h3.2 e rfl
    rw [hm] at hlt
    exact absurd hlt (Nat.not_lt.mpr (Nat.mod_le _ _))
  | Ok d =>
  obtain ⟨hd, _⟩ := h3.1 d rfl
  simp only [bind_tc_ok, core.cmp.min, liftFun2]
  refine ⟨_, rfl, ?_⟩
  have hmin' := core.cmp.impls.OrdU64.min_val c.exit_churn_cap d
  rw [hcap] at hmin'
  have hle : max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q.val % p.EFFECTIVE_BALANCE_INCREMENT
      ≤ max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q.val := Nat.mod_le _ _
  have hcond : max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q.val % p.EFFECTIVE_BALANCE_INCREMENT ≤
        p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA ∨
      max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q.val % p.EFFECTIVE_BALANCE_INCREMENT ≤ q.val := by
    rcases Nat.le_total p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA q.val with hq' | hq'
    · right; rw [Nat.max_eq_right hq'] at hle ⊢; exact hle
    · left; rw [Nat.max_eq_left hq'] at hle ⊢; exact hle
  simp [Spec.get_activation_churn_limit, Spec.uint64Div, Spec.uint64Mod, Spec.uint64Sub, hnz,
    ← hqv, hmnz, absResult, except_ok_bind, Pure.pure, Except.pure, hmin', hd, hm, hmax, hmin,
    hcond]

/-- The Lighthouse registry constants are the Fulu values: the exit churn is
`get_activation_exit_churn_limit`. -/
structure FuluChurnMatch (p : Spec.Preset) (f : Spec.FuluConfig) (c : LhRegistryConstants) :
    Prop where
  min_per_epoch_churn_limit : c.min_per_epoch_churn_limit.val = p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  churn_limit_quotient : c.churn_limit_quotient.val = f.CHURN_LIMIT_QUOTIENT
  effective_balance_increment : c.effective_balance_increment.val = p.EFFECTIVE_BALANCE_INCREMENT
  exit_churn_cap : c.exit_churn_cap.val = f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT

/-- With the Fulu constants, `exit_churn_limit` returns `get_activation_exit_churn_limit`. Before
Gloas Lighthouse passes the same constants for exits (`registry_constants`) and for pending
deposits (`activation_churn_constants`). -/
theorem exit_churn_limit_fulu (p : Spec.Preset) (f : Spec.FuluConfig) (total_active_balance : U64)
    (c : LhRegistryConstants) (hc : FuluChurnMatch p f c) :
    per_epoch_processing.registry_update.exit_churn_limit total_active_balance c ⦃ r =>
      absResult (·.val) r =
        Spec.get_activation_exit_churn_limit p f total_active_balance.val ⦄ := by
  rw [← Spec.get_activation_churn_limit_fuluView]
  exact exit_churn_limit_capped (p.fuluView f) total_active_balance c hc.min_per_epoch_churn_limit
    hc.churn_limit_quotient hc.effective_balance_increment hc.exit_churn_cap

/-- With the Gloas constants of `activation_churn_constants`, `exit_churn_limit` returns
`get_activation_churn_limit`. -/
theorem activation_churn_limit_gloas (p : Spec.Preset) (total_active_balance : U64)
    (c : LhRegistryConstants)
    (hmin : c.min_per_epoch_churn_limit.val = p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (hq : c.churn_limit_quotient.val = p.CHURN_LIMIT_QUOTIENT_GLOAS)
    (hinc : c.effective_balance_increment.val = p.EFFECTIVE_BALANCE_INCREMENT)
    (hcap : c.exit_churn_cap.val = p.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS) :
    per_epoch_processing.registry_update.exit_churn_limit total_active_balance c ⦃ r =>
      absResult (·.val) r = Spec.get_activation_churn_limit p total_active_balance.val ⦄ :=
  exit_churn_limit_capped p total_active_balance c hmin hq hinc hcap

/-- `next_sync_committee_indices` equals the Electra `get_next_sync_committee_indices`. -/
theorem next_sync_committee_indices_spec_fulu {H B : Type} (inst : ShuffleHashInst H)
    (ebi : EBInst B) (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_SYNC_COMMITTEE.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce → epoch.val = ce + 1)
    (hindices : indices.val.map (·.val) = Spec.get_active_validator_indices state epoch.val)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (size : Usize)
    (hsize : size.val = p.SYNC_COMMITTEE_SIZE) (hsize0 : 0 < p.SYNC_COMMITTEE_SIZE)
    (c : LhSelectionConstants) (hc : SelectionConstantsMatch p c)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max) (res : List Nat)
    (hspec : Spec.get_next_sync_committee_indices_fulu p o state = .ok res) :
    per_epoch_processing.epoch_committees.next_sync_committee_indices inst ebi balances indices
      domain epoch mix size c ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ :=
  next_sync_committee_indices_spec inst ebi balances p o hH state hEB indices domain hdomain epoch
    hepoch hindices mix hmix size hsize c hc hn24 hus res
    ((Spec.get_next_sync_committee_indices_fulu_iff p o state hsize0 res).mp hspec)

theorem get_beacon_proposer_indices_fulu_frame (p : Spec.Preset) (o : Spec.Oracle)
    (state : Spec.BeaconState) (L : List Nat) (e : Nat) :
    Spec.get_beacon_proposer_indices_fulu p o { state with proposer_lookahead := L } e =
      Spec.get_beacon_proposer_indices_fulu p o state e := rfl

/-- `next_proposer_lookahead` on all the active validators equals Fulu
`process_proposer_lookahead`. -/
theorem next_proposer_lookahead_spec_fulu {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (look : Slice U64) (hlook : look.val.map (·.val) = state.proposer_lookahead)
    (indices : Slice Usize) (domain : Array U8 4#usize)
    (hdomain : u8s domain.val = Spec.DOMAIN_BEACON_PROPOSER.toList) (epoch : U64)
    (hepoch : ∀ ce, Spec.get_current_epoch p state = .ok ce →
      epoch.val = ce + p.MIN_SEED_LOOKAHEAD + 1)
    (hindices : indices.val.map (·.val) = Spec.get_active_validator_indices state epoch.val)
    (hfin : ∀ s, Spec.ProposerFin p o state (Spec.get_active_validator_indices state epoch.val) s)
    (mix : Array U8 32#usize) (hmix : SeedMixLink p state epoch.val mix) (start_slot : U64)
    (hstart : Spec.compute_start_slot_at_epoch p epoch.val = .ok start_slot.val)
    (c : LhSelectionConstants) (hc : SelectionConstantsMatch p c)
    (hspe32 : p.SLOTS_PER_EPOCH < 2 ^ 32)
    (hn24 : indices.val.length ≤ 2 ^ 24) (hus : Usize.max = U64.max)
    (state' : Spec.BeaconState) (hspec : Spec.process_proposer_lookahead_fulu p o state = .ok state') :
    per_epoch_processing.epoch_committees.next_proposer_lookahead inst ebi balances look indices
      domain epoch mix start_slot c ⦃ r =>
        ∃ v : alloc.vec.Vec U64, r = .Ok v ∧ v.val.map (·.val) = state'.proposer_lookahead ⦄ := by
  unfold Spec.process_proposer_lookahead_fulu at hspec
  simp only [except_bind_ok_iff, get_beacon_proposer_indices_fulu_frame] at hspec
  obtain ⟨les, hles, ce, hce, e1, he1, e, he, props, hprops, hfin'⟩ := hspec
  simp only [pure, Except.pure, Except.ok.injEq] at hfin'
  have hlesv : les = state.proposer_lookahead.length - p.SLOTS_PER_EPOCH ∧
      p.SLOTS_PER_EPOCH ≤ state.proposer_lookahead.length := by
    simp only [Spec.uint64Sub] at hles
    split at hles
    · rename_i h; exact ⟨(Except.ok.inj hles).symm, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hles
  have hev : e = epoch.val := by
    rw [hepoch ce hce]
    simp only [Spec.uint64Add] at he1 he
    split at he1
    · split at he
      · rw [← Except.ok.inj he, ← Except.ok.inj he1]
      · simp [throw, throwThe, MonadExceptOf.throw] at he
    · simp [throw, throwThe, MonadExceptOf.throw] at he1
  subst hev
  unfold Spec.get_beacon_proposer_indices_fulu at hprops
  simp only [except_bind_ok_iff] at hprops
  obtain ⟨sd, hsd, hcpi⟩ := hprops
  have hcpi' := Spec.compute_proposer_indices_fulu_ok p o state epoch.val sd _
    (fun x hx => Spec.active_validator_index_lt state epoch.val x hx) hfin props hcpi
  rw [← hindices] at hcpi'
  obtain ⟨_, _, hplen, _⟩ := spec_proposers_get p o state epoch.val sd _ props hcpi'
  unfold per_epoch_processing.epoch_committees.next_proposer_lookahead
  apply spec_bind (compute_seed_eq inst p o hH state _ domain hdomain epoch mix hmix sd hsd)
  intro seed hseed
  apply spec_bind (compute_proposer_indices_spec inst ebi balances p o hH state hEB indices seed
    sd hseed epoch.val start_slot c.slots_per_epoch c.shuffle_round_count hc.shuffle_round_count
    c.max_effective_balance hc.max_effective_balance hc.slots_per_epoch hstart hn24 hus props hcpi')
  intro r hr
  obtain ⟨v, hrv, hv⟩ := hr
  simp only [hrv, bind_tc_ok, branch_ok, lift]
  have hspev : (UScalar.cast UScalarTy.Usize c.slots_per_epoch).val = p.SLOTS_PER_EPOCH := by
    rw [cast_usize_of_lt _ (by rw [hc.slots_per_epoch]; exact hspe32), hc.slots_per_epoch]
  have hlooklen : look.val.length = state.proposer_lookahead.length := by
    rw [← hlook]; simp
  have hvlen : (alloc.vec.Vec.deref v).val.length = p.SLOTS_PER_EPOCH := by
    have := congrArg List.length hv
    simp only [List.length_map] at this
    simp [alloc.vec.Vec.deref, this, hplen]
  apply spec_bind (shift_lookahead_spec look _ (alloc.vec.Vec.deref v)
    (by rw [hspev, hlooklen]; exact hlesv.2) (by rw [hvlen, hspev]))
  intro o1 ho1
  obtain ⟨w, hw, hwv⟩ := ho1
  simp only [hw, core.option.Option.ok_or, spec_ok]
  refine ⟨w, rfl, ?_⟩
  have hd : (look.val.drop p.SLOTS_PER_EPOCH).map (·.val) =
      state.proposer_lookahead.drop p.SLOTS_PER_EPOCH := by
    rw [List.map_drop, hlook]
  rw [hwv, ← hfin', hspev, hd, hlesv.1]
  simp only [alloc.vec.Vec.deref]
  rw [hv, List.take_append_of_le_length (by simp)]
  rw [List.take_of_length_le (by simp)]

end EpochProofs
