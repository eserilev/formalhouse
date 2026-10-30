import EpochProofs.Sanity.Invariants.LighthouseResets
import EpochProofs.Spec.PresetCfg
import EpochProofs.Sanity.Invariants.LighthouseTail
import EpochProofs.Sanity.EpochCommittees

/-!
# Moving the proposer lookahead and the PTC window

Lighthouse runs `process_proposer_lookahead` and `process_ptc_window` inside the single pass,
before the resets, the historical summaries update, the participation rotation and the sync
committee update. The spec runs them last. These steps write fields that the two committee
steps do not read, and the two committee steps write fields that these steps do not read. The
randao reset is the one exception: it writes the mix of the next epoch, and the committee steps
read the mix of the current epoch. The two positions differ.

`swap_shapes` is the general swap: two steps that each compute new values and write them commute
when neither reads what the other writes.
-/

namespace EpochProofs.Spec

/-! ## The committee helpers read only `validators` and `randao_mixes` -/

theorem get_active_validator_indices_congr {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) :
    get_active_validator_indices s1 = get_active_validator_indices s2 := by
  funext e
  simp only [get_active_validator_indices, hv]

theorem get_seed_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    (hr : s1.randao_mixes = s2.randao_mixes) : get_seed p o s1 = get_seed p o s2 := by
  funext e d
  simp only [get_seed, get_randao_mix, hr]

theorem compute_balance_weighted_selection_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) :
    compute_balance_weighted_selection p o s1 = compute_balance_weighted_selection p o s2 := by
  funext indices seed size shuffle
  simp only [compute_balance_weighted_selection, hv]

theorem compute_proposer_indices_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) :
    compute_proposer_indices p o s1 = compute_proposer_indices p o s2 := by
  funext e seed indices
  simp only [compute_proposer_indices, compute_balance_weighted_selection_congr hv]

theorem get_committee_count_per_slot_congr {p : Preset} {s1 s2 : BeaconState}
    (hv : s1.validators = s2.validators) :
    get_committee_count_per_slot p s1 = get_committee_count_per_slot p s2 := by
  funext e
  simp only [get_committee_count_per_slot, get_active_validator_indices_congr hv]

/-- `get_beacon_proposer_indices` reads `validators` and the proposer seed of `epoch`. -/
theorem get_beacon_proposer_indices_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    {epoch : Epoch} (hv : s1.validators = s2.validators)
    (hseed : get_seed p o s1 epoch DOMAIN_BEACON_PROPOSER =
      get_seed p o s2 epoch DOMAIN_BEACON_PROPOSER) :
    get_beacon_proposer_indices p o s1 epoch = get_beacon_proposer_indices p o s2 epoch := by
  simp only [get_beacon_proposer_indices, get_active_validator_indices_congr hv, hv, hseed,
    compute_proposer_indices_congr hv]

/-- `get_beacon_committee` reads `validators` and the attester seed of the epoch of `slot`. -/
theorem get_beacon_committee_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState} {slot : Slot}
    (hv : s1.validators = s2.validators)
    (hseed : ∀ epoch, compute_epoch_at_slot p slot = .ok epoch →
      get_seed p o s1 epoch DOMAIN_BEACON_ATTESTER = get_seed p o s2 epoch DOMAIN_BEACON_ATTESTER) :
    get_beacon_committee p o s1 slot = get_beacon_committee p o s2 slot := by
  funext index
  unfold get_beacon_committee
  cases he : compute_epoch_at_slot p slot with
  | error err => rfl
  | ok epoch =>
    simp only [bind, Except.bind, get_committee_count_per_slot_congr hv,
      get_active_validator_indices_congr hv, hseed epoch he]

/-- `compute_ptc` reads `validators` and two seeds of the epoch of `slot`. -/
theorem compute_ptc_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState} {slot : Slot}
    (hv : s1.validators = s2.validators)
    (hseed : ∀ epoch, compute_epoch_at_slot p slot = .ok epoch → ∀ d,
      get_seed p o s1 epoch d = get_seed p o s2 epoch d) :
    compute_ptc p o s1 slot = compute_ptc p o s2 slot := by
  unfold compute_ptc
  cases he : compute_epoch_at_slot p slot with
  | error err => rfl
  | ok epoch =>
    simp only [bind, Except.bind, hseed epoch he, get_committee_count_per_slot_congr hv,
      get_beacon_committee_congr hv (fun e he' => by rw [he] at he'; cases he'; exact hseed _ he _),
      compute_balance_weighted_selection_congr hv]

/-- `get_next_sync_committee` reads `slot`, `validators` and `randao_mixes`. -/
theorem get_next_sync_committee_congr {p : Preset} {o : Oracle} {s1 s2 : BeaconState}
    (hs : s1.slot = s2.slot) (hv : s1.validators = s2.validators)
    (hr : s1.randao_mixes = s2.randao_mixes) :
    get_next_sync_committee p o s1 = get_next_sync_committee p o s2 := by
  simp only [get_next_sync_committee, get_next_sync_committee_indices, get_current_epoch, hs,
    get_seed_congr hr, get_active_validator_indices_congr hv,
    compute_balance_weighted_selection_congr hv, hv]

/-! ## The general swap -/

/-- Two steps that compute new values and write them commute, when the computation of each does
not read what the other writes, and the two writes commute. -/
theorem swap_shapes {α β : Type} (X Y : BeaconState → SpecM BeaconState)
    (xNew : BeaconState → SpecM α) (G : α → BeaconState → BeaconState)
    (yNew : BeaconState → SpecM β) (H : β → BeaconState → BeaconState) (s : BeaconState)
    (hX : ∀ t, X t = (fun v => G v t) <$> xNew t)
    (hY : ∀ t, Y t = (fun w => H w t) <$> yNew t)
    (hYG : ∀ v, xNew s = .ok v → yNew (G v s) = yNew s)
    (hXH : ∀ w, yNew s = .ok w → xNew (H w s) = xNew s)
    (hGH : ∀ v w, G v (H w s) = H w (G v s)) :
    SameResultOrBothFail (X s >>= Y) (Y s >>= X) := by
  rw [hX s, hY s]
  cases hx : xNew s with
  | error e =>
    cases hy : yNew s with
    | error e' => exact SameResultOrBothFail.errors
    | ok w =>
      show SameResultOrBothFail (Except.error e) (X (H w s))
      rw [hX, hXH w hy, hx]
      exact SameResultOrBothFail.errors
  | ok v =>
    show SameResultOrBothFail (Y (G v s)) _
    rw [hY, hYG v hx]
    cases hy : yNew s with
    | error e' => exact SameResultOrBothFail.errors
    | ok w =>
      show SameResultOrBothFail (Except.ok (H w (G v s))) (X (H w s))
      rw [hX, hXH w hy, hx]
      show SameResultOrBothFail (Except.ok (H w (G v s))) (Except.ok (G v (H w s)))
      rw [hGH]
      exact SameResultOrBothFail.refl _

/-! ## The proposer lookahead -/

/-- `s` with a new `proposer_lookahead`. -/
def setPL (s : BeaconState) (l : List ValidatorIndex) : BeaconState :=
  { s with proposer_lookahead := l }

/-- The new `proposer_lookahead` that `process_proposer_lookahead` writes. -/
def plNew [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM (List ValidatorIndex) := do
  let last_epoch_start ← uint64Sub s.proposer_lookahead.length P.SLOTS_PER_EPOCH
  let st := setPL s (s.proposer_lookahead.drop P.SLOTS_PER_EPOCH ++
    s.proposer_lookahead.drop last_epoch_start)
  let last_epoch_proposers ← get_beacon_proposer_indices P o st
    (← uint64Add (← uint64Add (s.slot / P.SLOTS_PER_EPOCH)
      P.MIN_SEED_LOOKAHEAD) 1)
  pure (st.proposer_lookahead.take last_epoch_start ++ last_epoch_proposers)

theorem process_proposer_lookahead_eq [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    process_proposer_lookahead P o s = (fun l => setPL s l) <$> plNew o s := by
  unfold process_proposer_lookahead plNew setPL
  simp only [get_current_epoch_mainnet, ok_bind']
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

theorem error_bind' {α β : Type} (e : SpecError) (f : α → SpecM β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem uint64Add_of_ge (a b : Nat) (h : ¬ a + b < 2 ^ 64) :
    uint64Add a b = .error .overflow := by
  unfold uint64Add
  rw [if_neg (by simpa [UINT64_SIZE] using h)]
  rfl

/-- `plNew` reads `proposer_lookahead`, `slot`, `validators` and the proposer seed two epochs
ahead. -/
theorem plNew_congr [PresetCfg] (o : Oracle) (s1 s2 : BeaconState)
    (hpl : s1.proposer_lookahead = s2.proposer_lookahead) (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators)
    (hseed : get_seed P o s1 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1)
        DOMAIN_BEACON_PROPOSER =
      get_seed P o s2 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1)
        DOMAIN_BEACON_PROPOSER) :
    plNew o s1 = plNew o s2 := by
  have hg : ∀ l, get_beacon_proposer_indices P o (setPL s1 l)
      (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1) =
    get_beacon_proposer_indices P o (setPL s2 l)
      (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1) := fun l =>
    get_beacon_proposer_indices_congr hv
      ((congrFun (congrFun (get_seed_congr (s1 := setPL s1 l) (s2 := s1) rfl) _) _).trans
        (hseed.trans (congrFun (congrFun (get_seed_congr (s1 := s2) (s2 := setPL s2 l) rfl) _) _)))
  unfold plNew
  rw [hpl, hs]
  have hmsl : P.MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [hmsl]
  cases uint64Sub s2.proposer_lookahead.length P.SLOTS_PER_EPOCH with
  | error e => rfl
  | ok les =>
    simp only [ok_bind']
    by_cases h1 : s2.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64
    · simp only [uint64Add_of_lt _ _ h1, ok_bind']
      by_cases h2 : s2.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64
      · simp only [uint64Add_of_lt _ _ h2, ok_bind', hg]
        rfl
      · simp only [uint64Add_of_ge _ _ h2, error_bind']
    · simp only [uint64Add_of_ge _ _ h1, error_bind']

/-! ## The PTC window -/

/-- `s` with a new `ptc_window`. -/
def setPTC (s : BeaconState) (w : List (List ValidatorIndex)) : BeaconState :=
  { s with ptc_window := w }

/-- The new `ptc_window` that `process_ptc_window` writes. -/
def ptcNew [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM (List (List ValidatorIndex)) := do
  let shift_end ← uint64Sub s.ptc_window.length P.SLOTS_PER_EPOCH
  let st := setPTC s (s.ptc_window.drop P.SLOTS_PER_EPOCH ++
    s.ptc_window.drop shift_end)
  let next_epoch ← uint64Add (← uint64Add (s.slot / P.SLOTS_PER_EPOCH)
    P.MIN_SEED_LOOKAHEAD) 1
  let start_slot ← compute_start_slot_at_epoch P next_epoch
  let end_slot ← uint64Add start_slot P.SLOTS_PER_EPOCH
  let ptcs ← (List.range' start_slot (end_slot - start_slot)).mapM fun slot =>
    compute_ptc P o st slot
  let fill_start ← uint64Sub st.ptc_window.length P.SLOTS_PER_EPOCH
  pure (st.ptc_window.take fill_start ++ ptcs)

theorem process_ptc_window_eq [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState) :
    process_ptc_window P o s = (fun w => setPTC s w) <$> ptcNew o s := by
  unfold process_ptc_window ptcNew setPTC
  simp only [get_current_epoch_mainnet, ok_bind']
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

theorem uint64Mul_of_lt (a b : Nat) (h : a * b < 2 ^ 64) : uint64Mul a b = .ok (a * b) := by
  unfold uint64Mul
  rw [if_pos (by simpa [UINT64_SIZE] using h)]
  rfl

theorem uint64Mul_of_ge (a b : Nat) (h : ¬ a * b < 2 ^ 64) :
    uint64Mul a b = .error .overflow := by
  unfold uint64Mul
  rw [if_neg (by simpa [UINT64_SIZE] using h)]
  rfl

/-- `ptcNew` reads `ptc_window`, `slot`, `validators` and the seeds two epochs ahead. -/
theorem ptcNew_congr [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s1 s2 : BeaconState)
    (hptc : s1.ptc_window = s2.ptc_window) (hs : s1.slot = s2.slot)
    (hv : s1.validators = s2.validators)
    (hseed : ∀ d, get_seed P o s1 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1)
        d = get_seed P o s2 (s2.slot / P.SLOTS_PER_EPOCH + 1 + 1) d) :
    ptcNew o s1 = ptcNew o s2 := by
  unfold ptcNew
  rw [hptc, hs]
  have hmsl : P.MIN_SEED_LOOKAHEAD = 1 := rfl
  rw [hmsl]
  cases uint64Sub s2.ptc_window.length P.SLOTS_PER_EPOCH with
  | error e => simp only [error_bind']
  | ok shift_end =>
    simp only [ok_bind']
    by_cases h1 : s2.slot / P.SLOTS_PER_EPOCH + 1 < 2 ^ 64
    · simp only [uint64Add_of_lt _ _ h1, ok_bind']
      by_cases h2 : s2.slot / P.SLOTS_PER_EPOCH + 1 + 1 < 2 ^ 64
      · simp only [uint64Add_of_lt _ _ h2, ok_bind', compute_start_slot_at_epoch]
        generalize hN : s2.slot / P.SLOTS_PER_EPOCH + 1 + 1 = N at hseed ⊢
        by_cases h3 : N * P.SLOTS_PER_EPOCH < 2 ^ 64
        · simp only [uint64Mul_of_lt _ _ h3, ok_bind']
          by_cases h4 : N * P.SLOTS_PER_EPOCH + P.SLOTS_PER_EPOCH < 2 ^ 64
          · simp only [uint64Add_of_lt _ _ h4, ok_bind']
            rw [mapM_congr_mem' (fun slot => compute_ptc P o (setPTC s1 _) slot)
              (fun slot => compute_ptc P o (setPTC s2 _) slot)]
            · rfl
            intro slot hslot
            refine compute_ptc_congr hv (fun epoch he d => ?_)
            have he' : epoch = N := by
              simp only [compute_epoch_at_slot, uint64Div, Nat.ne_of_gt P_slots_pos, if_false,
                pure, Except.pure] at he
              cases he
              obtain ⟨i, hi, hs⟩ := List.mem_range'.mp hslot
              rw [hs]
              simp only [Slot, Epoch, Uint64] at *
              exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
            subst he'
            exact (congrFun (congrFun (get_seed_congr (s1 := setPTC s1 _) (s2 := s1) rfl) _) _).trans
              ((hseed d).trans
                (congrFun (congrFun (get_seed_congr (s1 := s2) (s2 := setPTC s2 _) rfl) _) _))
          · simp only [uint64Add_of_ge _ _ h4, error_bind']
        · simp only [uint64Mul_of_ge _ _ h3, error_bind']
      · simp only [uint64Add_of_ge _ _ h2, error_bind']
    · simp only [uint64Add_of_ge _ _ h1, error_bind']

end EpochProofs.Spec
