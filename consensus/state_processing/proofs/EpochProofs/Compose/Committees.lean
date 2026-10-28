import EpochProofs.Equiv.ListWrites
import EpochProofs.Sanity.GlueBounds
import EpochProofs.Sanity.Invariants.LighthouseOrder

/-!
# The proposer lookahead and the PTC window, composed from the translated functions

`lookahead` is `process_proposer_lookahead` of `single_pass.rs`: the translated
`next_proposer_lookahead` and the `Vector::new` write. `ptcWindow` is `process_ptc_window`: the
translated `ptc_for_epoch` and `shift_window`. The reads, the hash, the effective balance source,
the committees from the committee cache and the writes are untranslated glue
(`LookaheadGlue`, `PtcGlue`), each with the fact that links it to the spec (`LookaheadLinks`,
`PtcLinks`). `lookahead_spec` and `ptcWindow_spec` show that they return the states of the
models. The Fulu lookahead (`lookahead_spec_fulu`) differs only in the proposer candidates.
-/

namespace EpochProofs.Spec

/-- `process_proposer_lookahead` keeps the length of the lookahead. -/
theorem process_proposer_lookahead_len (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead p o s = .ok s') :
    s'.proposer_lookahead.length = s.proposer_lookahead.length := by
  unfold process_proposer_lookahead at h
  simp only [glue_bind_ok_iff] at h
  obtain ⟨les, hles, ce, -, e1, -, e, -, props, hprops, hfin⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at hfin
  subst hfin
  unfold uint64Sub at hles
  by_cases hle : p.SLOTS_PER_EPOCH ≤ s.proposer_lookahead.length
  · rw [if_pos hle] at hles
    simp only [pure, Except.pure, Except.ok.injEq] at hles
    subst hles
    have hrl := get_beacon_proposer_indices_length _ _ _ _ _ hprops
    simp only [List.length_append, List.length_take, List.length_drop, hrl]
    omega
  · rw [if_neg hle] at hles
    cases hles

theorem uint64Add_ok_sum {a b c : Nat} (h : uint64Add a b = .ok c) : c = a + b := by
  unfold uint64Add at h
  split at h
  · cases h; rfl
  · cases h

/-- The start slot of the lookahead epoch computes when `process_proposer_lookahead` succeeds. -/
theorem process_proposer_lookahead_start (p : Preset) (o : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead p o s = .ok s') (ce : Nat)
    (hce : get_current_epoch p s = .ok ce) :
    ∃ n, compute_start_slot_at_epoch p (ce + p.MIN_SEED_LOOKAHEAD + 1) = .ok n := by
  unfold process_proposer_lookahead at h
  simp only [glue_bind_ok_iff] at h
  obtain ⟨les, -, ce', hce', e1, he1, e, he, props, hprops, -⟩ := h
  have hc : ce' = ce := by
    rw [get_current_epoch_ok_eq hce', get_current_epoch_ok_eq hce]
  subst hc
  rw [uint64Add_ok_sum he, uint64Add_ok_sum he1] at hprops
  unfold get_beacon_proposer_indices compute_proposer_indices at hprops
  simp only [glue_bind_ok_iff] at hprops
  obtain ⟨-, -, -, -, n, hn, -⟩ := hprops
  exact ⟨n, hn⟩

end EpochProofs.Spec

namespace EpochProofs.Compose

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The untranslated Rust of `process_proposer_lookahead`. -/
structure LookaheadGlue (σ : Type) where
  /-- `Sha256Hash`, and the `BeaconState` as the effective balance source. -/
  H : Type
  hash : ShuffleHashInst H
  effectiveBalances : EBInst σ
  /-- The reads: the lookahead, the proposer candidates, the lookahead epoch
  (`current_epoch + min_seed_lookahead + 1`), its mix and start slot, `selection_constants`. -/
  lookahead : σ → Slice U64
  proposerIndices : σ → Slice Usize
  proposerDomain : Array U8 4#usize
  epoch : σ → U64
  mix : σ → Array U8 32#usize
  startSlot : σ → U64
  constants : σ → LhSelectionConstants
  /-- `*state.proposer_lookahead_mut()? = Vector::new(lookahead)?`. -/
  writeLookahead : σ → alloc.vec.Vec U64 → Option σ

/-- The untranslated Rust of `process_ptc_window`. It reads the lookahead epoch, its mix and
start slot and the constants as `process_proposer_lookahead` does. -/
structure PtcGlue (σ E : Type) where
  /-- The committees of each slot of the lookahead epoch, from the committee cache built for
  it. -/
  committees : σ → Slice (alloc.vec.Vec Usize)
  ptcDomain : Array U8 4#usize
  ptcSize : Usize
  slotsPerEpochUsize : Usize
  /-- `PtcWindowWrites`. -/
  W : Type
  window : LhWindowWrites W (alloc.vec.Vec Usize) E
  wview : W → List (List Nat)
  committed : W → List (List Nat)
  windowBorrow : σ → W
  windowReturn : σ → W → σ

variable {σ E : Type}

/-- `process_proposer_lookahead`, as the call of the translated `next_proposer_lookahead`
joined by the glue `L`. `none`: the Rust returns an error. -/
def lookahead (L : LookaheadGlue σ) (st : σ) : Result (Option σ) := do
  let r ← per_epoch_processing.epoch_committees.next_proposer_lookahead L.hash
    L.effectiveBalances st (L.lookahead st) (L.proposerIndices st) L.proposerDomain (L.epoch st)
    (L.mix st) (L.startSlot st) (L.constants st)
  match r with
  | .Err _ => ok none
  | .Ok look => ok (L.writeLookahead st look)

/-- `process_ptc_window`, as the calls of the translated `ptc_for_epoch` and `shift_window`
joined by the glue. `none`: the Rust returns an error. -/
def ptcWindow (L : LookaheadGlue σ) (G : PtcGlue σ E) (st : σ) : Result (Option σ) := do
  let r ← per_epoch_processing.epoch_committees.ptc_for_epoch L.hash L.effectiveBalances st
    (G.committees st) G.ptcDomain (L.epoch st) (L.mix st) (L.startSlot st) G.ptcSize
    (L.constants st)
  match r with
  | .Err _ => ok none
  | .Ok ptcs =>
  let (r, w) ← per_epoch_processing.list_writes.shift_window G.window (G.windowBorrow st)
    G.slotsPerEpochUsize (alloc.vec.Vec.deref ptcs)
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some (G.windowReturn st w))

/-- N1 at the lookahead input: the proposer candidates fit in the shuffle. -/
def LookaheadN1 (L : LookaheadGlue σ) (st : σ) : Prop :=
  (L.proposerIndices st).val.length ≤ 2 ^ 24

/-- N1 at the PTC window input: each slot's committees fit in the selection. -/
def PtcN1 (G : PtcGlue σ E) (st : σ) : Prop :=
  ∀ k (hk : k < (G.committees st).val.length), ((G.committees st).val[k]).val.length ≤ 2 ^ 24

variable [Spec.PresetCfg]

/-- The trusted facts about the glue `L`. The reads read the state they are given and the write
writes the spec value, so each fact holds for every state `t`. -/
structure LookaheadLinks (L : LookaheadGlue σ) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) : Prop where
  /-- `Sha256Hash` computes SHA-256, and the state gives its effective balances. -/
  hash : HashLink L.hash o
  effectiveBalances : ∀ t, EBLink L.effectiveBalances t
    ((view t).validators.map (·.effective_balance))
  lookahead : ∀ t, (L.lookahead t).val.map (·.val) = (view t).proposer_lookahead
  proposerDomain : u8s L.proposerDomain.val = Spec.DOMAIN_BEACON_PROPOSER.toList
  /-- L2: the lookahead epoch. -/
  epoch : ∀ t ce, Spec.get_current_epoch Spec.P (view t) = .ok ce →
    (L.epoch t).val = ce + Spec.P.MIN_SEED_LOOKAHEAD + 1
  /-- L4: `get_seed_mix`. -/
  mix : ∀ t, SeedMixLink Spec.P (view t) (L.epoch t).val (L.mix t)
  startSlot : ∀ t n, Spec.compute_start_slot_at_epoch Spec.P (L.epoch t).val = .ok n →
    (L.startSlot t).val = n
  constants : ∀ t, SelectionConstantsMatch Spec.P (L.constants t)
  /-- L5: `Vector::new` accepts a lookahead of the vector length. -/
  writeLookahead : ∀ t v,
    v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH →
    ∃ t', L.writeLookahead t v = some t' ∧
      view t' = { view t with proposer_lookahead := v.val.map (·.val) }
  usize64 : Usize.max = U64.max

/-- The Gloas proposer candidates: the active, unslashed validators at the lookahead epoch. -/
def GloasProposerIndices (L : LookaheadGlue σ) (view : σ → Spec.BeaconState) : Prop :=
  ∀ t l, (Spec.get_active_validator_indices (view t) (L.epoch t).val).filterM
      (fun index => do pure !(← Spec.listGet (view t).validators index).slashed) = .ok l →
    (L.proposerIndices t).val.map (·.val) = l

/-- The trusted facts about the glue `G`. -/
structure PtcLinks (L : LookaheadGlue σ) (G : PtcGlue σ E) (o : Spec.Oracle)
    (view : σ → Spec.BeaconState) : Prop where
  /-- The committees from the committee cache built for the lookahead epoch. The cache is built
  fresh from the state, so only its inputs are trusted. -/
  committees : ∀ t k (hk : k < (G.committees t).val.length) l,
    Spec.ptcIndices Spec.P o (view t) (L.epoch t).val ((L.startSlot t).val + k) = .ok l →
      ((G.committees t).val[k]).val.map (·.val) = l
  committeesLength : ∀ t, (G.committees t).val.length = Spec.P.SLOTS_PER_EPOCH
  ptcDomain : u8s G.ptcDomain.val = Spec.DOMAIN_PTC_ATTESTER.toList
  ptcSize : G.ptcSize.val = Spec.P.PTC_SIZE
  slotsPerEpochUsize : G.slotsPerEpochUsize.val = Spec.P.SLOTS_PER_EPOCH
  /-- `WindowContract`, and `PtcWindowWrites` holds the window of the state and writes only
  it. -/
  window : WindowContract G.window G.wview G.committed natsOf
    (fun t => (natsOf t).length = Spec.P.PTC_SIZE)
    ((Spec.P.MIN_SEED_LOOKAHEAD + 2) * Spec.P.SLOTS_PER_EPOCH)
  windowBorrow : ∀ t, G.wview (G.windowBorrow t) = (view t).ptc_window
  windowReturn : ∀ t w, view (G.windowReturn t w) = { view t with ptc_window := G.committed w }

theorem slots_lt_2_32 [Spec.PresetCfg.Bounds] : Spec.P.SLOTS_PER_EPOCH < 2 ^ 32 := by
  have : Spec.PresetCfg.v.SLOTS_PER_EPOCH ≤ 32 := Spec.PresetCfg.Bounds.slots_le
  show Spec.PresetCfg.v.SLOTS_PER_EPOCH < 2 ^ 32
  omega

/-- The composed Gloas lookahead returns the state of `process_proposer_lookahead`. -/
theorem lookahead_spec [Spec.PresetCfg.Ok] [Spec.PresetCfg.Bounds] (L : LookaheadGlue σ)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (hL : LookaheadLinks L o view)
    (hpi : GloasProposerIndices L view) (st : σ) (hn1 : LookaheadN1 L st)
    (hpl : (view st).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s1 : Spec.BeaconState) (h1 : Spec.process_proposer_lookahead Spec.P o (view st) = .ok s1) :
    ∃ st1, lookahead L st = ok (some st1) ∧ view st1 = s1 := by
  obtain ⟨l1, -, hs1⟩ :=
    Spec.map_ok_inv ((Spec.process_proposer_lookahead_eq o (view st)).symm.trans h1)
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (L.epoch st).val =
      .ok (L.startSlot st).val := by
    obtain ⟨n, hn⟩ := Spec.process_proposer_lookahead_start _ _ _ _ h1 _
      (Spec.get_current_epoch_mainnet (view st))
    rw [← hL.epoch st _ (Spec.get_current_epoch_mainnet (view st))] at hn
    rw [hL.startSlot st n hn, hn]
  have hla := next_proposer_lookahead_spec L.hash L.effectiveBalances st Spec.P o hL.hash
    (view st) (hL.effectiveBalances st) (L.lookahead st) (hL.lookahead st) (L.proposerIndices st)
    L.proposerDomain hL.proposerDomain (L.epoch st) (hL.epoch st) (hpi st) (L.mix st)
    (hL.mix st) (L.startSlot st) hstart (L.constants st) (hL.constants st)
    slots_lt_2_32 hn1 hL.usize64 s1 h1
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hla
  unfold lookahead
  rw [hr]
  simp only [bind_tc_ok]
  have hlen : v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := (·.val)), hv, Spec.process_proposer_lookahead_len _ _ _ _ h1, hpl]
  obtain ⟨st1, hw, hv1⟩ := hL.writeLookahead st v hlen
  refine ⟨st1, by rw [hw], ?_⟩
  rw [hv1, hv, hs1]
  rfl

/-- The composed PTC window returns the state of `process_ptc_window`. -/
theorem ptcWindow_spec [Spec.PresetCfg.Ok] (L : LookaheadGlue σ) (G : PtcGlue σ E)
    (o : Spec.Oracle) (view : σ → Spec.BeaconState) (hL : LookaheadLinks L o view)
    (hP : PtcLinks L G o view) (st : σ) (hn1 : PtcN1 G st)
    (hptc : (view st).ptc_window.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 2) * Spec.P.SLOTS_PER_EPOCH)
    (s2 : Spec.BeaconState) (h2 : Spec.process_ptc_window Spec.P o (view st) = .ok s2) :
    ∃ st', ptcWindow L G st = ok (some st') ∧ view st' = s2 := by
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (L.epoch st).val =
      .ok (L.startSlot st).val := by
    obtain ⟨e, n, -, ⟨ce, hce, rfl⟩, hn, -⟩ := spec_ptc_window_get Spec.P o (view st) s2 h2
    rw [← hL.epoch st ce hce] at hn
    rw [hL.startSlot st n hn, hn]
  have hptc4 := ptc_for_epoch_spec L.hash L.effectiveBalances st Spec.P o hL.hash (view st)
    (hL.effectiveBalances st) (G.committees st) (hP.committeesLength st) G.ptcDomain
    hP.ptcDomain (L.epoch st) (hL.epoch st) (L.mix st) (hL.mix st) (L.startSlot st)
    hstart (hP.committees st) hn1 G.ptcSize hP.ptcSize (L.constants st)
    (hL.constants st) Spec.P_slots_pos hL.usize64 s2 h2
  obtain ⟨r2, hr2, ptcs, rfl, hptcs⟩ := spec_imp_exists hptc4
  unfold ptcWindow
  rw [hr2]
  simp only [bind_tc_ok]
  have hwin := ptc_window_writes_spec Spec.P o G.window G.wview G.committed _ hP.window (view st)
    s2 h2 ptcs hptcs (G.windowBorrow st) (hP.windowBorrow st) hptc G.slotsPerEpochUsize
    hP.slotsPerEpochUsize
  obtain ⟨⟨rw, w⟩, hrw, w', hw', hc'⟩ := spec_imp_exists hwin
  simp only [Prod.mk.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  rw [hrw]
  simp only [bind_tc_ok, uncurry_apply_pair]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨l2, -, hs2⟩ := Spec.map_ok_inv ((Spec.process_ptc_window_eq o (view st)).symm.trans h2)
  rw [hP.windowReturn, hc', hs2]
  rfl

end EpochProofs.Compose
