import EpochProofs.AeneasCompat
import EpochProofs.TranslatedSteps.ListWrites
import EpochProofs.SpecFacts.ArithmeticBounds
import EpochProofs.LighthouseModel.Order

/-!
# The proposer lookahead and the PTC window, composed from the translated functions

`lookahead` is `process_proposer_lookahead` of `single_pass.rs`: the translated
`next_proposer_lookahead` and the `Vector::new` write. `ptcWindow` is `process_ptc_window`: the
translated `ptc_for_epoch` and `shift_window`. The reads, the hash, the effective balance source,
the committees from the committee cache and the writes are untranslated code
(`UntranslatedLookahead`, `UntranslatedPtcWindow`), each with the fact that links it to the spec
(`UntranslatedLookaheadFacts`, `UntranslatedPtcWindowFacts`). `translatedLookahead_matches_model`
and `translatedPtcWindow_matches_model` show that they return the states of the models. The Fulu
lookahead (`translatedLookaheadFulu_matches_model`) differs only in the proposer candidates.
-/

namespace EpochProofs.Spec

/-- `process_proposer_lookahead` keeps the length of the lookahead. -/
theorem process_proposer_lookahead_len (p : Preset) (oracle : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead p oracle s = .ok s') :
    s'.proposer_lookahead.length = s.proposer_lookahead.length := by
  unfold process_proposer_lookahead at h
  simp only [arithmetic_bind_ok_iff] at h
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
theorem process_proposer_lookahead_start (p : Preset) (oracle : Oracle) (s s' : BeaconState)
    (h : process_proposer_lookahead p oracle s = .ok s') (ce : Nat)
    (hce : get_current_epoch p s = .ok ce) :
    ∃ n, compute_start_slot_at_epoch p (ce + p.MIN_SEED_LOOKAHEAD + 1) = .ok n := by
  unfold process_proposer_lookahead at h
  simp only [arithmetic_bind_ok_iff] at h
  obtain ⟨les, -, ce', hce', e1, he1, e, he, props, hprops, -⟩ := h
  have hc : ce' = ce := by
    rw [get_current_epoch_ok_eq hce', get_current_epoch_ok_eq hce]
  subst hc
  rw [uint64Add_ok_sum he, uint64Add_ok_sum he1] at hprops
  unfold get_beacon_proposer_indices compute_proposer_indices at hprops
  simp only [arithmetic_bind_ok_iff] at hprops
  obtain ⟨-, -, -, -, n, hn, -⟩ := hprops
  exact ⟨n, hn⟩

end EpochProofs.Spec

namespace EpochProofs.TranslatedEpoch

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

/-- The untranslated Rust of `process_proposer_lookahead`. -/
structure UntranslatedLookahead (RustState : Type) where
  /-- `Sha256Hash`, and the `BeaconState` as the effective balance source. -/
  Hash : Type
  hash : ShuffleHashInst Hash
  effectiveBalances : EffectiveBalanceSource RustState
  /-- The reads: the lookahead, the proposer candidates, the lookahead epoch
  (`current_epoch + min_seed_lookahead + 1`), its mix and start slot, `selection_constants`. -/
  lookahead : RustState → Slice U64
  /-- The validators that the proposer selection draws from. -/
  proposerIndices : RustState → Slice Usize
  proposerDomain : Array U8 4#usize
  epoch : RustState → U64
  mix : RustState → Array U8 32#usize
  startSlot : RustState → U64
  constants : RustState → LighthouseSelectionConstants
  /-- `*state.proposer_lookahead_mut()? = Vector::new(lookahead)?`. -/
  writeLookahead : RustState → alloc.vec.Vec U64 → Option RustState

/-- The untranslated Rust of `process_ptc_window`. It reads the lookahead epoch, its mix and
start slot and the constants as `process_proposer_lookahead` does. -/
structure UntranslatedPtcWindow (RustState RustError : Type) where
  /-- The committees of each slot of the lookahead epoch, from the committee cache built for
  it. -/
  committees : RustState → Slice (alloc.vec.Vec Usize)
  ptcDomain : Array U8 4#usize
  ptcSize : Usize
  slotsPerEpochUsize : Usize
  /-- `PtcWindowWrites`. -/
  Window : Type
  windowOperations : LighthouseWindowWrites Window (alloc.vec.Vec Usize) RustError
  windowEntries : Window → List (List Nat)
  committedWindow : Window → List (List Nat)
  windowBorrow : RustState → Window
  windowReturn : RustState → Window → RustState

variable {RustState RustError : Type}

/-- `process_proposer_lookahead`, as the call of the translated `next_proposer_lookahead`
joined by the untranslated code. `none`: the Rust returns an error. -/
def translatedLookahead (lookaheadCode : UntranslatedLookahead RustState)
    (rustState : RustState) : Result (Option RustState) := do
  let r ← per_epoch_processing.epoch_committees.next_proposer_lookahead lookaheadCode.hash
    lookaheadCode.effectiveBalances rustState (lookaheadCode.lookahead rustState)
      (lookaheadCode.proposerIndices rustState) lookaheadCode.proposerDomain
      (lookaheadCode.epoch rustState)
    (lookaheadCode.mix rustState) (lookaheadCode.startSlot rustState)
      (lookaheadCode.constants rustState)
  match r with
  | .Err _ => ok none
  | .Ok look => ok (lookaheadCode.writeLookahead rustState look)

/-- `process_ptc_window`, as the calls of the translated `ptc_for_epoch` and `shift_window`
joined by the untranslated code. `none`: the Rust returns an error. -/
def translatedPtcWindow (lookaheadCode : UntranslatedLookahead RustState)
    (ptcCode : UntranslatedPtcWindow RustState RustError)
    (rustState : RustState) : Result (Option RustState) := do
  let r ← per_epoch_processing.epoch_committees.ptc_for_epoch lookaheadCode.hash
    lookaheadCode.effectiveBalances rustState
    (ptcCode.committees rustState) ptcCode.ptcDomain (lookaheadCode.epoch rustState)
      (lookaheadCode.mix rustState) (lookaheadCode.startSlot rustState) ptcCode.ptcSize
    (lookaheadCode.constants rustState)
  match r with
  | .Err _ => ok none
  | .Ok ptcs =>
  let (r, w) ← per_epoch_processing.list_writes.shift_window ptcCode.windowOperations
    (ptcCode.windowBorrow rustState)
    ptcCode.slotsPerEpochUsize (alloc.vec.Vec.deref ptcs)
  match r with
  | .Err _ => ok none
  | .Ok _ => ok (some (ptcCode.windowReturn rustState w))

variable [Spec.CurrentPreset]

/-- The trusted facts about the untranslated code. The reads read the state they are given and
the write writes the spec value, so each fact holds for every state `t`. -/
structure UntranslatedLookaheadFacts (lookaheadCode : UntranslatedLookahead RustState)
    (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) : Prop where
  /-- `Sha256Hash` computes SHA-256, and the state gives its effective balances. -/
  hash : HashMatches lookaheadCode.hash oracle
  effectiveBalances : ∀ t, EffectiveBalancesMatch lookaheadCode.effectiveBalances t
    ((rustStateToSpec t).validators.map (·.effective_balance))
  /-- The reads of the lookahead, the domain and the constants are the spec values. -/
  lookahead : ∀ t, (lookaheadCode.lookahead t).val.map (·.val) =
    (rustStateToSpec t).proposer_lookahead
  proposerDomain : byteValues lookaheadCode.proposerDomain.val = Spec.DOMAIN_BEACON_PROPOSER.toList
  /-- The lookahead epoch is the current epoch plus `MIN_SEED_LOOKAHEAD` plus one. -/
  epoch : ∀ t current, Spec.get_current_epoch Spec.P (rustStateToSpec t) = .ok current →
    (lookaheadCode.epoch t).val = current + Spec.P.MIN_SEED_LOOKAHEAD + 1
  /-- `get_seed_mix` reads the mix that the spec `get_seed` reads. -/
  mix : ∀ t, SeedMixMatches Spec.P (rustStateToSpec t) (lookaheadCode.epoch t).val
    (lookaheadCode.mix t)
  /-- The first slot of the lookahead epoch. -/
  startSlot : ∀ t n, Spec.compute_start_slot_at_epoch Spec.P (lookaheadCode.epoch t).val = .ok n →
    (lookaheadCode.startSlot t).val = n
  constants : ∀ t, SelectionConstantsMatch Spec.P (lookaheadCode.constants t)
  /-- `Vector::new` accepts a lookahead of the vector length. -/
  writeLookahead : ∀ t v,
    v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH →
    ∃ t', lookaheadCode.writeLookahead t v = some t' ∧
      rustStateToSpec t' = { rustStateToSpec t with proposer_lookahead := v.val.map (·.val) }
  usize64 : Usize.max = U64.max

/-- The trusted facts about the untranslated code. -/
structure UntranslatedPtcWindowFacts (lookaheadCode : UntranslatedLookahead RustState)
    (ptcCode : UntranslatedPtcWindow RustState RustError) (oracle : Spec.Oracle)
    (rustStateToSpec : RustState → Spec.BeaconState) : Prop where
  /-- The committees from the committee cache built for the lookahead epoch. The cache is built
  fresh from the state, so only its inputs are trusted. -/
  committees : ∀ t k (hk : k < (ptcCode.committees t).val.length) l,
    Spec.ptcIndices Spec.P oracle (rustStateToSpec t) (lookaheadCode.epoch t).val
      ((lookaheadCode.startSlot t).val + k) = .ok l →
      ((ptcCode.committees t).val[k]).val.map (·.val) = l
  /-- One list of committee members for each slot of the epoch. -/
  committeesLength : ∀ t, (ptcCode.committees t).val.length = Spec.P.SLOTS_PER_EPOCH
  ptcDomain : byteValues ptcCode.ptcDomain.val = Spec.DOMAIN_PTC_ATTESTER.toList
  ptcSize : ptcCode.ptcSize.val = Spec.P.PTC_SIZE
  slotsPerEpochUsize : ptcCode.slotsPerEpochUsize.val = Spec.P.SLOTS_PER_EPOCH
  /-- `PtcWindowWritesMatchSpec`, and `PtcWindowWrites` holds the window of the state and writes only
  it. -/
  window : PtcWindowWritesMatchSpec ptcCode.windowOperations ptcCode.windowEntries
    ptcCode.committedWindow indexValues
    (fun t => (indexValues t).length = Spec.P.PTC_SIZE)
    ((Spec.P.MIN_SEED_LOOKAHEAD + 2) * Spec.P.SLOTS_PER_EPOCH)
  windowBorrow : ∀ t, ptcCode.windowEntries (ptcCode.windowBorrow t) =
    (rustStateToSpec t).ptc_window
  /-- The end of the borrow writes the committed window, and only it. -/
  windowReturn : ∀ t w, rustStateToSpec (ptcCode.windowReturn t w) =
    { rustStateToSpec t with ptc_window := ptcCode.committedWindow w }

theorem slots_lt_2_32 [Spec.CurrentPreset.Bounds] : Spec.P.SLOTS_PER_EPOCH < 2 ^ 32 := by
  have : Spec.CurrentPreset.values.SLOTS_PER_EPOCH ≤ 32 := Spec.CurrentPreset.Bounds.slots_le
  show Spec.CurrentPreset.values.SLOTS_PER_EPOCH < 2 ^ 32
  omega

/-- The composed Gloas lookahead returns the state of `process_proposer_lookahead`. -/
theorem translatedLookahead_matches_model [Spec.CurrentPreset.Valid] [Spec.CurrentPreset.Bounds]
    (lookaheadCode : UntranslatedLookahead RustState)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedLookaheadFacts lookaheadCode oracle rustStateToSpec)
    (hpi : ∀ t l, (Spec.get_active_validator_indices (rustStateToSpec t)
    (lookaheadCode.epoch t).val).filterM
        (fun index => do pure !(← Spec.listGet (rustStateToSpec t).validators index).slashed) =
          .ok l →
      (lookaheadCode.proposerIndices t).val.map (·.val) = l) (rustState : RustState)
    (hfitsShuffle : (lookaheadCode.proposerIndices rustState).val.length ≤ 2 ^ 24)
    (hpl : (rustStateToSpec rustState).proposer_lookahead.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH)
    (s1 : Spec.BeaconState) (h1 : Spec.process_proposer_lookahead Spec.P oracle
    (rustStateToSpec rustState) = .ok s1) :
    ∃ rustState1, translatedLookahead lookaheadCode rustState = ok (some rustState1) ∧
      rustStateToSpec rustState1 = s1 := by
  obtain ⟨l1, -, hs1⟩ :=
    Spec.map_ok_inv ((Spec.process_proposer_lookahead_eq oracle
      (rustStateToSpec rustState)).symm.trans h1)
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (lookaheadCode.epoch rustState).val =
      .ok (lookaheadCode.startSlot rustState).val := by
    obtain ⟨n, hn⟩ := Spec.process_proposer_lookahead_start _ _ _ _ h1 _
      (Spec.get_current_epoch_mainnet (rustStateToSpec rustState))
    rw [← hL.epoch rustState _ (Spec.get_current_epoch_mainnet (rustStateToSpec rustState))] at hn
    rw [hL.startSlot rustState n hn, hn]
  have hla := next_proposer_lookahead_spec lookaheadCode.hash lookaheadCode.effectiveBalances
    rustState Spec.P oracle hL.hash
    (rustStateToSpec rustState) (hL.effectiveBalances rustState) (lookaheadCode.lookahead rustState)
      (hL.lookahead rustState) (lookaheadCode.proposerIndices rustState)
    lookaheadCode.proposerDomain hL.proposerDomain (lookaheadCode.epoch rustState)
      (hL.epoch rustState) (hpi rustState) (lookaheadCode.mix rustState)
    (hL.mix rustState) (lookaheadCode.startSlot rustState) hstart
      (lookaheadCode.constants rustState) (hL.constants rustState)
    slots_lt_2_32 hfitsShuffle hL.usize64 s1 h1
  obtain ⟨r, hr, v, rfl, hv⟩ := spec_imp_exists hla
  unfold translatedLookahead
  rw [hr]
  simp only [bind_tc_ok]
  have hlen : v.val.length = (Spec.P.MIN_SEED_LOOKAHEAD + 1) * Spec.P.SLOTS_PER_EPOCH := by
    rw [← List.length_map (f := (·.val)), hv, Spec.process_proposer_lookahead_len _ _ _ _ h1, hpl]
  obtain ⟨rustState1, hw, hv1⟩ := hL.writeLookahead rustState v hlen
  refine ⟨rustState1, by rw [hw], ?_⟩
  rw [hv1, hv, hs1]
  rfl

/-- The composed PTC window returns the state of `process_ptc_window`. -/
theorem translatedPtcWindow_matches_model [Spec.CurrentPreset.Valid]
    (lookaheadCode : UntranslatedLookahead RustState)
    (ptcCode : UntranslatedPtcWindow RustState RustError)
    (oracle : Spec.Oracle) (rustStateToSpec : RustState → Spec.BeaconState)
    (hL : UntranslatedLookaheadFacts lookaheadCode oracle rustStateToSpec)
    (hP : UntranslatedPtcWindowFacts lookaheadCode ptcCode oracle rustStateToSpec)
    (rustState : RustState) 
    (hfitsShuffle : ∀ k (hk : k < (ptcCode.committees rustState).val.length),
      ((ptcCode.committees rustState).val[k]).val.length ≤ 2 ^ 24)
    (hptc : (rustStateToSpec rustState).ptc_window.length =
      (Spec.P.MIN_SEED_LOOKAHEAD + 2) * Spec.P.SLOTS_PER_EPOCH)
    (s2 : Spec.BeaconState) (h2 : Spec.process_ptc_window Spec.P oracle (rustStateToSpec rustState)
    = .ok s2) :
    ∃ rustState', translatedPtcWindow lookaheadCode ptcCode rustState = ok (some rustState') ∧
      rustStateToSpec rustState' = s2 := by
  have hstart : Spec.compute_start_slot_at_epoch Spec.P (lookaheadCode.epoch rustState).val =
      .ok (lookaheadCode.startSlot rustState).val := by
    obtain ⟨e, n, -, ⟨current, hce, rfl⟩, hn, -⟩ :=
      spec_ptc_window_get Spec.P oracle (rustStateToSpec rustState) s2 h2
    rw [← hL.epoch rustState current hce] at hn
    rw [hL.startSlot rustState n hn, hn]
  have hptc4 := ptc_for_epoch_spec lookaheadCode.hash lookaheadCode.effectiveBalances rustState
    Spec.P oracle hL.hash (rustStateToSpec rustState)
    (hL.effectiveBalances rustState) (ptcCode.committees rustState) (hP.committeesLength rustState)
      ptcCode.ptcDomain
    hP.ptcDomain (lookaheadCode.epoch rustState) (hL.epoch rustState) (lookaheadCode.mix rustState)
      (hL.mix rustState) (lookaheadCode.startSlot rustState)
    hstart (hP.committees rustState) hfitsShuffle ptcCode.ptcSize hP.ptcSize
      (lookaheadCode.constants rustState)
    (hL.constants rustState) Spec.P_slots_pos hL.usize64 s2 h2
  obtain ⟨r2, hr2, ptcs, rfl, hptcs⟩ := spec_imp_exists hptc4
  unfold translatedPtcWindow
  rw [hr2]
  simp only [bind_tc_ok]
  have hwin := ptc_window_writes_spec Spec.P oracle ptcCode.windowOperations ptcCode.windowEntries
    ptcCode.committedWindow _ hP.window (rustStateToSpec rustState)
    s2 h2 ptcs hptcs (ptcCode.windowBorrow rustState) (hP.windowBorrow rustState) hptc
      ptcCode.slotsPerEpochUsize
    hP.slotsPerEpochUsize
  obtain ⟨⟨rw, w⟩, hrw, w', hw', hc'⟩ := spec_imp_exists hwin
  simp only [Prod.mk.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  rw [hrw]
  simp only [bind_tc_ok, uncurry_apply_pair]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨l2, -, hs2⟩ := Spec.map_ok_inv
    ((Spec.process_ptc_window_eq oracle (rustStateToSpec rustState)).symm.trans h2)
  rw [hP.windowReturn, hc', hs2]
  rfl

end EpochProofs.TranslatedEpoch
