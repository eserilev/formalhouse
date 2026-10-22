import EpochProofs.Sanity.Invariants.FuluBalance

/-!
# The invariants of every reachable Fulu state

This file is `Reachable.lean` for Fulu. `ReachableFulu` states come from a start state by
`state_transition_fulu` steps on mainnet. The start state has the invariants of a genesis
state. Then every input of the Fulu `process_epoch` in a reachable run has the facts that
`EpochInputOk''` lists (`fulu_reachable_invariants`):

- `BoundaryOk`: `FfgInvariant`, `RowsOk`, and `effective_balance ≤ 256 * balance` for every
  validator that is eligible for rewards (from the budget of the epoch, `FuluBalance.lean`);
- a `u64` slot, `EBOk`, `ExitEpochsU64`;
- `PubkeysUnique`, `ConsolidationsInRange`, `WithdrawableU64`, `WithdrawableValid`;
- the economic facts `Econ`, which stay a hypothesis on the run, as for Gloas.

The supply bound (the total active balance before each block is at most 139 million ETH) is a
hypothesis on the run, as for Gloas.
-/

namespace EpochProofs.Spec

open FuluTransitionSanity

/-- The Fulu `process_epoch` on mainnet. -/
abbrev process_epoch_fulu_m (o : Oracle) : BeaconState → SpecM BeaconState :=
  process_epoch_fulu Preset.mainnet FuluConfig.mainnet o

/-- The Fulu `process_epoch` keeps `ExitDelay`. -/
theorem process_epoch_fulu_exitDelay (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu_m o s = .ok s') (hs : ExitDelay Preset.mainnet s) :
    ExitDelay Preset.mainnet s' :=
  process_epoch_fulu_validators_inv _ _ fuluCompat_mainnet o (ExitDelay Preset.mainnet)
    (fun _ _ hv hs => ExitDelay.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_registry_updates_exitDelay _ _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_exitDelay _ o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_exitDelay _ _ _ h' hs)
    s s' h hs

/-- The Fulu `process_epoch` keeps `ExitEpochsU64`. -/
theorem process_epoch_fulu_exitEpochsU64 (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu_m o s = .ok s') (hs : ExitEpochsU64 s) : ExitEpochsU64 s' :=
  process_epoch_fulu_validators_inv _ _ fuluCompat_mainnet o ExitEpochsU64
    (fun _ _ hv hs => ExitEpochsU64.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_registry_updates_exitEpochsU64 _ _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_exitEpochsU64 _ o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_exitEpochsU64 _ _ _ h' hs)
    s s' h hs

/-- The Fulu `process_epoch` keeps `WithdrawableU64`. -/
theorem process_epoch_fulu_withdrawableU64 (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu_m o s = .ok s') (hs : WithdrawableU64 s) : WithdrawableU64 s' :=
  process_epoch_fulu_validators_inv _ _ fuluCompat_mainnet o WithdrawableU64
    (fun _ _ hv hs => WithdrawableU64.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_registry_updates_withdrawableU64 _ _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_withdrawableU64 _ o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_withdrawableU64 _ _ _ h' hs)
    s s' h hs

/-! ## The slot loop -/

/-- The five step facts of `LoopInv` in the Fulu `process_slots` loop with target `slot`: the
slot step, the Fulu `process_epoch` (to `PostEpoch`), the check `BoundaryOk`, and the two slot
increments. The last three do not depend on the fork. -/
theorem loopInv_steps_fulu (o : Oracle) (fo : FuluOracle) (slot : Slot) (start : Slot)
    (hslot64 : slot < 2 ^ 64) :
    (∀ fs fs', process_slot_fulu Preset.mainnet o fo fs = .ok fs' → fs.state.slot < slot →
      LoopInv start fs.state → LoopInv start fs'.state) ∧
    (∀ s s', s.slot < slot → (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 →
      process_epoch_fulu_m o s = .ok s' → LoopInv start s → PostEpoch start s') ∧
    (∀ s, s.slot < slot → (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 →
      LoopInv start s → BoundaryOk s) ∧
    (∀ s, (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 → PostEpoch start s →
      LoopInv start { s with slot := s.slot + 1 }) ∧
    (∀ s, s.slot < slot → (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH ≠ 0 →
      LoopInv start s → LoopInv start { s with slot := s.slot + 1 }) := by
  have hg := loopInv_steps o slot start hslot64
  refine ⟨?_, ?_, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩
  · intro t t' ht _ hP
    obtain ⟨hf, hcs⟩ := process_slot_fulu_frame _ o fo t t' ht
    have hsl := hcs.1
    obtain ⟨hffg, hrows, hd, hx, hst, s0, n, h0, hb, hn, hstrict⟩ := hP
    exact ⟨hffg.of_checkpointsStable hcs,
      (process_slot_fulu_len _ o fo t t' ht).rowsOk hrows, ExitDelay.of_validators_eq hf.1 hd,
      ExitEpochsU64.of_validators_eq hf.1 hx, hsl ▸ hst,
      s0, n, h0,
      Budget.of_eq hf.1 hf.2.1 (hsl ▸ hb), hsl ▸ hn, hsl ▸ hstrict⟩
  · intro t t' _ _ he hP
    obtain ⟨hffg, hrows, hd, hx, hst, s0, n, h0, hb, -⟩ := hP
    obtain ⟨he', hf⟩ := process_epoch_fulu_effective_balances o t t' he (hb.ebOk h0)
    obtain ⟨hffg', hsl⟩ := process_epoch_fulu_ffg _ _ o t t' he hffg
    exact ⟨hffg', process_epoch_fulu_rowsOk _ _ fuluCompat_mainnet o t t' he hrows,
      process_epoch_fulu_exitDelay o t t' he hd, process_epoch_fulu_exitEpochsU64 o t t' he hx,
      AfterEB.of_floor he' hf, hsl ▸ hst⟩

/-- The Fulu `process_slots` loop keeps `LoopInv` from slot `start`. -/
theorem process_slots_loop_fulu_reach (o : Oracle) (fo : FuluOracle) (slot : Slot)
    (start : Slot) (hslot64 : slot < 2 ^ 64) :
    ∀ fuel (fs fs' : FuluState), LoopInv start fs.state →
      process_slots_loop_fulu Preset.mainnet o fo (process_epoch_fulu_m o) slot fuel fs =
        .ok fs' → LoopInv start fs'.state := by
  have hst := loopInv_steps_fulu o fo slot start hslot64
  intro fuel
  induction fuel with
  | zero => intro fs fs' hP h; cases h; exact hP
  | succ n ih =>
    intro fs fs' hP h
    simp only [process_slots_loop_fulu] at h
    split at h
    · rename_i hlt
      obtain ⟨fs1, h1, h⟩ := specM_bind_ok h
      have hP1 := hst.1 _ _ h1 hlt hP
      have hs1 : fs1.state.slot = fs.state.slot := (process_slot_fulu_frame _ o fo _ _ h1).2.1
      have hlt1 : fs1.state.slot < slot := hs1 ▸ hlt
      obtain ⟨a, ha, h⟩ := specM_bind_ok h
      obtain ⟨m, hm, h⟩ := specM_bind_ok h
      rw [uint64Add_ok_eq ha] at hm
      have hm' := uint64Mod_ok_eq hm
      split at h
      · rename_i hz
        have hz' : (fs1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 := by
          rw [← hm']; simpa using hz
        obtain ⟨s2, he, h⟩ := specM_bind_ok h
        obtain ⟨_, hp, h⟩ := specM_bind_ok h
        cases hp
        have hQ := hst.2.1 _ _ hlt1 hz' he hP1
        have hs2 := process_epoch_fulu_slot _ _ o _ _ he
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        rw [uint64Add_ok_eq hc] at h
        rw [← hs2] at hz'
        exact ih _ _ (hst.2.2.2.1 _ hz' hQ) h
      · rename_i hz
        have hz' : (fs1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH ≠ 0 := by
          rw [← hm']; simpa using hz
        obtain ⟨_, h2, h⟩ := specM_bind_ok h
        cases h2
        obtain ⟨c, hc, h⟩ := specM_bind_ok h
        rw [uint64Add_ok_eq hc] at h
        exact ih _ _ (hst.2.2.2.2 _ hlt1 hz' hP1) h
    · cases h
      exact hP

/-- The Fulu `process_slots` from a state with the invariant: the result has `LoopInv` from the
old slot, at a later slot. -/
theorem process_slots_fulu_reach (o : Oracle) (fo : FuluOracle) (fs : FuluState) (slot : Slot)
    (hslot64 : slot < 2 ^ 64) (hs : ReachInv fs.state) :
    ∀ fs1, process_slots_fulu Preset.mainnet o fo (process_epoch_fulu_m o) fs slot = .ok fs1 →
      LoopInv fs.state.slot fs1.state ∧ fs.state.slot < fs1.state.slot := by
  intro fs1 h
  have hslot := process_slots_fulu_process_epoch_slot _ _ o fo _ _ _ h
  unfold process_slots_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i hlt
    refine ⟨process_slots_loop_fulu_reach o fo slot _ hslot64 _ _ _ hs h, ?_⟩
    rw [hslot]
    exact Decidable.of_not_not hlt

/-- One Fulu `state_transition` keeps the invariant. The block's slot is a `u64`, its sync
aggregate has at most 512 bits, and the total active balance before the block is at most 139
million ETH. -/
theorem state_transition_fulu_reach (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (fs fs' : FuluState) (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hslot64 : signed_block.message.slot < 2 ^ 64)
    (hbits : signed_block.message.body.sync_aggregate.sync_committee_bits.length ≤ 512)
    (htab : ∀ fs1, process_slots_fulu Preset.mainnet o fo (process_epoch_fulu_m o) fs
      signed_block.message.slot = .ok fs1 → ∀ tab,
        get_total_active_balance Preset.mainnet fs1.state = .ok tab → tab ≤ 139000000000000000)
    (hs : ReachInv fs.state)
    (h : state_transition_fulu Preset.mainnet o fo FuluConfig.mainnet c fs signed_block
      validate_result = .ok fs') : ReachInv fs'.state := by
  have hS : Preset.mainnet.SLOTS_PER_EPOCH = 32 := rfl
  unfold state_transition_fulu at h
  obtain ⟨fs1, h1, h⟩ := specM_bind_ok h
  obtain ⟨hinv1, hlt1⟩ := process_slots_fulu_reach o fo fs _ hslot64 hs fs1 h1
  have hs1 := process_slots_fulu_process_epoch_slot _ _ o fo fs fs1 _ h1
  obtain ⟨hffg1, hrows1, hd1, hx1, -, s0, n, h0, hb1, -, hstrict⟩ := hinv1
  have hn1 := hstrict hlt1
  have hblock : ∀ fs2, process_block_fulu Preset.mainnet o fo FuluConfig.mainnet c fs1
      signed_block.message = .ok fs2 → ReachInv fs2.state := by
    intro fs2 h2
    have hfar : fs1.state.slot / Preset.mainnet.SLOTS_PER_EPOCH < FAR_FUTURE_EPOCH := by
      rw [hs1]
      simp only [FAR_FUTURE_EPOCH, hS, Slot] at *
      omega
    obtain ⟨hb2, hd2, hsl2, -⟩ := process_block_fulu_budget_mainnet o fo c s0 _ n fs1 fs2 _ h2
      rfl hfar hd1 hb1 hbits (htab fs1 h1)
    refine ⟨hffg1.of_checkpointsStable (process_block_fulu_checkpointsStable _ o fo _ c _ _ _ h2),
      process_block_fulu_rowsOk _ o fo _ c _ _ _ h2 hrows1, hd2,
      process_block_fulu_validators_inv _ o fo _ c ExitEpochsU64
        (fun _ _ hv hs => ExitEpochsU64.of_validators_eq hv hs)
        (fun _ _ _ h' hs => process_operations_fulu_exitEpochsU64 _ o _ fuluCompat_mainnet _ _ _
          h' hs) _ _ _ h2 hx1,
      Nat.le_refl _, s0, n + 1, h0, hsl2 ▸ hb2, ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
    rw [hsl2]
    omega
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact hblock _ ‹_›)

/-! ## Reachable Fulu states -/

/-- The Fulu states that `state_transition_fulu` steps reach from `init` on mainnet. Each
block's slot is a `u64` and its sync aggregate has at most `SYNC_COMMITTEE_SIZE = 512` bits,
as their SSZ types say. -/
inductive ReachableFulu (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig) (init : FuluState) :
    FuluState → Prop
  | init : ReachableFulu o fo c init init
  | step {fs fs' : FuluState} (signed_block : FuluSignedBeaconBlock) (validate_result : Bool) :
      ReachableFulu o fo c init fs →
      signed_block.message.slot < 2 ^ 64 →
      signed_block.message.body.sync_aggregate.sync_committee_bits.length ≤ 512 →
      state_transition_fulu Preset.mainnet o fo FuluConfig.mainnet c fs signed_block
        validate_result = .ok fs' →
      ReachableFulu o fo c init fs'

/-- The supply hypothesis on a Fulu run: before each block, the total active balance is at most
139 million ETH. -/
def SupplyBoundFulu (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig) (init : FuluState) :
    Prop :=
  ∀ (fs fs1 : FuluState) (signed_block : FuluSignedBeaconBlock),
    ReachableFulu o fo c init fs →
    process_slots_fulu Preset.mainnet o fo (process_epoch_fulu_m o) fs
      signed_block.message.slot = .ok fs1 →
    ∀ tab, get_total_active_balance Preset.mainnet fs1.state = .ok tab → tab ≤ 139000000000000000

/-- The invariants of the start state: the facts of a genesis state. -/
structure FuluStartOk (s : BeaconState) : Prop where
  ffg : FfgInvariant Preset.mainnet s
  rows : RowsOk s
  exitDelay : ExitDelay Preset.mainnet s
  exitEpochs : ExitEpochsU64 s
  afterEB : AfterEB Preset.mainnet s
  pubkeys : PubkeysUnique s
  consolidations : ConsolidationsInRange s
  withdrawable : WithdrawableU64 s

/-- Every reachable Fulu state has the invariant. -/
theorem reachable_fulu_inv (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (init : FuluState) (hi : FuluStartOk init.state)
    (hsupply : SupplyBoundFulu o fo c init) :
    ∀ fs, ReachableFulu o fo c init fs → ReachInv fs.state := by
  intro fs hr
  induction hr with
  | init => exact ReachInv.of_start hi.ffg hi.rows hi.exitDelay hi.exitEpochs hi.afterEB
  | step signed_block validate_result hr hslot64 hbits h ih =>
    exact state_transition_fulu_reach o fo c _ _ signed_block validate_result hslot64 hbits
      (fun fs1 h1 => hsupply _ fs1 signed_block hr h1) ih h

/-- Every reachable Fulu state has unique pubkeys, in-range pending consolidations and `u64`
withdrawable epochs. -/
theorem reachable_fulu_tail (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (init : FuluState) (hi : FuluStartOk init.state) :
    ∀ fs, ReachableFulu o fo c init fs →
      PubkeysUnique fs.state ∧ ConsolidationsInRange fs.state ∧ WithdrawableU64 fs.state := by
  intro fs hr
  induction hr with
  | init => exact ⟨hi.pubkeys, hi.consolidations, hi.withdrawable⟩
  | step signed_block validate_result _ _ _ h ih =>
    exact ⟨state_transition_fulu_pubkeysUnique _ o fo _ fuluCompat_mainnet c _ _ _ _ ih.1 h,
      state_transition_fulu_inRange _ o fo _ fuluCompat_mainnet c _ _ _ _ ih.2.1 h,
      state_transition_fulu_withdrawableU64 _ o fo _ fuluCompat_mainnet c _ _ _ _ ih.2.2 h⟩

/-! ## Epoch inputs -/

/-- The states that the Fulu `process_slots` loop with target `slot` reaches from `fs` on
mainnet, one slot at a time. Each step runs `process_slot_fulu` below the target, then the Fulu
`process_epoch` at the last slot of an epoch, then moves to the next slot. -/
inductive SlotReachFulu (o : Oracle) (fo : FuluOracle) (fs : FuluState) (slot : Slot) :
    FuluState → Prop
  | refl : SlotReachFulu o fo fs slot fs
  | skip {t t1 : FuluState} : SlotReachFulu o fo fs slot t → t.state.slot < slot →
      process_slot_fulu Preset.mainnet o fo t = .ok t1 →
      (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH ≠ 0 →
      SlotReachFulu o fo fs slot { t1 with state := { t1.state with slot := t1.state.slot + 1 } }
  | epoch {t t1 : FuluState} {s2 : BeaconState} : SlotReachFulu o fo fs slot t →
      t.state.slot < slot → process_slot_fulu Preset.mainnet o fo t = .ok t1 →
      (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 →
      process_epoch_fulu_m o t1.state = .ok s2 →
      SlotReachFulu o fo fs slot { t1 with state := { s2 with slot := s2.slot + 1 } }

/-- The slot loop keeps `LoopInv`. -/
theorem SlotReachFulu.loopInv {o : Oracle} {fo : FuluOracle} {fs t : FuluState} {slot : Slot}
    (hslot64 : slot < 2 ^ 64) (hr : SlotReachFulu o fo fs slot t) (hs : ReachInv fs.state) :
    LoopInv fs.state.slot t.state := by
  have hst := loopInv_steps_fulu o fo slot fs.state.slot hslot64
  induction hr with
  | refl => exact hs
  | skip _ hlt ht hz ih =>
    have hP1 := hst.1 _ _ ht hlt ih
    have hs1 : _ = _ := (process_slot_fulu_frame _ o fo _ _ ht).2.1
    exact hst.2.2.2.2 _ (hs1 ▸ hlt) hz hP1
  | epoch _ hlt ht hz he ih =>
    have hP1 := hst.1 _ _ ht hlt ih
    have hs1 : _ = _ := (process_slot_fulu_frame _ o fo _ _ ht).2.1
    have hQ := hst.2.1 _ _ (hs1 ▸ hlt) hz he hP1
    have hs2 := process_epoch_fulu_slot _ _ o _ _ he
    rw [← hs2] at hz
    exact hst.2.2.2.1 _ hz hQ

/-- The slot loop keeps unique pubkeys, in-range pending consolidations and `u64` withdrawable
epochs. -/
theorem SlotReachFulu.tail {o : Oracle} {fo : FuluOracle} {fs t : FuluState} {slot : Slot}
    (hr : SlotReachFulu o fo fs slot t)
    (hs : PubkeysUnique fs.state ∧ ConsolidationsInRange fs.state ∧ WithdrawableU64 fs.state) :
    PubkeysUnique t.state ∧ ConsolidationsInRange t.state ∧ WithdrawableU64 t.state := by
  have hslot : ∀ t t1 : FuluState, process_slot_fulu Preset.mainnet o fo t = .ok t1 →
      PubkeysUnique t.state ∧ ConsolidationsInRange t.state ∧ WithdrawableU64 t.state →
      PubkeysUnique t1.state ∧ ConsolidationsInRange t1.state ∧ WithdrawableU64 t1.state := by
    intro t t1 ht ih
    have hv := (process_slot_fulu_frame _ o fo _ _ ht).1.1
    exact ⟨(PkSame.of_eq hv).pubkeysUnique ih.1,
      (process_slot_fulu_cstep _ o fo _ _ ht).inRange ih.2.1,
      WithdrawableU64.of_validators_eq hv ih.2.2⟩
  induction hr with
  | refl => exact hs
  | skip _ _ ht _ ih =>
    have h1 := hslot _ _ ht ih
    exact h1
  | epoch _ _ ht _ he ih =>
    have h1 := hslot _ _ ht ih
    have h2 : PubkeysUnique _ ∧ ConsolidationsInRange _ ∧ WithdrawableU64 _ :=
      ⟨process_epoch_fulu_pubkeysUnique _ _ fuluCompat_mainnet o _ _ he h1.1,
        process_epoch_fulu_inRange _ _ fuluCompat_mainnet o _ _ he h1.2.1,
        process_epoch_fulu_withdrawableU64 o _ _ he h1.2.2⟩
    exact h2

/-- The economic hypothesis on a Fulu run: every Fulu `process_epoch` input `t1` of a reachable
run satisfies `Econ`. An input comes from a state `t` that the slot loop reaches below its
target, by `process_slot_fulu`, at the last slot of an epoch. -/
def EpochEconFulu (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig) (init : FuluState)
    (Econ : BeaconState → Prop) : Prop :=
  ∀ (fs t t1 : FuluState) (slot : Slot), ReachableFulu o fo c init fs → slot < 2 ^ 64 →
    SlotReachFulu o fo fs slot t → t.state.slot < slot →
    process_slot_fulu Preset.mainnet o fo t = .ok t1 →
    (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 → Econ t1.state

/-- On mainnet, every input of the Fulu `process_epoch` in a reachable Fulu run has the
facts of `EpochInputOk''`. The start state has the invariants of a genesis state
(`FuluStartOk`). The total active balance before each block is at most 139 million ETH
(`SupplyBoundFulu`), and `Econ` holds at each epoch input (`EpochEconFulu`). -/
theorem fulu_reachable_invariants (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (init : FuluState) (hi : FuluStartOk init.state) (hsupply : SupplyBoundFulu o fo c init)
    (Econ : BeaconState → Prop) (hecon : EpochEconFulu o fo c init Econ)
    (fs t t1 : FuluState) (slot : Slot) (hr : ReachableFulu o fo c init fs)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachFulu o fo fs slot t) (hlt : t.state.slot < slot)
    (ht : process_slot_fulu Preset.mainnet o fo t = .ok t1)
    (hz : (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0) :
    EpochInputOk'' Econ t1.state := by
  have hst := loopInv_steps_fulu o fo slot fs.state.slot hslot64
  have hs := reachable_fulu_inv o fo c init hi hsupply fs hr
  have hinv := hst.1 _ _ ht hlt (hreach.loopInv hslot64 hs)
  have hs1 : t1.state.slot = t.state.slot := (process_slot_fulu_frame _ o fo _ _ ht).2.1
  have hlt1 : t1.state.slot < slot := hs1 ▸ hlt
  have hok := hst.2.2.1 _ hlt1 hz hinv
  have htail := hreach.tail (reachable_fulu_tail o fo c init hi fs hr)
  have hv := (process_slot_fulu_frame _ o fo _ _ ht).1.1
  have hp1 := (PkSame.of_eq hv).pubkeysUnique htail.1
  have hc1 := (process_slot_fulu_cstep _ o fo _ _ ht).inRange htail.2.1
  have hw1 := WithdrawableU64.of_validators_eq hv htail.2.2
  obtain ⟨-, -, hd, hx, -, s0, n, hA, hb, -⟩ := hinv
  exact ⟨⟨⟨hok, Nat.lt_trans hlt1 hslot64, hb.ebOk hA, hx, hecon fs t t1 slot hr hslot64 hreach hlt ht hz⟩,
    hp1, hc1⟩, hw1, withdrawableValid_of hd hw1⟩

end EpochProofs.Spec
