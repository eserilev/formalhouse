import EpochProofs.Spec.Block.Upgrade
import EpochProofs.Sanity.Invariants.FuluReachable
import EpochProofs.Sanity.Invariants.TotalityFulu
import EpochProofs.Sanity.SelectionPass

/-!
# The fork upgrades give start states

`upgrade_to_fulu` and `upgrade_to_gloas` keep every field that the start invariants read:
the validators, the balances, the inactivity scores, the participation flags, the checkpoints,
the slot and the pending consolidations (`UpgradeFrame`). So each upgrade keeps the eight start
facts of `FuluStartOk`. These are the start facts that the Gloas theorems take too
(`reachable_state_transition_sameOk'''`).

At the Gloas fork, the upgrade runs on the state right after the Fulu `process_epoch` of the
last Fulu epoch and the slot increment. `fulu_gloas_fork_startOk` proves the start facts there
from a reachable Fulu run, and `fulu_then_gloas_sameOk` runs the Gloas state transitions from
the upgraded state. `gloas_reachable_invariants` is `fulu_reachable_invariants` for Gloas: every
input of the Gloas `process_epoch` in a reachable Gloas run has `EpochInputOk''`.
-/

namespace EpochProofs.Spec

open FuluTransitionSanity

/-- The fields that the start invariants read stay the same. -/
def UpgradeFrame (s s' : BeaconState) : Prop :=
  s'.validators = s.validators ∧ s'.balances = s.balances ∧
    s'.inactivity_scores = s.inactivity_scores ∧
    s'.previous_epoch_participation = s.previous_epoch_participation ∧
    s'.current_epoch_participation = s.current_epoch_participation ∧
    CheckpointsStable s s' ∧ s'.pending_consolidations = s.pending_consolidations

theorem UpgradeFrame.refl (s : BeaconState) : UpgradeFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem UpgradeFrame.trans {s1 s2 s3 : BeaconState} (h12 : UpgradeFrame s1 s2)
    (h23 : UpgradeFrame s2 s3) : UpgradeFrame s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
    h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
    ⟨h23.2.2.2.2.2.1.1.trans h12.2.2.2.2.2.1.1, h23.2.2.2.2.2.1.2.1.trans h12.2.2.2.2.2.1.2.1,
      h23.2.2.2.2.2.1.2.2.1.trans h12.2.2.2.2.2.1.2.2.1,
      h23.2.2.2.2.2.1.2.2.2.trans h12.2.2.2.2.2.1.2.2.2⟩,
    h23.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

/-- A relation on states that onboarding keeps: reflexive, transitive, and true for a write of
the builder registry or of the pending deposits. -/
structure OnboardRel (R : BeaconState → BeaconState → Prop) : Prop where
  refl : ∀ s, R s s
  trans : ∀ {s1 s2 s3}, R s1 s2 → R s2 s3 → R s1 s3
  builders : ∀ s (b : List Builder), R s { s with builders := b }
  pending : ∀ s (d : List PendingDeposit), R s { s with pending_deposits := d }

theorem upgradeFrame_onboardRel : OnboardRel UpgradeFrame :=
  ⟨UpgradeFrame.refl, UpgradeFrame.trans, fun s _ => UpgradeFrame.refl s,
    fun s _ => UpgradeFrame.refl s⟩

/-- `add_builder_to_registry` writes only the builder registry. -/
theorem add_builder_to_registry_rel {R : BeaconState → BeaconState → Prop} (hR : OnboardRel R)
    (p : Preset) (state state' : BeaconState)
    (pubkey : BLSPubkey) (version : UInt8) (address : ExecutionAddress) (amount : Gwei)
    (slot : Slot) (h : add_builder_to_registry p state pubkey version address amount slot = .ok state') :
    R state state' := by
  unfold add_builder_to_registry at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  cases h
  exact hR.builders _ _

/-- One onboarding pass writes only the builder registry of the state. -/
theorem onboard_step_rel {R : BeaconState → BeaconState → Prop} (hR : OnboardRel R)
    (p : Preset) (o : Oracle) (validator_pubkeys : List BLSPubkey)
    (acc r : BeaconState × List PendingDeposit) (deposit : PendingDeposit)
    (h : onboard_step p o validator_pubkeys acc deposit = .ok r) : R acc.1 r.1 := by
  unfold onboard_step at h
  dsimp only at h
  split at h
  · cases h; exact hR.refl _
  split at h
  · split at h
    · cases h; exact hR.refl _
    split at h
    · cases h; exact hR.refl _
    split at h
    · cases h; exact hR.refl _
    obtain ⟨s1, h1, h⟩ := specM_bind_ok h
    cases h
    exact add_builder_to_registry_rel hR p _ _ _ _ _ _ _ h1
  · obtain ⟨_, -, h⟩ := specM_bind_ok h
    obtain ⟨_, -, h⟩ := specM_bind_ok h
    obtain ⟨_, -, h⟩ := specM_bind_ok h
    cases h
    exact hR.builders _ _

/-- The onboarding loop writes only the builder registry of the state. -/
theorem onboard_fold_rel {R : BeaconState → BeaconState → Prop} (hR : OnboardRel R)
    (p : Preset) (o : Oracle) (validator_pubkeys : List BLSPubkey) :
    ∀ (ds : List PendingDeposit) (acc r : BeaconState × List PendingDeposit),
      ds.foldlM (onboard_step p o validator_pubkeys) acc = .ok r → R acc.1 r.1
  | [], acc, r, h => by cases h; exact hR.refl _
  | d :: ds, acc, r, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨a1, h1, h⟩ := specM_bind_ok h
    exact hR.trans (onboard_step_rel hR p o _ _ _ _ h1) (onboard_fold_rel hR p o _ ds a1 r h)

/-- `onboard_builders_from_pending_deposits` writes only the builders and the pending
deposits. -/
theorem onboard_builders_rel {R : BeaconState → BeaconState → Prop} (hR : OnboardRel R)
    (p : Preset) (o : Oracle) (state state' : BeaconState)
    (h : onboard_builders_from_pending_deposits p o state = .ok state') : R state state' := by
  unfold onboard_builders_from_pending_deposits at h
  obtain ⟨⟨s1, pd⟩, h1, h⟩ := specM_bind_ok h
  cases h
  exact hR.trans (onboard_fold_rel hR p o _ _ _ _ h1) (hR.pending _ _)

theorem onboard_builders_frame (p : Preset) (o : Oracle) (state state' : BeaconState)
    (h : onboard_builders_from_pending_deposits p o state = .ok state') :
    UpgradeFrame state state' :=
  onboard_builders_rel upgradeFrame_onboardRel p o state state' h

/-- `initialize_ptc_window` does not write the state, and `upgrade_to_gloas` writes only the
fork, the Gloas fields, the pending deposits and the builders. -/
theorem upgrade_to_gloas_frame (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre : FuluState)
    (g : BeaconState) (h : upgrade_to_gloas p o c pre = .ok g) : UpgradeFrame pre.state g := by
  unfold upgrade_to_gloas at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  dsimp only at h
  refine UpgradeFrame.trans ?_ (onboard_builders_frame p o _ _ h)
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `upgrade_to_fulu` writes only the fork and the proposer lookahead. -/
theorem upgrade_to_fulu_frame (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre post : FuluState)
    (h : upgrade_to_fulu p o c pre = .ok post) : UpgradeFrame pre.state post.state := by
  unfold upgrade_to_fulu at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `UpgradeFrame` keeps the eight start facts. -/
theorem FuluStartOk.of_frame {s s' : BeaconState} (hf : UpgradeFrame s s') (h : FuluStartOk s) :
    FuluStartOk s' := by
  obtain ⟨hv, hb, hi, hpp, hcp, hcs, hpc⟩ := hf
  refine ⟨h.ffg.of_checkpointsStable hcs, ?_, ExitDelay.of_validators_eq hv h.exitDelay,
    ExitEpochsU64.of_validators_eq hv h.exitEpochs, AfterEB.of_eq hv hb h.afterEB,
    (PkSame.of_eq hv).pubkeysUnique h.pubkeys, ?_, WithdrawableU64.of_validators_eq hv h.withdrawable⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.rows
    exact ⟨by rw [hb, hv]; exact h1, by rw [hi, hv]; exact h2, by rw [hpp, hv]; exact h3,
      by rw [hcp, hv]; exact h4⟩
  · intro c hc
    rw [hpc] at hc
    rw [hv]
    exact h.consolidations c hc

/-- `upgrade_to_fulu` keeps the start facts of the Electra state. -/
theorem upgrade_to_fulu_startOk (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre post : FuluState)
    (h : upgrade_to_fulu p o c pre = .ok post) (hs : FuluStartOk pre.state) :
    FuluStartOk post.state :=
  FuluStartOk.of_frame (upgrade_to_fulu_frame p o c pre post h) hs

/-- `upgrade_to_gloas` keeps the start facts of the Fulu state. -/
theorem upgrade_to_gloas_startOk (p : Preset) (o : Oracle) (c : UpgradeConfig) (pre : FuluState)
    (g : BeaconState) (h : upgrade_to_gloas p o c pre = .ok g) (hs : FuluStartOk pre.state) :
    FuluStartOk g :=
  FuluStartOk.of_frame (upgrade_to_gloas_frame p o c pre g h) hs

/-! ## Vector lengths after the Gloas upgrade -/

/-- The fields of `VectorLengths` that onboarding does not write. -/
def VecFrame (s s' : BeaconState) : Prop :=
  s'.block_roots = s.block_roots ∧ s'.state_roots = s.state_roots ∧
    s'.randao_mixes = s.randao_mixes ∧ s'.slashings = s.slashings ∧
    s'.justification_bits = s.justification_bits ∧
    s'.current_sync_committee = s.current_sync_committee ∧
    s'.next_sync_committee = s.next_sync_committee ∧
    s'.proposer_lookahead = s.proposer_lookahead ∧
    s'.execution_payload_availability = s.execution_payload_availability ∧
    s'.builder_pending_payments = s.builder_pending_payments ∧ s'.ptc_window = s.ptc_window

theorem vecFrame_onboardRel : OnboardRel VecFrame := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  intro s1 s2 s3 h12 h23
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h12
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h23
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11⟩

/-- A successful balance weighted selection loop that starts with at most `size` items returns
exactly `size` items. -/
theorem compute_balance_weighted_selection_loop_length (p : Preset) (o : Oracle)
    (indices : List ValidatorIndex) (seed : Bytes32) (size : Uint64) (shuffle_indices : Bool)
    (total : Uint64) (effective_balances : List Gwei) :
    ∀ fuel (selected : List ValidatorIndex) (i : Uint64) (random_bytes : Bytes32)
      (r : List ValidatorIndex), selected.length ≤ size →
      compute_balance_weighted_selection_loop p o indices seed size shuffle_indices total
        effective_balances fuel selected i random_bytes = .ok r → r.length = size
  | 0, _, _, _, _, _, h => by
    simp only [compute_balance_weighted_selection_loop] at h
    cases h
  | fuel + 1, selected, i, random_bytes, r, hle, h => by
    rw [selection_loop_succ] at h
    split at h
    · rename_i hlt
      obtain ⟨c, -, h⟩ := specM_bind_ok h
      obtain ⟨_, -, h⟩ := specM_bind_ok h
      have hsel' : (selected ++ c.1.toList).length ≤ size := by
        cases c.1 <;> simp <;> omega
      exact compute_balance_weighted_selection_loop_length p o indices seed size shuffle_indices
        total effective_balances fuel _ _ _ r hsel' h
    · cases h
      omega

/-- A successful balance weighted selection returns `size` items. -/
theorem compute_balance_weighted_selection_length (p : Preset) (o : Oracle) (state : BeaconState)
    (indices : List ValidatorIndex) (seed : Bytes32) (size : Uint64) (shuffle_indices : Bool)
    (r : List ValidatorIndex)
    (h : compute_balance_weighted_selection p o state indices seed size shuffle_indices = .ok r) :
    r.length = size := by
  unfold compute_balance_weighted_selection at h
  dsimp only at h
  split at h
  · obtain ⟨_, h0, -⟩ := specM_bind_ok h
    cases h0
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  exact compute_balance_weighted_selection_loop_length p o _ _ _ _ _ _ _ [] _ _ r
    (Nat.zero_le _) h

/-- A successful `compute_ptc` returns `PTC_SIZE` validators. -/
theorem compute_ptc_length (p : Preset) (o : Oracle) (state : BeaconState) (slot : Slot)
    (r : List ValidatorIndex) (h : compute_ptc p o state slot = .ok r) : r.length = p.PTC_SIZE := by
  unfold compute_ptc at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  exact compute_balance_weighted_selection_length p o _ _ _ _ _ r h

/-- A successful `mapM` gives one result for each item, and each result is the `f` value of its
item. -/
theorem mapM_ok_forall {α β : Type} (f : α → SpecM β) (P : β → Prop)
    (hf : ∀ a b, f a = .ok b → P b) (l : List α) (r : List β) (h : l.mapM f = .ok r) :
    r.length = l.length ∧ ∀ b ∈ r, P b := by
  obtain ⟨hlen, hget⟩ := mapM_ok_getElem f l r h
  refine ⟨hlen, fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  exact hf _ _ (hget i (hlen ▸ hi) hi)

/-- `initialize_ptc_window` returns `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH` committees of
`PTC_SIZE` validators. -/
theorem initialize_ptc_window_lengths (p : Preset) (o : Oracle) (state : BeaconState)
    (w : List (List ValidatorIndex)) (h : initialize_ptc_window p o state = .ok w) :
    w.length = (p.MIN_SEED_LOOKAHEAD + 2) * p.SLOTS_PER_EPOCH ∧
      ∀ ptc ∈ w, ptc.length = p.PTC_SIZE := by
  unfold initialize_ptc_window at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨per, hper, h⟩ := specM_bind_ok h
  cases h
  obtain ⟨hlen, hall⟩ := mapM_ok_forall _
    (fun b : List (List ValidatorIndex) => b.length = p.SLOTS_PER_EPOCH ∧
      ∀ ptc ∈ b, ptc.length = p.PTC_SIZE) (fun e b hb => by
        obtain ⟨_, -, hb⟩ := specM_bind_ok hb
        obtain ⟨_, -, hb⟩ := specM_bind_ok hb
        have := mapM_ok_forall _ (fun ptc : List ValidatorIndex => ptc.length = p.PTC_SIZE)
          (fun i ptc hi => by
            obtain ⟨_, -, hi⟩ := specM_bind_ok hi
            exact compute_ptc_length p o state _ ptc hi) _ b hb
        simpa using this) _ per hper
  simp only [List.length_range] at hlen
  have hflat : per.flatten.length = (1 + p.MIN_SEED_LOOKAHEAD) * p.SLOTS_PER_EPOCH := by
    rw [List.length_flatten, ← hlen]
    have : ∀ l : List (List (List ValidatorIndex)), (∀ b ∈ l, b.length = p.SLOTS_PER_EPOCH ∧
        ∀ ptc ∈ b, ptc.length = p.PTC_SIZE) →
        (l.map List.length).sum = l.length * p.SLOTS_PER_EPOCH := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [(hl b List.mem_cons_self).1, ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'))]
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact this per hall
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, hflat]
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · intro ptc hm
    simp only [List.mem_append, List.mem_replicate, List.mem_flatten] at hm
    rcases hm with ⟨-, rfl⟩ | ⟨b, hb, hm⟩
    · exact List.length_replicate
    · exact (hall b hb).2 ptc hm

/-- The Gloas upgrade gives the SSZ vector lengths of the Gloas state from those of the Fulu
state. -/
theorem upgrade_to_gloas_vectorLengths (p : Preset) (o : Oracle) (c : UpgradeConfig)
    (pre : FuluState) (g : BeaconState) (h : upgrade_to_gloas p o c pre = .ok g)
    (hv : pre.state.FuluVectorLengths p) : g.VectorLengths p := by
  unfold upgrade_to_gloas at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨w, hw, h⟩ := specM_bind_ok h
  dsimp only at h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ :=
    onboard_builders_rel vecFrame_onboardRel p o _ _ h
  obtain ⟨hw1, hw2⟩ := initialize_ptc_window_lengths p o _ w hw
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b1]; exact v1
  · rw [b2]; exact v2
  · rw [b3]; exact v3
  · rw [b4]; exact v4
  · rw [b5]; exact v5
  · rw [b6]; exact v6
  · rw [b7]; exact v7
  · rw [b8]; exact v8
  · rw [b9]; exact List.length_replicate
  · rw [b10]; exact List.length_replicate
  · rw [b11]; exact hw1
  · rw [b11]; exact hw2

/-! ## The Gloas fork in a Fulu run -/

/-- The state at the Gloas fork has the start facts. In a reachable Fulu run, the slot loop
reaches `t`, `process_slot_fulu` gives `t1` at the last slot of an epoch, and the Fulu
`process_epoch` gives `s2`. The slot increment gives the input of `upgrade_to_gloas`. -/
theorem fulu_fork_state_startOk (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (init : FuluState) (hi : FuluStartOk init.state) (hsupply : SupplyBoundFulu o fo c init)
    (fs t t1 : FuluState) (s2 : BeaconState) (slot : Slot) (hr : ReachableFulu o fo c init fs)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachFulu o fo fs slot t) (hlt : t.state.slot < slot)
    (ht : process_slot_fulu Preset.mainnet o fo t = .ok t1)
    (hz : (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0)
    (he : process_epoch_fulu_m o t1.state = .ok s2) :
    FuluStartOk { s2 with slot := s2.slot + 1 } := by
  have hst := loopInv_steps_fulu o fo slot fs.state.slot hslot64
  have hs := reachable_fulu_inv o fo c init hi hsupply fs hr
  have hinv := hst.1 _ _ ht hlt (hreach.loopInv hslot64 hs)
  have hs1 : t1.state.slot = t.state.slot := (process_slot_fulu_frame _ o fo _ _ ht).2.1
  have hlt1 : t1.state.slot < slot := hs1 ▸ hlt
  have hpost := hst.2.1 _ _ hlt1 hz he hinv
  have hs2 := process_epoch_fulu_slot _ _ o _ _ he
  have hz2 : (s2.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 := by rw [hs2]; exact hz
  have hloop := hst.2.2.2.1 _ hz2 hpost
  have htail := hreach.tail (reachable_fulu_tail o fo c init hi fs hr)
  have hv := (process_slot_fulu_frame _ o fo _ _ ht).1.1
  have hp1 := (PkSame.of_eq hv).pubkeysUnique htail.1
  have hc1 := (process_slot_fulu_cstep _ o fo _ _ ht).inRange htail.2.1
  have hw1 := WithdrawableU64.of_validators_eq hv htail.2.2
  have hp2 := process_epoch_fulu_pubkeysUnique _ _ fuluCompat_mainnet o _ _ he hp1
  have hc2 := process_epoch_fulu_inRange _ _ fuluCompat_mainnet o _ _ he hc1
  have hw2 := process_epoch_fulu_withdrawableU64 o _ _ he hw1
  have hA2 : AfterEB Preset.mainnet s2 := hpost.2.2.2.2.1
  obtain ⟨hffg, hrows, hd, hx, -⟩ := hloop
  exact ⟨hffg, hrows, hd, hx, hA2, hp2, hc2, hw2⟩

/-- The Gloas state that `upgrade_to_gloas` makes at the fork of a reachable Fulu run has the
start facts of the Gloas theorems. -/
theorem fulu_gloas_fork_startOk (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (uc : UpgradeConfig) (init : FuluState) (hi : FuluStartOk init.state)
    (hsupply : SupplyBoundFulu o fo c init)
    (fs t t1 : FuluState) (s2 g : BeaconState) (slot : Slot) (hr : ReachableFulu o fo c init fs)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachFulu o fo fs slot t) (hlt : t.state.slot < slot)
    (ht : process_slot_fulu Preset.mainnet o fo t = .ok t1)
    (hz : (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0)
    (he : process_epoch_fulu_m o t1.state = .ok s2)
    (hup : upgrade_to_gloas Preset.mainnet o uc
      { t1 with state := { s2 with slot := s2.slot + 1 } } = .ok g) :
    FuluStartOk g :=
  upgrade_to_gloas_startOk _ o uc _ g hup
    (fulu_fork_state_startOk o fo c init hi hsupply fs t t1 s2 slot hr hslot64 hreach hlt ht hz he)

/-- A Fulu run that crosses the Gloas fork: every Gloas `state_transition` from a state that the
Gloas run reaches from the upgraded state `g` has the same `ok` results with any epoch function
`f` that agrees with `process_epoch` on the inputs that `EpochInputOk''` describes. The Gloas
supply and economic hypotheses are on the Gloas run, as in `reachable_state_transition_sameOk'''`. -/
theorem fulu_then_gloas_sameOk (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (uc : UpgradeConfig) (init : FuluState) (hi : FuluStartOk init.state)
    (hsupply : SupplyBoundFulu o fo c init)
    (fs t t1 : FuluState) (s2 g : BeaconState) (slot : Slot) (hr : ReachableFulu o fo c init fs)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachFulu o fo fs slot t) (hlt : t.state.slot < slot)
    (ht : process_slot_fulu Preset.mainnet o fo t = .ok t1)
    (hz : (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0)
    (he : process_epoch_fulu_m o t1.state = .ok s2)
    (hup : upgrade_to_gloas Preset.mainnet o uc
      { t1 with state := { s2 with slot := s2.slot + 1 } } = .ok g)
    (max_blobs_per_block : Epoch → Uint64) (GLOAS_FORK_EPOCH : Epoch)
    (hsupplyG : SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH g)
    (Econ : BeaconState → Prop) (hecon : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH g Econ)
    (f : BeaconState → SpecM BeaconState)
    (hf : ∀ t, EpochInputOk'' Econ t → SameOk (f t) (process_epoch Preset.mainnet o t))
    (s : BeaconState) (hrg : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH g s)
    (signed_block : SignedBeaconBlock) (validate_result : Bool)
    (hslotb : signed_block.message.slot < 2 ^ 64) :
    SameOk (state_transition_with o max_blobs_per_block GLOAS_FORK_EPOCH f s signed_block
        validate_result)
      (state_transition Preset.mainnet o max_blobs_per_block GLOAS_FORK_EPOCH s signed_block
        validate_result) := by
  have hg := fulu_gloas_fork_startOk o fo c uc init hi hsupply fs t t1 s2 g slot hr hslot64 hreach
    hlt ht hz he hup
  exact reachable_state_transition_sameOk''' o _ _ g hg.ffg hg.rows hg.exitDelay hg.exitEpochs
    hg.afterEB hg.pubkeys hg.consolidations hg.withdrawable hsupplyG Econ hecon f hf s hrg
    signed_block validate_result hslotb

/-! ## Every Gloas epoch input -/

/-- The states that the Gloas `process_slots` loop with target `slot` reaches from `s` on
mainnet, one slot at a time, below the target. -/
inductive SlotReachG (o : Oracle) (s : BeaconState) (slot : Slot) : BeaconState → Prop
  | refl : SlotReachG o s slot s
  | skip {t t1 : BeaconState} : SlotReachG o s slot t → t.slot < slot →
      process_slot Preset.mainnet o t = .ok t1 →
      (t1.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH ≠ 0 →
      SlotReachG o s slot { t1 with slot := t1.slot + 1 }
  | epoch {t t1 t2 : BeaconState} : SlotReachG o s slot t → t.slot < slot →
      process_slot Preset.mainnet o t = .ok t1 →
      (t1.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0 →
      process_epoch Preset.mainnet o t1 = .ok t2 →
      SlotReachG o s slot { t2 with slot := t2.slot + 1 }

/-- The Gloas slot loop keeps `LoopInv`. -/
theorem SlotReachG.loopInv {o : Oracle} {s t : BeaconState} {slot : Slot}
    (hslot64 : slot < 2 ^ 64) (hr : SlotReachG o s slot t) (hs : ReachInv s) :
    LoopInv s.slot t := by
  have hst := loopInv_steps o slot s.slot hslot64
  induction hr with
  | refl => exact hs
  | skip _ hlt ht hz ih =>
    have hP1 := hst.1 _ _ ht hlt ih
    have hs1 := (process_slot_frame _ o _ _ ht).2
    exact hst.2.2.2.2 _ (hs1 ▸ hlt) hz hP1
  | epoch _ hlt ht hz he ih =>
    have hP1 := hst.1 _ _ ht hlt ih
    have hs1 := (process_slot_frame _ o _ _ ht).2
    have hQ := hst.2.1 _ _ (hs1 ▸ hlt) hz he hP1
    have hs2 := process_epoch_slot _ o _ _ he
    rw [← hs2] at hz
    exact hst.2.2.2.1 _ hz hQ

/-- A target-bounded run of the loop is a run of `SlotReach`. -/
theorem SlotReachG.slotReach {o : Oracle} {s t : BeaconState} {slot : Slot}
    (hr : SlotReachG o s slot t) : SlotReach o s t := by
  induction hr with
  | refl => exact .refl
  | skip _ _ ht hz ih => exact .skip ih ht hz
  | epoch _ _ ht hz he ih => exact .epoch ih ht hz he

/-- On mainnet, every input of the Gloas `process_epoch` in a reachable Gloas run has the
facts of `EpochInputOk''`, if the start state has the eight start facts. The supply bound and
`Econ` are hypotheses on the run. -/
theorem gloas_reachable_invariants (o : Oracle) (max_blobs_per_block : Epoch → Uint64)
    (GLOAS_FORK_EPOCH : Epoch) (init : BeaconState) (hi : FuluStartOk init)
    (hsupply : SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH init)
    (Econ : BeaconState → Prop) (hecon : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH init Econ)
    (s t t1 : BeaconState) (slot : Slot)
    (hr : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH init s)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachG o s slot t) (hlt : t.slot < slot)
    (ht : process_slot Preset.mainnet o t = .ok t1)
    (hz : (t1.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0) :
    EpochInputOk'' Econ t1 := by
  have hst := loopInv_steps o slot s.slot hslot64
  have hs := reachable_inv o _ _ init hi.ffg hi.rows hi.exitDelay hi.exitEpochs hi.afterEB
    hsupply s hr
  have hinv := hst.1 _ _ ht hlt (hreach.loopInv hslot64 hs)
  have hs1 := (process_slot_frame _ o _ _ ht).2
  have hlt1 : t1.slot < slot := hs1 ▸ hlt
  have hok := hst.2.2.1 _ hlt1 hz hinv
  have htail := hreach.slotReach.tail (reachable_tail o _ _ init hi.pubkeys hi.consolidations s hr)
  have hwd := hreach.slotReach.withdrawable
    ⟨(reachable_inv o _ _ init hi.ffg hi.rows hi.exitDelay hi.exitEpochs hi.afterEB hsupply s hr).2.2.1,
      reachable_withdrawableU64 o _ _ init hi.withdrawable s hr⟩
  have hv := (process_slot_frame _ o _ _ ht).1.1
  have hp1 := (PkSame.of_eq hv).pubkeysUnique htail.1
  have hc1 := (process_slot_cstep _ o _ _ ht).inRange htail.2
  have hd1 := ExitDelay.of_validators_eq hv hwd.1
  have hw1 := WithdrawableU64.of_validators_eq hv hwd.2
  obtain ⟨-, -, -, hx, -, s0, n, hA, hb, -⟩ := hinv
  exact ⟨⟨⟨hok, Nat.lt_trans hlt1 hslot64, hb.ebOk hA, hx,
    hecon s t t1 hr hreach.slotReach ht hz⟩, hp1, hc1⟩, hw1, withdrawableValid_of hd1 hw1⟩

/-- A Fulu run that crosses the Gloas fork: every input of the Gloas `process_epoch` after the
fork has the facts of `EpochInputOk''`. -/
theorem fulu_then_gloas_reachable_invariants (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (uc : UpgradeConfig) (init : FuluState) (hi : FuluStartOk init.state)
    (hsupply : SupplyBoundFulu o fo c init)
    (fs t t1 : FuluState) (s2 g : BeaconState) (slot : Slot) (hr : ReachableFulu o fo c init fs)
    (hslot64 : slot < 2 ^ 64) (hreach : SlotReachFulu o fo fs slot t) (hlt : t.state.slot < slot)
    (ht : process_slot_fulu Preset.mainnet o fo t = .ok t1)
    (hz : (t1.state.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0)
    (he : process_epoch_fulu_m o t1.state = .ok s2)
    (hup : upgrade_to_gloas Preset.mainnet o uc
      { t1 with state := { s2 with slot := s2.slot + 1 } } = .ok g)
    (max_blobs_per_block : Epoch → Uint64) (GLOAS_FORK_EPOCH : Epoch)
    (hsupplyG : SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH g)
    (Econ : BeaconState → Prop) (hecon : EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH g Econ)
    (s u u1 : BeaconState) (slotG : Slot)
    (hrg : Reachable o max_blobs_per_block GLOAS_FORK_EPOCH g s)
    (hslotG : slotG < 2 ^ 64) (hreachG : SlotReachG o s slotG u) (hltG : u.slot < slotG)
    (hu : process_slot Preset.mainnet o u = .ok u1)
    (hzG : (u1.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0) :
    EpochInputOk'' Econ u1 :=
  gloas_reachable_invariants o _ _ g
    (fulu_gloas_fork_startOk o fo c uc init hi hsupply fs t t1 s2 g slot hr hslot64 hreach hlt ht
      hz he hup)
    hsupplyG Econ hecon s u u1 slotG hrg hslotG hreachG hltG hu hzG

end EpochProofs.Spec
