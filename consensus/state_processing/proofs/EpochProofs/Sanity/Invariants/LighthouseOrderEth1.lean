import EpochProofs.Sanity.Invariants.LighthouseOrderTail
import EpochProofs.Spec.PresetCfg

/-!
# Moving the eth1 reset after the deposits, consolidations and payments

The spec runs the eth1 reset before the pending deposits. Lighthouse runs it after the single
pass, so after the deposits, the consolidations, the builder payments, the proposer lookahead and
the PTC window. The eth1 reset reads only the slot and writes only `eth1_data_votes`. The steps
in between keep the slot and do not read `eth1_data_votes`, so the reset moves past them.
-/

namespace EpochProofs.Spec

/-- `t` with no eth1 data votes. -/
def clearVotes (t : BeaconState) : BeaconState := { t with eth1_data_votes := [] }

/-- `F` does not read `eth1_data_votes` and does not write it. -/
def VotesBlind (F : BeaconState → SpecM BeaconState) : Prop :=
  ∀ t, F (clearVotes t) = clearVotes <$> F t

/-- `F` keeps the slot and the historical summaries. -/
def SlotKeep (F : BeaconState → SpecM BeaconState) : Prop :=
  ∀ t t', F t = .ok t' → t'.slot = t.slot ∧ t'.historical_summaries = t.historical_summaries

theorem votesBlind_bind {F G : BeaconState → SpecM BeaconState} (hF : VotesBlind F)
    (hG : VotesBlind G) : VotesBlind (fun t => F t >>= G) := by
  intro t
  show (F (clearVotes t) >>= G) = clearVotes <$> (F t >>= G)
  rw [hF]
  cases F t with
  | error e => rfl
  | ok u => exact hG u

theorem slotKeep_bind {F G : BeaconState → SpecM BeaconState} (hF : SlotKeep F)
    (hG : SlotKeep G) : SlotKeep (fun t => F t >>= G) := by
  intro t t' h
  obtain ⟨u, hu, h⟩ := specM_bind_ok h
  obtain ⟨h1, h2⟩ := hG u t' h
  obtain ⟨h3, h4⟩ := hF t u hu
  exact ⟨h1.trans h3, h2.trans h4⟩

theorem votesBlind_foldlM {α : Type} (f : BeaconState → α → SpecM BeaconState)
    (hf : ∀ x, VotesBlind (fun t => f t x)) :
    ∀ (l : List α), VotesBlind (fun t => l.foldlM f t)
  | [], t => rfl
  | x :: xs, t => by
    show (f (clearVotes t) x >>= fun u => xs.foldlM f u) =
      clearVotes <$> (f t x >>= fun u => xs.foldlM f u)
    have hx := hf x t
    simp only at hx
    rw [hx]
    cases f t x with
    | error e => rfl
    | ok u => exact votesBlind_foldlM f hf xs u

theorem slotKeep_foldlM {α : Type} (f : BeaconState → α → SpecM BeaconState)
    (hf : ∀ x, SlotKeep (fun t => f t x)) :
    ∀ (l : List α), SlotKeep (fun t => l.foldlM f t)
  | [], t, t', h => by cases h; exact ⟨rfl, rfl⟩
  | x :: xs, t, t', h => by
    obtain ⟨u, hu, h⟩ := specM_bind_ok h
    obtain ⟨h1, h2⟩ := slotKeep_foldlM f hf xs u t' h
    obtain ⟨h3, h4⟩ := hf x t u hu
    exact ⟨h1.trans h3, h2.trans h4⟩

/-! ## The steps between the two positions -/

theorem add_validator_votesBlind [PresetCfg] (t : BeaconState) (pubkey : BLSPubkey)
    (withdrawal_credentials : Bytes32) (amount : Gwei) :
    add_validator_to_registry P (clearVotes t) pubkey withdrawal_credentials amount =
      clearVotes <$> add_validator_to_registry P t pubkey withdrawal_credentials
        amount := by
  unfold add_validator_to_registry get_index_for_new_validator clearVotes
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals first
    | rfl
    | (rename_i h; cases h; rfl)
    | (rename_i h; cases h)

theorem add_validator_slot [PresetCfg] (t t' : BeaconState) (pubkey : BLSPubkey)
    (withdrawal_credentials : Bytes32) (amount : Gwei)
    (h : add_validator_to_registry P t pubkey withdrawal_credentials amount =
      .ok t') : t'.slot = t.slot ∧ t'.historical_summaries = t.historical_summaries := by
  unfold add_validator_to_registry get_index_for_new_validator at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals try contradiction
  cases h
  exact ⟨rfl, rfl⟩

theorem apply_votesBlind [PresetCfg] (o : Oracle) (d : PendingDeposit) :
    VotesBlind (fun t => apply_pending_deposit P o t d) := by
  intro t
  simp only
  unfold apply_pending_deposit
  dsimp only
  have hv : (clearVotes t).validators = t.validators := rfl
  have hb : (clearVotes t).balances = t.balances := rfl
  rw [hv, hb]
  split
  · split
    · exact add_validator_votesBlind t _ _ _
    · rfl
  · cases increase_balance t.balances ((t.validators.map (·.pubkey)).idxOf d.pubkey) d.amount with
    | error err => rfl
    | ok bs => rfl

theorem apply_slotKeep [PresetCfg] (o : Oracle) (d : PendingDeposit) :
    SlotKeep (fun t => apply_pending_deposit P o t d) := by
  intro t t' h
  simp only at h
  unfold apply_pending_deposit at h
  by_cases hm : d.pubkey ∈ t.validators.map (·.pubkey)
  · simp only [hm, not_true_eq_false, if_false] at h
    obtain ⟨bs, -, h⟩ := specM_bind_ok h
    cases h
    exact ⟨rfl, rfl⟩
  · simp only [hm, not_false_eq_true, if_true] at h
    by_cases hs : is_valid_deposit_signature P o d.pubkey d.withdrawal_credentials
        d.amount d.signature = true
    · simp only [hs, if_true] at h
      exact add_validator_slot t t' _ _ _ h
    · simp only [hs, Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

theorem ebUpdateAt_votesBlind (i : Nat) : VotesBlind (fun t => ebUpdateAt t i) := by
  intro t
  simp only
  cases hv : t.validators[i]? with
  | none =>
    rw [ebUpdateAt_of_none_v (s := clearVotes t) hv, ebUpdateAt_of_none_v hv]
    rfl
  | some v =>
    cases hb : t.balances[i]? with
    | none =>
      rw [ebUpdateAt_of_none_b (s := clearVotes t) hv hb, ebUpdateAt_of_none_b hv hb]
      rfl
    | some b =>
      rw [ebUpdateAt_some (s := clearVotes t) hv hb, ebUpdateAt_some hv hb]
      cases ebNew v b with
      | error err => rfl
      | ok e =>
        show Except.ok (setEB (clearVotes t) i e) = Except.ok (clearVotes (setEB t i e))
        rw [setEB_some (s := clearVotes t) e hv, setEB_some e hv]
        rfl

theorem ebUpdateAt_slotKeep (i : Nat) : SlotKeep (fun t => ebUpdateAt t i) := by
  intro t t' h
  obtain ⟨_, _, _, _, _, _, rfl⟩ := (ebUpdateAt_ok t t' i).mp h
  unfold setEB
  split <;> exact ⟨rfl, rfl⟩

theorem payments_votesBlind [PresetCfg] (tab : Gwei) :
    VotesBlind (process_builder_pending_payments P tab) := by
  intro t
  unfold process_builder_pending_payments clearVotes
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  repeat' split
  all_goals rfl

theorem payments_slotKeep [PresetCfg] (tab : Gwei) :
    SlotKeep (process_builder_pending_payments P tab) := by
  intro t t' h
  unfold process_builder_pending_payments at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl⟩)

theorem consolidations_votesBlind [PresetCfg] :
    VotesBlind (process_pending_consolidations P) := by
  intro t
  unfold process_pending_consolidations
  have hc : get_current_epoch P (clearVotes t) =
      get_current_epoch P t := rfl
  rw [hc]
  cases get_current_epoch P t with
  | error err => rfl
  | ok ce =>
    simp only [ok_bind']
    cases uint64Add ce 1 with
    | error err => rfl
    | ok ne =>
      simp only [ok_bind']
      have hp : (clearVotes t).pending_consolidations = t.pending_consolidations := rfl
      rw [hp]
      rw [forIn_sim_eq t.pending_consolidations _
        (fun b : MProd Nat BeaconState => ⟨b.fst, clearVotes b.snd⟩)
        (fun _ => True) ?_ ?_ ⟨0, t⟩ _ rfl trivial]
      · refine map_bind_eq _ (fun r => ?_)
        rfl
      · intro x _ ⟨n, st⟩ _
        unfold clearVotes
        simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
        repeat' split
        all_goals first
          | rfl
          | (rename_i h; cases h; rfl)
          | (rename_i h; cases h)
      · intro _ _ _ _ _ _
        trivial

theorem consolidations_slotKeep [PresetCfg] : SlotKeep (process_pending_consolidations P) := by
  intro t t' h
  unfold process_pending_consolidations at h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨⟨n, st⟩, hr, h⟩ := specM_bind_ok h
  have hP := forIn_ok_inv (fun b : MProd Nat BeaconState => b.snd.slot = t.slot ∧
    b.snd.historical_summaries = t.historical_summaries) _ _ ?_ ⟨0, t⟩ _ ⟨rfl, rfl⟩ hr
  · cases h
    exact hP
  · intro x _ ⟨n0, st0⟩ r hs hb
    simp only [bind, Except.bind, pure, Except.pure] at hb
    repeat' split at hb
    all_goals first
      | contradiction
      | (cases hb; exact hs)

end EpochProofs.Spec
