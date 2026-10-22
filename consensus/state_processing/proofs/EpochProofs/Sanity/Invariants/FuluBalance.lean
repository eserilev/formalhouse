import EpochProofs.Sanity.Invariants.FuluExits
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluCfg
import EpochProofs.Sanity.Invariants.Reachable

/-!
# The balance floor for Fulu

This file is `BalanceFloor.lean` and the epoch part of `EpochEnd.lean` for the Fulu functions.

- Each Fulu slashing is a `SlashStep`. Each other Fulu operation is an `OpStep`
  (`FuluExits.lean`).
- The Fulu `process_withdrawals` takes the expected withdrawals from the payload. Each Fulu
  withdrawal lowers a balance only to a floor (`WithdrawalsSafeAll`), the same floors as Gloas.
  Fulu has no builder withdrawals, so the floor holds for every index.
- So one Fulu block keeps the budget of the epoch, with one more sync aggregate
  (`process_block_fulu_budget_mainnet`).
- The Fulu `process_epoch` keeps `EBOk` and ends with `EffectiveBalanceFloor`
  (`process_epoch_fulu_effective_balances`).
-/

namespace EpochProofs.Spec

open FuluLengthsSanity FuluEffectsSanity FuluExitsSanity

namespace FuluBalanceSanity

/-- `saturating_sub` is `Nat` subtraction. -/
theorem saturating_sub_eq (a b : Uint64) : saturating_sub a b = a - b := by
  unfold saturating_sub
  split
  · rfl
  · rename_i h
    rw [Nat.sub_self, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]

/-- `omega` on `Nat` atoms: a withdrawal that fits in the balance left. -/
theorem withdraw_fits {old b a : Nat} (hle : old ≤ b) (ha : a ≤ b - old) : old + a ≤ b := by
  omega

/-- A successful `uint64Sub` does not underflow. -/
theorem uint64Sub_ok' {a b c : Uint64} (h : uint64Sub a b = .ok c) : b ≤ a ∧ c = a - b := by
  unfold uint64Sub at h
  split at h
  · cases h
    exact ⟨by assumption, rfl⟩
  · cases h

/-- `omega` on `Nat` atoms: the pending partial amount leaves at least `MIN_ACTIVATION_BALANCE`. -/
theorem pending_amount_fits {balance m a : Nat} (h : m < balance) :
    min (balance - m) a ≤ balance ∧ m ≤ balance - min (balance - m) a := by
  omega

/-- `omega` on `Nat` atoms: the sweep partial amount leaves the max effective balance. -/
theorem sweep_amount_fits {balance m : Nat} (h : m < balance) :
    balance - m ≤ balance ∧ m ≤ balance - (balance - m) := by
  omega

end FuluBalanceSanity

open FuluBalanceSanity

/-! ## Withdrawals -/

/-- Each index either has no withdrawn amount, or its withdrawn amount fits in its balance and
leaves the balance above a floor. This is `WithdrawalsSafe` for every index: Fulu has no builder
withdrawals. -/
def WithdrawalsSafeAll (p : Preset) (state : BeaconState) (withdrawals : List Withdrawal) : Prop :=
  ∀ (i : ValidatorIndex) (b : Gwei), state.balances[i]? = some b →
    withdrawnAmount withdrawals i = 0 ∨
      (withdrawnAmount withdrawals i ≤ b ∧
        WithdrawalFloor p state i (b - withdrawnAmount withdrawals i))

/-- The empty list is safe. -/
theorem WithdrawalsSafeAll.nil (p : Preset) (state : BeaconState) :
    WithdrawalsSafeAll p state [] :=
  fun _ _ _ => Or.inl rfl

/-- A withdrawal that leaves the balance above a floor keeps `WithdrawalsSafeAll`. -/
theorem WithdrawalsSafeAll.append_validator {p : Preset} {state : BeaconState}
    {ws : List Withdrawal} {w : Withdrawal} {bj : Gwei}
    (hs : WithdrawalsSafeAll p state ws) (hb : state.balances[w.validator_index]? = some bj)
    (hle : withdrawnAmount ws w.validator_index ≤ bj)
    (hamount : w.amount ≤ bj - withdrawnAmount ws w.validator_index)
    (hfloor : WithdrawalFloor p state w.validator_index
      (bj - withdrawnAmount ws w.validator_index - w.amount)) :
    WithdrawalsSafeAll p state (ws ++ [w]) := by
  intro i b hbi
  rw [withdrawnAmount_append]
  by_cases he : w.validator_index = i
  case neg =>
    rw [if_neg he, Nat.add_zero]
    exact hs i b hbi
  case pos =>
    subst he
    rw [if_pos rfl]
    rw [hb] at hbi
    cases hbi
    right
    refine ⟨withdraw_fits hle hamount, ?_⟩
    rw [← Nat.sub_sub]
    exact hfloor

/-- The pending partial withdrawals loop keeps `WithdrawalsSafeAll`. -/
theorem get_pending_partial_withdrawals_loop_safeAll (p : Preset) (state : BeaconState)
    (epoch : Epoch) (prior : List Withdrawal) (limit : Uint64) :
    ∀ (rest : List PendingPartialWithdrawal) (wi pc : Nat) (ws out : List Withdrawal)
      (wi' pc' : Nat),
      get_pending_partial_withdrawals_loop p state epoch prior limit rest wi pc ws =
        .ok (out, wi', pc') →
      WithdrawalsSafeAll p state (prior ++ ws) → WithdrawalsSafeAll p state (prior ++ out) := by
  intro rest
  induction rest with
  | nil =>
    intro wi pc ws out wi' pc' h hs
    cases h
    exact hs
  | cons w rest ih =>
    intro wi pc ws out wi' pc' h hs
    simp only [get_pending_partial_withdrawals_loop] at h
    split at h
    · cases h
      exact hs
    · obtain ⟨_, -, h⟩ := specM_bind_ok h
      obtain ⟨validator, hv, h⟩ := specM_bind_ok h
      obtain ⟨balance, hbal, h⟩ := specM_bind_ok h
      obtain ⟨bj, hbj, hle, hbeq⟩ := get_balance_after_withdrawals_ok hbal
      split at h
      · rename_i helig
        obtain ⟨d, hd, h⟩ := specM_bind_ok h
        obtain ⟨_, -, h⟩ := specM_bind_ok h
        obtain ⟨_, -, h⟩ := specM_bind_ok h
        obtain ⟨_, -, h⟩ := specM_bind_ok h
        refine ih _ _ _ _ _ _ h ?_
        rw [← List.append_assoc]
        simp only [is_eligible_for_partial_withdrawals, Bool.and_eq_true, decide_eq_true_eq]
          at helig
        obtain ⟨-, hd⟩ := uint64Sub_ok' hd
        subst hd hbeq
        obtain ⟨h1, h2⟩ := pending_amount_fits (a := w.amount) helig.2
        exact hs.append_validator hbj hle h1 ⟨validator, (listGet_ok hv).2, Or.inl h2⟩
      · obtain ⟨_, -, h⟩ := specM_bind_ok h
        obtain ⟨_, -, h⟩ := specM_bind_ok h
        exact ih _ _ _ _ _ _ h hs

/-- The validators sweep loop keeps `WithdrawalsSafeAll`. -/
theorem get_validators_sweep_withdrawals_loop_safeAll (p : Preset) (state : BeaconState)
    (epoch : Epoch) (hepoch : epoch = state.slot / p.SLOTS_PER_EPOCH) (prior : List Withdrawal)
    (limit : Uint64) :
    ∀ (fuel validator_index wi pc : Nat) (ws out : List Withdrawal) (wi' pc' : Nat),
      get_validators_sweep_withdrawals_loop p state epoch prior limit fuel validator_index wi pc
        ws = .ok (out, wi', pc') →
      WithdrawalsSafeAll p state (prior ++ ws) → WithdrawalsSafeAll p state (prior ++ out) := by
  intro fuel
  induction fuel with
  | zero =>
    intro validator_index wi pc ws out wi' pc' h hs
    cases h
    exact hs
  | succ fuel ih =>
    intro validator_index wi pc ws out wi' pc' h hs
    simp only [get_validators_sweep_withdrawals_loop] at h
    split at h
    · cases h
      exact hs
    · obtain ⟨_, -, h⟩ := specM_bind_ok h
      obtain ⟨validator, hv, h⟩ := specM_bind_ok h
      obtain ⟨balance, hbal, h⟩ := specM_bind_ok h
      obtain ⟨bj, hbj, hle, hbeq⟩ := get_balance_after_withdrawals_ok hbal
      subst hbeq
      split at h
      · rename_i hfull
        repeat (obtain ⟨_, -, h⟩ := specM_bind_ok h)
        refine ih _ _ _ _ _ _ _ h ?_
        rw [← List.append_assoc]
        simp only [is_fully_withdrawable_validator, Bool.and_eq_true, decide_eq_true_eq] at hfull
        refine hs.append_validator hbj hle (Nat.le_refl _) ⟨validator, (listGet_ok hv).2, ?_⟩
        exact Or.inr (Or.inr ⟨Nat.sub_self _, hepoch ▸ hfull.1.2⟩)
      · split at h
        · rename_i _ hpartial
          obtain ⟨d, hd, h⟩ := specM_bind_ok h
          repeat (obtain ⟨_, -, h⟩ := specM_bind_ok h)
          refine ih _ _ _ _ _ _ _ h ?_
          rw [← List.append_assoc]
          simp only [is_partially_withdrawable_validator, Bool.and_eq_true, decide_eq_true_eq]
            at hpartial
          obtain ⟨-, hd⟩ := uint64Sub_ok' hd
          subst hd
          obtain ⟨h1, h2⟩ := sweep_amount_fits hpartial.2
          exact hs.append_validator hbj hle h1 ⟨validator, (listGet_ok hv).2, Or.inr (Or.inl h2)⟩
        · repeat (obtain ⟨_, -, h⟩ := specM_bind_ok h)
          exact ih _ _ _ _ _ _ _ h hs

/-- The Fulu expected withdrawals are safe for every balance. -/
theorem get_expected_withdrawals_fulu_safeAll {p : Preset} {state : BeaconState}
    {expected : FuluExpectedWithdrawals} (h : get_expected_withdrawals_fulu p state = .ok expected) :
    WithdrawalsSafeAll p state expected.withdrawals := by
  unfold get_expected_withdrawals_fulu at h
  obtain ⟨⟨w1, wi1, c1⟩, h1, h⟩ := specM_bind_ok h
  obtain ⟨⟨w2, wi2, c2⟩, h2, h⟩ := specM_bind_ok h
  cases h
  have s1 : WithdrawalsSafeAll p state ([] ++ w1) := by
    unfold get_pending_partial_withdrawals at h1
    simp only [throw, throwThe, MonadExceptOf.throw] at h1
    obtain ⟨epoch, -, h1⟩ := specM_bind_ok h1
    obtain ⟨_, -, h1⟩ := specM_bind_ok h1
    obtain ⟨_, -, h1⟩ := specM_bind_ok h1
    split at h1
    · cases h1
    · obtain ⟨_, -, h1⟩ := specM_bind_ok h1
      exact get_pending_partial_withdrawals_loop_safeAll p state epoch [] _ _ _ _ _ _ _ _ h1
        (WithdrawalsSafeAll.nil p state)
  unfold get_validators_sweep_withdrawals at h2
  simp only [throw, throwThe, MonadExceptOf.throw] at h2
  obtain ⟨epoch, hepoch, h2⟩ := specM_bind_ok h2
  split at h2
  · cases h2
  · obtain ⟨_, -, h2⟩ := specM_bind_ok h2
    exact get_validators_sweep_withdrawals_loop_safeAll p state epoch
      (get_current_epoch_ok_eq hepoch) _ _ _ _ _ _ _ _ _ _ h2
      (by simpa using s1)

/-- The Fulu `apply_withdrawals` writes only `balances`. Each index loses its withdrawn
amount. -/
theorem apply_withdrawals_fulu_balances :
    ∀ (withdrawals : List Withdrawal) (state state' : BeaconState),
      apply_withdrawals_fulu state withdrawals = .ok state' →
      (∃ balances : List Gwei, state' = { state with balances }) ∧
      state'.balances.length = state.balances.length ∧
      ∀ (i : ValidatorIndex) (b : Gwei), state.balances[i]? = some b →
        state'.balances[i]? = some (b - withdrawnAmount withdrawals i) := by
  intro withdrawals
  induction withdrawals with
  | nil =>
    intro state state' h
    cases h
    refine ⟨⟨state.balances, rfl⟩, rfl, fun i b hb => ?_⟩
    rw [withdrawnAmount_nil, Nat.sub_zero]
    exact hb
  | cons w rest ih =>
    intro state state' h
    simp only [apply_withdrawals_fulu] at h
    obtain ⟨balances1, hd, h⟩ := specM_bind_ok h
    obtain ⟨⟨bal, he⟩, hlen, hbal⟩ := ih _ state' h
    unfold decrease_balance at hd
    obtain ⟨bj, hbj, hd⟩ := specM_bind_ok hd
    have hbj' := (listGet_ok hbj).2
    unfold listSet at hd
    split at hd
    · cases hd
      refine ⟨⟨bal, by rw [he]⟩, by rw [hlen, List.length_set], fun i b hb => ?_⟩
      rw [withdrawnAmount_cons]
      by_cases hne : w.validator_index = i
      · subst hne
        rw [hbj'] at hb
        cases hb
        have hset : (state.balances.set w.validator_index
            (saturating_sub bj w.amount))[w.validator_index]? = some (bj - w.amount) := by
          rw [List.getElem?_set_self', hbj', saturating_sub_eq]
          rfl
        rw [hbal _ _ hset, if_pos rfl, Nat.sub_sub]
      · have hset : (state.balances.set w.validator_index (saturating_sub bj w.amount))[i]? =
            some b := by
          rw [List.getElem?_set_ne hne]
          exact hb
        rw [hbal _ _ hset, if_neg hne, Nat.zero_add]
    · cases hd

/-- The Fulu `process_withdrawals` lowers a balance only to a floor: `MIN_ACTIVATION_BALANCE`,
the max effective balance, or zero for a withdrawable validator. -/
theorem process_withdrawals_fulu_balances (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    s'.balances.length = s.balances.length ∧
      ∀ (i : ValidatorIndex) (b : Gwei), s.balances[i]? = some b →
        ∃ b' : Gwei, s'.balances[i]? = some b' ∧ b' ≤ b ∧
          (b' = b ∨ ∃ v : Validator, s.validators[i]? = some v ∧
            (p.MIN_ACTIVATION_BALANCE ≤ b' ∨ get_max_effective_balance p v ≤ b' ∨
              (b' = 0 ∧ v.withdrawable_epoch ≤ s.slot / p.SLOTS_PER_EPOCH))) := by
  unfold process_withdrawals_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try contradiction
  have hsafe := get_expected_withdrawals_fulu_safeAll ‹get_expected_withdrawals_fulu _ _ = _›
  obtain ⟨-, hlen, hbal⟩ := apply_withdrawals_fulu_balances _ _ _ ‹apply_withdrawals_fulu _ _ = _›
  obtain ⟨-, b2, -⟩ := update_next_withdrawal_index_frame ‹update_next_withdrawal_index _ _ = _›
  obtain ⟨-, b3, -⟩ := update_next_withdrawal_validator_index_frame h
  have hbs := b3.trans b2
  refine ⟨by rw [hbs]; exact hlen, fun i b hb => ?_⟩
  rw [hbs, hbal i b hb]
  refine ⟨_, rfl, Nat.sub_le _ _, ?_⟩
  rcases hsafe i b hb with h0 | ⟨-, hfloor⟩
  · left
    rw [h0, Nat.sub_zero]
  · exact Or.inr hfloor

/-- The Fulu `process_withdrawals` at epoch `E` keeps the budget. -/
theorem Budget.of_withdrawals_fulu {p : Preset} {s0 : BeaconState} {E : Epoch} {L : Nat → Gwei}
    {n : Nat} {s s' : BeaconState} {payload : FuluExecutionPayload}
    (hE : s.slot / p.SLOTS_PER_EPOCH = E) (hfar : E < FAR_FUTURE_EPOCH)
    (hmax : p.MIN_ACTIVATION_BALANCE ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hd : ExitDelay p s) (h : process_withdrawals_fulu p s payload = .ok s')
    (hb : Budget p s0 E L n s) : Budget p s0 E L n s' := by
  have hvs := (process_withdrawals_fulu_frame p s s' payload h).1
  obtain ⟨-, hbal⟩ := process_withdrawals_fulu_balances p s s' payload h
  obtain ⟨hlen, hall⟩ := hb
  refine ⟨by rw [hvs]; exact hlen, fun i v0 b0 h0 hb0 => ?_⟩
  obtain ⟨v, b, hv, hbb, heb, hsm, hcase⟩ := hall i v0 b0 h0 hb0
  obtain ⟨b', hb', -, hor⟩ := hbal i b hbb
  refine ⟨v, b', by rw [hvs]; exact hv, hb', heb, hsm, ?_⟩
  rcases hcase with hw | hcase
  · exact .inl hw
  rcases hor with rfl | ⟨u, hu, hfl⟩
  · exact .inr hcase
  rw [hv] at hu
  cases hu
  have hm : min b0 p.MIN_ACTIVATION_BALANCE ≤ p.MIN_ACTIVATION_BALANCE := Nat.min_le_right _ _
  rcases hfl with hle | hle | ⟨-, hw⟩
  · exact .inr (Nat.le_trans hm (Nat.le_trans hle
      (by rw [Nat.add_assoc]; exact Nat.le_add_right _ _)))
  · have := min_activation_le_max_effective_balance hmax v
    exact .inr (Nat.le_trans hm (Nat.le_trans (Nat.le_trans this hle)
      (by rw [Nat.add_assoc]; exact Nat.le_add_right _ _)))
  · rw [hE] at hw
    left
    refine ⟨hw, ?_⟩
    rcases hd v (List.mem_of_getElem? hv) with hf | hx
    · simp only [Epoch] at *
      omega
    · exact hx

/-- The Fulu `process_withdrawals` at epoch `E` keeps everything. -/
theorem Keeps.of_withdrawals_fulu {p : Preset} {s0 : BeaconState} {E : Epoch} {L : Nat → Gwei}
    {n : Nat} {s t : BeaconState} {payload : FuluExecutionPayload}
    (hE : s.slot / p.SLOTS_PER_EPOCH = E) (hfar : E < FAR_FUTURE_EPOCH)
    (hmax : p.MIN_ACTIVATION_BALANCE ≤ p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (h : process_withdrawals_fulu p s payload = .ok t) : Keeps p s0 E L n s t := by
  have hvs := (process_withdrawals_fulu_frame p s t payload h).1
  have hcp := process_withdrawals_fulu_checkpointsStable p s t payload h
  exact ⟨hcp.1, .of_eq hvs, fun hd =>
    ⟨ExitDelay.of_validators_eq hvs hd, Budget.of_withdrawals_fulu hE hfar hmax hd h⟩⟩

/-! ## Slashings -/

/-- A slashable validator becomes withdrawable after the epoch. -/
theorem lt_withdrawable_of_slashable' {v : Validator} {e : Epoch}
    (h : is_slashable_validator v e = true) : e < v.withdrawable_epoch := by
  simp only [is_slashable_validator, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.2

/-- The Fulu `process_proposer_slashing` at epoch `E` is a slashing step. -/
theorem process_proposer_slashing_fulu_slashStep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (E : Epoch) (hE : s.slot / p.SLOTS_PER_EPOCH = E)
    (ps : ProposerSlashing) (h : process_proposer_slashing_fulu p o f s ps = .ok s') :
    SlashStep p E s s' := by
  obtain ⟨-, -, -, heff, hother, ⟨v, v', hv, hv', hns, hs', hch⟩, hbal⟩ :=
    process_proposer_slashing_fulu_effects p o f hc s s' ps h
  obtain ⟨u, cur, hu, hcur, hsl, -⟩ := process_proposer_slashing_fulu_ok p o f s s' ps h
  rw [hv] at hu
  cases hu
  have hlt : E < v.withdrawable_epoch := by
    rw [← hE, ← get_current_epoch_ok_eq hcur]
    exact lt_withdrawable_of_slashable' hsl
  refine ⟨heff.2.1, fun j w w' hw hw' => ?_, fun j b hb => ?_⟩
  · by_cases hj : j = ps.signed_header_1.message.proposer_index
    · subst hj
      rw [hv] at hw
      rw [hv'] at hw'
      cases hw
      cases hw'
      exact .inr ⟨hns, hs', hch.keeps.2.2.1, hlt, hch.exitDelay, hch.exit_cases.1,
        hE ▸ hch.exit_cases.2⟩
    · rw [hother j hj, hw] at hw'
      cases hw'
      exact .inl rfl
  · obtain ⟨b', hb', hne, hle⟩ := hbal j b hb
    refine ⟨b', hb', ?_⟩
    by_cases hj : j = ps.signed_header_1.message.proposer_index
    · subst hj
      exact .inr ⟨v, v', hv, hv', hns, hs', hle v hv⟩
    · exact .inl (hne hj)

/-- In a Fulu attester slashing, each validator that changes was withdrawable only after the
current epoch. -/
theorem process_attester_slashing_fulu_slashable (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') :
    ∀ (j : Nat) (v v' : Validator), s.validators[j]? = some v → s'.validators[j]? = some v' →
      v' = v ∨ s.slot / p.SLOTS_PER_EPOCH < v.withdrawable_epoch := by
  unfold process_attester_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine (SlashingsSanity.forIn_invariant
    (fun r : MProd Bool BeaconState => r.snd.slot = s.slot ∧
      ∀ (j : Nat) (v v' : Validator), s.validators[j]? = some v → r.snd.validators[j]? = some v' →
        v' = v ∨ s.slot / p.SLOTS_PER_EPOCH < v.withdrawable_epoch) _ ?_ _
    (⟨false, s⟩ : MProd Bool BeaconState) _
    ⟨rfl, fun j v v' hv hv' => by rw [hv] at hv'; cases hv'; exact .inl rfl⟩
    ‹forIn _ _ _ = _›).2
  intro index r step ⟨hslot, hr⟩ hstep
  obtain ⟨u, hu, hstep⟩ := specM_bind_ok hstep
  obtain ⟨cur, hcur, hstep⟩ := specM_bind_ok hstep
  split at hstep
  · rename_i hsl
    obtain ⟨r', hr', hstep⟩ := specM_bind_ok hstep
    cases hstep
    obtain ⟨hcp, -, hother, -, -, -⟩ := slash_validator_fulu_ok p f hc _ _ index none hr'
    refine ⟨hcp.1.trans hslot, fun j w w' hw hw' => ?_⟩
    by_cases hj : j = index
    · subst hj
      rcases hr j w u hw (listGet_ok hu).2 with rfl | hlt
      · right
        have := lt_withdrawable_of_slashable' hsl
        rw [get_current_epoch_ok_eq hcur, hslot] at this
        exact this
      · exact .inr hlt
    · exact hr j w w' hw ((hother j hj).symm.trans hw')
  · cases hstep
    exact ⟨hslot, hr⟩

/-- The Fulu `process_attester_slashing` at epoch `E` is a slashing step. -/
theorem process_attester_slashing_fulu_slashStep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (E : Epoch) (hE : s.slot / p.SLOTS_PER_EPOCH = E)
    (as : AttesterSlashing) (h : process_attester_slashing_fulu p o f s as = .ok s') :
    SlashStep p E s s' := by
  obtain ⟨heff, hf⟩ := process_attester_slashing_fulu_ok p o f hc s s' as h
  have hsl := process_attester_slashing_fulu_slashable p o f hc s s' as h
  refine ⟨heff.2.1, fun j v v' hv hv' => ?_, heff.2.2.2.2.2⟩
  rcases hf j v v' hv hv' with rfl | ⟨hns, hch⟩
  · exact .inl rfl
  · obtain ⟨-, -, heb, hs', -, -⟩ := hch.keeps
    rcases hsl j v v' hv hv' with rfl | hlt
    · rw [hns] at hs'
      cases hs'
    · exact .inr ⟨hns, hs', heb, hE ▸ hlt, hch.exitDelay, hch.exit_cases.1,
        hE ▸ hch.exit_cases.2⟩

/-! ## One block -/

/-- The Fulu `process_block_header` is an operation step. -/
theorem process_block_header_fulu_opStep (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') : OpStep p s s' :=
  .of_registryFrame (process_block_header_fulu_frame p o fo s s' block h)
    (process_block_header_fulu_checkpointsStable p o fo s s' block h).1

/-- The Fulu `process_operations` at epoch `E` keeps everything. -/
theorem process_operations_fulu_keeps (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s0 : BeaconState) (E : Epoch) (L : Nat → Gwei) (n : Nat)
    (s t : BeaconState) (body : FuluBeaconBlockBody) (hE : s.slot / p.SLOTS_PER_EPOCH = E)
    (hfar : E < FAR_FUTURE_EPOCH) (h : process_operations_fulu p o f s body = .ok t) :
    Keeps p s0 E L n s t := by
  have hop : ∀ a b, OpStep p a b → Keeps p s0 E L n s a → Keeps p s0 E L n s b :=
    fun a b hab hsa => hsa.trans (.of_opStep (by rw [hsa.1]; exact hE) hfar hab)
  refine process_operations_fulu_inv p o f (Keeps p s0 E L n s) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s t body h
    (Keeps.refl p s0 E L n s)
  · intro a x b h' hsa
    have hEa : a.slot / p.SLOTS_PER_EPOCH = E := by rw [hsa.1]; exact hE
    exact hsa.trans (.of_slashStep hfar
      (process_proposer_slashing_fulu_effects p o f hc a b x h').2.1.1
      (process_proposer_slashing_fulu_slashStep p o f hc a b E hEa x h'))
  · intro a x b h' hsa
    have hEa : a.slot / p.SLOTS_PER_EPOCH = E := by rw [hsa.1]; exact hE
    exact hsa.trans (.of_slashStep hfar
      (process_attester_slashing_fulu_effects p o f hc a b x h').2.1.1
      (process_attester_slashing_fulu_slashStep p o f hc a b E hEa x h'))
  · exact fun a x b h' => hop a b (process_attestation_fulu_opStep p o a b x h')
  · exact fun a x b h' => hop a b (process_voluntary_exit_fulu_opStep p o f hc a b x h')
  · exact fun a x b h' => hop a b (process_bls_to_execution_change_opStep p o a b x h')
  · exact fun a x b h' => hop a b (process_deposit_request_opStep p a b x h')
  · exact fun a x b h' => hop a b (process_withdrawal_request_fulu_opStep p f hc a b x h')
  · exact fun a x b h' => hop a b (process_consolidation_request_fulu_opStep p f a b x h')

/-- On mainnet, one Fulu `process_block` at epoch `E` keeps `ExitDelay`, the slot and the
activity at `E`, and keeps the budget with one more sync aggregate. The sync aggregate has at
most 512 bits, and the total active balance is at most 139 million ETH. -/
theorem process_block_fulu_budget_mainnet [PresetCfg] [FuluCfg] [FuluCfg.Ok] (o : Oracle) (fo : FuluOracle) (c : FuluBlockConfig)
    (s0 : BeaconState) (E : Epoch) (n : Nat) (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu P o fo FC c fs block = .ok fs')
    (hE : fs.state.slot / P.SLOTS_PER_EPOCH = E) (hfar : E < FAR_FUTURE_EPOCH)
    (hd : ExitDelay P fs.state)
    (hb : Budget P s0 E (fun _ => syncLoss) n fs.state)
    (hbits : block.body.sync_aggregate.sync_committee_bits.length ≤ P.SYNC_COMMITTEE_SIZE)
    (htab : ∀ tab, get_total_active_balance P fs.state = .ok tab →
      tab ≤ 139000000000000000) :
    Budget P s0 E (fun _ => syncLoss) (n + 1) fs'.state ∧
      ExitDelay P fs'.state ∧ fs'.state.slot = fs.state.slot ∧
      ActiveAgree E fs.state fs'.state := by
  have hc := fuluCompat
  unfold process_block_fulu at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨fs3, h3, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  cases h
  have hs3 := process_execution_payload_fulu_state P o fo c _ _ _ h3
  simp only at hs3
  let K := Keeps P s0 E (fun _ => syncLoss) n
  have k1 : K fs.state s1 := .of_opStep hE hfar
    (process_block_header_fulu_opStep _ o fo _ _ block h1)
  have hE1 : s1.slot / P.SLOTS_PER_EPOCH = E := by rw [k1.1]; exact hE
  have k2 : K s1 s2 := .of_withdrawals_fulu hE1 hfar (by decide) h2
  have hE2 : s2.slot / P.SLOTS_PER_EPOCH = E := by rw [k2.1]; exact hE1
  rw [hs3] at h4
  have k4 : K s2 s4 := .of_opStep hE2 hfar (process_randao_opStep _ o s2 s4 _ h4)
  have hE4 : s4.slot / P.SLOTS_PER_EPOCH = E := by rw [k4.1]; exact hE2
  have k5 : K s4 s5 := .of_opStep hE4 hfar (process_eth1_data_opStep _ s4 s5 _ h5)
  have hE5 : s5.slot / P.SLOTS_PER_EPOCH = E := by rw [k5.1]; exact hE4
  have k6 : K s5 s6 :=
    process_operations_fulu_keeps _ o _ hc s0 E _ n s5 s6 _ hE5 hfar h6
  have k : K fs.state s6 := k1.trans (k2.trans (k4.trans (k5.trans k6)))
  obtain ⟨hslot, hagree, hkeep⟩ := k
  obtain ⟨hd6, hb6⟩ := hkeep hd
  have htab6 : ∀ tab, get_total_active_balance P s6 = .ok tab →
      tab ≤ 139000000000000000 := by
    intro tab ht
    rw [get_total_active_balance_congr P fs.state s6 (by rw [hslot])
      (hE ▸ hagree)] at ht
    exact htab tab ht
  obtain ⟨hfr, -⟩ := process_sync_aggregate_frame _ o s6 s7 _ h7
  have hvs : s7.validators = s6.validators := by rw [hfr]
  have hsl : s7.slot = s6.slot := by rw [hfr]
  exact ⟨Budget.of_sync_mainnet h7 hbits htab6 (hb6 hb),
    process_sync_aggregate_exitDelay _ o s6 s7 _ h7 hd6, hsl.trans hslot,
    hagree.trans (.of_eq hvs)⟩

/-! ## The Fulu epoch -/

/-- On mainnet, the Fulu `process_epoch` keeps `EBOk` and ends with `EffectiveBalanceFloor`. -/
theorem process_epoch_fulu_effective_balances [PresetCfg] [FuluCfg] [FuluCfg.Ok] (o : Oracle) (s s' : BeaconState)
    (h : process_epoch_fulu P FC o s = .ok s')
    (hs : EBOk P s) :
    EBOk P s' ∧ EffectiveBalanceFloor P s' := by
  have hp := ebPresetOk_mainnet
  rw [process_epoch_fulu_eq_tab _ _ fuluCompat] at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  obtain ⟨s8, h8, h⟩ := specM_bind_ok h
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  obtain ⟨s13, h13, h⟩ := specM_bind_ok h
  have e1 : EBOk _ s1 :=
    hs.of_validators (process_justification_and_finalization_frame _ _ _ h1).1.1
  have e2 : EBOk _ s2 := e1.of_validators (process_inactivity_updates_validators _ _ _ h2)
  have e3 : EBOk _ s3 := e2.of_validators (process_rewards_and_penalties_validators _ _ _ _ h3)
  have e4 : EBOk _ s4 := process_registry_updates_ebOk _ _ _ _ h4 e3
  have e5 : EBOk _ s5 := e4.of_validators (process_slashings_validators _ _ _ _ h5)
  have e6 : EBOk _ s6 := e5.of_validators (process_eth1_data_reset_frame _ _ _ h6).1.1
  have e7 : EBOk _ s7 := process_pending_deposits_ebOk _ o hp _ _ _ h7 e6
  have e8 : EBOk _ s8 := e7.of_validators (process_pending_consolidations_validators _ _ _ h8)
  have hfloor : EffectiveBalanceFloor _ s9 :=
    process_effective_balance_updates_floor_mainnet s8 s9 h9 fun v hv => (e8 v hv).1
  have hmax := process_effective_balance_updates_le_max _ hp _ _ hysteresisThresholds_mainnet
    s8 s9 h9 fun v hv => (e8 v hv).2
  have e9 : EBOk _ s9 := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact ⟨(hfloor.2 i hi).1, hmax _ hv⟩
  obtain ⟨_, _, rfl⟩ := process_sync_committee_updates_fulu_shape _ o _ _ h13
  obtain ⟨_, rfl⟩ := process_proposer_lookahead_fulu_shape _ o _ _ h
  have f : RegistryFrame s9 (process_participation_flag_updates s12) :=
    (process_slashings_reset_frame _ _ _ h10).1.trans
    ((process_randao_mixes_reset_frame _ _ _ h11).1.trans
    ((process_historical_summaries_update_frame _ o _ _ h12).1.trans
    (process_participation_flag_updates_frame _).1))
  obtain ⟨hvs, hbs, -⟩ := f
  refine ⟨e9.of_validators hvs, ?_⟩
  unfold EffectiveBalanceFloor
  simp only
  rw [hvs, hbs]
  exact hfloor

end EpochProofs.Spec
