import EpochProofs.Sanity.FuluTransition
import EpochProofs.Sanity.FuluRegistry

/-!
# Effects of the Fulu block functions

This file gives each Fulu block function the effect facts that the Gloas functions have in
`Sanity/Block/*`: `EBStable`, `BalancesUp`, `CheckpointsStable` (from `Sanity/FuluTransition`),
`ExitOrder`, `SlashEffect`, `SlashFields` and `RequestEffect`.

Most Fulu functions differ from the Gloas ones only in the exit churn. Under `FuluCompat`, the
Fulu `initiate_validator_exit` and `compute_exit_epoch_and_update_churn` are the Gloas functions
at `fuluTab` (`initiate_validator_exit_fulu_eq`, `compute_exit_epoch_and_update_churn_fulu_eq`).
The Gloas facts about these two functions hold for every total, so they carry over. The
consolidation churn is the Electra one, so `compute_consolidation_epoch_and_update_churn_fulu`
gets its own bound.
-/

namespace EpochProofs.Spec

open ExitsSanity SlashingsSanity FuluTransitionSanity

namespace FuluEffectsSanity

theorem uint64Add_iff {a b c : Nat} :
    uint64Add a b = .ok c ↔ a + b < UINT64_SIZE ∧ c = a + b := by
  unfold uint64Add
  by_cases hlt : a + b < UINT64_SIZE
  · simp [hlt, pure, Except.pure, eq_comm]
  · simp [hlt, throw, throwThe, MonadExceptOf.throw]

theorem listGet_some {α : Type} {l : List α} {i : Nat} {a : α}
    (h : listGet l i = .ok a) : l[i]? = some a := by
  unfold listGet at h
  cases hl : l[i]? with
  | none => simp [hl, throw, throwThe, MonadExceptOf.throw] at h
  | some b => simp only [hl, pure, Except.pure, Except.ok.injEq] at h; rw [h]

theorem listSet_eq {α : Type} {l l' : List α} {i : Nat} {a : α}
    (h : listSet l i a = .ok l') : l' = l.set i a := by
  unfold listSet at h
  split at h
  · cases h; rfl
  · cases h

theorem compute_activation_exit_epoch_eq {p : Preset} {c a : Nat}
    (h : compute_activation_exit_epoch p c = .ok a) : a = c + 1 + p.MAX_SEED_LOOKAHEAD := by
  unfold compute_activation_exit_epoch at h
  obtain ⟨b, hb, h⟩ := specM_bind_ok h
  rw [uint64Add_iff] at hb h
  omega

end FuluEffectsSanity

open FuluEffectsSanity

/-! ## Exits -/

/-- The effects of the Fulu `initiate_validator_exit`. -/
theorem initiate_validator_exit_fulu_effects (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (tab : Gwei) (s s' : BeaconState) (index : ValidatorIndex)
    (h : initiate_validator_exit_fulu p f tab s index = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') ∧
      s'.balances = s.balances := by
  rw [initiate_validator_exit_fulu_eq p f hc] at h
  exact initiate_validator_exit_effects p _ s s' index h

/-- A successful Fulu voluntary exit is `initiate_validator_exit` on the original state, for an
active validator with no exit. -/
theorem process_voluntary_exit_fulu_initiate (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') :
    ∃ tab cur v, s.validators[e.message.validator_index]? = some v ∧
      get_current_epoch p s = .ok cur ∧ is_active_validator v cur ∧
      v.exit_epoch = FAR_FUTURE_EPOCH ∧
      initiate_validator_exit p tab s e.message.validator_index = .ok s' := by
  unfold process_voluntary_exit_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hg : listGet s.validators e.message.validator_index with
  | error _ => simp [hg] at h
  | ok v =>
  simp only [hg] at h
  cases hcur : get_current_epoch p s with
  | error _ => simp [hcur] at h
  | ok cur =>
  simp only [hcur] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  exact ⟨_, cur, v, (listGet_ok hg).2, rfl,
    Decidable.of_not_not ‹¬¬is_active_validator v cur = true›,
    Decidable.of_not_not ‹¬¬v.exit_epoch = FAR_FUTURE_EPOCH›, h⟩

/-- The effects of a Fulu voluntary exit. Only the exiting validator changes, by
`ExitChange`. -/
theorem process_voluntary_exit_fulu_effects (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') ∧ BalancesUp s s' ∧
      (∀ j, j ≠ e.message.validator_index → s'.validators[j]? = s.validators[j]?) ∧
      ∃ v v', s.validators[e.message.validator_index]? = some v ∧
        s'.validators[e.message.validator_index]? = some v' ∧ ExitChange p s v v' := by
  obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc s s' e h
  obtain ⟨heb, hcp, hord, hbal⟩ := initiate_validator_exit_effects p tab s s' _ hi
  obtain ⟨-, -, hother, hv⟩ := initiate_validator_exit_ok p tab s s' _ hi
  exact ⟨heb, hcp, hord, ⟨by rw [hbal]; exact Nat.le_refl _,
    fun _ b hb => ⟨b, by rw [hbal]; exact hb, Nat.le_refl _⟩⟩, hother, hv⟩

/-! ## Slashings -/

/-- On success, the exit step of the Fulu `slash_validator` is `initiate_validator_exit` for
some total. -/
theorem slash_validator_fulu_initiate_ok (p : Preset) (f : FuluConfig) (s s1 : BeaconState)
    (i : ValidatorIndex) (v : Validator) (hv : listGet s.validators i = .ok v)
    (h : (if (v.exit_epoch != FAR_FUTURE_EPOCH) = true then pure s
      else get_total_active_balance p s >>= fun t => initiate_validator_exit p (fuluTab p f t) s i) =
      (.ok s1 : SpecM BeaconState)) :
    ∃ tab, initiate_validator_exit p tab s i = .ok s1 := by
  by_cases hx : v.exit_epoch = FAR_FUTURE_EPOCH
  · simp only [hx, bne_self_eq_false, Bool.false_eq_true, if_false] at h
    obtain ⟨tab, -, h⟩ := specM_bind_ok h
    exact ⟨_, h⟩
  · rw [if_pos (by simpa using hx)] at h
    cases h
    exact ⟨0, initiate_validator_exit_of_exiting p 0 s i v hv hx⟩

/-- The Fulu `slash_validator` changes only the validator at `i`, by `SlashChange`. The balance
at `i` drops by at most the slashing penalty. No other balance drops. -/
theorem slash_validator_fulu_ok (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (h : slash_validator_fulu p f s i w = .ok s') :
    CheckpointsStable s s' ∧
    s'.validators.length = s.validators.length ∧
    (∀ j, j ≠ i → s'.validators[j]? = s.validators[j]?) ∧
    (∃ v v', s.validators[i]? = some v ∧ s'.validators[i]? = some v' ∧ SlashChange p s v v') ∧
    s'.balances.length = s.balances.length ∧
    ∀ (j : Nat) (b : Gwei), s.balances[j]? = some b → ∃ b' : Gwei, s'.balances[j]? = some b' ∧
      (j ≠ i → b ≤ b') ∧ ∀ v : Validator, s.validators[j]? = some v →
        b ≤ b' + v.effective_balance / p.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA := by
  unfold slash_validator_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc] at h
  obtain ⟨epoch, hcur, h⟩ := specM_bind_ok h
  obtain ⟨v0, hv0, h⟩ := specM_bind_ok h
  obtain ⟨s1, hs1, h⟩ := SlashingsSanity.bind_if_ok h
  obtain ⟨tab, hs1⟩ := slash_validator_fulu_initiate_ok p f s s1 i v0 hv0 hs1
  obtain ⟨v1, hv1, h⟩ := specM_bind_ok h
  obtain ⟨we, hwe, h⟩ := specM_bind_ok h
  obtain ⟨vs2, hvs2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨pen, hpen, h⟩ := specM_bind_ok h
  obtain ⟨bs1, hbs1, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨bs2, hbs2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨bs3, hbs3, h⟩ := specM_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  dsimp only at hvs2 hpen hbs1 hbs2 hbs3 ⊢
  obtain ⟨⟨vs, x, y, rfl⟩, hlen, hother, v, v1', hv, hv1', hch⟩ :=
    initiate_validator_exit_ok p tab s _ i hs1
  obtain ⟨hlt, hv1⟩ := listGet_ok hv1
  rw [hv1'] at hv1
  cases hv1
  obtain ⟨-, rfl⟩ := ExitsSanity.listSet_ok hvs2
  rw [uint64Add_ok hwe] at *
  rw [SlashingsSanity.uint64Div_ok hpen] at hbs1
  obtain ⟨hl1, hb1⟩ := decrease_balance_ok hbs1
  obtain ⟨hl2, hb2⟩ := increase_balance_ok hbs2
  obtain ⟨hl3, hb3⟩ := increase_balance_ok hbs3
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, fun j hj => ?_, ⟨v, _, hv, List.getElem?_set_self hlt,
    _, epoch, hch, hcur, rfl⟩, ?_, fun j b hb => ?_⟩
  · simp only [List.length_set]
    exact hlen
  · rw [List.getElem?_set_ne (Ne.symm hj)]
    exact hother j hj
  · simp only [hl3, hl2, hl1]
  · obtain ⟨b1, hb1', hne, hle⟩ := hb1 j b hb
    obtain ⟨b2, hb2', hle2⟩ := hb2 j b1 hb1'
    obtain ⟨b3, hb3', hle3⟩ := hb3 j b2 hb2'
    refine ⟨b3, hb3', fun hj => ?_, fun u hu => ?_⟩
    · rw [← hne hj]
      exact Nat.le_trans hle2 hle3
    · by_cases hj : j = i
      · subst hj
        rw [hv] at hu
        cases hu
        rw [← hch.keeps.2.2.1]
        exact Nat.le_trans hle (Nat.add_le_add_right (Nat.le_trans hle2 hle3) _)
      · rw [← hne hj]
        exact Nat.le_trans (Nat.le_trans hle2 hle3) (Nat.le_add_right _ _)

/-- The Fulu `slash_validator` on a validator that is not slashed has `SlashEffect`. -/
theorem slash_validator_fulu_slashEffect (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (hns : ∀ v, s.validators[i]? = some v → v.slashed = false)
    (h : slash_validator_fulu p f s i w = .ok s') : SlashEffect p s s' := by
  obtain ⟨hcp, hlen, hother, ⟨v, v', hv, hv', hch⟩, hblen, hbal⟩ :=
    slash_validator_fulu_ok p f hc s s' i w h
  refine ⟨hcp, hlen, hblen, ExitsSanity.exitOrder_of_pointwise fun j u' hu' => ?_,
    fun j u hu => ?_, fun j b hb => ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [hv'] at hu'
      cases hu'
      exact ⟨v, hv, hch.exit_le⟩
    · exact ⟨u', (hother j hj).symm.trans hu', id⟩
  · by_cases hj : j = i
    · subst hj
      rw [hv] at hu
      cases hu
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hch.keeps
      exact ⟨v', hv', h1, h2, h3, h5, h6, fun _ => h4⟩
    · exact ⟨u, (hother j hj).trans hu, ValidatorKeeps.refl u⟩
  · obtain ⟨b', hb', hne, hle⟩ := hbal j b hb
    refine ⟨b', hb', ?_⟩
    by_cases hj : j = i
    · subst hj
      exact .inr ⟨v, v', hv, hv', hns v hv, hch.keeps.2.2.2.1, hle v hv⟩
    · exact .inl (hne hj)

/-- The Fulu `slash_validator` on a validator that is not slashed has `SlashFields`. -/
theorem slash_validator_fulu_slashFields (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (hns : ∀ v, s.validators[i]? = some v → v.slashed = false)
    (h : slash_validator_fulu p f s i w = .ok s') : SlashFields p s s' := by
  obtain ⟨-, -, hother, ⟨v, v', hv, hv', hch⟩, -, -⟩ := slash_validator_fulu_ok p f hc s s' i w h
  intro j u u' hu hu'
  by_cases hj : j = i
  · subst hj
    rw [hv] at hu
    rw [hv'] at hu'
    cases hu
    cases hu'
    exact .inr ⟨hns v hv, hch⟩
  · rw [hother j hj, hu] at hu'
    cases hu'
    exact .inl rfl

/-- A successful Fulu proposer slashing slashes the proposer. The proposer is slashable before
the slashing. Unlike Gloas, no builder payment changes. -/
theorem process_proposer_slashing_fulu_ok (p : Preset) (o : Oracle) (f : FuluConfig)
    (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') :
    ∃ v cur, s.validators[ps.signed_header_1.message.proposer_index]? = some v ∧
      get_current_epoch p s = .ok cur ∧ is_slashable_validator v cur ∧
      slash_validator_fulu p f s ps.signed_header_1.message.proposer_index = .ok s' := by
  unfold process_proposer_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals exact ⟨_, _, (listGet_ok ‹listGet s.validators _ = _›).2,
    ‹get_current_epoch p s = _›, Decidable.of_not_not ‹¬¬is_slashable_validator _ _ = true›, h⟩

/-- The effects of a Fulu proposer slashing. The proposer `i` was not slashed and is slashed
after. Its balance drops by at most `effective_balance / MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA`.
No other balance drops, and no other validator changes. -/
theorem process_proposer_slashing_fulu_effects (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') ∧ SlashEffect p s s' ∧
      (∀ j, j ≠ ps.signed_header_1.message.proposer_index →
        s'.validators[j]? = s.validators[j]?) ∧
      (∃ v v', s.validators[ps.signed_header_1.message.proposer_index]? = some v ∧
        s'.validators[ps.signed_header_1.message.proposer_index]? = some v' ∧
        v.slashed = false ∧ v'.slashed = true ∧ SlashChange p s v v') ∧
      ∀ (j : Nat) (b : Gwei), s.balances[j]? = some b → ∃ b' : Gwei, s'.balances[j]? = some b' ∧
        (j ≠ ps.signed_header_1.message.proposer_index → b ≤ b') ∧
        ∀ v : Validator, s.validators[j]? = some v →
          b ≤ b' + v.effective_balance / p.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA := by
  obtain ⟨v, cur, hv, -, hsl, h⟩ := process_proposer_slashing_fulu_ok p o f s s' ps h
  have hns : v.slashed = false := by
    unfold is_slashable_validator at hsl
    cases hs : v.slashed
    · rfl
    · simp [hs] at hsl
  have heff := slash_validator_fulu_slashEffect p f hc s s' _ none
    (fun u hu => by rw [hv] at hu; cases hu; exact hns) h
  obtain ⟨-, -, hother, ⟨u, u', hu, hu', hch⟩, -, hbal⟩ := slash_validator_fulu_ok p f hc s s' _ none h
  rw [hv] at hu
  cases hu
  exact ⟨heff.ebStable, heff.1, heff.2.2.2.1, heff, hother, ⟨v, u', hv, hu', hns,
    hch.keeps.2.2.2.1, hch⟩, hbal⟩

/-- A Fulu attester slashing has `SlashEffect` and `SlashFields`. -/
theorem process_attester_slashing_fulu_ok (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') :
    SlashEffect p s s' ∧ SlashFields p s s' := by
  unfold process_attester_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine SlashingsSanity.forIn_invariant
    (fun r : MProd Bool BeaconState => SlashEffect p s r.snd ∧ SlashFields p s r.snd) _ ?_ _ _ _
    ⟨SlashEffect.refl p s, SlashFields.refl p s⟩ ‹forIn _ _ _ = _›
  intro index r step ⟨hr, hrf⟩ hstep
  obtain ⟨v, hv, hstep⟩ := specM_bind_ok hstep
  obtain ⟨cur, -, hstep⟩ := specM_bind_ok hstep
  split at hstep
  · rename_i hsl
    obtain ⟨r', hr', hstep⟩ := specM_bind_ok hstep
    cases hstep
    have hns : ∀ u, r.snd.validators[index]? = some u → u.slashed = false := by
      intro u hu
      rw [(listGet_ok hv).2] at hu
      cases hu
      unfold is_slashable_validator at hsl
      cases hs : v.slashed
      · rfl
      · simp [hs] at hsl
    have heff := slash_validator_fulu_slashEffect p f hc _ _ index none hns hr'
    exact ⟨hr.trans heff, hrf.trans (slash_validator_fulu_slashFields p f hc _ _ index none hns hr')
      hr.1.1 hr.2.1⟩
  · cases hstep
    exact ⟨hr, hrf⟩

/-- The effects of a Fulu attester slashing. A balance drops only for a validator that was not
slashed before and is slashed after, and by at most
`effective_balance / MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA`. -/
theorem process_attester_slashing_fulu_effects (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') ∧
      SlashFields p s s' ∧
      ∀ (j : Nat) (b : Gwei), s.balances[j]? = some b → ∃ b' : Gwei, s'.balances[j]? = some b' ∧
        (∀ v v', s.validators[j]? = some v → s'.validators[j]? = some v' →
          ¬ (v.slashed = false ∧ v'.slashed = true) → b ≤ b') ∧
        (∀ v, s.validators[j]? = some v →
          b ≤ b' + v.effective_balance / p.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA) := by
  obtain ⟨heff, hf⟩ := process_attester_slashing_fulu_ok p o f hc s s' as h
  exact ⟨heff.ebStable, heff.1, heff.2.2.2.1, hf, heff.balance_le⟩

/-! ## Attestations -/

/-- On success, the Fulu `process_attestation` changes only one participation list and the
balances. The balances come from one `increase_balance` call. -/
theorem process_attestation_fulu_shape (p : Preset) (o : Oracle) (s s' : BeaconState)
    (attestation : Attestation) (h : process_attestation_fulu p o s attestation = .ok s') :
    ∃ (epoch_participation : List ParticipationFlags) (balances : List Gwei),
      (∃ index reward, increase_balance s.balances index reward = .ok balances) ∧
      (s' = { s with current_epoch_participation := epoch_participation, balances } ∨
        s' = { s with previous_epoch_participation := epoch_participation, balances }) := by
  unfold process_attestation_fulu at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨_, _, ⟨_, _, ‹increase_balance _ _ _ = _›⟩, .inl rfl⟩)
    | (cases h; exact ⟨_, _, ⟨_, _, ‹increase_balance _ _ _ = _›⟩, .inr rfl⟩)

/-- The effects of the Fulu `process_attestation`. It keeps the registry and only adds the
proposer reward, so no balance goes down. -/
theorem process_attestation_fulu_effects (p : Preset) (o : Oracle) (s s' : BeaconState)
    (attestation : Attestation) (h : process_attestation_fulu p o s attestation = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') ∧ BalancesUp s s' ∧
      s'.validators = s.validators := by
  obtain ⟨_, bal, ⟨_, _, hb⟩, h | h⟩ := process_attestation_fulu_shape p o s s' attestation h
  all_goals
    subst h
    obtain ⟨hlen, hup⟩ := increase_balance_up hb
    exact ⟨EBStable.refl s, ⟨rfl, rfl, rfl, rfl⟩, id, ⟨Nat.le_of_eq hlen.symm, hup⟩, rfl⟩

/-! ## Execution requests -/

/-- A churn update and then a write to another field of the state has a request effect. -/
private theorem exit_churn_effect {p : Preset} {tab : Gwei} {s : BeaconState} {x : Nat}
    {r : Epoch × BeaconState} (h : compute_exit_epoch_and_update_churn p tab s x = .ok r)
    (g : BeaconState → BeaconState) (hgv : ∀ t, (g t).validators = t.validators)
    (hgb : ∀ t, (g t).balances = t.balances) (hgc : ∀ t, CheckpointsStable t (g t)) :
    (g r.2).balances = s.balances ∧ RequestEffect p s (g r.2) := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hv, hb, hcs⟩ := compute_exit_epoch_and_update_churn_bound p tab s s1 x e h
  exact ⟨(hgb s1).trans hb, .of_eq ((hgv s1).trans hv) ((hgb s1).trans hb) (hcs.trans (hgc s1))⟩

/-- The Fulu `process_withdrawal_request` keeps balances. A full exit goes through
`initiate_validator_exit`. A partial withdrawal only writes the exit churn and the queue. -/
theorem process_withdrawal_request_fulu_effect (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') :
    s'.balances = s.balances ∧ RequestEffect p s s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, RequestEffect.refl p _⟩)
    | (cases h
       exact exit_churn_effect ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
         (fun t => { t with pending_partial_withdrawals := _ }) (fun _ => rfl) (fun _ => rfl)
         (fun _ => CheckpointsStable.refl _))
    | (cases h; exact initiate_validator_exit_effect ‹initiate_validator_exit _ _ _ _ = .ok _›)

/-- The Fulu `compute_consolidation_epoch_and_update_churn` returns an epoch at least
`current + 1 + MAX_SEED_LOOKAHEAD`. It only writes the two consolidation churn fields. -/
theorem compute_consolidation_epoch_and_update_churn_fulu_bound (p : Preset) (f : FuluConfig)
    (tab : Gwei) (s s' : BeaconState) (consolidation_balance e : Nat)
    (h : compute_consolidation_epoch_and_update_churn_fulu p f tab s consolidation_balance
      = .ok (e, s')) :
    ∃ c : Nat, get_current_epoch p s = .ok c ∧ c + 1 + p.MAX_SEED_LOOKAHEAD ≤ e ∧
      s'.validators = s.validators ∧ s'.balances = s.balances ∧ CheckpointsStable s s' := by
  unfold compute_consolidation_epoch_and_update_churn_fulu at h
  obtain ⟨c, hc, h⟩ := specM_bind_ok h
  obtain ⟨a, ha, h⟩ := specM_bind_ok h
  obtain ⟨churn, -, h⟩ := specM_bind_ok h
  have hmax : (c : Nat) + 1 + p.MAX_SEED_LOOKAHEAD
      ≤ (max s.earliest_consolidation_epoch a : Nat) :=
    (compute_activation_exit_epoch_eq ha) ▸ Nat.le_max_right _ _
  generalize max s.earliest_consolidation_epoch a = m at h hmax
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       refine ⟨c, hc, Nat.le_trans hmax ?_, rfl, rfl, CheckpointsStable.refl _⟩
       simp only [uint64Add_iff] at *
       omega)

/-- The last step of a Fulu consolidation: the churn update, the exit and withdrawable epochs
of the source, and the append to the queue. -/
private theorem consolidation_exit_effect_fulu {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v v' : Validator} {r : Epoch × BeaconState} {w : Uint64}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hw : uint64Add r.1 p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok w)
    (hl : listSet r.2.validators i v' = .ok l) (hv : listGet s.validators i = .ok v)
    (hv' : v'.effective_balance = v.effective_balance ∧ v'.exit_epoch = r.1 ∧
      v'.withdrawable_epoch = w)
    (pc : List PendingConsolidation) :
    RequestEffect p s { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, hbs, hcs⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [uint64Add_iff] at hw
  rw [hvs] at hl
  refine .of_set_validator (listGet_some hv) (listSet_eq hl) ⟨hv'.1, .inr ?_⟩ hbs hcs
  rw [hv'.2.1, hv'.2.2, hw.2]
  exact Nat.le_add_right _ _

/-- Splits the binds and `if`s of a successful run without `simp`. -/
local macro "peel_ok" h:ident : tactic => `(tactic| repeat' first
  | (guard_hyp $h:ident : ((_ : SpecM _) >>= _) = _; obtain ⟨_, _, $h:ident⟩ := specM_bind_ok $h)
  | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
     rcases ite_ok $h with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩))

/-- The Fulu `process_consolidation_request` has a request effect. A switch to compounding
lowers at most one balance to `MIN_ACTIVATION_BALANCE`. A consolidation sets the exit and
withdrawable epochs of the source in order. -/
theorem process_consolidation_request_fulu_effect (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    RequestEffect p s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact RequestEffect.refl p _)
    | exact switch_to_compounding_validator_effect h
    | (cases h
       exact consolidation_exit_effect_fulu
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹uint64Add _ _ = .ok _› ‹listSet _ _ _ = .ok _› ‹listGet _ _ = .ok _›
         (by exact ⟨rfl, rfl, rfl⟩) _)

/-! ## Withdrawals and header -/

/-- The Fulu `process_withdrawals` keeps the registry and the length of `balances`. -/
theorem process_withdrawals_fulu_frame (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    s'.validators = s.validators ∧ s'.balances.length = s.balances.length := by
  unfold process_withdrawals_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals try contradiction
  obtain ⟨hv1, hl1⟩ := apply_withdrawals_fulu_ok _ _ _ ‹apply_withdrawals_fulu _ _ = _›
  obtain ⟨hv2, hb2, -⟩ := update_next_withdrawal_index_frame ‹update_next_withdrawal_index _ _ = _›
  obtain ⟨hv3, hb3, -⟩ := update_next_withdrawal_validator_index_frame h
  exact ⟨hv3.trans (hv2.trans hv1), by rw [hb3]; exact (congrArg List.length hb2).trans hl1⟩

/-- The effects of the Fulu `process_withdrawals` on validators: effective balances and
`ExitOrder` stay. -/
theorem process_withdrawals_fulu_effects (p : Preset) (s s' : BeaconState)
    (payload : FuluExecutionPayload) (h : process_withdrawals_fulu p s payload = .ok s') :
    EBStable s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') := by
  have hv := (process_withdrawals_fulu_frame p s s' payload h).1
  refine ⟨⟨by rw [hv]; exact Nat.le_refl _, fun i v hi => ⟨v, by rw [hv]; exact hi, rfl⟩⟩,
    process_withdrawals_fulu_checkpointsStable p s s' payload h, fun hs => ?_⟩
  rw [ExitOrder, hv]
  exact hs

/-- The Fulu `process_block_header` keeps validators, balances and inactivity scores. -/
theorem process_block_header_fulu_frame (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') : RegistryFrame s s' := by
  unfold process_block_header_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨rfl, rfl, rfl⟩)

/-- The effects of the Fulu `process_block_header`. -/
theorem process_block_header_fulu_effects (p : Preset) (o : Oracle) (fo : FuluOracle)
    (s s' : BeaconState) (block : FuluBeaconBlock)
    (h : process_block_header_fulu p o fo s block = .ok s') :
    EBStable s s' ∧ BalancesUp s s' ∧ CheckpointsStable s s' ∧ (ExitOrder s → ExitOrder s') := by
  have hf := process_block_header_fulu_frame p o fo s s' block h
  refine ⟨hf.ebStable, hf.balancesUp, process_block_header_fulu_checkpointsStable p o fo s s' block h,
    fun hs => ?_⟩
  rw [ExitOrder, hf.1]
  exact hs

end EpochProofs.Spec
