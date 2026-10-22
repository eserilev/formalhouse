import EpochProofs.Sanity.Invariants.FuluConsolidations
import EpochProofs.Sanity.Invariants.WithdrawableEpochs

/-!
# Exit and withdrawable epochs, for Fulu

This file is `ExitEpochs.lean`, `WithdrawableEpochs.lean` and the block part of `ExitDelay.lean`
for the Fulu functions:

- `ExitEpochsU64`: every exit epoch is at most `FAR_FUTURE_EPOCH`.
- `WithdrawableU64`: every withdrawable epoch is at most `FAR_FUTURE_EPOCH`.
- `ExitDelay`: a withdrawable epoch is at least `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` after the
  exit epoch. Each Fulu operation that neither slashes nor withdraws is an `OpStep`.

A new exit epoch or withdrawable epoch comes from `uint64Add`, so it is a `u64` value. The
Fulu `initiate_validator_exit` and `compute_exit_epoch_and_update_churn` are the Gloas functions
at `fuluTab` (`FuluCompat`), so the Gloas lemmas about them apply. The Electra consolidation
churn gets its own lemmas.
-/

namespace EpochProofs.Spec

open FuluLengthsSanity FuluEffectsSanity

namespace FuluExitsSanity

/-- An epoch `e` with a successful `e + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` is a `u64` value. -/
theorem exit_le_far {p : Preset} {e w : Nat}
    (hw : uint64Add e p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok w) : e ≤ FAR_FUTURE_EPOCH := by
  unfold uint64Add at hw
  split at hw
  · rename_i hlt
    simp only [UINT64_SIZE, FAR_FUTURE_EPOCH, Uint64, Epoch] at *
    omega
  · cases hw

/-- A successful `uint64Add` is a `u64` value. -/
theorem wd_le_far {a b w : Nat} (hw : uint64Add a b = .ok w) : w ≤ FAR_FUTURE_EPOCH := by
  unfold uint64Add at hw
  split at hw
  · rename_i hlt
    cases hw
    simp only [UINT64_SIZE, FAR_FUTURE_EPOCH, Uint64, Epoch] at *
    omega
  · cases hw

end FuluExitsSanity

open FuluExitsSanity

/-- Splits the binds and `if`s of a successful run without `simp`. -/
local macro "peel_ok" h:ident : tactic => `(tactic| repeat' first
  | (guard_hyp $h:ident : ((_ : SpecM _) >>= _) = _; obtain ⟨_, _, $h:ident⟩ := specM_bind_ok $h)
  | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
     rcases ite_ok $h with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩))

/-! ## The last step of a Fulu consolidation -/

/-- The last step of a Fulu consolidation keeps `ExitEpochsU64`. -/
theorem consolidation_exit_fulu_exitEpochsU64 {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v' : Validator} {r : Epoch × BeaconState} {w : Uint64}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hw : uint64Add r.1 p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok w)
    (hl : listSet r.2.validators i v' = .ok l) (hv' : v'.exit_epoch = r.1)
    (pc : List PendingConsolidation) (hs : ExitEpochsU64 s) :
    ExitEpochsU64 { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [hvs] at hl
  intro u hu
  change u ∈ l at hu
  rw [(ExitsSanity.listSet_ok hl).2] at hu
  exact exitEpochsU64_set hs (hv' ▸ exit_le_far hw) u hu

/-- The last step of a Fulu consolidation keeps `WithdrawableU64`. -/
theorem consolidation_exit_fulu_withdrawableU64 {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v' : Validator} {r : Epoch × BeaconState} {w : Uint64}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hw : uint64Add r.1 p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok w)
    (hl : listSet r.2.validators i v' = .ok l) (hv' : v'.withdrawable_epoch = w)
    (pc : List PendingConsolidation) (hs : WithdrawableU64 s) :
    WithdrawableU64 { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [hvs] at hl
  intro u hu
  change u ∈ l at hu
  rw [(ExitsSanity.listSet_ok hl).2] at hu
  exact withdrawableU64_set hs (hv' ▸ wd_le_far hw) u hu

/-- The last step of a Fulu consolidation has the exit shape. -/
theorem consolidation_exit_fulu_exitShape {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v v' : Validator} {r : Epoch × BeaconState} {w : Uint64}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hw : uint64Add r.1 p.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = .ok w)
    (hl : listSet r.2.validators i v' = .ok l) (hv : listGet s.validators i = .ok v)
    (hv' : v'.exit_epoch = r.1 ∧ v'.withdrawable_epoch = w)
    (hfar : ¬(v.exit_epoch != FAR_FUTURE_EPOCH) = true)
    (pc : List PendingConsolidation) :
    ExitShape p s { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨c, hc, hle, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [uint64Add_iff] at hw
  rw [hvs] at hl
  refine .of_set_exit (listGet_some hv) (listSet_eq hl) ?_ hc (by rw [hv'.1]; exact hle)
    (by rw [hv'.1, hv'.2, hw.2])
  simpa using hfar

/-- The last step of a Fulu consolidation keeps the slashed flags. -/
theorem consolidation_exit_fulu_slashedKeep {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v v' : Validator} {r : Epoch × BeaconState}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hl : listSet r.2.validators i v' = .ok l) (hv : listGet s.validators i = .ok v)
    (hv' : v'.slashed = v.slashed ∧ v'.activation_epoch = v.activation_epoch)
    (pc : List PendingConsolidation) :
    SlashedKeep s { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [hvs] at hl
  refine .of_set (ExitsSanity.listSet_ok hl).2 fun w hw => ?_
  rw [(listGet_ok hv).2] at hw
  cases hw
  exact hv'

/-! ## Exit epochs are `u64` values -/

/-- The Fulu `slash_validator` keeps `ExitEpochsU64`. -/
theorem slash_validator_fulu_exitEpochsU64 (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (h : slash_validator_fulu p f s i w = .ok s') (hs : ExitEpochsU64 s) : ExitEpochsU64 s' := by
  unfold slash_validator_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc] at h
  obtain ⟨epoch, -, h⟩ := specM_bind_ok h
  obtain ⟨v0, hv0, h⟩ := specM_bind_ok h
  obtain ⟨s1, hs1, h⟩ := SlashingsSanity.bind_if_ok h
  obtain ⟨tab, hs1⟩ := slash_validator_fulu_initiate_ok p f s s1 i v0 hv0 hs1
  have h1 := initiate_validator_exit_exitEpochsU64 hs1 hs
  obtain ⟨v1, hv1, h⟩ := specM_bind_ok h
  obtain ⟨we, -, h⟩ := specM_bind_ok h
  obtain ⟨vs2, hvs2, h⟩ := specM_bind_ok h
  have hfinal : ∀ v ∈ vs2, v.exit_epoch ≤ FAR_FUTURE_EPOCH := by
    rw [(ExitsSanity.listSet_ok hvs2).2]
    exact exitEpochsU64_set h1 (h1 v1 (List.mem_of_getElem? (listGet_ok hv1).2))
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact hfinal)

/-- The Fulu `process_attester_slashing` keeps a property that the Fulu `slash_validator`
keeps. -/
theorem process_attester_slashing_fulu_keeps (p : Preset) (o : Oracle) (f : FuluConfig)
    (P : BeaconState → Prop)
    (hsl : ∀ st st' i, slash_validator_fulu p f st i none = .ok st' → P st → P st')
    (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') (hs : P s) : P s' := by
  unfold process_attester_slashing_fulu at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  refine SlashingsSanity.forIn_invariant (fun r : MProd Bool BeaconState => P r.snd) _ ?_ _
    (⟨false, s⟩ : MProd Bool BeaconState) _ hs ‹forIn _ _ _ = _›
  intro index r step hr hstep
  obtain ⟨_, -, hstep⟩ := specM_bind_ok hstep
  obtain ⟨_, -, hstep⟩ := specM_bind_ok hstep
  split at hstep
  · obtain ⟨r', hr', hstep⟩ := specM_bind_ok hstep
    cases hstep
    exact hsl _ _ index hr' hr
  · cases hstep
    exact hr

/-- The Fulu `process_withdrawal_request` keeps `ExitEpochsU64`. -/
theorem process_withdrawal_request_fulu_exitEpochsU64 (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s')
    (hs : ExitEpochsU64 s) : ExitEpochsU64 s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact hs)
    | exact initiate_validator_exit_exitEpochsU64 ‹initiate_validator_exit _ _ _ _ = .ok _› hs
    | (cases h
       exact initiate_validator_exit_exitEpochsU64 ‹initiate_validator_exit _ _ _ _ = .ok _› hs)
    | (cases h
       obtain ⟨-, -, -, hv, -, -⟩ := compute_exit_epoch_and_update_churn_bound p _ s _ _ _
         ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
       exact ExitEpochsU64.of_validators_eq hv hs)

/-- The Fulu `process_consolidation_request` keeps `ExitEpochsU64`. -/
theorem process_consolidation_request_fulu_exitEpochsU64 (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s')
    (hs : ExitEpochsU64 s) : ExitEpochsU64 s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact hs)
    | exact switch_to_compounding_validator_exitEpochsU64 h hs
    | (cases h
       exact consolidation_exit_fulu_exitEpochsU64
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹uint64Add _ _ = .ok _› ‹listSet _ _ _ = .ok _› rfl _ hs)

/-- The Fulu `process_operations` keeps `ExitEpochsU64`. -/
theorem process_operations_fulu_exitEpochsU64 (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : ExitEpochsU64 s) :
    ExitEpochsU64 s' :=
  process_operations_fulu_inv p o f ExitEpochsU64
    (fun _ _ _ h' hs => by
      obtain ⟨_, _, -, -, -, hsl⟩ := process_proposer_slashing_fulu_ok p o f _ _ _ h'
      exact slash_validator_fulu_exitEpochsU64 p f hc _ _ _ none hsl hs)
    (fun _ _ _ h' hs => process_attester_slashing_fulu_keeps p o f ExitEpochsU64
      (fun _ _ _ h'' hs' => slash_validator_fulu_exitEpochsU64 p f hc _ _ _ none h'' hs')
      _ _ _ h' hs)
    (fun _ _ _ h' hs => ExitEpochsU64.of_validators_eq
      (process_attestation_fulu_effects p o _ _ _ h').2.2.2.2 hs)
    (fun _ _ _ h' hs => by
      obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc _ _ _ h'
      exact initiate_validator_exit_exitEpochsU64 hi hs)
    (fun _ _ _ h' hs => process_bls_to_execution_change_exitEpochsU64 p o _ _ _ h' hs)
    (fun _ _ _ h' hs => ExitEpochsU64.of_validators_eq (by cases h'; rfl) hs)
    (fun _ _ _ h' hs => process_withdrawal_request_fulu_exitEpochsU64 p f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_consolidation_request_fulu_exitEpochsU64 p f _ _ _ h' hs)
    s s' body h hs

/-- A Fulu block step that keeps the validators keeps every property of the validators. -/
theorem process_block_fulu_validators_inv (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (c : FuluBlockConfig) (P : BeaconState → Prop)
    (hv : ∀ s s', s'.validators = s.validators → P s → P s')
    (hO : ∀ a b body, process_operations_fulu p o f a body = .ok b → P a → P b)
    (fs fs' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fs block = .ok fs') (hs : P fs.state) : P fs'.state :=
  process_block_fulu_inv p o fo f c P
    (fun _ _ _ h' hs => hv _ _ (process_block_header_fulu_frame p o fo _ _ _ h').1 hs)
    (fun _ _ _ h' hs => hv _ _ (process_withdrawals_fulu_frame p _ _ _ h').1 hs)
    (fun _ _ _ h' hs => hv _ _ (process_randao_frame p o _ _ _ h').1.1 hs)
    (fun _ _ _ h' hs => hv _ _ (process_eth1_data_frame p _ _ _ h').1.1 hs)
    hO
    (fun _ _ _ h' hs => by
      obtain ⟨hfr, -⟩ := process_sync_aggregate_frame p o _ _ _ h'
      exact hv _ _ (by rw [hfr]) hs)
    fs fs' block h hs

/-- The Fulu `process_epoch` keeps every property of the validators that the registry update,
the pending deposits and the effective balance update keep. -/
theorem process_epoch_fulu_validators_inv (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (P : BeaconState → Prop)
    (hv : ∀ s s', s'.validators = s.validators → P s → P s')
    (hReg : ∀ tab a b, process_registry_updates p tab a = .ok b → P a → P b)
    (hD : ∀ tab a b, process_pending_deposits p tab (apply_pending_deposit p o) a = .ok b →
      P a → P b)
    (hEB : ∀ a b, process_effective_balance_updates p a = .ok b → P a → P b)
    (s s' : BeaconState) (h : process_epoch_fulu p f o s = .ok s') (hs : P s) : P s' :=
  process_epoch_fulu_inv p f hc o P
    (fun _ _ h' hs => hv _ _ (process_justification_and_finalization_frame p _ _ h').1.1 hs)
    (fun _ _ h' hs => hv _ _ (process_inactivity_updates_validators p _ _ h') hs)
    (fun _ _ _ h' hs => hv _ _ (process_rewards_and_penalties_validators p _ _ _ h') hs)
    hReg
    (fun _ _ _ h' hs => hv _ _ (process_slashings_validators p _ _ _ h') hs)
    (fun _ _ h' hs => hv _ _ (process_eth1_data_reset_frame p _ _ h').1.1 hs)
    hD
    (fun _ _ h' hs => hv _ _ (process_pending_consolidations_validators p _ _ h') hs)
    hEB
    (fun _ _ h' hs => hv _ _ (process_slashings_reset_frame p _ _ h').1.1 hs)
    (fun _ _ h' hs => hv _ _ (process_randao_mixes_reset_frame p _ _ h').1.1 hs)
    (fun _ _ h' hs => hv _ _ (process_historical_summaries_update_frame p o _ _ h').1.1 hs)
    (fun a hs => hv a _ (by rfl) hs)
    (fun _ _ h' hs => by
      obtain ⟨_, _, rfl⟩ := process_sync_committee_updates_fulu_shape p o _ _ h'
      exact hv _ _ (by rfl) hs)
    (fun _ _ h' hs => by
      obtain ⟨_, rfl⟩ := process_proposer_lookahead_fulu_shape p o _ _ h'
      exact hv _ _ (by rfl) hs)
    s s' h hs

/-- `state_transition_fulu` keeps every property of the validators that the Fulu operations and
the three epoch steps keep. -/
theorem state_transition_fulu_validators_inv (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (P : BeaconState → Prop)
    (hv : ∀ s s', s'.validators = s.validators → P s → P s')
    (hO : ∀ a b body, process_operations_fulu p o f a body = .ok b → P a → P b)
    (hReg : ∀ tab a b, process_registry_updates p tab a = .ok b → P a → P b)
    (hD : ∀ tab a b, process_pending_deposits p tab (apply_pending_deposit p o) a = .ok b →
      P a → P b)
    (hEB : ∀ a b, process_effective_balance_updates p a = .ok b → P a → P b)
    (fs fs' : FuluState) (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : P fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    P fs'.state :=
  state_transition_fulu_inv p o fo f c P
    (fun _ _ _ h' hs => process_slots_fulu_inv p o fo (process_epoch_fulu p f o) P
      (fun _ _ h'' hs' => hv _ _ (process_slot_fulu_frame p o fo _ _ h'').1.1 hs')
      (fun _ _ h'' hs' => process_epoch_fulu_validators_inv p f hc o P hv hReg hD hEB _ _ h'' hs')
      (fun _ _ hs' => hv _ _ (by rfl) hs') _ _ _ hs h')
    (fun _ _ _ h' hs => process_block_fulu_validators_inv p o fo f c P hv hO _ _ _ h' hs)
    fs fs' signed_block validate_result hs h

/-- `state_transition_fulu` keeps `ExitEpochsU64`. -/
theorem state_transition_fulu_exitEpochsU64 [PresetCfg] (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : ExitEpochsU64 fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    ExitEpochsU64 fs'.state :=
  state_transition_fulu_validators_inv p o fo f hc c ExitEpochsU64
    (fun _ _ hv hs => ExitEpochsU64.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_operations_fulu_exitEpochsU64 p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_registry_updates_exitEpochsU64 p _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_exitEpochsU64 p o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_exitEpochsU64 p _ _ h' hs)
    fs fs' signed_block validate_result hs h

/-! ## Withdrawable epochs are `u64` values -/

/-- The Fulu `slash_validator` keeps `WithdrawableU64`. -/
theorem slash_validator_fulu_withdrawableU64 (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (h : slash_validator_fulu p f s i w = .ok s') (hs : WithdrawableU64 s) :
    WithdrawableU64 s' := by
  unfold slash_validator_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc] at h
  obtain ⟨epoch, -, h⟩ := specM_bind_ok h
  obtain ⟨v0, hv0, h⟩ := specM_bind_ok h
  obtain ⟨s1, hs1, h⟩ := SlashingsSanity.bind_if_ok h
  obtain ⟨tab, hs1⟩ := slash_validator_fulu_initiate_ok p f s s1 i v0 hv0 hs1
  have h1 := initiate_validator_exit_withdrawableU64 hs1 hs
  obtain ⟨v1, hv1, h⟩ := specM_bind_ok h
  obtain ⟨we, hwe, h⟩ := specM_bind_ok h
  obtain ⟨vs2, hvs2, h⟩ := specM_bind_ok h
  have hfinal : ∀ v ∈ vs2, v.withdrawable_epoch ≤ FAR_FUTURE_EPOCH := by
    rw [(ExitsSanity.listSet_ok hvs2).2]
    exact withdrawableU64_set h1 (Nat.max_le.mpr
      ⟨h1 v1 (List.mem_of_getElem? (listGet_ok hv1).2), wd_le_far hwe⟩)
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; exact hfinal)

/-- The Fulu `process_withdrawal_request` keeps `WithdrawableU64`. -/
theorem process_withdrawal_request_fulu_withdrawableU64 (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s')
    (hs : WithdrawableU64 s) : WithdrawableU64 s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact hs)
    | exact initiate_validator_exit_withdrawableU64 ‹initiate_validator_exit _ _ _ _ = .ok _› hs
    | (cases h
       exact initiate_validator_exit_withdrawableU64 ‹initiate_validator_exit _ _ _ _ = .ok _› hs)
    | (cases h
       obtain ⟨-, -, -, hv, -, -⟩ := compute_exit_epoch_and_update_churn_bound p _ s _ _ _
         ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
       exact WithdrawableU64.of_validators_eq hv hs)

/-- The Fulu `process_consolidation_request` keeps `WithdrawableU64`. -/
theorem process_consolidation_request_fulu_withdrawableU64 (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s')
    (hs : WithdrawableU64 s) : WithdrawableU64 s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact hs)
    | exact switch_to_compounding_validator_withdrawableU64 h hs
    | (cases h
       refine consolidation_exit_fulu_withdrawableU64
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ?_ ‹listSet _ _ _ = .ok _› rfl _ hs
       assumption)

/-- The Fulu `process_operations` keeps `WithdrawableU64`. -/
theorem process_operations_fulu_withdrawableU64 (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : WithdrawableU64 s) :
    WithdrawableU64 s' :=
  process_operations_fulu_inv p o f WithdrawableU64
    (fun _ _ _ h' hs => by
      obtain ⟨_, _, -, -, -, hsl⟩ := process_proposer_slashing_fulu_ok p o f _ _ _ h'
      exact slash_validator_fulu_withdrawableU64 p f hc _ _ _ none hsl hs)
    (fun _ _ _ h' hs => process_attester_slashing_fulu_keeps p o f WithdrawableU64
      (fun _ _ _ h'' hs' => slash_validator_fulu_withdrawableU64 p f hc _ _ _ none h'' hs')
      _ _ _ h' hs)
    (fun _ _ _ h' hs => WithdrawableU64.of_validators_eq
      (process_attestation_fulu_effects p o _ _ _ h').2.2.2.2 hs)
    (fun _ _ _ h' hs => by
      obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc _ _ _ h'
      exact initiate_validator_exit_withdrawableU64 hi hs)
    (fun _ _ _ h' hs => process_bls_to_execution_change_withdrawableU64 p o _ _ _ h' hs)
    (fun _ _ _ h' hs => WithdrawableU64.of_validators_eq (by cases h'; rfl) hs)
    (fun _ _ _ h' hs => process_withdrawal_request_fulu_withdrawableU64 p f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_consolidation_request_fulu_withdrawableU64 p f _ _ _ h' hs)
    s s' body h hs

/-- `state_transition_fulu` keeps `WithdrawableU64`. -/
theorem state_transition_fulu_withdrawableU64 [PresetCfg] (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : WithdrawableU64 fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    WithdrawableU64 fs'.state :=
  state_transition_fulu_validators_inv p o fo f hc c WithdrawableU64
    (fun _ _ hv hs => WithdrawableU64.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_operations_fulu_withdrawableU64 p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_registry_updates_withdrawableU64 p _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_withdrawableU64 p o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_withdrawableU64 p _ _ h' hs)
    fs fs' signed_block validate_result hs h

/-! ## Operation steps and the exit delay -/

/-- The Fulu `process_voluntary_exit` is an operation step. -/
theorem process_voluntary_exit_fulu_opStep (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') : OpStep p s s' := by
  obtain ⟨-, hcp, -, hbu, hother, v, v', hv, hv', hch⟩ :=
    process_voluntary_exit_fulu_effects p o f hc s s' e h
  obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc s s' e h
  obtain ⟨-, hlen, -, -⟩ := initiate_validator_exit_ok p tab s s' _ hi
  refine ⟨hcp.1, hlen, fun j u u' hu hu' => ?_, hbu.1, fun j b hb => ?_⟩
  · by_cases hj : j = e.message.validator_index
    · subst hj
      rw [hv] at hu
      rw [hv'] at hu'
      cases hu
      cases hu'
      exact hch.vStep
    · rw [hother j hj, hu] at hu'
      cases hu'
      exact VStep.refl p _ u
  · obtain ⟨b', h', hle⟩ := hbu.2 j b hb
    exact ⟨b', h', Nat.le_trans (Nat.min_le_left _ _) hle⟩

/-- The Fulu `process_attestation` is an operation step. -/
theorem process_attestation_fulu_opStep (p : Preset) (o : Oracle) (s s' : BeaconState)
    (attestation : Attestation) (h : process_attestation_fulu p o s attestation = .ok s') :
    OpStep p s s' :=
  have he := process_attestation_fulu_effects p o s s' attestation h
  .of_balancesUp he.2.1.1 he.2.2.2.2 he.2.2.2.1

/-- The Fulu `process_withdrawal_request` has the exit shape. -/
theorem process_withdrawal_request_fulu_exitShape (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') :
    ExitShape p s s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact .of_eq rfl)
    | exact initiate_validator_exit_exitShape ‹initiate_validator_exit _ _ _ _ = .ok _›
    | (cases h; exact initiate_validator_exit_exitShape ‹initiate_validator_exit _ _ _ _ = .ok _›)
    | (cases h
       obtain ⟨-, -, -, hv, -, -⟩ := compute_exit_epoch_and_update_churn_bound p _ s _ _ _
         ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
       exact .of_eq hv)

/-- The Fulu `process_withdrawal_request` keeps the slashed flags. -/
theorem process_withdrawal_request_fulu_slashedKeep (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') :
    SlashedKeep s s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact .of_eq rfl)
    | exact initiate_validator_exit_slashedKeep ‹initiate_validator_exit _ _ _ _ = .ok _›
    | (cases h
       exact initiate_validator_exit_slashedKeep ‹initiate_validator_exit _ _ _ _ = .ok _›)
    | (cases h
       obtain ⟨-, -, -, hv, -, -⟩ := compute_exit_epoch_and_update_churn_bound p _ s _ _ _
         ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
       exact .of_eq hv)

/-- The Fulu `process_withdrawal_request` is an operation step. -/
theorem process_withdrawal_request_fulu_opStep (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') : OpStep p s s' :=
  .of_request (process_withdrawal_request_fulu_effect p f hc s s' withdrawal_request h).2
    (process_withdrawal_request_fulu_exitShape p f hc s s' withdrawal_request h)
    (process_withdrawal_request_fulu_slashedKeep p f hc s s' withdrawal_request h)

/-- The Fulu `process_consolidation_request` has the exit shape. -/
theorem process_consolidation_request_fulu_exitShape (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    ExitShape p s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact .of_eq rfl)
    | exact switch_to_compounding_validator_exitShape h
    | (cases h
       exact consolidation_exit_fulu_exitShape
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹uint64Add _ _ = .ok _› ‹listSet _ _ _ = .ok _› ‹listGet _ _ = .ok _›
         (by exact ⟨rfl, rfl⟩) ‹¬(_ != FAR_FUTURE_EPOCH) = true› _)

/-- The Fulu `process_consolidation_request` keeps the slashed flags. -/
theorem process_consolidation_request_fulu_slashedKeep (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    SlashedKeep s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact .of_eq rfl)
    | exact switch_to_compounding_validator_slashedKeep h
    | (cases h
       refine consolidation_exit_fulu_slashedKeep
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹listSet _ _ _ = .ok _› ‹listGet _ _ = .ok _› ?_ _
       exact ⟨rfl, rfl⟩)

/-- The Fulu `process_consolidation_request` is an operation step. -/
theorem process_consolidation_request_fulu_opStep (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    OpStep p s s' :=
  .of_request (process_consolidation_request_fulu_effect p f s s' consolidation_request h)
    (process_consolidation_request_fulu_exitShape p f s s' consolidation_request h)
    (process_consolidation_request_fulu_slashedKeep p f s s' consolidation_request h)

/-- The Fulu `process_proposer_slashing` keeps `ExitDelay`. -/
theorem process_proposer_slashing_fulu_exitDelay (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') (hs : ExitDelay p s) :
    ExitDelay p s' := by
  obtain ⟨-, -, -, -, hother, ⟨v, v', hv, hv', -, -, hch⟩, -⟩ :=
    process_proposer_slashing_fulu_effects p o f hc s s' ps h
  refine ExitDelay.of_pointwise (fun j u' hu' => ?_) hs
  by_cases hj : j = ps.signed_header_1.message.proposer_index
  · subst hj
    rw [hv'] at hu'
    cases hu'
    exact ⟨v, hv, hch.exitDelay⟩
  · exact ⟨u', (hother j hj).symm.trans hu', id⟩

/-- The Fulu `process_attester_slashing` keeps `ExitDelay`. -/
theorem process_attester_slashing_fulu_exitDelay (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') (hs : ExitDelay p s) :
    ExitDelay p s' := by
  obtain ⟨heff, hf⟩ := process_attester_slashing_fulu_ok p o f hc s s' as h
  exact hf.exitDelay heff.2.1 hs

/-- The Fulu `process_operations` keeps `ExitDelay`. -/
theorem process_operations_fulu_exitDelay (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : ExitDelay p s) : ExitDelay p s' :=
  process_operations_fulu_inv p o f (ExitDelay p)
    (fun _ _ _ h' hs => process_proposer_slashing_fulu_exitDelay p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_attester_slashing_fulu_exitDelay p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => (process_attestation_fulu_opStep p o _ _ _ h').exitDelay hs)
    (fun _ _ _ h' hs => (process_voluntary_exit_fulu_opStep p o f hc _ _ _ h').exitDelay hs)
    (fun _ _ _ h' hs => (process_bls_to_execution_change_opStep p o _ _ _ h').exitDelay hs)
    (fun _ _ _ h' hs => (process_deposit_request_opStep p _ _ _ h').exitDelay hs)
    (fun _ _ _ h' hs => (process_withdrawal_request_fulu_opStep p f hc _ _ _ h').exitDelay hs)
    (fun _ _ _ h' hs => (process_consolidation_request_fulu_opStep p f _ _ _ h').exitDelay hs)
    s s' body h hs

/-- `state_transition_fulu` keeps `ExitDelay`. -/
theorem state_transition_fulu_exitDelay [PresetCfg] (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : ExitDelay p fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    ExitDelay p fs'.state :=
  state_transition_fulu_validators_inv p o fo f hc c (ExitDelay p)
    (fun _ _ hv hs => ExitDelay.of_validators_eq hv hs)
    (fun _ _ _ h' hs => process_operations_fulu_exitDelay p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => process_registry_updates_exitDelay p _ _ _ h' hs)
    (fun _ _ _ h' hs => process_pending_deposits_exitDelay p o _ _ _ h' hs)
    (fun _ _ h' hs => process_effective_balance_updates_exitDelay p _ _ h' hs)
    fs fs' signed_block validate_result hs h

end EpochProofs.Spec
