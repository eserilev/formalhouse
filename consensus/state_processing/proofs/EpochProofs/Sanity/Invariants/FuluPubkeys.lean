import EpochProofs.Sanity.Invariants.FuluLengths
import EpochProofs.Sanity.Invariants.PubkeysUnique

/-!
# Validator pubkeys are unique, for Fulu

This file is `PubkeysUnique.lean` for the Fulu functions. Every Fulu block step keeps the
pubkey list (`PkSame`). The Fulu `process_epoch` keeps `PubkeysUnique` with the Gloas epoch
lemmas: a pending deposit appends a validator only for a pubkey that is not in the list. So
`state_transition_fulu` keeps `PubkeysUnique`.
-/

namespace EpochProofs.Spec

open FuluLengthsSanity

/-- The Fulu `initiate_validator_exit` keeps the pubkeys. -/
theorem initiate_validator_exit_fulu_pkSame {p : Preset} {f : FuluConfig} (hc : FuluCompat p f)
    {tab : Gwei} {s s' : BeaconState} {index : Nat}
    (h : initiate_validator_exit_fulu p f tab s index = .ok s') : PkSame s s' := by
  rw [initiate_validator_exit_fulu_eq p f hc] at h
  exact initiate_validator_exit_pkSame h

/-- The Fulu `slash_validator` keeps the pubkeys. -/
theorem slash_validator_fulu_pkSame (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (i : ValidatorIndex) (w : Option ValidatorIndex)
    (h : slash_validator_fulu p f s i w = .ok s') : PkSame s s' := by
  obtain ⟨-, hlen, hother, ⟨v, v', hv, hv', hch⟩, -⟩ := slash_validator_fulu_ok p f hc s s' i w h
  refine .of_pointwise hlen fun j u u' hu hu' => ?_
  by_cases hj : j = i
  · subst hj
    rw [hv] at hu
    rw [hv'] at hu'
    cases hu
    cases hu'
    exact hch.keeps.1
  · rw [hother j hj, hu] at hu'
    cases hu'
    rfl

/-- The Fulu `process_proposer_slashing` keeps the pubkeys. -/
theorem process_proposer_slashing_fulu_pkSame (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (ps : ProposerSlashing)
    (h : process_proposer_slashing_fulu p o f s ps = .ok s') : PkSame s s' := by
  obtain ⟨_, _, -, -, -, hsl⟩ := process_proposer_slashing_fulu_ok p o f s s' ps h
  exact slash_validator_fulu_pkSame p f hc s s' _ none hsl

/-- The Fulu `process_attester_slashing` keeps the pubkeys. -/
theorem process_attester_slashing_fulu_pkSame (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (as : AttesterSlashing)
    (h : process_attester_slashing_fulu p o f s as = .ok s') : PkSame s s' := by
  obtain ⟨heff, hf⟩ := process_attester_slashing_fulu_ok p o f hc s s' as h
  refine .of_pointwise heff.2.1 fun j v v' hv hv' => ?_
  rcases hf j v v' hv hv' with rfl | ⟨-, hch⟩
  · rfl
  · exact hch.keeps.1

/-- The Fulu `process_voluntary_exit` keeps the pubkeys. -/
theorem process_voluntary_exit_fulu_pkSame (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (e : SignedVoluntaryExit)
    (h : process_voluntary_exit_fulu p o f s e = .ok s') : PkSame s s' := by
  obtain ⟨tab, -, -, -, -, -, -, hi⟩ := process_voluntary_exit_fulu_initiate p o f hc s s' e h
  exact initiate_validator_exit_pkSame hi

/-- The Fulu `process_withdrawal_request` keeps the pubkeys. -/
theorem process_withdrawal_request_fulu_pkSame (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (s s' : BeaconState) (withdrawal_request : WithdrawalRequest)
    (h : process_withdrawal_request_fulu p f s withdrawal_request = .ok s') : PkSame s s' := by
  unfold process_withdrawal_request_fulu at h
  simp only [initiate_validator_exit_fulu_eq p f hc,
    compute_exit_epoch_and_update_churn_fulu_eq p f hc] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact PkSame.refl _)
    | exact initiate_validator_exit_pkSame ‹initiate_validator_exit _ _ _ _ = .ok _›
    | (cases h; exact initiate_validator_exit_pkSame ‹initiate_validator_exit _ _ _ _ = .ok _›)
    | (cases h
       obtain ⟨-, -, -, hv, -, -⟩ := compute_exit_epoch_and_update_churn_bound p _ s _ _ _
         ‹compute_exit_epoch_and_update_churn _ _ _ _ = .ok _›
       exact PkSame.of_eq hv)

/-- Splits the binds and `if`s of a successful run without `simp`. -/
local macro "peel_ok" h:ident : tactic => `(tactic| repeat' first
  | (guard_hyp $h:ident : ((_ : SpecM _) >>= _) = _; obtain ⟨_, _, $h:ident⟩ := specM_bind_ok $h)
  | (guard_hyp $h:ident : (@ite (SpecM _) _ (_) _ _) = _
     rcases ite_ok $h with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩))

/-- The last step of a Fulu consolidation keeps the pubkeys. -/
theorem consolidation_exit_fulu_pkSame {p : Preset} {f : FuluConfig} {tab : Gwei}
    {s : BeaconState} {x i : Nat} {v v' : Validator} {r : Epoch × BeaconState}
    {l : List Validator}
    (hr : compute_consolidation_epoch_and_update_churn_fulu p f tab s x = .ok r)
    (hl : listSet r.2.validators i v' = .ok l) (hv : listGet s.validators i = .ok v)
    (hv' : v'.pubkey = v.pubkey) (pc : List PendingConsolidation) :
    PkSame s { r.2 with validators := l, pending_consolidations := pc } := by
  obtain ⟨e, s1⟩ := r
  obtain ⟨-, -, -, hvs, -, -⟩ :=
    compute_consolidation_epoch_and_update_churn_fulu_bound p f tab s s1 x e hr
  rw [hvs] at hl
  show l.map _ = _
  rw [(ExitsSanity.listSet_ok hl).2]
  exact map_pubkey_set (listGet_ok hv).2 hv'

/-- The Fulu `process_consolidation_request` keeps the pubkeys. -/
theorem process_consolidation_request_fulu_pkSame (p : Preset) (f : FuluConfig)
    (s s' : BeaconState) (consolidation_request : ConsolidationRequest)
    (h : process_consolidation_request_fulu p f s consolidation_request = .ok s') :
    PkSame s s' := by
  unfold process_consolidation_request_fulu at h
  peel_ok h
  all_goals first
    | (cases h; exact PkSame.refl _)
    | exact switch_to_compounding_validator_pkSame h
    | (cases h
       refine consolidation_exit_fulu_pkSame
         ‹compute_consolidation_epoch_and_update_churn_fulu _ _ _ _ _ = .ok _›
         ‹listSet _ _ _ = .ok _› ‹listGet _ _ = .ok _› ?_ _
       rfl)

/-- The Fulu `process_operations` keeps `PubkeysUnique`. -/
theorem process_operations_fulu_pubkeysUnique (p : Preset) (o : Oracle) (f : FuluConfig)
    (hc : FuluCompat p f) (s s' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f s body = .ok s') (hs : PubkeysUnique s) :
    PubkeysUnique s' :=
  process_operations_fulu_inv p o f PubkeysUnique
    (fun _ _ _ h' hs => (process_proposer_slashing_fulu_pkSame p o f hc _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs => (process_attester_slashing_fulu_pkSame p o f hc _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs =>
      (PkSame.of_eq (process_attestation_fulu_effects p o _ _ _ h').2.2.2.2).pubkeysUnique hs)
    (fun _ _ _ h' hs => (process_voluntary_exit_fulu_pkSame p o f hc _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs =>
      (process_bls_to_execution_change_pkSame p o _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs => (PkSame.of_eq (by cases h'; rfl)).pubkeysUnique hs)
    (fun _ _ _ h' hs => (process_withdrawal_request_fulu_pkSame p f hc _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs => (process_consolidation_request_fulu_pkSame p f _ _ _ h').pubkeysUnique hs)
    s s' body h hs

/-- The Fulu `process_block` keeps `PubkeysUnique`. -/
theorem process_block_fulu_pubkeysUnique (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (block : FuluBeaconBlock) (h : process_block_fulu p o fo f c fs block = .ok fs')
    (hs : PubkeysUnique fs.state) : PubkeysUnique fs'.state :=
  process_block_fulu_inv p o fo f c PubkeysUnique
    (fun _ _ _ h' hs =>
      (PkSame.of_eq (process_block_header_fulu_frame p o fo _ _ _ h').1).pubkeysUnique hs)
    (fun _ _ _ h' hs =>
      (PkSame.of_eq (process_withdrawals_fulu_frame p _ _ _ h').1).pubkeysUnique hs)
    (fun _ _ _ h' hs => (PkSame.of_eq (process_randao_frame p o _ _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ _ h' hs => (PkSame.of_eq (process_eth1_data_frame p _ _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ _ h' hs => process_operations_fulu_pubkeysUnique p o f hc _ _ _ h' hs)
    (fun _ _ _ h' hs => by
      obtain ⟨hfr, -⟩ := process_sync_aggregate_frame p o _ _ _ h'
      exact (PkSame.of_eq (by rw [hfr])).pubkeysUnique hs)
    fs fs' block h hs

/-- The Fulu `process_epoch` keeps `PubkeysUnique`. -/
theorem process_epoch_fulu_pubkeysUnique [PresetCfg] (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (s s' : BeaconState) (h : process_epoch_fulu p f o s = .ok s')
    (hs : PubkeysUnique s) : PubkeysUnique s' :=
  process_epoch_fulu_inv p f hc o PubkeysUnique
    (fun _ _ h' hs => (PkSame.of_eq
      (process_justification_and_finalization_frame p _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ h' hs => (PkSame.of_eq (process_inactivity_updates_validators p _ _ h')).pubkeysUnique hs)
    (fun _ _ _ h' hs =>
      (PkSame.of_eq (process_rewards_and_penalties_validators p _ _ _ h')).pubkeysUnique hs)
    (fun _ _ _ h' hs => (process_registry_updates_pkSame p _ _ _ h').pubkeysUnique hs)
    (fun _ _ _ h' hs => (PkSame.of_eq (process_slashings_validators p _ _ _ h')).pubkeysUnique hs)
    (fun _ _ h' hs => (PkSame.of_eq (process_eth1_data_reset_frame p _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ _ h' hs => process_pending_deposits_pubkeysUnique p o _ _ _ h' hs)
    (fun _ _ h' hs =>
      (PkSame.of_eq (process_pending_consolidations_validators p _ _ h')).pubkeysUnique hs)
    (fun _ _ h' hs => (process_effective_balance_updates_pkSame p _ _ h').pubkeysUnique hs)
    (fun _ _ h' hs => (PkSame.of_eq (process_slashings_reset_frame p _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ h' hs =>
      (PkSame.of_eq (process_randao_mixes_reset_frame p _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ h' hs =>
      (PkSame.of_eq (process_historical_summaries_update_frame p o _ _ h').1.1).pubkeysUnique hs)
    (fun _ hs => hs)
    (fun _ _ h' hs => by
      obtain ⟨_, _, rfl⟩ := process_sync_committee_updates_fulu_shape p o _ _ h'
      exact hs)
    (fun _ _ h' hs => by
      obtain ⟨_, rfl⟩ := process_proposer_lookahead_fulu_shape p o _ _ h'
      exact hs)
    s s' h hs

/-- `process_slots_fulu` with the Fulu `process_epoch` keeps `PubkeysUnique`. -/
theorem process_slots_fulu_pubkeysUnique [PresetCfg] (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (o : Oracle) (fo : FuluOracle) (fs fs' : FuluState) (slot : Slot)
    (h : process_slots_fulu p o fo (process_epoch_fulu p f o) fs slot = .ok fs')
    (hs : PubkeysUnique fs.state) : PubkeysUnique fs'.state :=
  process_slots_fulu_inv p o fo (process_epoch_fulu p f o) PubkeysUnique
    (fun _ _ h' hs => (PkSame.of_eq (process_slot_fulu_frame p o fo _ _ h').1.1).pubkeysUnique hs)
    (fun _ _ h' hs => process_epoch_fulu_pubkeysUnique p f hc o _ _ h' hs)
    (fun _ _ hs => hs) fs fs' slot hs h

/-- `state_transition_fulu` keeps `PubkeysUnique`. -/
theorem state_transition_fulu_pubkeysUnique [PresetCfg] (p : Preset) (o : Oracle) (fo : FuluOracle)
    (f : FuluConfig) (hc : FuluCompat p f) (c : FuluBlockConfig) (fs fs' : FuluState)
    (signed_block : FuluSignedBeaconBlock) (validate_result : Bool)
    (hs : PubkeysUnique fs.state)
    (h : state_transition_fulu p o fo f c fs signed_block validate_result = .ok fs') :
    PubkeysUnique fs'.state :=
  state_transition_fulu_inv p o fo f c PubkeysUnique
    (fun _ _ _ h' hs => process_slots_fulu_pubkeysUnique p f hc o fo _ _ _ h' hs)
    (fun _ _ _ h' hs => process_block_fulu_pubkeysUnique p o fo f hc c _ _ _ h' hs)
    fs fs' signed_block validate_result hs h

end EpochProofs.Spec
