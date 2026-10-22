import EpochProofs.Spec.Block.FuluBlock

/-!
# Sanity: the Fulu block functions

Small facts about the Fulu block reference that later proofs use:

- `process_operations_fulu` rejects a block with an old-style deposit.
- `process_withdrawals_fulu` accepts a payload only if its withdrawals are the expected ones.
- `apply_withdrawals_fulu` keeps the registry.
- `process_execution_payload_fulu` changes only the payload header, checks the parent hash, and
  caches the payload block hash.
- `process_attestation_fulu` keeps the registry.
- `process_block_fulu` caches the payload block hash of the block.
-/

namespace EpochProofs.Spec

private theorem bind_ok {α β : Type} {x : SpecM α} {k : α → SpecM β} {v : β}
    (h : x >>= k = .ok v) : ∃ a, x = .ok a ∧ k a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem throw_ne_ok {α : Type} {e : SpecError} {v : α} :
    (throw e : SpecM α) ≠ .ok v := by
  intro h; cases h

/-- Fulu removed the old deposit path: a block with a deposit fails. -/
theorem process_operations_fulu_deposits (p : Preset) (o : Oracle) (f : FuluConfig)
    (state : BeaconState) (body : FuluBeaconBlockBody) (h : body.deposits ≠ []) :
    process_operations_fulu p o f state body = .error .assertionFailed := by
  have hlen : ¬ body.deposits.length = 0 := by
    simpa [List.length_eq_zero_iff] using h
  simp [process_operations_fulu, hlen, throw, throwThe, MonadExceptOf.throw]
  rfl

/-- On success, the block has no deposit. -/
theorem process_operations_fulu_ok_deposits (p : Preset) (o : Oracle) (f : FuluConfig)
    (state state' : BeaconState) (body : FuluBeaconBlockBody)
    (h : process_operations_fulu p o f state body = .ok state') : body.deposits = [] := by
  cases hd : body.deposits with
  | nil => rfl
  | cons d ds =>
    rw [process_operations_fulu_deposits p o f state body (by simp [hd])] at h
    cases h

/-- `apply_withdrawals_fulu` keeps the registry and the length of `balances`. -/
theorem apply_withdrawals_fulu_ok (state state' : BeaconState) (withdrawals : List Withdrawal)
    (h : apply_withdrawals_fulu state withdrawals = .ok state') :
    state'.validators = state.validators ∧ state'.balances.length = state.balances.length := by
  induction withdrawals generalizing state with
  | nil =>
    simp [apply_withdrawals_fulu, pure, Except.pure] at h
    subst h; exact ⟨rfl, rfl⟩
  | cons w rest ih =>
    simp only [apply_withdrawals_fulu] at h
    obtain ⟨balances, hb, hrest⟩ := bind_ok h
    have ⟨hv, hl⟩ := ih _ hrest
    refine ⟨hv, ?_⟩
    rw [hl]
    simp only [decrease_balance, listSet] at hb
    obtain ⟨old, _, hset⟩ := bind_ok hb
    split at hset
    · simp [pure, Except.pure] at hset
      subst hset; simp
    · cases hset

/-- `process_withdrawals_fulu` accepts a payload only if its withdrawals are the expected
withdrawals of the state. -/
theorem process_withdrawals_fulu_expected (p : Preset) (state state' : BeaconState)
    (payload : FuluExecutionPayload)
    (h : process_withdrawals_fulu p state payload = .ok state') :
    ∃ expected, get_expected_withdrawals_fulu p state = .ok expected ∧
      payload.withdrawals = expected.withdrawals := by
  simp only [process_withdrawals_fulu] at h
  obtain ⟨expected, he, hk⟩ := bind_ok h
  refine ⟨expected, he, ?_⟩
  by_cases hne : payload.withdrawals = expected.withdrawals
  · exact hne
  · simp [hne, throw, throwThe, MonadExceptOf.throw] at hk
    cases hk

/-- `process_execution_payload_fulu` keeps the inner state, checks the parent hash and caches
the payload block hash. -/
theorem process_execution_payload_fulu_ok (p : Preset) (o : Oracle) (fo : FuluOracle)
    (c : FuluBlockConfig) (fstate fstate' : FuluState) (body : FuluBeaconBlockBody)
    (h : process_execution_payload_fulu p o fo c fstate body = .ok fstate') :
    fstate'.state = fstate.state ∧
      body.execution_payload.parent_hash = fstate.latest_execution_payload_header.block_hash ∧
      fstate'.latest_execution_payload_header.block_hash = body.execution_payload.block_hash := by
  simp only [process_execution_payload_fulu, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; refine ⟨rfl, ?_, rfl⟩; simp_all)
    | (refine ⟨rfl, ?_, rfl⟩; simp_all)

/-- `process_attestation_fulu` keeps the registry. -/
theorem process_attestation_fulu_validators (p : Preset) (o : Oracle)
    (state state' : BeaconState) (attestation : Attestation)
    (h : process_attestation_fulu p o state attestation = .ok state') :
    state'.validators = state.validators := by
  simp only [process_attestation_fulu, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; rfl)
    | rfl

/-- `process_block_fulu` caches the block hash of the block's payload. -/
theorem process_block_fulu_header (p : Preset) (o : Oracle) (fo : FuluOracle) (f : FuluConfig)
    (c : FuluBlockConfig) (fstate fstate' : FuluState) (block : FuluBeaconBlock)
    (h : process_block_fulu p o fo f c fstate block = .ok fstate') :
    fstate'.latest_execution_payload_header.block_hash =
      block.body.execution_payload.block_hash := by
  simp only [process_block_fulu] at h
  obtain ⟨s1, _, h⟩ := bind_ok h
  obtain ⟨s2, _, h⟩ := bind_ok h
  obtain ⟨fs3, h3, h⟩ := bind_ok h
  have hpay := (process_execution_payload_fulu_ok p o fo c _ fs3 block.body h3).2.2
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  simp [pure, Except.pure] at h
  subst h
  exact hpay

end EpochProofs.Spec
