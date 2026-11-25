import EthLib.Cryptography.Proofs.Bls.Represents
import EthLib.Cryptography.Proofs.Bls.KeyValidate
import EpochProofs.ResultsOnPresets

/-!
# The assumptions of the main theorems hold together for an example

A theorem with assumptions that cannot hold together proves nothing. This file gives a Gloas state
and a Fulu state on the minimal preset, and proves that the state assumptions hold there.
`exampleEthLibState` is the same state in EthLib. The last two theorems say that the assumptions of
the EthLib theorems hold there too, and that the epoch succeeds.

Not covered: the runs (`FuluThenGloasRun`, `FuluOnlyRun`), the caches and the untranslated Rust.
-/

namespace EpochProofs.Spec

/-- Every pass of the balance weighted selection accepts when every candidate has the maximum
effective balance, whatever the hash values. -/
theorem selectionAccepts_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (i : Nat) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    selectionAccepts p o seed ebs shuffle i = true := by
  have hk : selectionCandidate p o seed ebs.length shuffle i < ebs.length := by
    unfold selectionCandidate; split
    · exact shuffledIndexAfterRounds_lt o seed.toList ebs.length p.SHUFFLE_ROUND_COUNT _ hpos (Nat.mod_lt _ hpos)
    · exact Nat.mod_lt _ hpos
  unfold selectionAccepts
  rw [List.getD_eq_getElem _ _ hk, hall _ (List.getElem_mem hk)]
  have := littleEndianValue_take2_lt ((selectionBytes o seed i).toList.drop (i % 16 * 2))
  simp only [decide_eq_true_eq, ge_iff_le]
  exact Nat.mul_le_mul_left _ (by omega)

theorem selectionAcceptedCount_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) (m : Nat) :
    selectionAcceptedCount p o seed ebs shuffle m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [selectionAcceptedCount_succ, ih, selectionAccepts_full p o seed ebs shuffle m hpos hall]; rfl

/-- `SelectionEnds` holds for every seed when the candidates are validators with the maximum effective
balance. -/
theorem selectionEnds_full (p : Preset) (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffle : Bool) (hne : indices ≠ [])
    (hin : ∀ j ∈ indices, j < s.validators.length)
    (heb : ∀ v ∈ s.validators, v.effective_balance = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hsize : size < 2 ^ 64) : SelectionEnds p o s indices seed size shuffle := by
  refine ⟨size, hsize, ?_⟩
  rw [selectionAcceptedCount_full]
  · simpa [effectiveBalancesOf, List.length_pos_iff] using hne
  · intro x hx
    simp only [effectiveBalancesOf, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.getElem?_eq_getElem (hin j hj)]
    exact heb _ (List.getElem_mem _)

end EpochProofs.Spec

namespace EpochProofs.Example

open EpochProofs.Spec
open _root_.EthLib.Cryptography.Bls (Fr G1)

/-- The public key of the secret key `k + 1`. -/
def examplePubkey (k : Nat) : BLSPubkey := G1.compress (G1.mul G1.generator (Fr.ofNat (k + 1)))

/-- A validator that is active from epoch 0, never exits, and has the maximum effective balance. -/
def exampleValidator (k : Nat) : Validator :=
  { pubkey := examplePubkey k
    withdrawal_credentials := Bytes32.zero.set 0 2
    effective_balance := 2048000000000, slashed := false
    activation_eligibility_epoch := 0, activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- Eight validators at the last slot of epoch 0, as a reference state. -/
def exampleGloasState : BeaconState :=
  { slot := 7
    block_roots := List.replicate 64 Bytes32.zero
    state_roots := List.replicate 64 Bytes32.zero
    validators := (List.range 8).map exampleValidator
    balances := List.replicate 8 2048000000000
    randao_mixes := List.replicate 64 Bytes32.zero
    slashings := List.replicate 64 0
    previous_epoch_participation := List.replicate 8 0
    current_epoch_participation := List.replicate 8 0
    justification_bits := List.replicate 4 false
    inactivity_scores := List.replicate 8 0
    current_sync_committee := { pubkeys := List.replicate 32 BLSPubkey.zero }
    next_sync_committee := { pubkeys := List.replicate 32 BLSPubkey.zero }
    proposer_lookahead := List.replicate 16 0
    execution_payload_availability := List.replicate 64 false
    builder_pending_payments := List.replicate 16 BuilderPendingPayment.empty
    builder_pending_withdrawals := []
    ptc_window := List.replicate 24 (List.replicate 16 0) }

/-- `exampleGloasState` without the Gloas fields: a Fulu reference state. -/
def exampleFuluState : BeaconState :=
  { exampleGloasState with
    execution_payload_availability := [], builder_pending_payments := [], ptc_window := [] }

/-- Each example key is the key of a nonzero secret key, so it decodes to a valid point. -/
theorem examplePubkey_point (k : Nat) (hk : k < 8) :
    ∃ point, G1.keyValidatePoint (examplePubkey k) = .ok point ∧
      G1.Represents point (Fr.ofNat (k + 1)) := by
  have hne : ∀ k < 8, Fr.ofNat (k + 1) ≠ 0 := by decide +kernel
  unfold examplePubkey
  exact G1.keyValidatePoint_compress_mul (hne k hk)

/-- Each example key passes `KeyValidate`. -/
theorem examplePubkey_valid (k : Nat) (hk : k < 8) :
    G1.keyValidate (examplePubkey k) = .ok () := by
  obtain ⟨point, hpoint, -⟩ := examplePubkey_point k hk
  generalize examplePubkey k = pubkey at hpoint
  unfold G1.keyValidate
  rw [hpoint]
  rfl

/-- Two example keys are different, because their secret keys are different. -/
theorem examplePubkeys_unique : ((List.range 8).map examplePubkey).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj heq
  rw [List.mem_range] at hi hj
  have hinj : ∀ i < 8, ∀ j < 8, Fr.ofNat (i + 1) = Fr.ofNat (j + 1) → i = j := by decide +kernel
  obtain ⟨point, hpoint, hi'⟩ := examplePubkey_point i hi
  obtain ⟨point', hpoint', hj'⟩ := examplePubkey_point j hj
  rw [heq, hpoint', Except.ok.injEq] at hpoint
  subst hpoint
  exact hinj i hi j hj (hi'.unique hj')

section Minimal

attribute [local instance] currentPresetMinimal currentFuluConfigMinimal
local instance : @CurrentPreset.Valid currentPresetMinimal := currentPresetMinimal_ok
local instance : @CurrentPreset.Bounds currentPresetMinimal := currentPresetMinimal_bounds
local instance : CurrentFuluConfig.Valid := ⟨fuluCompat_minimal⟩

/-- The steps before the committee steps return `exampleGloasState` itself: at epoch 0 the
justification, inactivity and rewards steps skip, and nothing else changes on this state. -/
theorem exampleGloasState_epochBeforeCommitteeSteps
    (o : Oracle) : epochBeforeCommitteeSteps P o exampleGloasState = .ok exampleGloasState := by rfl

theorem exampleFuluState_epochBeforeCommitteeStepsFulu
    (o : Oracle) : epochBeforeCommitteeStepsFulu P FC o exampleFuluState = .ok exampleFuluState := by
  rfl

theorem exampleGloasState_effectiveBalances : ∀ v ∈ exampleGloasState.validators,
    v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide +kernel

theorem exampleGloasState_active_lt (e j : Nat)
    (h : j ∈ get_active_validator_indices exampleGloasState e) :
    j < exampleGloasState.validators.length := active_lt exampleGloasState e j h

theorem exampleGloasState_committeeStepFacts (o : Oracle) (hk : ∀ v ∈ exampleGloasState.validators,
    o.bls_KeyValidate v.pubkey = true) :
    CommitteeStepFacts o exampleGloasState :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, hk⟩

theorem exampleGloasState_committeeStepPreconditions (o : Oracle) :
    CommitteeStepPreconditions o exampleGloasState where
  syncCommitteeHasCandidate := by decide +kernel
  proposerHasCandidate := by decide +kernel
  enoughActiveForPtc := by decide +kernel
  syncSelectionEnds seed := selectionEnds_full P o exampleGloasState _ seed _ true (by decide +kernel)
    (exampleGloasState_active_lt _) exampleGloasState_effectiveBalances (by decide +kernel)
  proposerSelectionEnds seed := selectionEnds_full P o exampleGloasState _ seed _ true (by decide +kernel)
    (fun j hj => exampleGloasState_active_lt _ j (List.mem_of_mem_filter hj))
      exampleGloasState_effectiveBalances
      (by decide +kernel)
  ptcSelectionEnds slot hslot l hl seed := by
    have he : slot / P.SLOTS_PER_EPOCH = 2 := hslot
    have h32 : P.SLOTS_PER_EPOCH ≤
        (get_active_validator_indices exampleGloasState (slot / P.SLOTS_PER_EPOCH)).length := by
      rw [he]; decide +kernel
    obtain ⟨l', hl1, hl2, hl3⟩ := ptcIndices_total o exampleGloasState slot
      (by rw [he]; decide +kernel) (by decide +kernel)
      ((active_len_le _ _).trans (by decide +kernel))
    have hll : l' = l := by rw [hl1] at hl; exact Except.ok.inj hl
    rw [← hll]
    have hne : l' ≠ [] := by
      intro h; rw [h] at hl2
      have := ptc_len_pos _ (slot % P.SLOTS_PER_EPOCH) _ P_slots_pos h32
      simp at hl2; omega
    exact selectionEnds_full P o exampleGloasState l' seed _ false hne
      (fun j hj => exampleGloasState_active_lt _ j (hl3 j hj)) exampleGloasState_effectiveBalances
      (by decide +kernel)

/-- The Gloas committee conditions hold at `exampleGloasState`, for every oracle that accepts the
eight keys. -/
theorem exampleGloasState_atCommitteeStepState (o : Oracle)
    (hk : ∀ v ∈ exampleGloasState.validators, o.bls_KeyValidate v.pubkey = true) :
    AtCommitteeStepState o exampleGloasState := by
  intro s hs
  rw [exampleGloasState_epochBeforeCommitteeSteps] at hs
  cases hs
  exact ⟨exampleGloasState_committeeStepFacts o hk, exampleGloasState_committeeStepPreconditions o⟩

theorem exampleGloasState_listLengthsMatch : ListLengthsMatch exampleGloasState := by unfold ListLengthsMatch; decide +kernel

theorem exampleGloasState_pubkeys : PubkeysUnique exampleGloasState := examplePubkeys_unique

theorem exampleGloasState_vectors : exampleGloasState.VectorLengths P :=
    by unfold BeaconState.VectorLengths; decide +kernel

theorem exampleGloasState_fuluVectors : exampleGloasState.FuluVectorLengths P := by
  unfold BeaconState.FuluVectorLengths; decide +kernel

theorem exampleGloasState_atLastSlotOfEpoch : AtLastSlotOfEpoch exampleGloasState := by
  unfold AtLastSlotOfEpoch; decide +kernel

theorem exampleGloasState_supplyAndTimeLimits : SupplyAndTimeLimits exampleGloasState where
  inactivityScoresBounded := by decide +kernel
  effectiveBalancesBounded := by decide +kernel
  balancesAndDepositsBounded := by decide +kernel
  earliestExitEpochBounded := by decide +kernel
  exitBalanceBounded := by decide +kernel
  validatorCountBounded := by decide +kernel
  participationBounded tab htab f hf x hx := by
    rw [show get_total_active_balance P exampleGloasState = .ok 16384000000000 from rfl] at htab
    cases htab
    have h0 : rewardsFlagIncrements P exampleGloasState
      (exampleGloasState.slot / P.SLOTS_PER_EPOCH - 1) 0 = .ok 1 := rfl
    have h1 : rewardsFlagIncrements P exampleGloasState
      (exampleGloasState.slot / P.SLOTS_PER_EPOCH - 1) 1 = .ok 1 := rfl
    have h2 : rewardsFlagIncrements P exampleGloasState
      (exampleGloasState.slot / P.SLOTS_PER_EPOCH - 1) 2 = .ok 1 := rfl
    interval_cases f
    · rw [h0] at hx; cases hx; decide
    · rw [h1] at hx; cases hx; decide
    · rw [h2] at hx; cases hx; decide

theorem exampleGloasState_genesisInvariants : GenesisInvariants exampleGloasState where
  checkpointsInOrder := by unfold CheckpointsInOrder CheckpointOrder epochOf; decide +kernel
  listLengthsMatch := exampleGloasState_listLengthsMatch
  exitToWithdrawableDelay := by unfold ExitToWithdrawableDelay ValidatorExitToWithdrawableDelay; decide +kernel
  exitEpochsAreUint64 := by unfold ExitEpochsAreUint64; decide +kernel
  afterEffectiveBalanceUpdates := by unfold AfterEffectiveBalanceUpdates; decide +kernel
  pubkeysUnique := exampleGloasState_pubkeys
  consolidationsInRange := by unfold ConsolidationsInRange; decide +kernel
  withdrawableEpochsFitUint64 := by unfold WithdrawableEpochsFitUint64; decide +kernel

theorem exampleGloasState_epochInputInvariants : EpochInputInvariants exampleGloasState := by
  unfold EpochInputInvariants EpochInputInvariantsFor EpochInputInvariantsWithPubkeys BasicEpochInputInvariants EpochEndInvariants BalancesFarFromOverflow
  refine ⟨⟨⟨⟨exampleGloasState_genesisInvariants.checkpointsInOrder, exampleGloasState_listLengthsMatch, ?_⟩, by decide +kernel, ?_,
    exampleGloasState_genesisInvariants.exitEpochsAreUint64,
    by decide +kernel, by decide +kernel, by decide +kernel⟩, exampleGloasState_pubkeys,
    exampleGloasState_genesisInvariants.consolidationsInRange⟩, exampleGloasState_genesisInvariants.withdrawableEpochsFitUint64, ?_⟩
  · unfold EligibleBalancesAboveFloor; decide +kernel
  · unfold EffectiveBalancesValid EffectiveBalanceValid; decide +kernel
  · unfold NoWithdrawableEpochWithoutExit; decide +kernel

/-- For an oracle that accepts the eight keys, the Gloas assumptions about the state hold together
at `exampleGloasState`. The epoch reaches its committee steps, and the spec `process_epoch` returns
`ok`. -/
theorem gloas_assumptions_hold_for_example (o : Oracle)
    (hk : ∀ v ∈ exampleGloasState.validators, o.bls_KeyValidate v.pubkey = true) :
    GenesisInvariants exampleGloasState ∧ EpochInputInvariants exampleGloasState ∧
      PubkeysUnique exampleGloasState ∧ exampleGloasState.VectorLengths P ∧
      AtLastSlotOfEpoch exampleGloasState ∧ exampleGloasState.slot + 8192 < 2 ^ 64 ∧
      SupplyAndTimeLimits exampleGloasState ∧ AtCommitteeStepState o exampleGloasState ∧
      epochBeforeCommitteeSteps P o exampleGloasState = .ok exampleGloasState ∧ ∃ s',
        process_epoch P o exampleGloasState = .ok s' := by
  have hc := exampleGloasState_atCommitteeStepState o hk
  have hokc := committeesOk_of o exampleGloasState (by decide +kernel) hc exampleGloasState
    (exampleGloasState_epochBeforeCommitteeSteps o)
    ⟨rfl, exampleGloasState_listLengthsMatch, by decide +kernel⟩
  obtain ⟨s', hs', -⟩ := hokc
  refine ⟨exampleGloasState_genesisInvariants, exampleGloasState_epochInputInvariants,
    exampleGloasState_pubkeys, exampleGloasState_vectors, exampleGloasState_atLastSlotOfEpoch,
    by decide +kernel, exampleGloasState_supplyAndTimeLimits, hc,
    exampleGloasState_epochBeforeCommitteeSteps o, s', ?_⟩
  rw [process_epoch_committees, exampleGloasState_epochBeforeCommitteeSteps, tot_bind_ok]
  exact hs'

theorem exampleFuluState_effectiveBalances : ∀ v ∈ exampleFuluState.validators,
    v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA :=
  exampleGloasState_effectiveBalances

theorem exampleFuluState_atCommitteeStepState (o : Oracle)
    (hk : ∀ v ∈ exampleFuluState.validators,
      o.bls_KeyValidate v.pubkey = true) : AtCommitteeStepStateFulu o exampleFuluState := by
  intro s hs
  rw [exampleFuluState_epochBeforeCommitteeStepsFulu] at hs
  cases hs
  exact ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, hk⟩,
    ⟨by decide +kernel, by decide +kernel,
      fun seed => selectionEnds_full P o exampleFuluState _ seed _ true (by decide +kernel)
        (fun j hj => active_lt exampleFuluState _ j hj) exampleFuluState_effectiveBalances
          (by decide +kernel),
      fun seed => selectionEnds_full P o exampleFuluState _ seed _ true (by decide +kernel)
        (fun j hj => active_lt exampleFuluState _ j hj) exampleFuluState_effectiveBalances
          (by decide +kernel)⟩⟩

theorem exampleFuluState_listLengthsMatch : ListLengthsMatch exampleFuluState := exampleGloasState_listLengthsMatch

theorem exampleFuluState_supplyAndTimeLimits : SupplyAndTimeLimits exampleFuluState where
  inactivityScoresBounded := by decide +kernel
  effectiveBalancesBounded := by decide +kernel
  balancesAndDepositsBounded := by decide +kernel
  earliestExitEpochBounded := by decide +kernel
  exitBalanceBounded := by decide +kernel
  validatorCountBounded := by decide +kernel
  participationBounded tab htab f hf x hx :=
    exampleGloasState_supplyAndTimeLimits.participationBounded tab htab f hf x hx

theorem exampleFuluState_genesisInvariants : GenesisInvariants exampleFuluState where
  checkpointsInOrder := exampleGloasState_genesisInvariants.checkpointsInOrder
  listLengthsMatch := exampleGloasState_listLengthsMatch
  exitToWithdrawableDelay := exampleGloasState_genesisInvariants.exitToWithdrawableDelay
  exitEpochsAreUint64 := exampleGloasState_genesisInvariants.exitEpochsAreUint64
  afterEffectiveBalanceUpdates := exampleGloasState_genesisInvariants.afterEffectiveBalanceUpdates
  pubkeysUnique := exampleGloasState_pubkeys
  consolidationsInRange := exampleGloasState_genesisInvariants.consolidationsInRange
  withdrawableEpochsFitUint64 := exampleGloasState_genesisInvariants.withdrawableEpochsFitUint64

theorem exampleFuluState_epochInputInvariants : EpochInputInvariants exampleFuluState :=
    exampleGloasState_epochInputInvariants

theorem exampleFuluState_fuluVectors : exampleFuluState.FuluVectorLengths P :=
    exampleGloasState_fuluVectors

theorem exampleFuluState_atLastSlotOfEpoch : AtLastSlotOfEpoch exampleFuluState :=
  exampleGloasState_atLastSlotOfEpoch

/-- For an oracle that accepts the eight keys, the Fulu assumptions about the state hold together at
`exampleFuluState`. The epoch reaches its committee steps, and the Fulu spec `process_epoch` returns
`ok`. -/
theorem fulu_assumptions_hold_for_example (o : Oracle)
    (hk : ∀ v ∈ exampleFuluState.validators, o.bls_KeyValidate v.pubkey = true) :
    GenesisInvariants exampleFuluState ∧ EpochInputInvariants exampleFuluState ∧
      exampleFuluState.FuluVectorLengths P ∧ AtLastSlotOfEpoch exampleFuluState ∧
      exampleFuluState.slot + 8192 < 2 ^ 64 ∧ SupplyAndTimeLimits exampleFuluState ∧
        AtCommitteeStepStateFulu o exampleFuluState ∧
      epochBeforeCommitteeStepsFulu P FC o exampleFuluState = .ok exampleFuluState ∧
      ∃ s', process_epoch_fulu P FC o exampleFuluState = .ok s' := by
  have hc := exampleFuluState_atCommitteeStepState o hk
  obtain ⟨s', hs', -⟩ := committeesOkFulu_of o exampleFuluState
    (by decide +kernel) hc exampleFuluState
    (exampleFuluState_epochBeforeCommitteeStepsFulu o) ⟨rfl, exampleFuluState_listLengthsMatch, by decide +kernel⟩
  refine ⟨exampleFuluState_genesisInvariants, exampleFuluState_epochInputInvariants,
    exampleFuluState_fuluVectors, exampleGloasState_atLastSlotOfEpoch, by decide +kernel,
    exampleFuluState_supplyAndTimeLimits, hc, exampleFuluState_epochBeforeCommitteeStepsFulu o, s', ?_⟩
  rw [process_epoch_fulu_committees, exampleFuluState_epochBeforeCommitteeStepsFulu, tot_bind_ok]
  exact hs'


/-- The state hypotheses of the Gloas agreement theorem hold at `exampleGloasState`. -/
theorem gloas_agreement_assumptions_hold_for_example :
    EpochInputInvariants exampleGloasState ∧ AtLastSlotOfEpoch exampleGloasState ∧
      exampleGloasState.historical_summaries.length < LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT :=
  ⟨exampleGloasState_epochInputInvariants, exampleGloasState_atLastSlotOfEpoch,
    exampleGloasState_atLastSlotOfEpoch.2.2⟩

/-- The state hypotheses of the Fulu agreement theorem hold at `exampleFuluState`. -/
theorem fulu_agreement_assumptions_hold_for_example :
    EpochInputInvariants exampleFuluState ∧ AtLastSlotOfEpoch exampleFuluState ∧
      exampleFuluState.historical_summaries.length < LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT :=
  ⟨exampleFuluState_epochInputInvariants, exampleFuluState_atLastSlotOfEpoch,
    exampleFuluState_atLastSlotOfEpoch.2.2⟩

/-- At `exampleGloasState`, the Lean model of Lighthouse's Gloas epoch and the transcription agree,
for every oracle. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_for_example (o : Oracle) :
    SameResultOrBothFail (process_epoch_lighthouse o exampleGloasState)
      (process_epoch P o exampleGloasState) :=
  Formalhouse.lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants o
    exampleGloasState_epochInputInvariants exampleGloasState_atLastSlotOfEpoch

end Minimal

/-! ## EthLib states -/

section EthLib

open EpochProofs.EthLib
open _root_.EthLib.Consensus (Config Preset SignatureChecks processEpoch)

/-- `exampleValidator` as an EthLib validator. -/
def exampleEthLibValidator (k : Nat) : _root_.EthLib.Consensus.Validator where
  pubkey := examplePubkey k
  withdrawalCredentials := Bytes32.zero.set 0 2
  effectiveBalance := 2048000000000
  slashed := false
  activationEligibilityEpoch := 0
  activationEpoch := 0
  exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH
  withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH

/-- The example as an EthLib state of a fork on the minimal preset: eight validators, at the last
slot of epoch 0. Every other field is zero or empty. -/
def exampleEthLibState (fork : _root_.EthLib.Base.Fork) :
    _root_.EthLib.Consensus.BeaconState Preset.minimal fork where
  genesisTime := 0
  genesisValidatorsRoot := Bytes32.zero
  slot := 7
  forkVersions := ⟨Vector.replicate 4 0, Vector.replicate 4 0, 0⟩
  latestBlockHeader := ⟨0, 0, Bytes32.zero, Bytes32.zero, Bytes32.zero⟩
  blockRoots := .ofVector (Vector.replicate _ Bytes32.zero)
  stateRoots := .ofVector (Vector.replicate _ Bytes32.zero)
  historicalRoots := ⟨#[], by decide⟩
  eth1Data := fun _ => ⟨Bytes32.zero, 0, Bytes32.zero⟩
  eth1DataVotes := fun _ => ⟨#[], by decide⟩
  eth1DepositIndex := fun _ => 0
  validators := .ofData #[exampleEthLibValidator 0, exampleEthLibValidator 1,
    exampleEthLibValidator 2, exampleEthLibValidator 3, exampleEthLibValidator 4,
    exampleEthLibValidator 5, exampleEthLibValidator 6, exampleEthLibValidator 7]
    fun _ => by decide
  balances := ⟨Array.replicate 8 2048000000000, fun _ => by decide⟩
  randaoMixes := .ofVector (Vector.replicate _ Bytes32.zero)
  slashings := .ofVector (Vector.replicate _ 0)
  previousEpochAttestations := fun _ => ⟨#[], by decide⟩
  currentEpochAttestations := fun _ => ⟨#[], by decide⟩
  previousEpochParticipation := fun _ => ⟨Array.replicate 8 0, fun _ => by decide⟩
  currentEpochParticipation := fun _ => ⟨Array.replicate 8 0, fun _ => by decide⟩
  justificationBits := ⟨Vector.replicate _ false⟩
  previousJustifiedCheckpoint := ⟨0, Bytes32.zero⟩
  currentJustifiedCheckpoint := ⟨0, Bytes32.zero⟩
  finalizedCheckpoint := ⟨0, Bytes32.zero⟩
  inactivityScores := fun _ => ⟨Array.replicate 8 0, fun _ => by decide⟩
  currentSyncCommittee := fun _ =>
    .of ⟨Vector.replicate _ BLSPubkey.zero, BLSPubkey.zero⟩
  nextSyncCommittee := fun _ =>
    .of ⟨Vector.replicate _ BLSPubkey.zero, BLSPubkey.zero⟩
  latestExecutionPayloadHeader := fun _ =>
    { parentHash := Bytes32.zero
      feeRecipient := Vector.replicate _ 0
      stateRoot := Bytes32.zero
      receiptsRoot := Bytes32.zero
      logsBloom := Vector.replicate _ 0
      prevRandao := Bytes32.zero
      blockNumber := 0
      gasLimit := 0
      gasUsed := 0
      timestamp := 0
      extraData := ⟨#[], by decide⟩
      baseFeePerGas := 0
      blockHash := Bytes32.zero
      transactionsRoot := Bytes32.zero
      withdrawalsRoot := fun _ => Bytes32.zero
      blobGasUsed := fun _ => 0
      excessBlobGas := fun _ => 0 }
  latestBlockHash := fun _ => Bytes32.zero
  nextWithdrawalIndex := fun _ => 0
  nextWithdrawalValidatorIndex := fun _ => 0
  historicalSummaries := fun _ => ⟨#[], by decide⟩
  depositRequestsStartIndex := fun _ => 0
  depositBalanceToConsume := fun _ => 0
  exitBalanceToConsume := fun _ => 0
  earliestExitEpoch := fun _ => 0
  consolidationBalanceToConsume := fun _ => 0
  earliestConsolidationEpoch := fun _ => 0
  pendingDeposits := fun _ => ⟨#[], fun _ => by decide⟩
  pendingPartialWithdrawals := fun _ => ⟨#[], fun _ => by decide⟩
  pendingConsolidations := fun _ => ⟨#[], fun _ => by decide⟩
  proposerLookahead := fun _ => Vector.replicate _ 0
  builders := fun _ => ⟨#[]⟩
  nextWithdrawalBuilderIndex := fun _ => 0
  executionPayloadAvailability := fun _ => ⟨Vector.replicate _ false⟩
  builderPendingPayments := fun _ => .ofVector (Vector.replicate _ .empty)
  builderPendingWithdrawals := fun _ => ⟨#[]⟩
  latestExecutionPayloadBid := fun _ =>
    { parentBlockHash := Bytes32.zero
      parentBlockRoot := Bytes32.zero
      blockHash := Bytes32.zero
      prevRandao := Bytes32.zero
      feeRecipient := Vector.replicate _ 0
      gasLimit := 0
      builderIndex := 0
      slot := 0
      value := 0
      executionPayment := 0
      blobKzgCommitments := ⟨#[], fun _ => by decide⟩
      executionRequestsRoot := Bytes32.zero
      inclusionListBits := fun _ => ⟨Vector.replicate _ false⟩ }
  payloadExpectedWithdrawals := fun _ => ⟨#[], fun _ => by decide⟩
  ptcWindow := fun _ => .ofVector (Vector.replicate _ (Vector.replicate _ 0))

theorem toSpecState_exampleGloas :
    toSpecState (exampleEthLibState .glamsterdam) = exampleGloasState := by rfl

theorem toSpecState_exampleFulu :
    toSpecState (exampleEthLibState .fusaka) = exampleFuluState := by rfl

/-- The example keys pass the `KeyValidate` of every oracle that matches EthLib. -/
theorem exampleGloasState_keys {checks : SignatureChecks} {oracle : Oracle}
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    ∀ v ∈ exampleGloasState.validators, oracle.bls_KeyValidate v.pubkey = true := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  exact (oracleMatches.keyValidate _).mpr (examplePubkey_valid k (List.mem_range.mp hk))

attribute [local instance] currentPresetMinimal currentFuluConfigMinimal
local instance : @CurrentPreset.Valid currentPresetMinimal := currentPresetMinimal_ok
local instance : @CurrentPreset.Bounds currentPresetMinimal := currentPresetMinimal_bounds
local instance : CurrentFuluConfig.Valid := ⟨fuluCompat_minimal⟩

/-- The Gloas assumptions about the oracle, the chain, the state and the room hold together for an
EthLib state, and the epoch succeeds there: the model and EthLib give the same state. -/
theorem gloas_ethlib_assumptions_hold_for_example (checks : SignatureChecks) :
    let state := exampleEthLibState .glamsterdam
    ∃ oracle, OracleMatches Preset.minimal checks oracle ∧
      Formalhouse.GloasChainConditions oracle (toSpecState state) ∧
      EpochInputInvariants (toSpecState state) ∧ AtLastSlotOfEpoch (toSpecState state) ∧
      RoomForDeposits (by decide) state ∧
      ∃ result, process_epoch_lighthouse oracle (toSpecState state) = .ok (toSpecState result) ∧
        processEpoch Config.minimal checks state = .ok result := by
  obtain ⟨oracle, ho⟩ := exists_oracle (preset := Preset.minimal) checks (by decide)
  have hcommittees := exampleGloasState_atCommitteeStepState oracle (exampleGloasState_keys ho)
  have hroom : RoomForDeposits (by decide) (exampleEthLibState .glamsterdam) := by
    unfold RoomForDeposits
    decide +kernel
  have hinvariants : EpochInputInvariants (toSpecState (exampleEthLibState .glamsterdam)) :=
    toSpecState_exampleGloas ▸ exampleGloasState_epochInputInvariants
  have hboundary : AtLastSlotOfEpoch (toSpecState (exampleEthLibState .glamsterdam)) :=
    toSpecState_exampleGloas ▸ exampleGloasState_atLastSlotOfEpoch
  have hchain : Formalhouse.GloasChainConditions oracle
      (toSpecState (exampleEthLibState .glamsterdam)) := by
    rw [toSpecState_exampleGloas]
    exact {
      committeeSteps := fun t h =>
        ⟨(hcommittees t h).2, (hcommittees t h).1.registryBelowLimit, (hcommittees t h).1.pubkeysValid⟩
      supplyAndTimeLimits := exampleGloasState_supplyAndTimeLimits
      slotFarFromOverflow := by decide +kernel
      historicalSummariesBelowLimit := exampleGloasState_atLastSlotOfEpoch.2.2 }
  exact ⟨oracle, ho, hchain, hinvariants, hboundary, hroom,
    Formalhouse.lighthouse_model_gloas_epoch_eq_ethlib_of_invariants
      Formalhouse.presetMatchesEthLib_minimal hinvariants hboundary hchain hroom ho⟩

/-- The Fulu assumptions about the oracle, the chain, the state and the room hold together for an
EthLib state, and the epoch succeeds there: the model and EthLib give the same state. -/
theorem fulu_ethlib_assumptions_hold_for_example (checks : SignatureChecks) :
    let state := exampleEthLibState .fusaka
    ∃ oracle, OracleMatches Preset.minimal checks oracle ∧
      Formalhouse.FuluChainConditions oracle (toSpecState state) ∧
      EpochInputInvariants (toSpecState state) ∧ AtLastSlotOfEpoch (toSpecState state) ∧
      RoomForDeposits (by decide) state ∧
      ∃ result,
        process_epoch_lighthouse_fulu oracle (toSpecState state) = .ok (toSpecState result) ∧
        processEpoch Config.minimal checks state = .ok result ∧
        result.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader := by
  obtain ⟨oracle, ho⟩ := exists_oracle (preset := Preset.minimal) checks (by decide)
  have hcommittees := exampleFuluState_atCommitteeStepState oracle (exampleGloasState_keys ho)
  have hroom : RoomForDeposits (by decide) (exampleEthLibState .fusaka) := by
    unfold RoomForDeposits
    decide +kernel
  have hinvariants : EpochInputInvariants (toSpecState (exampleEthLibState .fusaka)) :=
    toSpecState_exampleFulu ▸ exampleFuluState_epochInputInvariants
  have hboundary : AtLastSlotOfEpoch (toSpecState (exampleEthLibState .fusaka)) :=
    toSpecState_exampleFulu ▸ exampleFuluState_atLastSlotOfEpoch
  have hchain : Formalhouse.FuluChainConditions oracle
      (toSpecState (exampleEthLibState .fusaka)) := by
    rw [toSpecState_exampleFulu]
    exact {
      committeeSteps := fun t h =>
        ⟨(hcommittees t h).2, (hcommittees t h).1.registryBelowLimit, (hcommittees t h).1.pubkeysValid⟩
      supplyAndTimeLimits := exampleFuluState_supplyAndTimeLimits
      slotFarFromOverflow := by decide +kernel
      historicalSummariesBelowLimit := exampleFuluState_atLastSlotOfEpoch.2.2 }
  exact ⟨oracle, ho, hchain, hinvariants, hboundary, hroom,
    Formalhouse.lighthouse_model_fulu_epoch_eq_ethlib_of_invariants
      Formalhouse.presetMatchesEthLib_minimal toSpecFuluConfig_minimal hinvariants hboundary hchain
      hroom ho⟩

end EthLib

end EpochProofs.Example
