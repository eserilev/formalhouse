import EpochProofs.Headline

/-!
# The hypotheses of the headline theorems can hold together

A theorem with hypotheses that cannot hold together proves nothing. The headline theorems had
this bug: the committee conditions held at every state `s` with `CommFrame t s`. `CommFrame`
fixes only the slot, the list lengths and the RANDAO length, so it admits `t` with every
validator list emptied, where a sync committee candidate fails to exist. That hypothesis was false
for every input. It now holds at the one state that the epoch passes to the committee steps
(`Spec.AtCommitteeStepState`, `Spec.FuluAtCommitteeStepState`).

This file gives a witness: `witnessState`, a minimal-preset state at the last slot of epoch 0
with eight active compounding validators (`witnessValidator`) at `2048 ETH`; `witnessStateFulu`,
the same state without the Gloas fields; and `witnessEtheorem`, `witnessEtheoremFulu`, the
Etheorem states that map to them. Lean computes the epoch steps on it.

- `gloas_bundles_at_witness`: the chain, Etheorem divergence and oracle bundles of the Gloas
  headline theorems (`Assumptions.lean`) hold together at `witnessEtheorem`, with an oracle that
  agrees with Etheorem, given that SHA-256 returns 32 bytes.
- `fulu_bundles_at_witness`: the chain and oracle bundles of the Fulu headline theorems hold at
  `witnessEtheoremFulu`, given also the Etheorem bridge bundle (`FuluEtheoremBridgeConditions`).
- `gloas_spec_witness`, `fulu_spec_witness`: at the same state, the start-state facts
  (`FuluStartOk`), unique pubkeys and the reachable-state facts that the run gives
  (`ReachableInvariants`) hold too, the epoch reaches its committee steps (so the committee
  conditions are not vacuous), and the spec `process_epoch` returns `ok`.
- `agrees_pyspec_hyps_at_witness`, `agrees_pyspec_hyps_at_witness_fulu`: the state hypotheses
  that the `_agrees_pyspec` theorems use hold at `witnessState`, `witnessStateFulu`, and
  `lighthouse_model_gloas_epoch_agrees_pyspec_at_witness` applies the Gloas one there.
- `selFin_full`: the selection facts in `CommitteeStepPreconds` hold for every hash when every
  candidate has the maximum effective balance.

Not covered: the runs (`GloasEpochRun`, `FuluEpochRun`, whose supply bounds range over every
run), the Fulu Etheorem bridge conditions (`FuluEtheoremBridgeConditions`), the hash backend
(`sha`), the cache facts and the Rust glue.
-/

namespace EpochProofs.Spec

/-- Every pass of the balance weighted selection accepts when every candidate has the maximum
effective balance, whatever the hash values. -/
theorem bwsAccept_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (i : Nat) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    bwsAccept p o seed ebs shuffle i = true := by
  have hk : bwsNext p o seed ebs.length shuffle i < ebs.length := by
    unfold bwsNext; split
    · exact csiFold_lt o seed.toList ebs.length p.SHUFFLE_ROUND_COUNT _ hpos (Nat.mod_lt _ hpos)
    · exact Nat.mod_lt _ hpos
  unfold bwsAccept
  rw [List.getD_eq_getElem _ _ hk, hall _ (List.getElem_mem hk)]
  have := leNat_take2_lt ((bwsBytes o seed i).toList.drop (i % 16 * 2))
  simp only [decide_eq_true_eq, ge_iff_le]
  exact Nat.mul_le_mul_left _ (by omega)

theorem bwsCount_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) (m : Nat) :
    bwsCount p o seed ebs shuffle m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bwsCount_succ, ih, bwsAccept_full p o seed ebs shuffle m hpos hall]; rfl

/-- `SelFin` holds for every seed when the candidates are validators with the maximum effective
balance. -/
theorem selFin_full (p : Preset) (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffle : Bool) (hne : indices ≠ [])
    (hin : ∀ j ∈ indices, j < s.validators.length)
    (heb : ∀ v ∈ s.validators, v.effective_balance = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hsize : size < 2 ^ 64) : SelFin p o s indices seed size shuffle := by
  refine ⟨size, hsize, ?_⟩
  rw [bwsCount_full]
  · simpa [ebsOf, List.length_pos_iff] using hne
  · intro x hx
    simp only [ebsOf, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.getElem?_eq_getElem (hin j hj)]
    exact heb _ (List.getElem_mem _)

end EpochProofs.Spec

namespace EpochProofs.Witness

open EpochProofs.Spec


/-- `witnessEtheoremValidator` as a reference validator. -/
def witnessValidator (k : Nat) : Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawal_credentials := Bytes32.zero.set 0 2
    effective_balance := 2048000000000, slashed := false
    activation_eligibility_epoch := 0, activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- The witness as a reference state. -/
def witnessState : BeaconState :=
  { slot := 7
    block_roots := List.replicate 64 Bytes32.zero
    state_roots := List.replicate 64 Bytes32.zero
    validators := (List.range 8).map witnessValidator
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

/-- `witnessState` without the Gloas fields: the witness as a Fulu reference state. -/
def witnessStateFulu : BeaconState :=
  { witnessState with
    execution_payload_availability := [], builder_pending_payments := [], ptc_window := [] }

section Minimal

attribute [local instance] minimalCfg fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- The steps before the committee steps return `witnessState` itself: at epoch 0 the justification,
inactivity and rewards steps skip, and nothing else changes on this state. -/
theorem witnessState_epochToCommittees
    (o : Oracle) : epochToCommittees P o witnessState = .ok witnessState := by rfl

theorem witnessStateFulu_epochToCommitteesFulu
    (o : Oracle) : epochToCommitteesFulu P FC o witnessStateFulu = .ok witnessStateFulu := by
  rfl

theorem witnessState_eb : ∀ v ∈ witnessState.validators,
    v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide +kernel

theorem witnessState_active_lt (e j : Nat) (h : j ∈ get_active_validator_indices witnessState e) :
    j < witnessState.validators.length := active_lt witnessState e j h

theorem witnessState_committeeStepFacts (o : Oracle) (hk : ∀ v ∈ witnessState.validators,
    o.bls_KeyValidate v.pubkey = true) :
    CommitteeStepFacts o witnessState :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, hk⟩

theorem witnessState_committeeStepPreconds (o : Oracle) : CommitteeStepPreconds o witnessState where
  syncActive := by decide +kernel
  proposers := by decide +kernel
  ptc32 := by decide +kernel
  selSync seed := selFin_full P o witnessState _ seed _ true (by decide +kernel)
    (witnessState_active_lt _) witnessState_eb (by decide +kernel)
  selProp seed := selFin_full P o witnessState _ seed _ true (by decide +kernel)
    (fun j hj => witnessState_active_lt _ j (List.mem_of_mem_filter hj)) witnessState_eb
      (by decide +kernel)
  selPtc slot hslot l hl seed := by
    have he : slot / P.SLOTS_PER_EPOCH = 2 := hslot
    have h32 : P.SLOTS_PER_EPOCH ≤
        (get_active_validator_indices witnessState (slot / P.SLOTS_PER_EPOCH)).length := by
      rw [he]; decide +kernel
    obtain ⟨l', hl1, hl2, hl3⟩ := ptcIndices_total o witnessState slot
      (by rw [he]; decide +kernel) (by decide +kernel)
      ((active_len_le _ _).trans (by decide +kernel))
    have hll : l' = l := by rw [hl1] at hl; exact Except.ok.inj hl
    rw [← hll]
    have hne : l' ≠ [] := by
      intro h; rw [h] at hl2
      have := ptc_len_pos _ (slot % P.SLOTS_PER_EPOCH) _ P_slots_pos h32
      simp at hl2; omega
    exact selFin_full P o witnessState l' seed _ false hne (fun j hj => witnessState_active_lt _ j
      (hl3 j hj)) witnessState_eb
      (by decide +kernel)

/-- The Gloas committee hypothesis holds at `witnessState`, for every oracle that accepts the eight
keys. -/
theorem witnessState_atCommitteeStepState (o : Oracle) (hk : ∀ v ∈ witnessState.validators,
    o.bls_KeyValidate v.pubkey = true) :
    AtCommitteeStepState o witnessState := by
  intro s hs
  rw [witnessState_epochToCommittees] at hs
  cases hs
  exact ⟨witnessState_committeeStepFacts o hk, witnessState_committeeStepPreconds o⟩

theorem witnessState_rowsOk : RowsOk witnessState := by unfold RowsOk; decide +kernel

theorem witnessState_pubkeys : PubkeysUnique witnessState := by unfold PubkeysUnique; decide +kernel

theorem witnessState_vectors : witnessState.VectorLengths P :=
    by unfold BeaconState.VectorLengths; decide +kernel

theorem witnessState_fuluVectors : witnessState.FuluVectorLengths P := by
  unfold BeaconState.FuluVectorLengths; decide +kernel

theorem witnessState_atEpochBoundary : AtEpochBoundary witnessState := by unfold AtEpochBoundary; decide +kernel

theorem witnessState_physicalLimits : PhysicalLimits witnessState where
  scores := by decide +kernel
  supply := by decide +kernel
  funds := by decide +kernel
  earliest := by decide +kernel
  exit_balance := by decide +kernel
  count := by decide +kernel
  participation tab htab f hf x hx := by
    rw [show get_total_active_balance P witnessState = .ok 16384000000000 from rfl] at htab
    cases htab
    have h0 : rewardsFlagIncrements P witnessState
      (witnessState.slot / P.SLOTS_PER_EPOCH - 1) 0 = .ok 1 := rfl
    have h1 : rewardsFlagIncrements P witnessState
      (witnessState.slot / P.SLOTS_PER_EPOCH - 1) 1 = .ok 1 := rfl
    have h2 : rewardsFlagIncrements P witnessState
      (witnessState.slot / P.SLOTS_PER_EPOCH - 1) 2 = .ok 1 := rfl
    interval_cases f
    · rw [h0] at hx; cases hx; decide
    · rw [h1] at hx; cases hx; decide
    · rw [h2] at hx; cases hx; decide

theorem witnessState_startOk : FuluStartOk witnessState where
  ffg := by unfold FfgInvariant CheckpointOrder epochOf; decide +kernel
  rows := witnessState_rowsOk
  exitDelay := by unfold ExitDelay ExitDelayV; decide +kernel
  exitEpochs := by unfold ExitEpochsU64; decide +kernel
  afterEB := by unfold AfterEB; decide +kernel
  pubkeys := witnessState_pubkeys
  consolidations := by unfold ConsolidationsInRange; decide +kernel
  withdrawable := by unfold WithdrawableU64; decide +kernel

theorem witnessState_reachableInvariants : ReachableInvariants witnessState := by
  unfold ReachableInvariants EpochInputOk'' EpochInputOk' EpochInputOk BoundaryOk EpochBalanceBounds
  refine ⟨⟨⟨⟨witnessState_startOk.ffg, witnessState_rowsOk, ?_⟩, by decide +kernel, ?_,
    witnessState_startOk.exitEpochs,
    by decide +kernel, by decide +kernel, by decide +kernel⟩, witnessState_pubkeys,
    witnessState_startOk.consolidations⟩, witnessState_startOk.withdrawable, ?_⟩
  · unfold EntryEB; decide +kernel
  · unfold EBOk EBOkV; decide +kernel
  · unfold WithdrawableValid; decide +kernel

/-- The Gloas witness. At `witnessState`, for every oracle that accepts the eight keys: the
spec-state facts of the Gloas chain bundle, the start-state facts and the reachable-state facts
hold together, the epoch reaches its committee steps, and the spec `process_epoch` returns `ok`. -/
theorem gloas_spec_witness (o : Oracle)
    (hk : ∀ v ∈ witnessState.validators, o.bls_KeyValidate v.pubkey = true) :
    FuluStartOk witnessState ∧ ReachableInvariants witnessState ∧
      PubkeysUnique witnessState ∧ witnessState.VectorLengths P ∧
      AtEpochBoundary witnessState ∧ witnessState.slot + 8192 < 2 ^ 64 ∧ PhysicalLimits witnessState ∧
        AtCommitteeStepState o witnessState ∧
      epochToCommittees P o witnessState = .ok witnessState ∧ ∃ s',
        process_epoch P o witnessState = .ok s' := by
  have hc := witnessState_atCommitteeStepState o hk
  have hokc := committeesOk_of o witnessState (by decide +kernel) hc witnessState
    (witnessState_epochToCommittees o)
    ⟨rfl, witnessState_rowsOk, by decide +kernel⟩
  obtain ⟨s', hs', -⟩ := hokc
  refine ⟨witnessState_startOk, witnessState_reachableInvariants, witnessState_pubkeys,
    witnessState_vectors, witnessState_atEpochBoundary,
    by decide +kernel, witnessState_physicalLimits, hc, witnessState_epochToCommittees o, s', ?_⟩
  rw [process_epoch_committees, witnessState_epochToCommittees, tot_bind_ok]
  exact hs'

theorem witnessStateFulu_eb : ∀ v ∈ witnessStateFulu.validators,
    v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA :=
  witnessState_eb

theorem witnessStateFulu_atCommitteeStepState (o : Oracle)
    (hk : ∀ v ∈ witnessStateFulu.validators,
      o.bls_KeyValidate v.pubkey = true) : FuluAtCommitteeStepState o witnessStateFulu := by
  intro s hs
  rw [witnessStateFulu_epochToCommitteesFulu] at hs
  cases hs
  exact ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, hk⟩,
    ⟨by decide +kernel, by decide +kernel,
      fun seed => selFin_full P o witnessStateFulu _ seed _ true (by decide +kernel)
        (fun j hj => active_lt witnessStateFulu _ j hj) witnessStateFulu_eb (by decide +kernel),
      fun seed => selFin_full P o witnessStateFulu _ seed _ true (by decide +kernel)
        (fun j hj => active_lt witnessStateFulu _ j hj) witnessStateFulu_eb (by decide +kernel)⟩⟩

theorem witnessStateFulu_rowsOk : RowsOk witnessStateFulu := witnessState_rowsOk

theorem witnessStateFulu_physicalLimits : PhysicalLimits witnessStateFulu where
  scores := by decide +kernel
  supply := by decide +kernel
  funds := by decide +kernel
  earliest := by decide +kernel
  exit_balance := by decide +kernel
  count := by decide +kernel
  participation tab htab f hf x hx := witnessState_physicalLimits.participation tab htab f hf x hx

theorem witnessStateFulu_startOk : FuluStartOk witnessStateFulu where
  ffg := witnessState_startOk.ffg
  rows := witnessState_rowsOk
  exitDelay := witnessState_startOk.exitDelay
  exitEpochs := witnessState_startOk.exitEpochs
  afterEB := witnessState_startOk.afterEB
  pubkeys := witnessState_pubkeys
  consolidations := witnessState_startOk.consolidations
  withdrawable := witnessState_startOk.withdrawable

theorem witnessStateFulu_reachableInvariants : ReachableInvariants witnessStateFulu :=
    witnessState_reachableInvariants

theorem witnessStateFulu_fuluVectors : witnessStateFulu.FuluVectorLengths P :=
    witnessState_fuluVectors

theorem witnessStateFulu_atEpochBoundary : AtEpochBoundary witnessStateFulu := witnessState_atEpochBoundary

/-- The Fulu witness: at `witnessStateFulu`, for every oracle that accepts the eight keys, the
spec-state facts of the Fulu chain bundle, the start-state facts and the reachable-state facts hold
together, the epoch reaches its committee steps, and the Fulu spec `process_epoch` returns `ok`. -/
theorem fulu_spec_witness (o : Oracle)
    (hk : ∀ v ∈ witnessStateFulu.validators, o.bls_KeyValidate v.pubkey = true) :
    FuluStartOk witnessStateFulu ∧ ReachableInvariants witnessStateFulu ∧
      witnessStateFulu.FuluVectorLengths P ∧ AtEpochBoundary witnessStateFulu ∧
      witnessStateFulu.slot + 8192 < 2 ^ 64 ∧ PhysicalLimits witnessStateFulu ∧
        FuluAtCommitteeStepState o witnessStateFulu ∧
      epochToCommitteesFulu P FC o witnessStateFulu = .ok witnessStateFulu ∧
      ∃ s', process_epoch_fulu P FC o witnessStateFulu = .ok s' := by
  have hc := witnessStateFulu_atCommitteeStepState o hk
  obtain ⟨s', hs', -⟩ := committeesOkFulu_of o witnessStateFulu
    (by decide +kernel) hc witnessStateFulu
    (witnessStateFulu_epochToCommitteesFulu o) ⟨rfl, witnessStateFulu_rowsOk, by decide +kernel⟩
  refine ⟨witnessStateFulu_startOk, witnessStateFulu_reachableInvariants,
    witnessStateFulu_fuluVectors, witnessState_atEpochBoundary, by decide +kernel,
    witnessStateFulu_physicalLimits, hc, witnessStateFulu_epochToCommitteesFulu o, s', ?_⟩
  rw [process_epoch_fulu_committees, witnessStateFulu_epochToCommitteesFulu, tot_bind_ok]
  exact hs'


/-- The state hypotheses of the Gloas agreement theorem hold at `witnessState`. -/
theorem agrees_pyspec_hyps_at_witness :
    ReachableInvariants witnessState ∧ AtEpochBoundary witnessState ∧
      HistoricalSummariesBelowLimit witnessState :=
  ⟨witnessState_reachableInvariants, witnessState_atEpochBoundary,
    witnessState_atEpochBoundary.2.2⟩

/-- The state hypotheses of the Fulu agreement theorem hold at `witnessStateFulu`. -/
theorem agrees_pyspec_hyps_at_witness_fulu :
    ReachableInvariants witnessStateFulu ∧ AtEpochBoundary witnessStateFulu ∧
      HistoricalSummariesBelowLimit witnessStateFulu :=
  ⟨witnessStateFulu_reachableInvariants, witnessStateFulu_atEpochBoundary,
    witnessStateFulu_atEpochBoundary.2.2⟩

/-- At `witnessState`, the Lean model of Lighthouse's Gloas epoch and the transcription agree,
for every oracle. -/
theorem lighthouse_model_gloas_epoch_agrees_pyspec_at_witness (o : Oracle) :
    SameResultOrBothFail (process_epoch_lighthouse o witnessState)
      (process_epoch P o witnessState) :=
  Formalhouse.lighthouse_model_gloas_epoch_agrees_pyspec_of_invariants o
    witnessState_reachableInvariants witnessState_atEpochBoundary

end Minimal

/-! ## The assumption structures

The witnesses above are reference states. Here they are the `toSpecState` of Etheorem states, so
they give the bundles of `Assumptions.lean` directly. -/

/-- An `Oracle` that accepts every key. Its other fields are constants. -/
def keyOracle : Oracle where
  hash _ := default
  hash_tree_root_BeaconState _ := default
  hash_tree_root_BeaconBlockHeader _ := default
  hash_tree_root_BeaconBlock _ := default
  hash_tree_root_BeaconBlockBody _ := default
  hash_tree_root_BlockRoots _ := default
  hash_tree_root_StateRoots _ := default
  hash_tree_root_Epoch _ := default
  hash_tree_root_SigningData _ := default
  hash_tree_root_ForkData _ := default
  hash_tree_root_AttestationData _ := default
  hash_tree_root_VoluntaryExit _ := default
  hash_tree_root_DepositMessage _ := default
  hash_tree_root_BLSToExecutionChange _ := default
  hash_tree_root_ExecutionPayloadBid _ := default
  hash_tree_root_ExecutionPayloadEnvelope _ := default
  hash_tree_root_PayloadAttestationData _ := default
  hash_tree_root_ExecutionRequests _ := default
  hash_tree_root_Withdrawals _ := default
  bls_Verify _ _ _ := false
  bls_FastAggregateVerify _ _ _ := false
  bls_AggregateVerify _ _ _ := false
  bls_AggregatePKs _ := default
  bls_KeyValidate _ := true
  bls_SubtractPK _ _ := default

section GloasEState

attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩


/-- A validator of the witness: active from epoch 0, never exits, compounding credentials, the
maximum effective balance. -/
def witnessEtheoremValidator (k : Nat) : EthCLSpecs.Gloas.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The witness as an Etheorem state on the minimal preset: the last slot of epoch 0, eight
validators, every other field at its default. -/
def witnessEtheorem : EthCLSpecs.Gloas.BeaconState :=
  { (default : EthCLSpecs.Gloas.BeaconState) with
    slot := 7
    validators := ⟨#[witnessEtheoremValidator 0, witnessEtheoremValidator 1,
      witnessEtheoremValidator 2,
      witnessEtheoremValidator 3, witnessEtheoremValidator 4, witnessEtheoremValidator 5,
      witnessEtheoremValidator 6, witnessEtheoremValidator 7], by decide⟩
    balances := ⟨Array.replicate 8 2048000000000, by decide⟩
    previousEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    currentEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    inactivityScores := ⟨Array.replicate 8 0, by decide⟩ }


theorem witnessEtheorem_abs : Etheorem.toSpecState witnessEtheorem = witnessState := by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The oracle hypotheses hold for an oracle that accepts every key (`etheoremOracle_agrees`). -/
theorem oracle_witness : ∃ o, Etheorem.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.etheoremOracle keyOracle, Etheorem.etheoremOracle_agrees _, fun _ => rfl⟩

/-- The chain, Etheorem divergence and oracle bundles of the Gloas headline theorems hold
together at `witnessEtheorem` on the minimal preset, given the fact about the hash backend that
the oracle bundle takes as it is: SHA-256 returns 32 bytes. -/
theorem gloas_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Formalhouse.GloasChainAssumptions o (Etheorem.toSpecState witnessEtheorem) ∧
      Etheorem.GloasEtheoremDivergenceAssumptions witnessEtheorem ∧
      Etheorem.GloasOracleMatchesEtheorem o := by
  obtain ⟨o, ho, hk⟩ := oracle_witness
  have hc := witnessState_atCommitteeStepState o (fun v _ => hk _)
  rw [witnessEtheorem_abs]
  refine ⟨o, {
    syncCandidate := fun t h => (hc t h).2.syncActive
    proposerCandidate := fun t h => (hc t h).2.proposers
    enoughActiveForPtc := fun t h => (hc t h).2.ptc32
    syncSelectionEnds := fun t h => (hc t h).2.selSync
    proposerSelectionEnds := fun t h => (hc t h).2.selProp
    ptcSelectionEnds := fun t h => (hc t h).2.selPtc
    physicalLimits := witnessState_physicalLimits
    slotFarFromOverflow := by decide +kernel
    historicalSummariesBelowLimit := witnessState_atEpochBoundary.2.2
    vectorLengths := witnessState_vectors
    committeeStepStateFacts := fun t h => (hc t h).1 },
    ⟨by rw [witnessEtheorem_abs]; decide +kernel, by decide +kernel⟩, ⟨ho, hsha⟩⟩

end GloasEState

section FuluEState

attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- `witnessEtheoremValidator` as a Fulu validator. -/
def witnessEtheoremValidatorFulu (k : Nat) : EthCLSpecs.Fulu.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The Fulu witness as an Etheorem Fulu state. -/
def witnessEtheoremFulu : EthCLSpecs.Fulu.BeaconState :=
  { (default : EthCLSpecs.Fulu.BeaconState) with
    slot := 7
    validators := ⟨#[witnessEtheoremValidatorFulu 0, witnessEtheoremValidatorFulu 1,
      witnessEtheoremValidatorFulu 2,
      witnessEtheoremValidatorFulu 3, witnessEtheoremValidatorFulu 4,
        witnessEtheoremValidatorFulu 5,
      witnessEtheoremValidatorFulu 6, witnessEtheoremValidatorFulu 7], by decide⟩
    balances := ⟨Array.replicate 8 2048000000000, by decide⟩
    previousEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    currentEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    inactivityScores := ⟨Array.replicate 8 0, by decide⟩ }

theorem witnessEtheoremFulu_abs : Etheorem.Fulu.toSpecState witnessEtheoremFulu = witnessStateFulu :=
    by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

theorem fulu_oracle_witness :
    ∃ o, Etheorem.Fulu.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.Fulu.etheoremOracle keyOracle, Etheorem.Fulu.etheoremOracle_agrees _, fun _ => rfl⟩

/-- The chain and oracle bundles of the Fulu headline theorems hold at `witnessEtheoremFulu` on
the minimal preset, with the Etheorem bridge bundle, given that bundle and SHA-256 returning 32
bytes. The bridge conditions are facts about Etheorem's intermediate states, taken as they
are. -/
theorem fulu_bundles_at_witness
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Etheorem.Fulu.FuluEtheoremBridgeConditions P o witnessEtheoremFulu →
      Formalhouse.FuluChainAssumptions o (Etheorem.Fulu.toSpecState witnessEtheoremFulu) ∧
        Etheorem.Fulu.FuluEtheoremBridgeConditions P o witnessEtheoremFulu ∧
        Etheorem.Fulu.FuluOracleMatchesEtheorem o := by
  obtain ⟨o, ho, hk⟩ := fulu_oracle_witness
  refine ⟨o, fun hconds => ⟨?_, hconds, ⟨ho, hsha⟩⟩⟩
  rw [witnessEtheoremFulu_abs]
  have hc := witnessStateFulu_atCommitteeStepState o (fun v _ => hk _)
  exact {
    syncCandidate := fun t h => (hc t h).2.syncActive
    proposerCandidate := fun t h => (hc t h).2.proposers
    syncSelectionEnds := fun t h => (hc t h).2.selSync
    proposerSelectionEnds := fun t h => (hc t h).2.selProp
    physicalLimits := witnessStateFulu_physicalLimits
    slotFarFromOverflow := by decide +kernel
    historicalSummariesBelowLimit := witnessStateFulu_atEpochBoundary.2.2
    vectorLengths := witnessStateFulu_fuluVectors
    committeeStepStateFacts := fun t h => (hc t h).1 }

end FuluEState

end EpochProofs.Witness
