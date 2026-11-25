import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.Transition.BlockCredits
import EthLib.Consensus.Proofs.Transition.RetiredValidator
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EpochProofs.EthLib.ChainFacts

/-!
# How far a balance falls in one epoch of an EthLib run

In one block, a balance falls by a withdrawal, a sync committee penalty and a slashing penalty. A
validator that is not yet withdrawable keeps `MIN_ACTIVATION_BALANCE` after a withdrawal.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64 _root_.EthLib.Consensus
open _root_.EthLib.Consensus.BlockLedger

open private partials_floor builders_unflagged_zero
  from EthLib.Consensus.Proofs.Transition.EffectiveFall
open private credited_processOperations from EthLib.Consensus.Proofs.Transition.BlockCredits

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The withdrawals -/

/-- The withdrawals of a block do not lower a balance below `MIN_ACTIVATION_BALANCE`, if the
validator is not yet withdrawable. -/
theorem withdrawals_balance_floor {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ f) (within : s.RegistryWithinLimit)
    (computed : processWithdrawals s capella payload = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    min (actualBalanceAt ⟨f, s⟩ v.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      actualBalanceAt ⟨f, t⟩ v.toNat := by
  by_cases skipped : ∃ gloas : .glamsterdam ≤ f, isParentBlockFull s gloas = false
  · obtain ⟨gloas, empty⟩ := skipped
    rw [processWithdrawals_of_parentEmpty payload gloas empty, Except.ok.injEq] at computed
    subst computed
    exact Nat.min_le_left _ _
  have full : ∀ gloas : .glamsterdam ≤ f, isParentBlockFull s gloas = true := fun gloas => by
    cases parent : isParentBlockFull s gloas
    · exact absurd ⟨gloas, parent⟩ skipped
    · rfl
  obtain ⟨expected, expectedOk⟩ : ∃ expected, getExpectedWithdrawals s capella = .ok expected := by
    by_cases gloas : .glamsterdam ≤ f
    · obtain ⟨expected, expectedOk, -, -⟩ := processWithdrawals_recorded gloas (full gloas) computed
      exact ⟨expected, expectedOk⟩
    · obtain ⟨expected, expectedOk, -, -⟩ :=
        processWithdrawals_expected (Nat.lt_of_not_le gloas) computed
      exact ⟨expected, expectedOk⟩
  obtain ⟨builders, partials, buildersSweep, sweep, index1, index2, index3, index4, count1,
    count2, count3, count4, split, -, buildersOk, buildersEmpty, partialsOk, -, buildersSweepOk,
    buildersSweepEmpty, sweepOk⟩ := getExpectedWithdrawals_parts expectedOk
  -- From Gloas an index that names a builder keeps its balance.
  by_cases flagged : .glamsterdam ≤ f ∧ isBuilderIndex v = true
  · obtain ⟨gloas, flag⟩ := flagged
    obtain ⟨found', foundOk, appliedOk, -⟩ :=
      processWithdrawals_recorded gloas (full gloas) computed
    obtain ⟨applied, applyOk, balances, -⟩ := applyExpectedWithdrawals_balances appliedOk
    unfold applyWithdrawals at applyOk
    rw [← Array.foldlM_toList] at applyOk
    have same : actualBalanceAt ⟨f, t⟩ v.toNat = actualBalanceAt ⟨f, s⟩ v.toNat := by
      -- A withdrawal for that index debits the builder, and any other names another index.
      simp only [actualBalanceAt, balances, applyWithdrawals_unnamed (index := v.toNat) _ _ _
        applyOk fun _ _ named => ⟨gloas, UInt64.toNat_inj.mp named ▸ flag⟩]
    rw [same]
    exact Nat.min_le_left _ _
  have named : f < .glamsterdam ∨ isBuilderIndex v = false := by
    by_cases gloas : .glamsterdam ≤ f
    · exact .inr (by simpa [gloas] using flagged)
    · exact .inl (Nat.lt_of_not_le gloas)
  have zeros : withdrawnFrom builders v = 0 ∧ withdrawnFrom buildersSweep v = 0 := by
    by_cases gloas : .glamsterdam ≤ f
    · exact builders_unflagged_zero (buildersOk gloas) (buildersSweepOk gloas)
        (by simpa [gloas] using flagged)
    · obtain ⟨rfl, -⟩ := buildersEmpty (Nat.lt_of_not_le gloas)
      obtain ⟨rfl, -⟩ := buildersSweepEmpty (Nat.lt_of_not_le gloas)
      simp [withdrawnFrom]
  cases read : s.balances.data[v.toNat]? with
  | none => simp [actualBalanceAt, read]
  | some balance =>
    obtain ⟨bounded, lowered⟩ :=
      processWithdrawals_balance_of_notBuilder computed expectedOk full named read
    have after : actualBalanceAt ⟨f, t⟩ v.toNat =
        balance.toNat - withdrawnFrom expected.withdrawals v := by
      simp only [actualBalanceAt]
      cases h : t.balances.data[v.toNat]? <;> rw [h] at lowered <;> simp_all
    have before : actualBalanceAt ⟨f, s⟩ v.toNat = balance.toNat := by
      simp [actualBalanceAt, read]
    rw [after, before]
    rw [split] at bounded ⊢
    simp only [withdrawnFrom_append, zeros.1, zeros.2, Nat.zero_add, Nat.add_zero] at bounded ⊢
    by_cases swept : ∃ k, ∃ inside : k < sweep.size, sweep[k].validatorIndex = v
    · -- The sweep pays the validator its excess, down to its largest effective balance.
      --
      -- Here, that largest effective balance is its effective balance.
      obtain ⟨k, inside, named⟩ := swept
      obtain ⟨pays, distinct⟩ := getValidatorsSweepWithdrawals_pays within sweepOk
      obtain ⟨validator, left, validatorOk, leftOk, kind⟩ := pays k inside
      have total := withdrawnFrom_split distinct inside
      rw [named] at validatorOk leftOk total
      rw [getValidator_eq_ok_iff, found, Option.some.injEq] at validatorOk
      subst validator
      obtain ⟨balance', read', sum⟩ := getBalanceAfterWithdrawals_ok leftOk
      rw [read, Option.some.injEq] at read'
      subst balance'
      simp only [withdrawnFrom_append, zeros.1, zeros.2, Nat.zero_add, Nat.add_zero] at sum
      rcases kind with ⟨full, -⟩ | ⟨-, excess, amount⟩
      · simp only [isFullyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq] at full
        exact absurd full.1.2 (UInt64.not_le.mpr later)
      · simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at excess
        rw [amount, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt excess.2)] at total
        have above := UInt64.lt_iff_toNat_lt.mp excess.2
        have capFloor : preset.MIN_ACTIVATION_BALANCE.toNat ≤ val.effectiveBalance.toNat := by
          rw [excess.1.2]
          simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance]
          split
          · exact UInt64.le_iff_toNat_le.mp compounding
          · exact Nat.le_refl _
        rw [← excess.1.2] at above total
        omega
    · -- Otherwise only the queued partial withdrawals pay it.
      have zero : withdrawnFrom sweep v = 0 := withdrawnFrom_eq_zero fun w member same => by
        obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
        exact swept ⟨k, inside, same⟩
      rw [zero] at bounded ⊢
      by_cases positive : 0 < withdrawnFrom partials v
      · obtain ⟨floor, effective⟩ :=
          partials_floor (partialsOk electra) zeros.1 found read positive
        have := UInt64.le_iff_toNat_le.mp effective
        omega
      · omega


/-- The execution payload of a block does not lower a balance below `MIN_ACTIVATION_BALANCE`, if the
validator is not yet withdrawable. -/
theorem execution_balance_floor {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {body : BeaconBlockBody preset f}
    {bellatrix : .bellatrix ≤ f}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ f) (within : s.RegistryWithinLimit)
    (computed : processBlockExecution config checks engine s body bellatrix = .ok t)
    {v : ValidatorIndex} {val : Validator} (found : s.validators.data[v.toNat]? = some val)
    (later : getCurrentEpoch s < val.withdrawableEpoch) :
    min (actualBalanceAt ⟨f, s⟩ v.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      actualBalanceAt ⟨f, t⟩ v.toNat := by
  have capella : .shapella ≤ f := Nat.le_trans (by decide) electra
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, bidOk⟩ := computed
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bidOk
    simpa [actualBalanceAt] using withdrawals_balance_floor compounding electra within withdrawnOk found later
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, withdrawnOk, paidOk⟩ := computed
    obtain ⟨-, header, -, rfl⟩ := processExecutionPayload_ok paidOk
    simpa [actualBalanceAt] using withdrawals_balance_floor compounding electra within withdrawnOk found later

/-! ## One block -/

/-- A step keeps the slot, and a validator that is not yet withdrawable stays so. -/
def KeepsNotWithdrawable {fork : Fork} (before after : BeaconState preset fork) : Prop :=
  after.slot = before.slot ∧ ∀ (i : Nat) (old new : Validator),
    before.validators.data[i]? = some old → after.validators.data[i]? = some new →
    getCurrentEpoch before < old.withdrawableEpoch → getCurrentEpoch before < new.withdrawableEpoch

theorem KeepsNotWithdrawable.of_validators {fork : Fork} {before after : BeaconState preset fork}
    (slot : after.slot = before.slot) (validators : after.validators.data = before.validators.data) :
    KeepsNotWithdrawable before after :=
  ⟨slot, fun i old new found read early => by
    rw [validators, found] at read
    exact Option.some.inj read ▸ early⟩

theorem KeepsNotWithdrawable.of_setValidator {fork : Fork} {before middle after : BeaconState preset fork}
    (slot : middle.slot = before.slot) (validators : middle.validators.data = before.validators.data)
    {index : ValidatorIndex} {old new : Validator}
    (found : before.validators.data[index.toNat]? = some old)
    (set : middle.setValidator index new = .ok after)
    (kept : getCurrentEpoch before < old.withdrawableEpoch →
      getCurrentEpoch before < new.withdrawableEpoch) : KeepsNotWithdrawable before after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨slot, fun i a b foundA read early => ?_⟩
  simp only [BeaconState.putValidator, _root_.EthLib.Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i same
    subst same
    rw [found] at foundA
    cases Option.some.inj foundA
    cases Option.some.inj read
    exact kept early
  · rw [validators, foundA] at read
    exact Option.some.inj read ▸ early

theorem KeepsNotWithdrawable.refl {fork : Fork} (state : BeaconState preset fork) :
    KeepsNotWithdrawable state state := .of_validators rfl rfl

theorem KeepsNotWithdrawable.exit {fork : Fork} {before after : BeaconState preset fork}
    {index : ValidatorIndex} (ok : initiateValidatorExit config before index = .ok after) :
    KeepsNotWithdrawable before after := by
  obtain ⟨old, read, unchanged | ⟨_, queued, _, _, queue, delayed, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact .refl _
  · refine .of_setValidator (frame_exitQueue queue).slot
      (congrArg (·.data) (exitQueue_validators queue).1) (getValidator_eq_ok_iff.mp read) set
      fun _ => UInt64.lt_iff_toNat_lt.mpr ?_
    have later := exitQueue_lt queue
    have sum := (addChecked_ok_iff.mp delayed).2
    dsimp only
    omega

theorem KeepsNotWithdrawable.withdrawalRequest {fork : Fork} {before after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config before electra request = .ok after) :
    KeepsNotWithdrawable before after := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, withdrawn⟩
  · exact .refl _
  · exact .exit exited
  · exact .of_validators (frame_requestPartialWithdrawal withdrawn).slot
      (congrArg (·.data) (requestPartialWithdrawal_kept withdrawn).1)

theorem KeepsNotWithdrawable.consolidationRequest {fork : Fork}
    {before after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config before electra request = .ok after) :
    KeepsNotWithdrawable before after := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ |
    ⟨_, _, _, _, accepted, queued⟩
  · exact .refl _
  · simp only [switchToCompoundingValidator, bind_ok_iff] at switched
    obtain ⟨_, found, middle, set, queued⟩ := switched
    have first := KeepsNotWithdrawable.of_setValidator (before := before) rfl rfl
      (getValidator_eq_ok_iff.mp found) set fun early => early
    simp only [queueExcessActiveBalance, bind_ok_iff] at queued
    obtain ⟨_, _, queued⟩ := queued
    split at queued
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
      obtain ⟨_, _, _, _, _, setBalance, rfl⟩ := queued
      obtain ⟨_, rfl⟩ := setBalance_ok setBalance
      exact first
    · cases queued
      exact first
  · obtain ⟨exitEpoch, withdrawable, rest, written, _, churn, delayed, set, _, rfl⟩ :=
      queueConsolidation_steps queued
    refine KeepsNotWithdrawable.of_setValidator (before := before) (middle := { before with
        consolidationBalanceToConsume := fun _ => rest
        earliestConsolidationEpoch := fun _ => exitEpoch }) (after := written) rfl rfl accepted.sourceAt set
      fun _ => UInt64.lt_iff_toNat_lt.mpr ?_
    cases first : computeActivationExitEpoch preset (getCurrentEpoch before) with
    | error =>
      simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError,
        bind, Except.bind] at churn
    | ok firstEpoch =>
      have later := UInt64.le_iff_toNat_le.mp
        (computeConsolidationEpochAndUpdateChurn_first first churn).1
      have value := (computeActivationExitEpoch_ok_iff.mp first).2
      have sum := (addChecked_ok_iff.mp delayed).2
      dsimp only at *
      omega

theorem KeepsNotWithdrawable.trans {fork : Fork} {first second third : BeaconState preset fork}
    (grows : RegistryLifecycle first second)
    (one : KeepsNotWithdrawable first second) (two : KeepsNotWithdrawable second third) :
    KeepsNotWithdrawable first third := by
  refine ⟨two.1.trans one.1, fun i old new found read early => ?_⟩
  obtain ⟨middle, middleFound, -⟩ := grows.validators i old found
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.1]
  have := two.2 i middle new middleFound read
  rw [epoch] at this
  exact this (one.2 i old middle found middleFound early)

/-- The parent payload of a Gloas block keeps a validator not withdrawable. -/
theorem KeepsNotWithdrawable.parentPayload {fork : Fork} {before after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks before gloas body = .ok after) :
    KeepsNotWithdrawable before after :=
  (processParentExecutionPayload_step_of
    (fun a b : BeaconState preset fork => KeepsNotWithdrawable a b ∧ RegistryLifecycle a b)
    (fun a => ⟨.refl a, .refl a⟩)
    (fun one two => ⟨one.1.trans one.2 two.1, one.2.trans two.2⟩)
    (fun frame validators => ⟨.of_validators frame.slot (congrArg (·.data) validators),
      .of_data (congrArg (·.data) validators)⟩)
    (fun requested => ⟨.withdrawalRequest requested,
      registryLifecycle_processWithdrawalRequest requested⟩)
    (fun requested => ⟨.consolidationRequest requested,
      registryLifecycle_processConsolidationRequest requested⟩) ok).1

/-- One block of Fulu or Gloas, and a validator that is not yet withdrawable. Its balance, up to
`MIN_ACTIVATION_BALANCE`, falls by at most a sync committee penalty and one slashing penalty. -/
theorem block_balance_floor {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (fulu : .fusaka ≤ fork)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (within : after.RegistryWithinLimit) (matched : BalancesMatch before)
    (computed : processBlock config checks engine before block = .ok after)
    {index : ValidatorIndex} {validator : Validator}
    (found : before.validators.data[index.toNat]? = some validator)
    (early : getCurrentEpoch before < validator.withdrawableEpoch) :
    ∃ syncPenalty slashingPenalty : Nat,
      min (actualBalanceAt ⟨fork, before⟩ index.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
        actualBalanceAt ⟨fork, after⟩ index.toNat + syncPenalty + slashingPenalty ∧
      syncPenalty ≤
        syncSeats after (Nat.le_trans (by decide) fulu) index.toNat * syncRewardAt after ∧
      (slashingPenalty = 0 ∨ validator.slashed = false ∧
        (∃ later, after.validators.data[index.toNat]? = some later ∧ later.slashed = true) ∧
        slashingPenalty ≤ effectiveAt ⟨fork, before⟩ index.toNat /
          (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  obtain ⟨voted, operated, started, operatedOk, -, synced⟩ := processBlock_operationsInput computed
  simp only [altair, ↓reduceDIte] at synced
  have frameVoted : Frame before voted := (frame_operationsInput started).toFrame
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [bellatrix, ↓reduceDIte] at executedOk
  -- The payload of the parent.
  obtain ⟨parentFloor, parentEarly, parentSlot, parentSize, parentLife⟩ :
      min (actualBalanceAt ⟨fork, before⟩ index.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
        actualBalanceAt ⟨fork, parented⟩ index.toNat ∧ KeepsNotWithdrawable before parented ∧
      parented.slot = before.slot ∧
      parented.validators.data.size = before.validators.data.size ∧
      RegistryLifecycle before parented := by
    split at paidOk
    · obtain ⟨converted, ledger, -⟩ := ledger_processParentExecutionPayload paidOk
      have keeps := KeepsNotWithdrawable.parentPayload paidOk
      refine ⟨?_, keeps, keeps.1, (effectiveKept_parentPayload paidOk).2,
        registryLifecycle_processParentExecutionPayload paidOk⟩
      by_cases member : index ∈ converted
      · simpa using ledger.lowered index member (Finset.notMem_empty _)
      · have := ledger.down index (Finset.notMem_empty _) member
        simp only [Pi.zero_apply] at this
        omega
    · cases paidOk
      exact ⟨Nat.min_le_left _ _, .refl _, rfl, rfl, .refl _⟩
  obtain ⟨middle, middleFound, -⟩ := parentLife.validators _ _ found
  have middleEarly := parentEarly.2 _ _ _ found middleFound early
  -- The header, the withdrawals, the RANDAO reveal and the deposit contract vote.
  have headedLedger := ledger_processBlockHeader headedOk
  have headedValidators : headed.validators = parented.validators ∧ headed.slot = parented.slot := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact ⟨rfl, rfl⟩
  have afterSize : before.validators.data.size ≤ after.validators.data.size :=
    (registryLifecycle_processBlock computed).size_le
  have headedWithin : headed.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit at within ⊢
    rw [headedValidators.1]
    omega
  have headedFloor := execution_balance_floor compounding electra headedWithin executedOk
    (v := index) (val := middle) (by rw [headedValidators.1]; exact middleFound)
    (by simpa only [getCurrentEpoch, headedValidators.2, parentSlot] using middleEarly)
  have votedLedger : Ledger revealed voted ∅ ∅ 0 0 0 := by
    split at votedOk
    · exact ledger_processEth1Data votedOk
    · cases votedOk
      exact Ledger.refl _
  have one := headedLedger.down index (Finset.notMem_empty _) (Finset.notMem_empty _)
  have two := (ledger_processRandao revealedOk).down index (Finset.notMem_empty _)
    (Finset.notMem_empty _)
  have three := votedLedger.down index (Finset.notMem_empty _) (Finset.notMem_empty _)
  simp only [Pi.zero_apply] at one two three
  -- The operations.
  obtain ⟨_, _, slashed, converted, _, slash, operations, -⟩ :=
    credited_processOperations fulu (frameVoted.balancesMatch matched) operatedOk
  have four : min (actualBalanceAt ⟨fork, voted⟩ index.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      actualBalanceAt ⟨fork, operated⟩ index.toNat + slash index := by
    by_cases member : index ∈ converted
    · simpa using operations.ledger.lowered index member (Finset.notMem_empty _)
    · have := operations.ledger.down index (Finset.notMem_empty _) member
      simp only [Pi.zero_apply] at this
      omega
  -- The sync committee.
  obtain ⟨_, reward, _, sync, rewardOk, -, -, seats, syncLedger⟩ :=
    ledger_processSyncAggregate synced
  have five := syncLedger.down index (Finset.notMem_empty _) (Finset.notMem_empty _)
  simp only [Pi.zero_apply] at five
  have syncKept := (processSyncAggregate_kept synced).1
  have syncSlot : after.slot = operated.slot := (frame_processSyncAggregate synced).slot
  have totalSame : activeBalanceTotal after = activeBalanceTotal operated :=
    activeBalanceTotal_eq (by simp only [getCurrentEpoch, syncSlot])
      ((ActiveStep.of_validators (congrArg (·.data) syncKept) syncSlot).2)
      (effectiveKept_data (congrArg (·.data) syncKept)) (by rw [syncKept])
  have rewardValue := (syncRewardRead_of_ok rewardOk).1
  refine ⟨sync index, slash index, by omega, ?_, ?_⟩
  · have := seats index
    rw [rewardValue] at this
    unfold syncRewardAt at this ⊢
    rwa [totalSame]
  · have bound := operations.penalized index
    split at bound
    · rename_i member
      right
      obtain ⟨clear, later, laterFound, marked⟩ := operations.newly index member
      refine ⟨?_, ⟨later, by rw [syncKept]; exact laterFound, marked⟩, ?_⟩
      · cases flag : validator.slashed
        · rfl
        · have inside := (Array.getElem?_eq_some_iff.mp found).1
          have inside' : index.toNat < voted.validators.data.size :=
            Nat.lt_of_lt_of_le inside frameVoted.registryGrows
          have kept := frameVoted.slashed _ _ _ found (Array.getElem?_eq_getElem inside') flag
          rw [clear _ (Array.getElem?_eq_getElem inside')] at kept
          cases kept
      · have same := effectiveKept_processBlock computed index.toNat
          (Array.getElem?_eq_some_iff.mp found).1
        simp only [effectiveAt, syncKept] at same bound ⊢
        rw [← same]
        exact bound
    · exact .inl (by omega)

/-! ## Validators that a block adds -/

/-- A step keeps each effective balance, and each validator that it adds has none. -/
def AddsNoEffectiveBalance {fork : Fork} (before after : BeaconState preset fork) : Prop :=
  EffectiveKept before after ∧ before.validators.data.size ≤ after.validators.data.size ∧
    ∀ i, before.validators.data.size ≤ i → effectiveAt ⟨fork, after⟩ i = 0

namespace AddsNoEffectiveBalance

variable {fork : Fork} {before after : BeaconState preset fork}

theorem of_size (kept : EffectiveKept before after)
    (size : after.validators.data.size = before.validators.data.size) :
    AddsNoEffectiveBalance before after :=
  ⟨kept, Nat.le_of_eq size.symm, fun i outside => by
    simp [effectiveAt, Array.getElem?_eq_none (by omega : after.validators.data.size ≤ i)]⟩

theorem of_validators (validators : after.validators = before.validators) :
    AddsNoEffectiveBalance before after :=
  of_size (effectiveKept_data (congrArg (·.data) validators)) (by rw [validators])

theorem refl (state : BeaconState preset fork) : AddsNoEffectiveBalance state state :=
  of_validators rfl

theorem trans {first second third : BeaconState preset fork}
    (one : AddsNoEffectiveBalance first second) (two : AddsNoEffectiveBalance second third) :
    AddsNoEffectiveBalance first third :=
  ⟨effectiveKept_trans one.1 two.1 one.2.1, Nat.le_trans one.2.1 two.2.1, fun i outside => by
    by_cases inside : i < second.validators.data.size
    · exact (two.1 i inside).trans (one.2.2 i outside)
    · exact two.2.2 i (Nat.le_of_not_lt inside)⟩

theorem foldlM {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
    (each : ∀ a x b, step a x = .ok b → AddsNoEffectiveBalance a b) {items : List α}
    (ok : items.foldlM step before = .ok after) : AddsNoEffectiveBalance before after :=
  foldlM_ok_invariant (AddsNoEffectiveBalance before)
    (fun _ _ _ prior stepped => prior.trans (each _ _ _ stepped)) (refl before) ok

/-- A new validator with balance zero has no effective balance. -/
private theorem newValidator_effectiveBalance (key : _root_.EthLib.Cryptography.Bls.BLSPubkey)
    (credentials : Bytes32) :
    (getValidatorFromDeposit preset fork key credentials 0).effectiveBalance.toNat = 0 := by
  simp only [getValidatorFromDeposit, UInt64.min_def]
  split
  · simp
  · rename_i above
    simp only [UInt64.zero_mod, UInt64.sub_self, UInt64.le_iff_toNat_le, UInt64.toNat_zero] at above
    omega

theorem addValidator {key : _root_.EthLib.Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    (added : addValidatorToRegistry before key credentials 0 = .ok after) :
    AddsNoEffectiveBalance before after := by
  have pushed := addValidatorToRegistry_validators_eq_push added
  refine ⟨fun i inside => ?_, ?_, fun i outside => ?_⟩
  · simp [effectiveAt, pushed, Array.getElem?_push, Nat.ne_of_lt inside]
  · rw [pushed, Array.size_push]
    omega
  · unfold effectiveAt
    dsimp only
    rw [pushed, Array.getElem?_push]
    split
    · rw [Option.map_some, Option.getD_some]
      exact newValidator_effectiveBalance key credentials
    · rw [Array.getElem?_eq_none outside]
      rfl

/-- From Electra, a deposit adds a validator with balance zero. -/
theorem deposit {early : fork < .hegota} {deposit : Deposit} (electra : .pectra ≤ fork)
    (ok : processDeposit config checks early before deposit = .ok after) :
    AddsNoEffectiveBalance before after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  have first : AddsNoEffectiveBalance before
      { before with eth1DepositIndex := fun _ => next } := of_validators rfl
  rcases applyDeposit_cases credited with same | ⟨_, middle, pending, added, same⟩ | ⟨notElectra, _⟩
  · rw [same]
    exact first
  · have last : AddsNoEffectiveBalance middle after := of_validators (by rw [same])
    rcases added with rfl | added
    · exact first.trans last
    · exact first.trans ((addValidator added).trans last)
  · exact absurd electra (Nat.not_le_of_lt notElectra)

/-- A block from Electra adds only validators that have no effective balance. -/
theorem block {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (electra : .pectra ≤ fork)
    (ok : processBlock config checks engine before block = .ok after) :
    AddsNoEffectiveBalance before after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : AddsNoEffectiveBalance before input :=
    started.step_of AddsNoEffectiveBalance refl trans
      (fun _ paid => of_size (effectiveKept_parentPayload paid).1 (effectiveKept_parentPayload paid).2)
      (fun headed => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact of_validators rfl)
      (fun _ executed => of_validators (processBlockExecution_validators executed))
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact of_validators rfl)
      (fun _ voted => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]
        exact of_validators rfl)
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of AddsNoEffectiveBalance refl trans
      (fun deposited => deposit electra deposited)
      (fun exited => of_size (effectiveKept_voluntaryExit exited)
        (sameSizes_processVoluntaryExit exited).1)
      (fun changed => of_size (effectiveKept_blsChange changed)
        (sameSizes_processBlsToExecutionChange changed).1)
      (fun requested => of_size (effectiveKept_requests requested)
        (sameSizes_processExecutionRequests requested).1)
      (fun attested => of_validators (by rw [processPayloadAttestation_eq attested])) operated
  have tail : AddsNoEffectiveBalance last after := by
    split at synced
    · exact of_validators (processSyncAggregate_kept synced).1
    · cases synced
      exact refl _
  exact head.trans <| (foldlM (fun _ _ _ slashed => of_size (effectiveKept_proposerSlashing slashed)
      (sameSizes_processProposerSlashing slashed).1) proposersOk).trans <|
    (foldlM (fun _ _ _ slashed => of_size (effectiveKept_attesterSlashing slashed)
      (sameSizes_processAttesterSlashing slashed).1) slashingsOk).trans <|
    (foldlM (fun _ _ _ attested => of_size
      (effectiveKept_data (by rw [(processAttestation_registry attested).1]))
      (sameSizes_processAttestation attested).1) attestedOk).trans <| rest.trans tail

end AddsNoEffectiveBalance

/-! ## One epoch -/

/-- A validator that is withdrawable stays withdrawable across one step of a run. -/
theorem Run.withdrawable_persists {before after : ForkedBeaconState preset}
    (caps : CapOrder preset) (run : Run config checks before after)
    (invariant : Invariant before.state) (far : getCurrentEpoch before.state < FAR_FUTURE_EPOCH)
    {i : Nat} {old new : Validator}
    (found : before.state.validators.data[i]? = some old)
    (read : after.state.validators.data[i]? = some new)
    (withdrawable : old.withdrawableEpoch ≤ getCurrentEpoch before.state) :
    new.withdrawableEpoch ≤ getCurrentEpoch before.state := by
  have member := Array.mem_of_getElem? found
  have exited := UInt64.le_trans (invariant.exitsOrdered old member) withdrawable
  have assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH := fun none =>
    UInt64.not_le.mpr far (none ▸ exited)
  cases flag : old.slashed
  · rw [(run.retired_validator caps.activation caps.compounding i old new found read exited flag
      withdrawable).2.2]
    exact withdrawable
  · rw [(run.slashed_withdrawable_eq caps.activation caps.compounding i old new found read flag
      assigned).2]
    exact withdrawable

/-- The largest slashing penalty that the blocks of one epoch charge a validator: one penalty, if
the validator was not slashed at the start of the epoch and is slashed now. -/
def slashingPenaltyBound (preset : Preset) (fork : Fork) (effectiveBalance : Nat)
    (slashedBefore slashedNow : Bool) : Nat :=
  if slashedBefore = false ∧ slashedNow = true then
    effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  else 0

/-- What holds for validator `index` inside an epoch that starts at `first`, after `blocks` blocks.
Each block takes at most `syncPenalty` from a balance for the sync committee. -/
structure BalanceInEpoch (first current : ForkedBeaconState preset) (syncPenalty blocks : Nat)
    (index : ValidatorIndex) (atStart now : Validator) : Prop where
  /-- The validator is in the registry. -/
  found : current.state.validators.data[index.toNat]? = some now
  /-- A slashed validator stays slashed. -/
  slashed : atStart.slashed = true → now.slashed = true
  /-- The validator is withdrawable, or its balance is above the floor. -/
  floor : now.withdrawableEpoch ≤ getCurrentEpoch first.state ∨
    min (actualBalanceAt first index.toNat) preset.MIN_ACTIVATION_BALANCE.toNat ≤
      actualBalanceAt current index.toNat + blocks * syncPenalty +
        slashingPenaltyBound preset first.fork atStart.effectiveBalance.toNat atStart.slashed
          now.slashed

private theorem effectiveAt_found {state : ForkedBeaconState preset} {i : Nat} {validator : Validator}
    (found : state.state.validators.data[i]? = some validator) :
    effectiveAt state i = validator.effectiveBalance.toNat := by
  simp [effectiveAt, found]

/-- Two states of a run in one epoch have the same total active balance. -/
theorem Run.activeBalanceTotal_same_epoch {fork : Fork} {first last : BeaconState preset fork}
    (run : Run config checks ⟨fork, first⟩ ⟨fork, last⟩)
    (same : getCurrentEpoch last = getCurrentEpoch first) :
    activeBalanceTotal last = activeBalanceTotal first := by
  have active := activeKept_of_chainSteps run.chainSteps
  have effective := run.effectiveKept_of_same_epoch same
  have grows := registryGrows_of_chainSteps run.chainSteps
  dsimp only at active effective grows
  exact activeBalanceTotal_eq same active effective grows

/-- A run inside one epoch keeps the fork. -/
theorem Run.fork_same_epoch {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (same : getCurrentEpoch last.state = getCurrentEpoch first.state) : last.fork = first.fork :=
  Run.induction_of_same_epoch (fun current _ => current.fork = first.fork) rfl
    (fun _ _ _ _ _ prior => prior) (fun _ _ lastEq _ _ prior => by rw [lastEq]; exact prior) run same

/-- The seats of a validator are at most the size of the sync committee. -/
theorem syncSeats_le {fork : Fork} (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (i : Nat) : syncSeats state altair i ≤ preset.SYNC_COMMITTEE_SIZE.toNat :=
  Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Inside one epoch of Fulu or Gloas, a run keeps the balance floor of each validator. -/
theorem Run.balanceInEpoch {first last : ForkedBeaconState preset} (caps : CapOrder preset)
    (fulu : .fusaka ≤ first.fork) (facts : ChainFacts config first.state)
    (far : getCurrentEpoch first.state < FAR_FUTURE_EPOCH) {syncPenalty : Nat}
    (reward : preset.SYNC_COMMITTEE_SIZE.toNat * syncRewardAt first.state ≤ syncPenalty)
    (run : Run config checks first last)
    (same : getCurrentEpoch last.state = getCurrentEpoch first.state) :
    last.fork = first.fork ∧ getCurrentEpoch last.state = getCurrentEpoch first.state ∧
    (∀ i, first.state.validators.data.size ≤ i → effectiveAt last i = 0) ∧
    (last.state.RegistryWithinLimit →
      ∀ (index : ValidatorIndex) (atStart : Validator),
        first.state.validators.data[index.toNat]? = some atStart →
        ∃ now, BalanceInEpoch first last syncPenalty run.blockCount index atStart now) := by
  obtain ⟨fork, first⟩ := first
  refine Run.induction_of_same_epoch (fun current pre =>
    current.fork = fork ∧ getCurrentEpoch current.state = getCurrentEpoch first ∧
    (∀ i, first.validators.data.size ≤ i → effectiveAt current i = 0) ∧
    (current.state.RegistryWithinLimit →
      ∀ (index : ValidatorIndex) (atStart : Validator),
        first.validators.data[index.toNat]? = some atStart →
        ∃ now, BalanceInEpoch ⟨fork, first⟩ current syncPenalty pre.blockCount index atStart now))
    ?_ ?_ ?_ run same
  · refine ⟨rfl, rfl, fun i outside => ?_, fun _ index atStart found => ⟨atStart, found, id, .inr ?_⟩⟩
    · simp [effectiveAt, Array.getElem?_eq_none outside]
    · exact Nat.le_trans (Nat.min_le_left _ _) (by omega)
  · intro f before after engine signed due ok pre prior
    obtain ⟨forkSame, epochSame, added, floors⟩ := prior
    have forkSame : f = fork := forkSame
    subst forkSame
    have processed := (applySignedBlock_ok ok).2.1
    have adds := AddsNoEffectiveBalance.block (Nat.le_trans (by decide) fulu) processed
    have frame := frame_processBlock processed
    have afterEpoch : getCurrentEpoch after = getCurrentEpoch first := by
      rw [← epochSame]
      simp only [getCurrentEpoch, frame.slot]
    refine ⟨rfl, afterEpoch, fun i outside => ?_, fun within index atStart found => ?_⟩
    · by_cases inside : i < before.validators.data.size
      · exact (adds.1 i inside).trans (added i outside)
      · exact adds.2.2 i (Nat.le_of_not_lt inside)
    have withinBefore : before.RegistryWithinLimit := by
      unfold BeaconState.RegistryWithinLimit at within ⊢
      exact Nat.le_trans adds.2.1 within
    obtain ⟨now, nowFound, slashed, floor⟩ := floors withinBefore index atStart found
    obtain ⟨later, laterFound, -⟩ :=
      (registryLifecycle_processBlock processed).validators _ _ nowFound
    have factsBefore := facts.run caps pre
    have keptSlashed := frame.slashed _ _ _ nowFound laterFound
    refine ⟨later, laterFound, fun flag => keptSlashed (slashed flag), ?_⟩
    have nowEpoch : getCurrentEpoch before = getCurrentEpoch first := epochSame
    by_cases withdrawable : now.withdrawableEpoch ≤ getCurrentEpoch first
    · left
      have step : Run config checks ⟨f, before⟩ ⟨f, after⟩ :=
        Run.nil.snoc (.block engine signed due ok)
      have persists := Run.withdrawable_persists caps step factsBefore.invariant
        (by rw [nowEpoch]; exact far) nowFound laterFound (by rw [nowEpoch]; exact withdrawable)
      rwa [nowEpoch] at persists
    right
    have floor := floor.resolve_left withdrawable
    obtain ⟨sync, slash, moved, syncBound, slashBound⟩ := block_balance_floor fulu caps.compounding
      within factsBefore.invariant.balancesMatch processed nowFound
      (by rw [nowEpoch]; exact UInt64.not_le.mp withdrawable)
    have total : activeBalanceTotal after = activeBalanceTotal first :=
      Run.activeBalanceTotal_same_epoch (pre.snoc (.block engine signed due ok)) afterEpoch
    have syncLe : sync ≤ syncPenalty := by
      have seats := Nat.mul_le_mul_right (syncRewardAt after)
        (syncSeats_le after (Nat.le_trans (by decide) fulu) index.toNat)
      have rewardSame : syncRewardAt after = syncRewardAt first := by
        unfold syncRewardAt
        rw [total]
      rw [rewardSame] at seats syncBound
      exact Nat.le_trans syncBound (Nat.le_trans seats reward)
    -- The effective balance of the validator is the one at the start of the epoch.
    have effective : effectiveAt ⟨f, before⟩ index.toNat = atStart.effectiveBalance.toNat := by
      rw [pre.effectiveKept_of_same_epoch epochSame index.toNat
        (Array.getElem?_eq_some_iff.mp found).1]
      exact effectiveAt_found (state := ⟨f, first⟩) found
    have penalty : slash + slashingPenaltyBound preset f atStart.effectiveBalance.toNat
          atStart.slashed now.slashed ≤
        slashingPenaltyBound preset f atStart.effectiveBalance.toNat atStart.slashed
          later.slashed := by
      unfold slashingPenaltyBound
      rcases slashBound with zero | ⟨nowClear, ⟨later', laterFound', marked⟩, bound⟩
      · subst zero
        split
        · rename_i both
          rw [ite_eq_left ⟨both.1, keptSlashed both.2⟩]
          omega
        · omega
      · obtain rfl := Option.some.inj (laterFound'.symm.trans laterFound)
        have startClear : atStart.slashed = false := by
          cases flag : atStart.slashed
          · rfl
          · rw [slashed flag] at nowClear
            cases nowClear
        rw [effective] at bound
        simp only [nowClear, startClear, marked, Bool.false_eq_true, and_false, and_self,
          ↓reduceIte, Nat.add_zero]
        exact bound
    have count : (pre.snoc (.block engine signed due ok)).blockCount = pre.blockCount + 1 := rfl
    rw [count, Nat.add_mul, Nat.one_mul]
    dsimp only at moved floor ⊢
    omega
  · intro middle last cached next pre ok lastEq cachedOk epochSame prior
    subst lastEq
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨forkSame, middleEpoch, added, floors⟩ := prior
    refine ⟨forkSame, epochSame.trans middleEpoch, added, fun within index atStart found => ?_⟩
    obtain ⟨now, nowFound, slashed, floor⟩ := floors within index atStart found
    exact ⟨now, nowFound, slashed, floor⟩

end EpochProofs.EthLib
