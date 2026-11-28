import EthLib.Consensus.Transition.EpochPending
import EpochProofs.EthLib.Churn
import EpochProofs.EthLib.Consolidations
import EpochProofs.EthLib.Oracle

/-!
# `process_pending_deposits`: the reference and EthLib agree

Gloas and Fulu read different churn limits. `specPendingDeposits` is the reference step with the
churn limit as a parameter, and the reference steps of both forks are equal to it.

`hroom` names a difference. The registry has room for the deposits that one epoch reads, at most
`MAX_PENDING_DEPOSITS_PER_EPOCH`. On Fulu, EthLib fails when it appends to a full registry, and the
reference appends. On Gloas, EthLib fails when a registry position does not fit in 64 bits.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- `process_pending_deposits` of the reference, on the churn limit of the fork. -/
def specPendingDeposits (p : Spec.Preset) (churnLimit : Spec.SpecM Nat)
    (apply_pending_deposit : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (state : Spec.BeaconState) : Spec.SpecM Spec.BeaconState := do
  let next_epoch ← Spec.uint64Add (← Spec.get_current_epoch p state) 1
  let available_for_processing ←
    Spec.uint64Add state.deposit_balance_to_consume (← churnLimit)
  let mut processed_amount := 0
  let mut next_deposit_index := 0
  let mut deposits_to_postpone := []
  let mut is_churn_limit_reached := false
  let finalized_slot ← Spec.compute_start_slot_at_epoch p state.finalized_checkpoint.epoch

  let mut state := state
  for deposit in state.pending_deposits do
    if deposit.slot > finalized_slot then
      break

    if next_deposit_index ≥ p.MAX_PENDING_DEPOSITS_PER_EPOCH then
      break

    let mut is_validator_exited := false
    let mut is_validator_withdrawn := false
    let validator_pubkeys := state.validators.map (·.pubkey)
    if deposit.pubkey ∈ validator_pubkeys then
      let validator ← Spec.listGet state.validators (validator_pubkeys.idxOf deposit.pubkey)
      is_validator_exited := validator.exit_epoch < Spec.FAR_FUTURE_EPOCH
      is_validator_withdrawn := validator.withdrawable_epoch < next_epoch

    if is_validator_withdrawn then
      state ← apply_pending_deposit state deposit
    else if is_validator_exited then
      deposits_to_postpone := deposits_to_postpone ++ [deposit]
    else
      is_churn_limit_reached :=
        decide ((← Spec.uint64Add processed_amount deposit.amount) > available_for_processing)
      if is_churn_limit_reached then
        break
      processed_amount ← Spec.uint64Add processed_amount deposit.amount
      state ← apply_pending_deposit state deposit

    next_deposit_index := next_deposit_index + 1

  state := { state with
    pending_deposits := state.pending_deposits.drop next_deposit_index ++ deposits_to_postpone }

  if is_churn_limit_reached then
    state := { state with
      deposit_balance_to_consume := ← Spec.uint64Sub available_for_processing processed_amount }
  else
    state := { state with deposit_balance_to_consume := 0 }
  pure state

theorem specPendingDeposits_gloas (p : Spec.Preset) (total : Nat) :
    Spec.process_pending_deposits p total =
      specPendingDeposits p (Spec.get_activation_churn_limit p total) := rfl

theorem specPendingDeposits_fulu (p : Spec.Preset) (f : Spec.FuluConfig) (total : Nat) :
    Spec.process_pending_deposits_fulu p f total =
      specPendingDeposits p (Spec.get_activation_exit_churn_limit p f total) := rfl

/-! ## One deposit -/

theorem findIdx_pubkey (s : BeaconState preset fork) (pubkey : Vector UInt8 48) :
    (match s.validators.data.findIdx? (·.pubkey == pubkey) with
    | some i => i < s.validators.data.size ∧
        pubkey ∈ (toSpecState s).validators.map (·.pubkey) ∧
        ((toSpecState s).validators.map (·.pubkey)).idxOf pubkey = i
    | none => pubkey ∉ (toSpecState s).validators.map (·.pubkey)) := by
  have hmap : (toSpecState s).validators.map (·.pubkey) =
      s.validators.data.toList.map (·.pubkey) := by
    simp [toSpecState, readList, toSpecValidator]
  rw [hmap]
  cases h : s.validators.data.findIdx? (·.pubkey == pubkey) with
  | none =>
    simp only [Array.findIdx?_eq_none_iff] at h
    simp only [List.mem_map, not_exists, not_and]
    intro v hv hp
    have := h v (by simpa using hv)
    simp [hp] at this
  | some i =>
    obtain ⟨hi, hp, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
    have hlt : i < (s.validators.data.toList.map (·.pubkey)).length := by simpa using hi
    have hget : (s.validators.data.toList.map (·.pubkey))[i] = pubkey := by simpa using hp
    refine ⟨hi, List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩, ?_⟩
    rw [List.idxOf, List.findIdx_eq hlt]
    refine ⟨by simpa using hget, fun j hj => ?_⟩
    have := hbefore j hj
    simpa using this

/-! ## A new validator -/

theorem setOrAppendList_same {switch : _root_.EthLib.Base.Fork} {α β : Type} {limit : Nat}
    (read : α → β) (list : ForkList switch fork α limit) {index : UInt64}
    (hindex : index.toNat < limit) (value : α) :
    SameOutcome (fun a b => b = readList read a.data) (setOrAppendList list index value)
      (Spec.set_or_append_list (readList read list.data) index.toNat (read value)) := by
  unfold setOrAppendList Spec.set_or_append_list
  have hlength : (readList read list.data).length = list.data.size := by simp [readList]
  rw [hlength]
  refine .ite (by simp) (fun h => ?_) (fun h => ?_)
  · rw [appendWithinLimit, dite_eq_left (fun _ => by omega)]
    exact .returned (by simp [readList])
  · rw [Spec.listSet, hlength]
    by_cases hlt : index.toNat < list.data.size
    · rw [dite_eq_left hlt, ite_eq_left hlt]
      exact .returned (by simp [readList, List.map_set])
    · rw [dite_eq_right hlt, ite_eq_right hlt]
      exact .failed

theorem get_validator_from_deposit_eq (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (pubkey : Vector UInt8 48) (credentials : Vector UInt8 32)
    (amount : UInt64) :
    Spec.get_validator_from_deposit (toSpecPreset preset config) pubkey credentials amount.toNat =
      .ok (toSpecValidator (getValidatorFromDeposit preset fork pubkey credentials amount)) := by
  unfold Spec.get_validator_from_deposit getValidatorFromDeposit
  simp only [spec_preset]
  rw [← bind_assoc, round_to_increment_eq hdiv.increment, bind_ok]
  have hmax := get_max_effective_balance_eq (config := config) (preset := preset) electra
    { pubkey, withdrawalCredentials := credentials, effectiveBalance := 0, slashed := false,
      activationEligibilityEpoch := FAR_FUTURE_EPOCH, activationEpoch := FAR_FUTURE_EPOCH,
      exitEpoch := FAR_FUTURE_EPOCH, withdrawableEpoch := FAR_FUTURE_EPOCH }
  refine congrArg Except.ok ?_
  simp only [toSpecValidator, toNat_min, ← hmax]
  rfl

theorem add_validator_to_registry_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (s : BeaconState preset fork)
    (hroom : s.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pubkey : Vector UInt8 48) (credentials : Vector UInt8 32) (amount : UInt64) :
    SameOutcome (fun st acc => acc = toSpecState st ∧
        st.validators.data.size = s.validators.data.size + 1 ∧
        st.pendingDeposits = s.pendingDeposits)
      (addValidatorToRegistry s pubkey credentials amount)
      (Spec.add_validator_to_registry (toSpecPreset preset config) (toSpecState s) pubkey
        credentials amount.toNat) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have hlength : (toSpecState s).validators.length = s.validators.data.size := by
    simp [toSpecState, readList]
  unfold addValidatorToRegistry addValidatorToRegistryAltair Spec.add_validator_to_registry
    getIndexForNewValidator Spec.get_index_for_new_validator
  rw [dite_eq_left altair]
  refine .liftAccessor ?_
  obtain ⟨index, hindex, hnat⟩ := ofNatChecked_ok
    (Nat.lt_trans hroom preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt)
  rw [hindex, get_validator_from_deposit_eq hdiv electra]
  simp only [_root_.EthLib.Consensus.liftArith, Except.mapError, bind_ok, hlength]
  rw [← hnat] at hroom ⊢
  have hvalidators : ∃ l : Validators preset fork,
      setOrAppendRooted s.validators index
        (getValidatorFromDeposit preset fork pubkey credentials amount) = .ok l ∧
      l.data.size = s.validators.data.size + 1 ∧
      Spec.set_or_append_list (toSpecState s).validators index.toNat
        (toSpecValidator (getValidatorFromDeposit preset fork pubkey credentials amount)) =
        .ok (readList toSpecValidator l.data) := by
    refine ⟨s.validators.push (getValidatorFromDeposit preset fork pubkey credentials amount)
      (fun _ => by rw [← hnat]; exact hroom), ?_, ?_, ?_⟩
    · rw [setOrAppendRooted, ite_eq_left hnat, dite_eq_left (fun _ => by omega)]
    · simp [RootedForkList.push]
    · rw [Spec.set_or_append_list, hlength, ite_eq_left (by simpa using hnat)]
      simp [RootedForkList.push, readList, toSpecState, pure, Except.pure]
  obtain ⟨l, hset, hsize, hspecSet⟩ := hvalidators
  rw [hset, hspecSet]
  simp only [bind_ok]
  refine .bind (setOrAppendList_same UInt64.toNat s.balances hroom amount) ?_
  rintro balances _ rfl -
  have hflags (list : EpochParticipation preset fork) :=
    setOrAppendList_same id list hroom (0 : UInt8)
  simp only [readList, List.map_id, id] at hflags
  rw [toSpecState_previous_epoch_participation s altair,
    toSpecState_current_epoch_participation s altair, toSpecState_inactivity_scores s altair]
  refine .bind (hflags (s.previousEpochParticipation altair)) ?_
  rintro previous _ rfl -
  refine .bind (hflags (s.currentEpochParticipation altair)) ?_
  rintro current _ rfl -
  refine .bind (setOrAppendList_same UInt64.toNat (s.inactivityScores altair) hroom 0) ?_
  rintro scores _ rfl -
  refine .returned ⟨?_, by rw [hnat]; exact hsize, rfl⟩
  simp [toSpecState, fieldOr, altair, readList]

/-- The deposit of an amount to a key. A new key gets a new validator. -/
theorem apply_pending_deposit_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (beforeHeze : fork < .hegota) {checks : SignatureChecks}
    {o : Spec.Oracle} (ho : OracleMatches preset checks o) (s : BeaconState preset fork)
    (hroom : s.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (deposit : PendingDeposit) :
    SameOutcome (fun st acc => acc = toSpecState st ∧
        st.validators.data.size ≤ s.validators.data.size + 1 ∧
        st.pendingDeposits = s.pendingDeposits)
      (applyPendingDeposit config checks s deposit)
      (Spec.apply_pending_deposit (toSpecPreset preset config) o (toSpecState s)
        (toSpecPendingDeposit deposit)) := by
  unfold applyPendingDeposit Spec.apply_pending_deposit
  have hfind := findIdx_pubkey s deposit.pubkey
  have hkey : (toSpecPendingDeposit deposit).pubkey = deposit.pubkey := rfl
  rw [hkey]
  cases h : s.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | none =>
    rw [h] at hfind
    simp only at hfind ⊢
    rw [ite_eq_left hfind, ite_eq_right (fun h => Nat.not_le_of_lt beforeHeze h.1),
      is_valid_deposit_signature_same ho, bind_ok]
    refine .ite Iff.rfl (fun _ => ?_) (fun _ => .returned ⟨rfl, Nat.le_succ _, rfl⟩)
    exact (add_validator_to_registry_same hdiv electra s hroom _ _ _).mono
      fun _ _ h => ⟨h.1, Nat.le_of_eq h.2.1, h.2.2⟩
  | some i =>
    rw [h] at hfind
    simp only at hfind ⊢
    obtain ⟨hi, hmem, hidx⟩ := hfind
    rw [ite_eq_right (by simpa using hmem), hidx]
    obtain ⟨index, hindex, rfl⟩ := ofNatChecked_ok
      (Nat.lt_trans hi (Nat.lt_trans hroom preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
    rw [hindex]
    show SameOutcome _ (liftAccessor (increaseBalance s index deposit.amount)) _
    rw [← bind_pure (liftAccessor (increaseBalance s index deposit.amount))]
    refine .bind (increase_balance_same (.refl s) index deposit.amount).liftAccessor ?_
    rintro st balances hst -
    refine .returned ⟨hst.toSpecState_eq, ?_, ?_⟩
    · obtain ⟨l, rfl, -, -⟩ := hst
      exact Nat.le_succ _
    · obtain ⟨l, rfl, -, -⟩ := hst
      rfl

/-! ## The loop over the deposits -/

/-- The values that the reference loop carries: the processed amount, the number of deposits read,
the postponed deposits, the churn flag and the state. -/
abbrev DepositLoop := Nat × Nat × List Spec.PendingDeposit × Bool × Spec.BeaconState

/-- The part of one reference loop step after the status of the target is known. -/
def depositStepAfter (available : Nat)
    (apply_pending_deposit : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (deposit : Spec.PendingDeposit) (acc : DepositLoop) (exited withdrawn : Bool) :
    Spec.SpecM (ForInStep DepositLoop) :=
  if withdrawn = true then do
    let state ← apply_pending_deposit acc.2.2.2.2 deposit
    pure (.yield (acc.1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2.1, state))
  else if exited = true then
    pure (.yield (acc.1, acc.2.1 + 1, acc.2.2.1 ++ [deposit], acc.2.2.2.1, acc.2.2.2.2))
  else do
    let total ← Spec.uint64Add acc.1 deposit.amount
    if decide (total > available) = true then
      pure (.done (acc.1, acc.2.1, acc.2.2.1, decide (total > available), acc.2.2.2.2))
    else do
      let processed ← Spec.uint64Add acc.1 deposit.amount
      let state ← apply_pending_deposit acc.2.2.2.2 deposit
      pure (.yield (processed, acc.2.1 + 1, acc.2.2.1, decide (total > available), state))

/-- One step of the reference loop. -/
def depositStep (p : Spec.Preset) (next available finalizedSlot : Nat)
    (apply_pending_deposit : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (deposit : Spec.PendingDeposit) (acc : DepositLoop) : Spec.SpecM (ForInStep DepositLoop) :=
  if deposit.slot > finalizedSlot then
    pure (.done (acc.1, acc.2.1, acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2))
  else if acc.2.1 ≥ p.MAX_PENDING_DEPOSITS_PER_EPOCH then
    pure (.done (acc.1, acc.2.1, acc.2.2.1, acc.2.2.2.1, acc.2.2.2.2))
  else if deposit.pubkey ∈ acc.2.2.2.2.validators.map (·.pubkey) then do
    let validator ← Spec.listGet acc.2.2.2.2.validators
      ((acc.2.2.2.2.validators.map (·.pubkey)).idxOf deposit.pubkey)
    depositStepAfter available apply_pending_deposit deposit acc
      (decide (validator.exit_epoch < Spec.FAR_FUTURE_EPOCH))
      (decide (validator.withdrawable_epoch < next))
  else depositStepAfter available apply_pending_deposit deposit acc false false

theorem deposit_status_same {st : BeaconState preset fork}
    (hregistry : st.validators.data.size < 2 ^ 64) (next : UInt64) (deposit : PendingDeposit)
    (available : Nat)
    (apply : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (processed count : Nat) (postponed : List Spec.PendingDeposit) (reached : Bool) :
    ∃ status, depositTargetStatus st next deposit.pubkey = .ok status ∧
      (if (toSpecPendingDeposit deposit).pubkey ∈ (toSpecState st).validators.map (·.pubkey) then do
        let validator ← Spec.listGet (toSpecState st).validators
          (((toSpecState st).validators.map (·.pubkey)).idxOf (toSpecPendingDeposit deposit).pubkey)
        depositStepAfter available apply (toSpecPendingDeposit deposit)
          (processed, count, postponed, reached, toSpecState st)
          (decide (validator.exit_epoch < Spec.FAR_FUTURE_EPOCH))
          (decide (validator.withdrawable_epoch < next.toNat))
      else depositStepAfter available apply (toSpecPendingDeposit deposit)
        (processed, count, postponed, reached, toSpecState st) false false) =
      depositStepAfter available apply (toSpecPendingDeposit deposit)
        (processed, count, postponed, reached, toSpecState st) status.1 status.2 := by
  have hfind := findIdx_pubkey st deposit.pubkey
  have hkey : (toSpecPendingDeposit deposit).pubkey = deposit.pubkey := rfl
  unfold depositTargetStatus
  rw [hkey]
  cases h : st.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | none =>
    rw [h] at hfind
    simp only at hfind ⊢
    exact ⟨_, rfl, by rw [ite_eq_right hfind]⟩
  | some i =>
    rw [h] at hfind
    simp only at hfind ⊢
    obtain ⟨hi, hmem, hidx⟩ := hfind
    obtain ⟨index, hindex, rfl⟩ := ofNatChecked_ok (Nat.lt_trans hi hregistry)
    have hget : getValidator st index = .ok st.validators.data[index.toNat] := by
      simp [getValidator, hi]
    rw [hindex]
    simp only [_root_.EthLib.Consensus.liftArith, Except.mapError, bind_ok, hget]
    refine ⟨_, rfl, ?_⟩
    rw [ite_eq_left hmem, hidx, listGet_validators hi, bind_ok]
    simp only [UInt64.lt_iff_toNat_lt]
    rfl

theorem pass_pending_deposits_same (hdiv : DivisorsNonzero preset config)
    (electra : .pectra ≤ fork) (beforeHeze : fork < .hegota) {checks : SignatureChecks}
    {o : Spec.Oracle} (ho : OracleMatches preset checks o) (stop : PendingDeposit → Bool)
    (next available finalizedSlot : UInt64)
    (hstop : ∀ d, stop d = decide (finalizedSlot < d.slot)) :
    ∀ (l : List PendingDeposit) (st : BeaconState preset fork) (processed : UInt64) (count : Nat)
      (postponed : Array PendingDeposit),
      st.validators.data.size + min l.length (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count) ≤
        preset.VALIDATOR_REGISTRY_LIMIT.toNat →
      SameOutcome (fun pass (acc : DepositLoop) => ∃ read,
          acc = (pass.1.processed.toNat, count + read,
            readList toSpecPendingDeposit pass.1.postponed, pass.1.churnReached,
            toSpecState pass.1.state) ∧
          pass.1.rest = l.drop read ∧ pass.1.state.pendingDeposits = st.pendingDeposits ∧
          pass.1.state.RegistryWithinLimit)
        (passPendingDeposits config checks stop next available st processed count postponed l)
        (forIn (l.map toSpecPendingDeposit)
          (processed.toNat, count, readList toSpecPendingDeposit postponed, false, toSpecState st)
          (depositStep (toSpecPreset preset config) next.toNat available.toNat finalizedSlot.toNat
            (Spec.apply_pending_deposit (toSpecPreset preset config) o)))
  | [], st, processed, count, postponed, hroom =>
    .returned ⟨0, rfl, rfl, rfl, Nat.le_trans (Nat.le_add_right _ _) hroom⟩
  | deposit :: rest, st, processed, count, postponed, hroom => by
    have ih := pass_pending_deposits_same hdiv electra beforeHeze ho stop next available
      finalizedSlot hstop rest
    rw [List.length_cons] at hroom
    have hregistry : st.RegistryWithinLimit := Nat.le_trans (Nat.le_add_right _ _) hroom
    simp only [List.map_cons, List.forIn_cons]
    rw [passPendingDeposits, hstop]
    generalize hloop : depositStep (toSpecPreset preset config) next.toNat available.toNat
      finalizedSlot.toNat (Spec.apply_pending_deposit (toSpecPreset preset config) o) = loop
      at ih ⊢
    rw [show loop (toSpecPendingDeposit deposit) _ = _ from by rw [← hloop, depositStep]]
    by_cases hslot : finalizedSlot < deposit.slot
    · have hslot' : (toSpecPendingDeposit deposit).slot > finalizedSlot.toNat :=
        UInt64.lt_iff_toNat_lt.mp hslot
      simp only [hslot, hslot', decide_true, Bool.true_or, ite_true, pure_eq_ok, bind_ok]
      exact .returned ⟨0, rfl, rfl, rfl, hregistry⟩
    have hslot' : ¬(toSpecPendingDeposit deposit).slot > finalizedSlot.toNat := fun h =>
      hslot (UInt64.lt_iff_toNat_lt.mpr h)
    by_cases hcount : preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count
    · simp only [hslot, hslot', hcount, decide_true, decide_false, Bool.or_true, ite_true,
        ite_false, spec_preset, pure_eq_ok, bind_ok]
      exact .returned ⟨0, rfl, rfl, rfl, hregistry⟩
    simp only [hslot, hslot', hcount, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      spec_preset]
    obtain ⟨⟨exited, withdrawn⟩, hstatus, hspec⟩ := deposit_status_same (st := st)
      (registry_lt hregistry) next deposit
      available.toNat (Spec.apply_pending_deposit (toSpecPreset preset config) o) processed.toNat
      count (readList toSpecPendingDeposit postponed) false
    rw [hspec, hstatus]
    simp only [liftAccessor, Except.mapError, bind_ok]
    unfold depositStepAfter
    have happly := apply_pending_deposit_same hdiv electra beforeHeze ho st (by omega) deposit
    cases withdrawn
    · cases exited
      · simp only [Bool.false_eq_true, ite_false, bind_assoc]
        refine .bind (addChecked_same processed deposit.amount).liftArith.liftAccessor ?_
        rintro total _ rfl htotal
        have htotal' : Spec.uint64Add processed.toNat deposit.amount.toNat = .ok total.toNat := by
          obtain ⟨_, h, rfl⟩ :=
            (addChecked_same processed deposit.amount).liftArith.liftAccessor.returns htotal
          exact h
        by_cases hlimit : available < total
        · have hlimit' : total.toNat > available.toNat := UInt64.lt_iff_toNat_lt.mp hlimit
          simp only [hlimit, hlimit', decide_true, ite_true, pure_eq_ok, bind_ok]
          exact .returned ⟨0, rfl, rfl, rfl, hregistry⟩
        · have hlimit' : ¬total.toNat > available.toNat := fun h =>
            hlimit (UInt64.lt_iff_toNat_lt.mpr h)
          have hagain : Spec.uint64Add processed.toNat (toSpecPendingDeposit deposit).amount =
              .ok total.toNat := htotal'
          simp only [hlimit, hlimit', decide_false, Bool.false_eq_true, ite_false, hagain, bind_ok,
            bind_assoc]
          refine .bind happly ?_
          rintro st' _ ⟨rfl, hsize, hpending⟩ -
          simp only [pure_eq_ok, bind_ok]
          refine .bind_pure (ih st' total (count + 1) postponed (by omega)) ?_
          rintro pass _ ⟨read, rfl, hrest, hpending', hlimit'⟩
          exact ⟨read + 1, by rw [Nat.add_assoc, Nat.add_comm 1], hrest,
            hpending'.trans hpending, hlimit'⟩
      · simp only [Bool.false_eq_true, ite_false, ite_true, pure_eq_ok, bind_ok]
        have hpush : readList toSpecPendingDeposit postponed ++ [toSpecPendingDeposit deposit] =
            readList toSpecPendingDeposit (postponed.push deposit) := by simp [readList]
        rw [hpush]
        refine .bind_pure (ih st processed (count + 1) (postponed.push deposit) (by omega)) ?_
        rintro pass _ ⟨read, rfl, hrest, hpending', hlimit'⟩
        exact ⟨read + 1, by rw [Nat.add_assoc, Nat.add_comm 1], hrest, hpending', hlimit'⟩
    · simp only [ite_true, bind_assoc]
      refine .bind happly ?_
      rintro st' _ ⟨rfl, hsize, hpending⟩ -
      simp only [pure_eq_ok, bind_ok]
      refine .bind_pure (ih st' processed (count + 1) postponed (by omega)) ?_
      rintro pass _ ⟨read, rfl, hrest, hpending', hlimit'⟩
      exact ⟨read + 1, by rw [Nat.add_assoc, Nat.add_comm 1], hrest,
        hpending'.trans hpending, hlimit'⟩

theorem pending_deposits_same (hdiv : DivisorsNonzero preset config) (fulu : .fusaka ≤ fork)
    (electra : .pectra ≤ fork) (beforeHeze : fork < .hegota) {checks : SignatureChecks}
    {o : Spec.Oracle} (ho : OracleMatches preset checks o) {s : BeaconState preset fork}
    (hroom : s.validators.data.size +
      min (s.pendingDeposits electra).data.size preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤
        preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    {churnLimit : Spec.SpecM Nat} {churn : UInt64}
    (hchurn : depositChurnLimit config s = .ok churn) (hspec : churnLimit = .ok churn.toNat) :
    SameOutcome (fun st acc => acc = toSpecState st ∧ st.RegistryWithinLimit)
      (processPendingDeposits config checks s electra)
      (specPendingDeposits (toSpecPreset preset config) churnLimit
        (Spec.apply_pending_deposit (toSpecPreset preset config) o) (toSpecState s)) := by
  unfold processPendingDeposits specPendingDeposits
  rw [get_current_epoch_eq hdiv.slots, hchurn, hspec]
  simp only [bind_ok]
  refine .bind (next_epoch_same s) ?_
  rintro next _ rfl -
  rw [toSpecState_deposit_balance_to_consume s electra, toSpecState_pending_deposits s electra]
  simp only [liftAccessor, Except.mapError, bind_ok]
  refine .bind (addChecked_same _ churn).liftArith.liftAccessor ?_
  rintro available _ rfl -
  refine .bind (mulChecked_same s.finalizedCheckpoint.epoch
    preset.SLOTS_PER_EPOCH).liftArith.liftAccessor ?_
  rintro finalizedSlot _ rfl -
  refine .bind (pass_pending_deposits_same hdiv electra beforeHeze ho
    (depositWaits s finalizedSlot) next available finalizedSlot ?_
    (s.pendingDeposits electra).data.toList s 0 0 #[] (by simpa using hroom)) ?_
  · intro d
    have hbridge : bridgeDepositsPending s = false := by
      rw [bridgeDepositsPending, dite_eq_right]
      exact fun h => Nat.not_lt_of_le fulu h.2
    rw [depositWaits, hbridge, Bool.false_and, Bool.false_or]
  · rintro ⟨pass, hpass⟩ _ ⟨read, rfl, hrest, hpending, hregistry⟩ -
    simp only at hrest hpending ⊢
    have hqueue : (toSpecState pass.state).pending_deposits.drop (0 + read) ++
        readList toSpecPendingDeposit pass.postponed =
        readList toSpecPendingDeposit (pass.rest.toArray ++ pass.postponed) := by
      rw [toSpecState_pending_deposits _ electra, hpending, hrest]
      simp [readList, List.map_drop]
    refine .ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · refine .bind (subChecked_same available pass.processed).liftArith.liftAccessor ?_
      rintro carried _ rfl -
      refine .returned ⟨?_, hregistry⟩
      rw [hqueue]
      simp [toSpecState, fieldOr, electra]
    · refine .returned ⟨?_, hregistry⟩
      rw [hqueue]
      simp [toSpecState, fieldOr, electra]

end EpochProofs.EthLib
