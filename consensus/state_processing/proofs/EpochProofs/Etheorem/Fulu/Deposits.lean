import EpochProofs.Etheorem.Fulu.Registry
import EpochProofs.Etheorem.Fulu.Consolidations
import EpochProofs.Etheorem.Fulu.Oracle
import EpochProofs.Sanity.Invariants.LighthouseTailDeposits

/-!
# The reference `process_pending_deposits` equals Etheorem's

The main theorem is `process_pending_deposits_etheorem`. Etheorem scans the queue with a fuel
loop, `ppdLoop`. `ppdLoop_fuel` proves that it stops where the reference loop stops, applies
the same deposits, and postpones the same deposits.

`apply_pending_deposit_etheorem` proves one deposit equal. It needs `OracleAgrees`, so the
deposit signature check reads the same SSZ roots and BLS check.

Conditions:
- `hlens`: the registry lists have the same length.
- `hroom`: the validators fit under `VALIDATOR_REGISTRY_LIMIT` after one new validator for
  each pending deposit. Etheorem drops a validator past the limit.
- `hbridge`: each pending deposit has slot 0, or `eth1_deposit_index` has reached
  `deposit_requests_start_index`. Etheorem keeps the Electra eth1 bridge stop, and pyspec
  removed it in Fulu (finding F2, `ppdStep_bridge_stop`).
-/

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Fulu (FuluRun)

section Body
variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]
variable {p : Spec.Preset} (hp : PresetAgrees p)

include hp in
theorem compute_domain_deposit_eq (o : Spec.Oracle) (ho : OracleAgrees o) :
    Spec.compute_domain p o Spec.DOMAIN_DEPOSIT =
      computeDomain EthCLSpecs.Fulu.Const.domainDeposit EthCLSpecs.Fulu.Const.genesisForkVersion
        (Vector.replicate 32 0) := by
  unfold Spec.compute_domain computeDomain Spec.compute_fork_data_root
  simp only [ho.forkData, hp.genesisForkVersion]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_cast, Vector.getElem_ofFn]
  have hz : Spec.Bytes32.zero = Vector.replicate 32 0 := rfl
  rw [hz, Vector.getElem_append]
  generalize computeForkDataRoot p.GENESIS_FORK_VERSION (Vector.replicate 32 0) = r
  by_cases h4 : i < 4
  · rw [dif_pos h4, if_pos h4]
    match i, h4 with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  · rw [dif_neg h4, if_neg h4]
    simp only [Vector.getElem_extract, vget]
    rw [getElem!_pos r.toArray (i - 4) (by simp; omega)]
    simp

include hp in
theorem is_valid_deposit_signature_eq (o : Spec.Oracle) (ho : OracleAgrees o)
    (d : EthCLSpecs.Fulu.PendingDeposit) :
    Spec.is_valid_deposit_signature p o d.pubkey d.withdrawalCredentials d.amount.toNat
        d.signature =
      EthCLSpecs.Fulu.isValidDepositSignature d.pubkey d.withdrawalCredentials d.amount
        d.signature := by
  unfold Spec.is_valid_deposit_signature EthCLSpecs.Fulu.isValidDepositSignature
    Spec.compute_signing_root computeSigningRoot
  rw [compute_domain_deposit_eq hp o ho]
  simp only [ho.signingData, ho.depositMessage, ho.verify, UInt64.ofNat_toNat]

omit [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
theorem findIdx_pubkey_list (l : List EthCLSpecs.Fulu.Validator) (pk : Spec.BLSPubkey) :
    l.findIdx? (fun v => v.pubkey == pk) =
      if pk ∈ (l.map absValidator).map (·.pubkey) then
        some (((l.map absValidator).map (·.pubkey)).idxOf pk)
      else none := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.findIdx?_cons]
    by_cases hv : v.pubkey = pk
    · simp [hv, absValidator]
    · have hv' : (v.pubkey == pk) = false := by simpa using hv
      rw [hv', ih]
      simp only [List.map_cons, List.mem_cons, absValidator, List.idxOf_cons]
      have hne : ¬ pk = v.pubkey := fun h => hv h.symm
      simp [hne, absValidator, hv']

omit [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
theorem findIdx_pubkey (vs : SSZList EthCLSpecs.Fulu.Validator
      EthCLSpecs.Fulu.Const.validatorRegistryLimit) (pk : Spec.BLSPubkey) :
    vs.findIdx? (fun v => v.pubkey == pk) =
      if pk ∈ (vs.toList.map absValidator).map (·.pubkey) then
        some (((vs.toList.map absValidator).map (·.pubkey)).idxOf pk)
      else none := by
  rw [← findIdx_pubkey_list]
  show vs.val.findIdx? _ = _
  rw [← List.findIdx?_toArray]

/-- The registry lists of a state have the same length. -/
def LensEq (e : EState) : Prop :=
  e.balances.val.size = e.validators.val.size ∧
    e.previousEpochParticipation.val.size = e.validators.val.size ∧
    e.currentEpochParticipation.val.size = e.validators.val.size ∧
    e.inactivityScores.val.size = e.validators.val.size

/-- `e'` is `e` with new registry lists. -/
def RegistryWrite (e e' : EState) : Prop :=
  ∃ V B P1 P2 I, e' = { e with
    validators := V
    balances := B
    previousEpochParticipation := P1
    currentEpochParticipation := P2
    inactivityScores := I }

omit [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
theorem RegistryWrite.refl (e : EState) : RegistryWrite e e :=
  ⟨_, _, _, _, _, rfl⟩

omit [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
theorem RegistryWrite.trans {e1 e2 e3 : EState} (h12 : RegistryWrite e1 e2)
    (h23 : RegistryWrite e2 e3) : RegistryWrite e1 e3 := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h12
  obtain ⟨V, B, P1, P2, I, rfl⟩ := h23
  exact ⟨V, B, P1, P2, I, rfl⟩

omit [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
theorem is_compounding_eq (wc : Spec.Bytes32) :
    Spec.is_compounding_withdrawal_credential wc =
      (EthCLSpecs.Fulu.credPrefix wc == EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix) := by
  unfold Spec.is_compounding_withdrawal_credential EthCLSpecs.Fulu.credPrefix vget
  rw [getElem!_pos wc.toArray 0 (by simp)]
  have : wc.toList.take 1 = [wc[0]] := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    have hn : n = 0 := by simp at h2; omega
    subst hn
    simp
  rw [this]
  simp [Spec.COMPOUNDING_WITHDRAWAL_PREFIX, EthCLSpecs.Fulu.Const.compoundingWithdrawalPrefix]

section Deposit
variable (hq : QueuesPresetAgrees p)
include hp hq

omit [HasherTag] [CryptoBackend] in
theorem get_validator_from_deposit_ok (pk : Spec.BLSPubkey) (wc : Spec.Bytes32) (amount : UInt64)
    {v' : Spec.Validator}
    (h : Spec.get_validator_from_deposit p pk wc amount.toNat = .ok v') :
    v' = absValidator (EthCLSpecs.Fulu.getValidatorFromDeposit pk wc amount) := by
  unfold Spec.get_validator_from_deposit at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  next m hm =>
  split at h
  · cases h
  next d hd =>
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rw [← hp.effectiveBalanceIncrementG] at hm
  have hm' := uint64Mod_ok hm
  rw [← hm'] at hd
  have hd' := uint64Sub_ok hd
  simp only [EthCLSpecs.Fulu.getValidatorFromDeposit, absValidator, umin_toNat, hd',
    EthCLSpecs.Fulu.getMaxEffectiveBalance, Spec.get_max_effective_balance,
    Spec.has_compounding_withdrawal_credential, EthCLSpecs.Fulu.hasCompoundingWithdrawalCredential,
    is_compounding_eq]
  split <;> simp [hq.maxEffectiveBalanceElectra, hq.minActivationBalance, far_toNat]

omit [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] hp hq in
theorem push_toList {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α) (h : xs.val.size < cap) :
    (xs.push x).toList = xs.toList ++ [x] := by
  simp [SSZList.push, h, SSZList.toList]

omit [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] hp hq in
theorem push_size {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α) (h : xs.val.size < cap) :
    (xs.push x).val.size = xs.val.size + 1 := by
  simp [SSZList.push, h]

omit [CryptoBackend] in
theorem add_validator_to_registry_etheorem (e : EState) (pk : Spec.BLSPubkey) (wc : Spec.Bytes32)
    (amount : UInt64) {s' : Spec.BeaconState} (hlens : LensEq e)
    (hroom : e.validators.val.size < EthCLSpecs.Fulu.Const.validatorRegistryLimit)
    (h : Spec.add_validator_to_registry p (absEState e) pk wc amount.toNat = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.addValidatorToRegistry (StateTransition := FuluRun) pk wc
        amount).run (pureState e) = .ok ((), pureState e') ∧ s' = absEState e' ∧
      RegistryWrite e e' ∧ LensEq e' ∧ e'.validators.val.size = e.validators.val.size + 1 := by
  obtain ⟨hb, hp1, hp2, hi⟩ := hlens
  unfold Spec.add_validator_to_registry Spec.get_index_for_new_validator at h
  obtain ⟨v', hv', h⟩ := Spec.specM_bind_ok h
  rw [get_validator_from_deposit_ok hp hq pk wc amount hv'] at h
  simp only [Spec.set_or_append_list, absEState_validators, absEState_balances,
    absEState_previous_epoch_participation, absEState_current_epoch_participation,
    absEState_inactivity_scores, List.length_map, SSZList.toList, Array.length_toList, hb, hp1, hp2,
    hi, beq_self_eq_true, if_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨{ e with
    validators := e.validators.push (EthCLSpecs.Fulu.getValidatorFromDeposit pk wc amount)
    balances := e.balances.push amount
    previousEpochParticipation := e.previousEpochParticipation.push 0
    currentEpochParticipation := e.currentEpochParticipation.push 0
    inactivityScores := e.inactivityScores.push 0 }, rfl, ?_, ⟨_, _, _, _, _, rfl⟩, ?_, ?_⟩
  · simp only [absEState]
    rw [push_toList _ _ hroom, push_toList _ _ (by omega), push_toList _ _ (by omega),
      push_toList _ _ (by omega), push_toList _ _ (by omega)]
    simp [SSZList.toList]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [push_size _ _ hroom] <;> first | rw [push_size _ _ (by omega)]; omega
  · exact push_size _ _ hroom

theorem apply_pending_deposit_etheorem (o : Spec.Oracle) (ho : OracleAgrees o) (e : EState)
    (d : EthCLSpecs.Fulu.PendingDeposit) {s' : Spec.BeaconState} (hlens : LensEq e)
    (hroom : e.validators.val.size < EthCLSpecs.Fulu.Const.validatorRegistryLimit)
    (h : Spec.apply_pending_deposit p o (absEState e) (absPendingDeposit d) = .ok s') :
    ∃ e', (EthCLSpecs.Fulu.applyPendingDeposit (StateTransition := FuluRun) d).run
        (pureState e) = .ok ((), pureState e') ∧ s' = absEState e' ∧
      RegistryWrite e e' ∧ LensEq e' ∧ e'.validators.val.size ≤ e.validators.val.size + 1 := by
  unfold Spec.apply_pending_deposit at h
  unfold EthCLSpecs.Fulu.applyPendingDeposit EthCLSpecs.Fulu.validatorIndexByPubkey?
  simp only [run_bind, run_get_gloas, except_bind_ok, view_uncachedBox, findIdx_pubkey]
  simp only [absEState_validators, absPendingDeposit] at h
  by_cases hm : d.pubkey ∈ (e.validators.toList.map absValidator).map (·.pubkey)
  · simp only [hm, not_true_eq_false, if_false, if_true] at h ⊢
    obtain ⟨bs, hbs, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    generalize hk : ((e.validators.toList.map absValidator).map (·.pubkey)).idxOf d.pubkey = k at hbs ⊢
    have hklt : k < e.validators.val.size := by
      rw [← hk]
      have := List.idxOf_lt_length_of_mem hm
      simpa using this
    have hk64 : k < 2 ^ 64 := Nat.lt_of_lt_of_le hklt
      (Nat.le_trans e.validators.property (Nat.le_of_lt hp.validatorRegistryLimit))
    have hofNat : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' hk64
    rw [← hofNat] at hbs
    obtain ⟨hrun, hbs'⟩ := increase_balance_etheorem e e (UInt64.ofNat k) d.amount hbs
    rw [run_bind, hrun, except_bind_ok]
    refine ⟨_, rfl, ?_, ⟨_, _, _, _, _, rfl⟩, ?_, by simp⟩
    · rw [hbs']; rfl
    · obtain ⟨hb, hp1, hp2, hi⟩ := hlens
      refine ⟨?_, hp1, hp2, hi⟩
      simp [hb]
  · simp only [hm, not_false_eq_true, if_true] at h ⊢
    rw [is_valid_deposit_signature_eq hp o ho d] at h
    by_cases hs : EthCLSpecs.Fulu.isValidDepositSignature d.pubkey d.withdrawalCredentials
        d.amount d.signature = true
    · simp only [hs, if_true] at h ⊢
      obtain ⟨e', hrun, hs', hw, hl, hsz⟩ :=
        add_validator_to_registry_etheorem hp hq e _ _ _ hlens hroom h
      exact ⟨e', hrun, hs', hw, hl, by omega⟩
    · simp only [hs, Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h
      exact ⟨e, rfl, rfl, .refl e, hlens, by omega⟩

end Deposit

/-- The eth1 bridge stop in Etheorem's `ppdLoop` (F2). pyspec has no such stop since Fulu. -/
def ppdBridge (v : EState) (deposit : EthCLSpecs.Fulu.PendingDeposit) : Bool :=
  deposit.slot > EthCLSpecs.Fulu.Const.genesisSlot && v.eth1DepositIndex < v.depositRequestsStartIndex

/-- Whether the validator of a deposit is withdrawn and whether it has exited. -/
def ppdStatus (v : EState) (deposit : EthCLSpecs.Fulu.PendingDeposit) (nextEpoch : UInt64) :
    Bool × Bool :=
  match v.validators.findIdx? (·.pubkey == deposit.pubkey) with
  | some vi =>
    let w := v.validators[vi]!
    (decide (w.withdrawableEpoch < nextEpoch), decide (w.exitEpoch < EthCLSpecs.Fulu.Const.farFutureEpoch))
  | none => (false, false)

/-- The loop body of Etheorem's `ppdLoop`. -/
def ppdStep (deposits : Array EthCLSpecs.Fulu.PendingDeposit) (finalizedSlot avail : UInt64)
    (nextEpoch : UInt64) (s : EthCLSpecs.Fulu.DepositScan) :
    FuluRun (Step EthCLSpecs.Fulu.DepositScan EthCLSpecs.Fulu.DepositScan) := do
  if s.ndi ≥ deposits.size then return .done s
  let state ← get
  let deposit := deposits[s.ndi]!
  if ppdBridge state.view deposit then return .done s
  if deposit.slot > finalizedSlot then return .done s
  if s.ndi ≥ EthCLSpecs.Fulu.Const.maxPendingDepositsPerEpoch then return .done s
  let advance (processed : UInt64) (postpone : Array EthCLSpecs.Fulu.PendingDeposit) :
      Step EthCLSpecs.Fulu.DepositScan EthCLSpecs.Fulu.DepositScan :=
    .next { s with ndi := s.ndi + 1, processed, postpone }
  let (isWithdrawn, isExited) := ppdStatus state.view deposit nextEpoch
  if isWithdrawn then EthCLSpecs.Fulu.applyPendingDeposit deposit; return advance s.processed s.postpone
  else if isExited then return advance s.processed (s.postpone.push deposit)
  else if s.processed + deposit.amount > avail then return .done { s with churnReached := true }
  else EthCLSpecs.Fulu.applyPendingDeposit deposit; return advance (s.processed + deposit.amount) s.postpone

theorem ppdLoop_eq (deposits : Array EthCLSpecs.Fulu.PendingDeposit) (fs avail ne : UInt64) :
    EthCLSpecs.Fulu.ppdLoop (StateTransition := FuluRun) deposits fs avail ne =
      fuelLoop (deposits.size + 1) {} {} (ppdStep deposits fs avail ne) := rfl

/-- `Spec.depCont` for any preset and any `apply_pending_deposit`. -/
def depContP (apd : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (avail : Nat) (d : Spec.PendingDeposit) (r : Spec.DepAcc) (ex wd : Bool) :
    Spec.SpecM (ForInStep Spec.DepAcc) :=
  if wd = true then do
    let T ← apd r.2.2.2.2 d
    pure (.yield ⟨r.1, r.2.1, r.2.2.1 + 1, r.2.2.2.1, T⟩)
  else if ex = true then pure (.yield ⟨r.1 ++ [d], r.2.1, r.2.2.1 + 1, r.2.2.2.1, r.2.2.2.2⟩)
  else do
    let x ← Spec.uint64Add r.2.2.2.1 d.amount
    if decide (x > avail) = true then
      pure (.done ⟨r.1, decide (x > avail), r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩)
    else do
      let proc ← Spec.uint64Add r.2.2.2.1 d.amount
      let T ← apd r.2.2.2.2 d
      pure (.yield ⟨r.1, decide (x > avail), r.2.2.1 + 1, proc, T⟩)

/-- `Spec.depBody` for any preset and any `apply_pending_deposit`. -/
def depBodyP (q : Spec.Preset)
    (apd : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (fs avail next : Nat) (d : Spec.PendingDeposit) (r : Spec.DepAcc) :
    Spec.SpecM (ForInStep Spec.DepAcc) :=
  if d.slot > fs then pure (.done r)
  else if r.2.2.1 ≥ q.MAX_PENDING_DEPOSITS_PER_EPOCH then pure (.done r)
  else if d.pubkey ∈ r.2.2.2.2.validators.map (·.pubkey) then do
    let v ← Spec.listGet r.2.2.2.2.validators
      ((r.2.2.2.2.validators.map (·.pubkey)).idxOf d.pubkey)
    depContP apd avail d r (decide (v.exit_epoch < Spec.FAR_FUTURE_EPOCH))
      (decide (v.withdrawable_epoch < next))
  else depContP apd avail d r false false

omit [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
/-- The reference `process_pending_deposits` with its loop body and its end named. -/
theorem process_pending_deposits_eqP (q : Spec.Preset)
    (apd : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (total_active_balance : Spec.Gwei) (s : Spec.BeaconState) :
    Spec.process_pending_deposits q total_active_balance apd s = (do
      let c ← Spec.get_current_epoch q s
      let next_epoch ← Spec.uint64Add c 1
      let cl ← Spec.get_activation_churn_limit q total_active_balance
      let avail ← Spec.uint64Add s.deposit_balance_to_consume cl
      let fs ← Spec.compute_start_slot_at_epoch q s.finalized_checkpoint.epoch
      let r ← forIn s.pending_deposits ⟨[], false, 0, 0, s⟩ (depBodyP q apd fs avail next_epoch)
      Spec.depFinish avail r) := by
  rfl

/-- Finding F2. Etheorem stops the deposit scan at a deposit with `slot > 0` when
`eth1_deposit_index < deposit_requests_start_index`. pyspec removed this stop in Fulu, so pyspec
goes on and can apply the deposit. -/
theorem ppdStep_bridge_stop (deposits : Array EthCLSpecs.Fulu.PendingDeposit)
    (fsU availU neU : UInt64) (sc : EthCLSpecs.Fulu.DepositScan) (e : EState)
    (hk : sc.ndi < deposits.size) (hslot : deposits[sc.ndi]!.slot > 0)
    (hidx : e.eth1DepositIndex < e.depositRequestsStartIndex) :
    (ppdStep deposits fsU availU neU sc).run (pureState e) = .ok (.done sc, pureState e) := by
  have hbr : ppdBridge e deposits[sc.ndi]! = true := by
    simp [ppdBridge, hslot, hidx, EthCLSpecs.Fulu.Const.genesisSlot]
  unfold ppdStep
  rw [if_neg (by omega)]
  simp only [run_bind, run_get_gloas, run_pure, except_bind_ok, view_uncachedBox, hbr, if_true]

/-- The reference loop state `acc` and the Etheorem scan `sc` on state `e` agree. -/
structure DepRel (e0 : EState) (acc : Spec.DepAcc) (sc : EthCLSpecs.Fulu.DepositScan)
    (e : EState) : Prop where
  postpone : acc.1 = sc.postpone.toList.map absPendingDeposit
  churn : acc.2.1 = sc.churnReached
  ndi : acc.2.2.1 = sc.ndi
  processed : acc.2.2.2.1 = sc.processed.toNat
  state : acc.2.2.2.2 = absEState e
  lens : LensEq e
  write : RegistryWrite e0 e
  size : e.validators.val.size ≤ e0.validators.val.size + sc.ndi
  postpone_le : sc.postpone.size ≤ sc.ndi

/-- How one reference loop step and one Etheorem `ppdStep` agree. -/
def StepOut (e0 : EState) (n k : Nat) (res : ForInStep Spec.DepAcc)
    (st : Step EthCLSpecs.Fulu.DepositScan EthCLSpecs.Fulu.DepositScan) (e' : EState) : Prop :=
  match res, st with
  | .done racc, .done sc' => DepRel e0 racc sc' e' ∧ sc'.ndi ≤ n
  | .yield acc', .next sc' => DepRel e0 acc' sc' e' ∧ sc'.ndi = k + 1 ∧ sc'.churnReached = false
  | _, _ => False

omit [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend] in
/-- The reference reads the same status as Etheorem's `ppdStatus`. -/
theorem depBody_status (q : Spec.Preset)
    (apd : Spec.BeaconState → Spec.PendingDeposit → Spec.SpecM Spec.BeaconState)
    (avail fs : Nat) (neU : UInt64) (d : EthCLSpecs.Fulu.PendingDeposit) (acc : Spec.DepAcc)
    (e : EState) (hstate : acc.2.2.2.2 = absEState e)
    (hs : ¬ (absPendingDeposit d).slot > fs) (hm : ¬ acc.2.2.1 ≥ q.MAX_PENDING_DEPOSITS_PER_EPOCH) :
    depBodyP q apd fs avail neU.toNat (absPendingDeposit d) acc =
      depContP apd avail (absPendingDeposit d) acc (ppdStatus e d neU).2 (ppdStatus e d neU).1 := by
  unfold depBodyP ppdStatus
  rw [if_neg hs, if_neg hm, hstate, absEState_validators, findIdx_pubkey]
  simp only [absPendingDeposit]
  by_cases hin : d.pubkey ∈ (e.validators.toList.map absValidator).map (·.pubkey)
  · rw [if_pos hin, if_pos hin]
    have hlt : ((e.validators.toList.map absValidator).map (·.pubkey)).idxOf d.pubkey <
        e.validators.val.size := by
      have := List.idxOf_lt_length_of_mem hin
      simpa using this
    generalize hidx : ((e.validators.toList.map absValidator).map (·.pubkey)).idxOf d.pubkey = i
      at hlt ⊢
    have hget : Spec.listGet (e.validators.toList.map absValidator) i =
        .ok (absValidator e.validators[i]!) := by
      have h1 : (e.validators.toList.map absValidator)[i]? = some (absValidator e.validators[i]!) := by
        rw [sszList_getElem!_val, getElem!_pos e.validators.val i hlt]
        simp [SSZList.toList, hlt]
      simp [Spec.listGet, h1, pure, Except.pure]
    rw [hget]
    simp only [bind, Except.bind, absValidator]
    have h2 : (Spec.FAR_FUTURE_EPOCH : Nat) = EthCLSpecs.Fulu.Const.farFutureEpoch.toNat := rfl
    simp [UInt64.lt_iff_toNat_lt, h2]
    rfl
  · rw [if_neg hin, if_neg hin]

theorem processPendingDeposits_run (e e' : EState)
    (sc : EthCLSpecs.Fulu.DepositScan)
    (hloop : (fuelLoop (e.pendingDeposits.toArray.size + 1) {} {}
      (ppdStep e.pendingDeposits.toArray
        (EthCLSpecs.Fulu.computeStartSlotAtEpoch e.finalizedCheckpoint.epoch)
        (e.depositBalanceToConsume + EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e))
        (EthCLSpecs.Fulu.currentEpochOf (pureState e) + 1))).run (pureState e) =
      .ok (sc, pureState e')) :
    (EthCLSpecs.Fulu.processPendingDeposits (StateTransition := FuluRun)).run (pureState e) =
      .ok ((), pureState { e' with
        pendingDeposits := sszOfArray (e.pendingDeposits.toArray.extract sc.ndi
          e.pendingDeposits.toArray.size ++ sc.postpone)
        depositBalanceToConsume := if sc.churnReached then
          (e.depositBalanceToConsume + EthCLSpecs.Fulu.getActivationExitChurnLimit (pureState e)) -
            sc.processed else 0 }) := by
  unfold EthCLSpecs.Fulu.processPendingDeposits
  simp only [run_bind, run_get_gloas, except_bind_ok]
  rw [ppdLoop_eq]
  erw [hloop]
  rfl

section Step
variable (hq : QueuesPresetAgrees p)
include hp hq

theorem ppdStep_ok (o : Spec.Oracle) (ho : OracleAgrees o)
    (deposits : Array EthCLSpecs.Fulu.PendingDeposit) (fsU availU neU : UInt64)
    (e0 e : EState) (k : Nat) (hk : k < deposits.size) (acc : Spec.DepAcc)
    (sc : EthCLSpecs.Fulu.DepositScan) (hrel : DepRel e0 acc sc e) (hndi : sc.ndi = k)
    (hch : sc.churnReached = false)
    (hroom : e0.validators.val.size + deposits.size ≤ EthCLSpecs.Fulu.Const.validatorRegistryLimit)
    (hbridge : deposits[k]!.slot = 0 ∨ e0.depositRequestsStartIndex ≤ e0.eth1DepositIndex)
    {res : ForInStep Spec.DepAcc}
    (h : depBodyP p (Spec.apply_pending_deposit p o) fsU.toNat availU.toNat neU.toNat
      (absPendingDeposit deposits[k]!) acc = .ok res) :
    ∃ st e', (ppdStep deposits fsU availU neU sc).run (pureState e) = .ok (st, pureState e') ∧
      StepOut e0 deposits.size k res st e' := by
  have hrel0 := hrel
  obtain ⟨hpost, hchurn, hn, hproc, hstate, hlens, hwrite, hsize, hple⟩ := hrel
  generalize hd : deposits[k]! = d at h hbridge
  have hbr : ppdBridge e d = false := by
    unfold ppdBridge
    obtain ⟨V, B, P1, P2, I, rfl⟩ := hwrite
    rcases hbridge with h0 | h0
    · simp [h0, EthCLSpecs.Fulu.Const.genesisSlot]
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      exact Nat.not_lt.mpr h0
  unfold ppdStep
  rw [if_neg (by omega)]
  simp only [run_bind, run_get_gloas, run_pure, except_bind_ok, view_uncachedBox, hndi, hd, hbr,
    Bool.false_eq_true, if_false]
  by_cases hs : d.slot > fsU
  · have hs' : (absPendingDeposit d).slot > fsU.toNat := UInt64.lt_iff_toNat_lt.mp hs
    unfold depBodyP at h
    simp only [hs', if_true, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨.done sc, e, by simp only [hs, if_true]; rfl, ?_⟩
    exact ⟨hrel0, by omega⟩
  have hs' : ¬ (absPendingDeposit d).slot > fsU.toNat := fun h' => hs (UInt64.lt_iff_toNat_lt.mpr h')
  simp only [hs, if_false, run_bind, run_pure, except_bind_ok]
  by_cases hmx : k ≥ EthCLSpecs.Fulu.Const.maxPendingDepositsPerEpoch
  · have hmx' : acc.2.2.1 ≥ p.MAX_PENDING_DEPOSITS_PER_EPOCH := by
      rw [hn, hndi, ← hq.maxPendingDepositsPerEpoch]; exact hmx
    unfold depBodyP at h
    simp only [hs', hmx', if_true, if_false, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨.done sc, e, by simp only [hmx, if_true]; rfl, ?_⟩
    exact ⟨hrel0, by omega⟩
  have hmx' : ¬ acc.2.2.1 ≥ p.MAX_PENDING_DEPOSITS_PER_EPOCH := by
    rw [hn, hndi, ← hq.maxPendingDepositsPerEpoch]; exact hmx
  simp only [hmx, if_false, run_bind, run_pure, except_bind_ok]
  rw [depBody_status p _ _ _ neU d acc e hstate hs' hmx'] at h
  unfold depContP at h
  have hroom1 : e.validators.val.size < EthCLSpecs.Fulu.Const.validatorRegistryLimit := by omega
  by_cases hwd : (ppdStatus e d neU).1 = true
  · simp only [hwd, if_true] at h ⊢
    obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [hstate] at hT
    obtain ⟨e1, hrun1, rfl, hw1, hl1, hsz1⟩ :=
      apply_pending_deposit_etheorem hp hq o ho e d hlens hroom1 hT
    refine ⟨.next { sc with ndi := k + 1 }, e1,
      by simp only [run_bind, hrun1, except_bind_ok, run_pure], ?_⟩
    refine ⟨⟨hpost, hchurn, by simp [hn, hndi], hproc, rfl, hl1, hwrite.trans hw1, ?_, ?_⟩, rfl, hch⟩
    · dsimp only; omega
    · dsimp only; omega
  have hwd' : (ppdStatus e d neU).1 = false := by simpa using hwd
  simp only [hwd', Bool.false_eq_true, if_false] at h ⊢
  by_cases hex : (ppdStatus e d neU).2 = true
  · simp only [hex, if_true, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    refine ⟨.next { sc with ndi := k + 1, postpone := sc.postpone.push d }, e, rfl, ?_⟩
    refine ⟨⟨?_, hchurn, by simp [hn, hndi], hproc, hstate, hlens, hwrite, ?_, ?_⟩, rfl, hch⟩
    · simp [hpost]
    · dsimp only; omega
    · simp only [Array.size_push]; omega
  have hex' : (ppdStatus e d neU).2 = false := by simpa using hex
  simp only [hex', Bool.false_eq_true, if_false] at h ⊢
  obtain ⟨x, hx, h⟩ := Spec.specM_bind_ok h
  rw [hproc] at hx
  have hx' := uint64Add_ok (a := sc.processed) (b := d.amount) hx
  by_cases hgt : sc.processed + d.amount > availU
  · have hgt' : decide (x > availU.toNat) = true := by
      simp only [decide_eq_true_eq]; rw [← hx']; exact UInt64.lt_iff_toNat_lt.mp hgt
    simp only [hgt', if_true, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨.done { sc with ndi := k, churnReached := true }, e,
      by simp only [hgt, if_true]; rfl, ?_⟩
    refine ⟨⟨hpost, rfl, hn.trans hndi, hproc, hstate, hlens, hwrite, by dsimp only; omega,
      by dsimp only; omega⟩, by dsimp only; omega⟩
  · have hgt' : decide (x > availU.toNat) = false := by
      simp only [decide_eq_false_iff_not]; rw [← hx']
      exact fun h' => hgt (UInt64.lt_iff_toNat_lt.mpr h')
    simp only [hgt', Bool.false_eq_true, if_false] at h
    obtain ⟨proc, hproc2, h⟩ := Spec.specM_bind_ok h
    rw [hproc, hx] at hproc2
    cases hproc2
    obtain ⟨T, hT, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [hstate] at hT
    obtain ⟨e1, hrun1, rfl, hw1, hl1, hsz1⟩ :=
      apply_pending_deposit_etheorem hp hq o ho e d hlens hroom1 hT
    refine ⟨.next { sc with ndi := k + 1, processed := sc.processed + d.amount }, e1,
      by simp only [hgt, if_false, run_bind, hrun1, except_bind_ok, run_pure], ?_⟩
    refine ⟨⟨hpost, by rw [hch], by simp [hn, hndi], hx'.symm, rfl, hl1, hwrite.trans hw1, ?_, ?_⟩,
      rfl, hch⟩
    · dsimp only; omega
    · dsimp only; omega

theorem ppdLoop_fuel (o : Spec.Oracle) (ho : OracleAgrees o)
    (deposits : Array EthCLSpecs.Fulu.PendingDeposit) (fsU availU neU : UInt64) (e0 : EState)
    (hroom : e0.validators.val.size + deposits.size ≤ EthCLSpecs.Fulu.Const.validatorRegistryLimit)
    (hbridge : ∀ k < deposits.size,
      deposits[k]!.slot = 0 ∨ e0.depositRequestsStartIndex ≤ e0.eth1DepositIndex) :
    ∀ (j k : Nat) (acc : Spec.DepAcc) (sc : EthCLSpecs.Fulu.DepositScan) (e : EState)
      {racc : Spec.DepAcc}, k + j = deposits.size → DepRel e0 acc sc e → sc.ndi = k →
      sc.churnReached = false →
      forIn ((deposits.toList.drop k).map absPendingDeposit) acc
          (depBodyP p (Spec.apply_pending_deposit p o) fsU.toNat availU.toNat neU.toNat) =
        .ok racc →
      ∃ sc' e', (fuelLoop (j + 1) sc {} (ppdStep deposits fsU availU neU)).run (pureState e) =
          .ok (sc', pureState e') ∧ DepRel e0 racc sc' e' ∧ sc'.ndi ≤ deposits.size := by
  intro j
  induction j with
  | zero =>
    intro k acc sc e racc hk hrel hndi hch h
    have hdrop : deposits.toList.drop k = [] := by simp; omega
    rw [hdrop] at h
    simp only [List.map_nil, List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨sc, e, ?_, hrel, by omega⟩
    rw [fuelLoop_succ_run]
    unfold ppdStep
    rw [if_pos (by omega)]
    rfl
  | succ j ih =>
    intro k acc sc e racc hk hrel hndi hch h
    have hlt : k < deposits.size := by omega
    have hdrop : deposits.toList.drop k = deposits[k]! :: deposits.toList.drop (k + 1) := by
      have hlt' : k < deposits.toList.length := by simpa using hlt
      rw [List.drop_eq_getElem_cons hlt', getElem!_pos deposits k hlt, Array.getElem_toList]
    rw [hdrop, List.map_cons, List.forIn_cons] at h
    obtain ⟨res, hres, h⟩ := Spec.specM_bind_ok h
    obtain ⟨st, e1, hrun1, hout⟩ := ppdStep_ok hp hq o ho deposits fsU availU neU e0 e k hlt acc sc
      hrel hndi hch hroom (hbridge k hlt) hres
    rw [fuelLoop_succ_run, hrun1, except_bind_ok]
    cases res with
    | done racc' =>
      cases st with
      | done sc' =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨sc', e1, rfl, hout.1, hout.2⟩
      | next sc' => exact hout.elim
    | yield acc' =>
      cases st with
      | done sc' => exact hout.elim
      | next sc' =>
        obtain ⟨hrel1, hndi1, hch1⟩ := hout
        exact ih (k + 1) acc' sc' e1 (by omega) hrel1 hndi1 hch1 h

/-- The reference `process_pending_deposits` equals Etheorem's. -/
theorem process_pending_deposits_etheorem {f : Spec.FuluConfig} (hf : FuluChurnAgrees p f)
    (o : Spec.Oracle) (ho : OracleAgrees o) (e : EState) {tab : Nat} {s' : Spec.BeaconState}
    (htab : Spec.get_total_active_balance p (absEState e) = .ok tab) (hlens : LensEq e)
    (hroom : e.validators.val.size + e.pendingDeposits.val.size ≤
      EthCLSpecs.Fulu.Const.validatorRegistryLimit)
    (hbridge : ∀ d ∈ e.pendingDeposits.val.toList,
      d.slot = 0 ∨ e.depositRequestsStartIndex ≤ e.eth1DepositIndex)
    (h : Spec.process_pending_deposits p (Spec.fuluTab p f tab) (Spec.apply_pending_deposit p o)
      (absEState e) = .ok s') :
    ∃ e' : EState,
      (EthCLSpecs.Fulu.processPendingDeposits (StateTransition := FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ s' = absEState e' := by
  have htab' := get_total_active_balance_ok hp e htab
  rw [process_pending_deposits_eqP] at h
  rw [get_current_epoch_eq hp] at h
  obtain ⟨c, hc, h⟩ := Spec.specM_bind_ok h
  cases hc
  obtain ⟨ne, hne, h⟩ := Spec.specM_bind_ok h
  have hne' := uint64Add_ok (a := EthCLSpecs.Fulu.currentEpochOf (pureState e)) (b := 1)
    (by simpa using hne)
  obtain ⟨cl, hcl, h⟩ := Spec.specM_bind_ok h
  rw [← htab'] at hcl
  have hcl' := get_activation_churn_limit_ok hp hf e hcl
  obtain ⟨av, hav, h⟩ := Spec.specM_bind_ok h
  rw [absEState_deposit_balance_to_consume, ← hcl'] at hav
  have hav' := uint64Add_ok hav
  obtain ⟨fs, hfs, h⟩ := Spec.specM_bind_ok h
  have hfs' := compute_start_slot_at_epoch_ok hp _ hfs
  obtain ⟨racc, hloop, h⟩ := Spec.specM_bind_ok h
  generalize hdeps : e.pendingDeposits.toArray = deposits
  have hpd : (absEState e).pending_deposits = (deposits.toList.drop 0).map absPendingDeposit := by
    simp [← hdeps, SSZList.toArray, SSZList.toList]
  rw [hpd, ← hne', ← hav', ← hfs'] at hloop
  have hsize : deposits.size = e.pendingDeposits.val.size := by rw [← hdeps]
  have hrel0 : DepRel e ⟨[], false, 0, 0, absEState e⟩ {} e :=
    ⟨rfl, rfl, rfl, rfl, rfl, hlens, .refl e, by simp, by simp⟩
  obtain ⟨sc, e1, hrun, hrel, hndi⟩ := ppdLoop_fuel hp hq o ho deposits _ _ _ e (by omega)
    (by
      intro k hk
      apply hbridge
      rw [← hdeps] at hk ⊢
      rw [getElem!_pos _ k hk]
      simp [SSZList.toArray])
    deposits.size 0 _ {} e (by omega) hrel0 rfl rfl hloop
  obtain ⟨hpost, hchurn, hn, hproc, hstate, hlens1, hwrite, -, hple⟩ := hrel
  subst hdeps
  have hrun' := processPendingDeposits_run e e1 sc hrun
  have he1pd : e1.pendingDeposits = e.pendingDeposits := by
    obtain ⟨V, B, P1, P2, I, rfl⟩ := hwrite; rfl
  have harr : (e.pendingDeposits.toArray.extract sc.ndi e.pendingDeposits.toArray.size ++
      sc.postpone).size ≤ EthCLSpecs.Fulu.Const.pendingDepositsLimit := by
    have := e.pendingDeposits.property
    simp only [Array.size_append, Array.size_extract, SSZList.toArray]
    omega
  refine ⟨_, hrun', ?_⟩
  unfold Spec.depFinish at h
  rw [hstate] at h
  have hpend : (absEState e1).pending_deposits.drop racc.2.2.1 ++ racc.1 = ((sszOfArray (e.pendingDeposits.toArray.extract sc.ndi
          e.pendingDeposits.toArray.size ++ sc.postpone) : SSZList _
            EthCLSpecs.Fulu.Const.pendingDepositsLimit).toList.map absPendingDeposit) := by
    simp only [sszOfArray, harr, dif_pos, SSZList.toList, Array.toList_append, List.map_append,
      hpost, hn, absEState_pending_deposits, he1pd]
    simp [SSZList.toArray, Array.toList_extract, List.map_drop]
    rw [List.take_of_length_le (by simp)]
  by_cases hc : sc.churnReached = true
  · rw [hchurn, hc] at h
    simp only [if_true] at h
    obtain ⟨x, hx, h⟩ := Spec.specM_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [hproc, ← hav'] at hx
    have hx' := uint64Sub_ok hx
    rw [hpend, ← hx']
    simp only [hc, if_true]
    rfl
  · have hc' : sc.churnReached = false := by simpa using hc
    rw [hchurn, hc'] at h
    simp only [Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [hpend]
    simp only [hc', Bool.false_eq_true, if_false]
    rfl

end Step

end Body
end EpochProofs.Etheorem.Fulu
