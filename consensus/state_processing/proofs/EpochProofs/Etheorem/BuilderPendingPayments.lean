import EpochProofs.Equiv.BuilderPendingPayments
import EthCLSpecs.Proofs.Gloas.BuilderPendingPayments

/-!
# The reference `process_builder_pending_payments` equals Etheorem's

The main theorem is `builder_pending_payments_etheorem`. Etheorem
(https://github.com/etheorem/etheorem) is a Lean spec that passes the EF vectors.
`lighthouse_builder_pending_payments_etheorem` joins the theorem to
`builder_pending_payments_equiv`, so Lighthouse equals Etheorem.

Etheorem uses `UInt64` and the reference uses `Nat`. The `abs*` functions read an Etheorem
value as a reference value. `Agrees` relates the two fields that the step reads and writes.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [HasherTag]

abbrev EWithdrawal := EthCLSpecs.Gloas.BuilderPendingWithdrawal
abbrev EPayment := EthCLSpecs.Gloas.BuilderPendingPayment
abbrev EState := EthCLSpecs.Gloas.BeaconState

def absWithdrawal (w : EWithdrawal) : Spec.BuilderPendingWithdrawal :=
  { fee_recipient := w.feeRecipient
    amount := w.amount.toNat
    builder_index := w.builderIndex.toNat }

def absPayment (p : EPayment) : Spec.BuilderPendingPayment :=
  { weight := p.weight.toNat
    withdrawal := absWithdrawal p.withdrawal
    proposer_index := p.proposerIndex.toNat }

/-- The builder payment fields of the two states agree. -/
def Agrees (e : EState) (s : Spec.BeaconState) : Prop :=
  s.builder_pending_payments = e.builderPendingPayments.toList.map absPayment ∧
    s.builder_pending_withdrawals = e.builderPendingWithdrawals.val.toList.map absWithdrawal

/-- `get_total_active_balance` in Etheorem. -/
def totalActiveBalance (e : EState) : Nat :=
  (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat

omit [HasherTag] in
theorem absPayment_default : absPayment (default : EPayment) = Spec.BuilderPendingPayment.empty :=
  rfl

theorem quorum_toNat (e : EState) (hslots : 6 ≤ EthCLSpecs.Gloas.Const.slotsPerEpoch) :
    (builderPaymentQuorum e).toNat =
      totalActiveBalance e / EthCLSpecs.Gloas.Const.slotsPerEpoch * 6 / 10 := by
  have hlt := EthCLSpecs.Gloas.Const.slotsPerEpochLt
  unfold builderPaymentQuorum totalActiveBalance
  have htab := UInt64.toNat_lt (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e))
  have hmul : (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat /
      EthCLSpecs.Gloas.Const.slotsPerEpoch * 6 < 2 ^ 64 :=
    calc _ ≤ (EthCLSpecs.Gloas.getTotalActiveBalance (pureState e)).toNat /
            EthCLSpecs.Gloas.Const.slotsPerEpoch * EthCLSpecs.Gloas.Const.slotsPerEpoch :=
          Nat.mul_le_mul_left _ hslots
      _ ≤ _ := Nat.div_mul_le_self _ _
      _ < 2 ^ 64 := htab
  rw [UInt64.toNat_div, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' hlt]
  have h6 : EthCLSpecs.Gloas.Const.builderPaymentThresholdNumerator.toNat = 6 := rfl
  have h10 : EthCLSpecs.Gloas.Const.builderPaymentThresholdDenominator.toNat = 10 := rfl
  rw [h6, h10, Nat.mod_eq_of_lt hmul]

theorem window_toList (e : EState) :
    (expectedPaymentWindow e).toList =
      e.builderPendingPayments.toList.drop EthCLSpecs.Gloas.Const.slotsPerEpoch ++
        List.replicate EthCLSpecs.Gloas.Const.slotsPerEpoch default := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [Vector.length_toList] at h1
    rw [Vector.getElem_toList]
    by_cases hi : i < EthCLSpecs.Gloas.Const.slotsPerEpoch
    · have := expectedPaymentWindow_get_lt e i hi
      unfold vget at this
      rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ _ (by simp; omega)] at this
      simp only [Vector.getElem_toArray] at this
      rw [this, List.getElem_append_left (by simp; omega)]
      simp [Nat.add_comm]
    · have := expectedPaymentWindow_get_upper e i (by omega) h1
      unfold vget at this
      rw [getElem!_pos _ i (by simp; omega)] at this
      simp only [Vector.getElem_toArray] at this
      rw [this, List.getElem_append_right (by simp; omega)]
      simp

theorem qualifying_eq (e : EState) (q : Nat) (hq : (builderPaymentQuorum e).toNat = q) :
    (qualifyingBuilderWithdrawals e).map absWithdrawal =
      (((e.builderPendingPayments.toList.map absPayment).take
          EthCLSpecs.Gloas.Const.slotsPerEpoch).filter (·.weight ≥ q)).map (·.withdrawal) := by
  have hrange : (List.range EthCLSpecs.Gloas.Const.slotsPerEpoch).map
      (vget e.builderPendingPayments) =
        e.builderPendingPayments.toList.take EthCLSpecs.Gloas.Const.slotsPerEpoch := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_take, vget]
      rw [getElem!_pos _ _ (by simp; omega)]
      simp
  simp only [qualifyingBuilderWithdrawals, ← List.map_take, ← hrange, List.map_map,
    List.filter_map]
  simp [Function.comp_def, absPayment, ← hq, UInt64.le_iff_toNat_le]

/-- The reference equals Etheorem.

Both runs succeed. Their results agree on the builder payment fields, and every other field
keeps its value.

`hslots`: the two presets have the same `SLOTS_PER_EPOCH`. `hslots6`: `SLOTS_PER_EPOCH ≥ 6`
(both presets), so the quorum does not overflow. `hfits`: the new withdrawals fit under the
list limit. Etheorem's `SSZList.push` drops an item past the limit, and the spec raises an
error. -/
theorem builder_pending_payments_etheorem (p : Spec.Preset)
    (hslots : EthCLSpecs.Gloas.Const.slotsPerEpoch = p.SLOTS_PER_EPOCH)
    (hslots6 : 6 ≤ p.SLOTS_PER_EPOCH)
    (e : EState) (s : Spec.BeaconState) (hagree : Agrees e s)
    (hfits : e.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e).length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit) :
    ∃ e' s',
      runPure (EthCLSpecs.Gloas.processBuilderPendingPayments (StateTransition := GloasRun)) e =
          .ok ((), e') ∧
        Spec.process_builder_pending_payments p (totalActiveBalance e) s = .ok s' ∧
        Agrees e' s' ∧
        e' = { e with builderPendingPayments := e'.builderPendingPayments,
                      builderPendingWithdrawals := e'.builderPendingWithdrawals } ∧
        s' = { s with builder_pending_payments := s'.builder_pending_payments,
                      builder_pending_withdrawals := s'.builder_pending_withdrawals } := by
  obtain ⟨hpay, hwd⟩ := hagree
  have hwf : s.WellFormed p := by
    simp [Spec.BeaconState.WellFormed, hpay, hslots]
  have htab : totalActiveBalance e < Spec.UINT64_SIZE := UInt64.toNat_lt _
  have hq := quorum_toNat e (hslots ▸ hslots6)
  refine ⟨_, Spec.builderPendingPaymentsResult p
      (totalActiveBalance e / p.SLOTS_PER_EPOCH * 6 / 10) s,
    processBuilderPendingPayments_run_of_fits e hfits, ?_, ?_, ?_, ?_⟩
  · rw [Spec.process_builder_pending_payments_eq p _ s hwf,
      Spec.get_builder_payment_quorum_threshold_ok p _ hslots6 htab]
    rfl
  · rw [hslots] at hq
    refine ⟨?_, ?_⟩
    · simp only [Spec.builderPendingPaymentsResult, hpay, window_toList, List.map_append,
        List.map_drop, List.map_replicate, absPayment_default, hslots]
    · simp only [Spec.builderPendingPaymentsResult, hwd, hpay, Array.toList_append,
        List.map_append, qualifying_eq e _ hq, hslots]
  · rfl
  · rfl

open Aeneas Aeneas.Std Aeneas.Std.WP in
/-- Lighthouse equals Etheorem.

Lighthouse returns `Ok`. Etheorem's run succeeds, and the two results agree on the builder
payment fields.

`htab`: Lighthouse reads the total active balance from its cache. The cache equals
`get_total_active_balance`. -/
theorem lighthouse_builder_pending_payments_etheorem (p : Spec.Preset)
    (hslots : EthCLSpecs.Gloas.Const.slotsPerEpoch = p.SLOTS_PER_EPOCH)
    (hslots6 : 6 ≤ p.SLOTS_PER_EPOCH)
    (total_active_balance slots_per_epoch : U64) (spe : Usize)
    (hslots_lh : slots_per_epoch.val = p.SLOTS_PER_EPOCH) (hspe : spe.val = p.SLOTS_PER_EPOCH)
    (payments : Slice LhPayment) (withdrawals : List LhWithdrawal)
    (e : EState) (hagree : Agrees e (absState (withdrawals, payments.val)))
    (htab : total_active_balance.val = totalActiveBalance e)
    (hfits : e.builderPendingWithdrawals.val.size + (qualifyingBuilderWithdrawals e).length ≤
      EthCLSpecs.Gloas.Const.builderPendingWithdrawalsLimit) :
    lighthouseBuilderPendingPayments total_active_balance slots_per_epoch spe payments withdrawals
      ⦃ r => ∃ res e', r = .Ok res ∧
        runPure (EthCLSpecs.Gloas.processBuilderPendingPayments (StateTransition := GloasRun)) e =
          .ok ((), e') ∧
        Agrees e' (absState res) ⦄ := by
  have hlen : payments.val.length = 2 * p.SLOTS_PER_EPOCH := by
    have h := congrArg List.length hagree.1
    simp only [absState, List.length_map, Vector.length_toList] at h
    omega
  obtain ⟨e', s', hrun, hspec, hag, -, -⟩ :=
    builder_pending_payments_etheorem p hslots hslots6 e _ hagree hfits
  apply spec_mono (builder_pending_payments_equiv p total_active_balance slots_per_epoch spe
    hslots_lh hspe payments withdrawals hlen)
  intro r hr
  rw [htab, hspec] at hr
  cases r with
  | Err err => simp [absResult] at hr
  | Ok res =>
    simp only [absResult, Except.ok.injEq] at hr
    exact ⟨res, e', rfl, hrun, hr ▸ hag⟩

end EpochProofs.Etheorem
