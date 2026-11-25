import EpochProofs.Sanity.Invariants.LighthouseTailNF
import EpochProofs.Spec.PresetCfg

/-!
# The Lighthouse tail in the common form

`lighthouseFullTail_nf` shows that `lighthouseFullTail` gives the same `ok` results as the first
pass followed by `stepsAfterSinglePassCommonOrder`. The deposit plan does not depend on the pass,
so it moves after the first pass. The full pass splits into the first pass and the top-up and
update pass, which is a fold over the validator indices.
-/

namespace EpochProofs.Spec

/-- The steps of `lighthouseFullTailG` after the pass, for a plan and the result of the pass. -/
def lighthouseAfterPassG [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState)
    (s : BeaconState)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState := do
  let s1 ← process_eth1_data_reset P (s.withRowsChurn x.1 x.2)
  let s2 := { s1 with
    pending_deposits := s.pending_deposits.drop plan.next_deposit_index ++ plan.postponed
    deposit_balance_to_consume := plan.deposit_balance_to_consume }
  let s3 ← plan.new_validator_deposits.foldlM (apply_pending_deposit P o) s2
  let s4 ← (List.range' s2.validators.length (s3.validators.length - s2.validators.length)).foldlM
    updateEffectiveBalanceAt s3
  let s5 ← process_pending_consolidations P s4
  let s6 ← (validatorsInConsolidations s).foldlM updateEffectiveBalanceAt s5
  K s6

/-- The steps of `lighthouseFullTail` after the pass. -/
def lighthouseAfterPass [CurrentPreset] (o : Oracle) (s : BeaconState) (total_active_balance : Gwei)
    (plan : LighthouseDepositPlan) (x : (Epoch × Gwei) × List Row) : SpecM BeaconState :=
  lighthouseAfterPassG o (gloasFin o total_active_balance) s plan x

/-- `lighthouseFullTailG` once the context values are known. -/
theorem lighthouseFullTailG_eq [CurrentPreset] (o : Oracle) (rt : Gwei → Gwei)
    (fin : Gwei → BeaconState → SpecM BeaconState) (s1 : BeaconState) (current_epoch : Epoch)
    (total_active_balance : Gwei) (rctx : RewardsContext) (adjusted per : Gwei)
    (downward upward : Uint64)
    (hcur : get_current_epoch P s1 = .ok current_epoch)
    (htab : get_total_active_balance P s1 = .ok total_active_balance)
    (hctx : rewardsContextOf P total_active_balance s1 = .ok rctx)
    (hpre : slashingsPreamble P total_active_balance s1.slashings =
      .ok (adjusted, per))
    (hthr : hysteresisThresholds P = .ok (downward, upward)) :
    lighthouseFullTailG o rt fin s1 =
      (lighthouseDepositPlan s1 (rt total_active_balance) current_epoch >>=
      fun plan => passM (fun churn r => lighthouseValidatorStep P
          (lighthouseContextOf s1 (rt total_active_balance) current_epoch rctx per) downward upward
          ⟨lighthouseBaseReward total_active_balance r, plan.topups.getD r.index 0,
            decide (r.index ∈ validatorsInConsolidations s1)⟩ churn r)
        (s1.earliest_exit_epoch, s1.exit_balance_to_consume) (rowsOf s1) >>=
      lighthouseAfterPassG o (fin total_active_balance) s1 plan) := by
  unfold lighthouseFullTailG
  rw [hcur, ok_bind', htab, ok_bind', hctx, ok_bind', hpre, ok_bind']
  simp only [hthr, ok_bind']
  rfl

/-- The deposit decisions of the plan. -/
def planDec [CurrentPreset] (s : BeaconState) (total_active_balance : Gwei) (current_epoch : Epoch) :
    SpecM (Nat × Gwei × List Bool) := do
  let finalized_slot ←
    compute_start_slot_at_epoch P s.finalized_checkpoint.epoch
  depositDecisions P finalized_slot s.deposit_balance_to_consume
    (← get_activation_churn_limit P total_active_balance)
    ((s.pending_deposits.take P.MAX_PENDING_DEPOSITS_PER_EPOCH).map
      (lighthouseDepositView s current_epoch))

/-- The handled deposits for a decision. -/
def handledOfDec (s : BeaconState) (dec : Nat × Gwei × List Bool) :
    List (PendingDeposit × Bool) :=
  (s.pending_deposits.take dec.1).zip dec.2.2

/-- The top-up sums for a decision. -/
def sumsOfDec (s : BeaconState) (dec : Nat × Gwei × List Bool) : SpecM (List Gwei) :=
  (knownTopups (s.validators.map (·.pubkey)) (handledOfDec s dec)).foldlM
    (fun acc x => increase_balance acc x.1 x.2) (List.replicate s.validators.length 0)

/-- The plan for a decision and its top-up sums. -/
def planOf (s : BeaconState) (dec : Nat × Gwei × List Bool) (sums : List Gwei) :
    LighthouseDepositPlan :=
  ⟨dec.1, dec.2.1, sums, ((handledOfDec s dec).filter (·.2)).map (·.1),
    newDeposits (s.validators.map (·.pubkey)) (handledOfDec s dec)⟩

/-- `lighthouseDepositPlan` is the decisions, then the top-up sums. -/
theorem lighthouseDepositPlan_eq [CurrentPreset] (s : BeaconState) (total_active_balance : Gwei)
    (current_epoch : Epoch) :
    lighthouseDepositPlan s total_active_balance current_epoch =
      (planDec s total_active_balance current_epoch >>= fun dec =>
        planOf s dec <$> sumsOfDec s dec) := by
  unfold lighthouseDepositPlan planDec
  cases compute_start_slot_at_epoch P s.finalized_checkpoint.epoch with
  | error e => rfl
  | ok fs =>
    simp only [ok_bind']
    cases get_activation_churn_limit P total_active_balance with
    | error e => rfl
    | ok cl =>
      simp only [ok_bind']
      cases depositDecisions P fs s.deposit_balance_to_consume cl
          ((s.pending_deposits.take P.MAX_PENDING_DEPOSITS_PER_EPOCH).map
            (lighthouseDepositView s current_epoch)) with
      | error e => rfl
      | ok dec =>
        obtain ⟨next, dbtc, pp⟩ := dec
        simp only [ok_bind']
        rw [lighthousePlan_fold_eq]
        unfold sumsOfDec handledOfDec
        cases (knownTopups (s.validators.map (·.pubkey))
            ((s.pending_deposits.take next).zip pp)).foldlM
            (fun acc x => increase_balance acc x.1 x.2) (List.replicate s.validators.length 0) with
        | error e => rfl
        | ok sums => rfl

/-- The steps of `stepsAfterSinglePassCommonOrder` after the top-up sums. -/
def nfAfterG [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState) (s1 S4 : BeaconState)
    (dec : Nat × Gwei × List Bool) (sums : List Gwei) : SpecM BeaconState := do
  let handled := handledOfDec s1 dec
  let pubkeys := s1.validators.map (·.pubkey)
  let n := s1.validators.length
  let named := validatorsInConsolidations s1
  let t1 ← addSums S4 sums
  let t2 ← ((List.range n).filter (fun i => !decide (i ∈ named))).foldlM updateEffectiveBalanceAt t1
  let t3 ← process_eth1_data_reset P t2
  let t4 ← writeQueue (s1.pending_deposits.drop dec.1 ++ (handled.filter (·.2)).map (·.1))
    dec.2.1 t3
  let t5 ← (newDeposits pubkeys handled).foldlM (apply_pending_deposit P o) t4
  let t6 ← (List.range' n (t5.validators.length - n)).foldlM updateEffectiveBalanceAt t5
  let t7 ← process_pending_consolidations P t6
  let t8 ← named.foldlM updateEffectiveBalanceAt t7
  K t8

/-- `tailNFG` is the decisions, the top-up sums, then `nfAfterG`. -/
theorem tailNFG_eq [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState) (s1 S4 : BeaconState)
    (total_active_balance : Gwei) (current_epoch : Epoch) :
    tailNFG o K s1 S4 total_active_balance current_epoch =
      (planDec s1 total_active_balance current_epoch >>= fun dec =>
        sumsOfDec s1 dec >>= fun sums => nfAfterG o K s1 S4 dec sums) := by
  unfold tailNFG planDec
  cases compute_start_slot_at_epoch P s1.finalized_checkpoint.epoch with
  | error e => rfl
  | ok fs =>
    simp only [ok_bind']
    cases get_activation_churn_limit P total_active_balance with
    | error e => rfl
    | ok cl =>
      simp only [ok_bind']
      cases depositDecisions P fs s1.deposit_balance_to_consume cl
          ((s1.pending_deposits.take P.MAX_PENDING_DEPOSITS_PER_EPOCH).map
            (lighthouseDepositView s1 current_epoch)) with
      | error e => rfl
      | ok dec => rfl

/-! ## Moving the plan after the first pass -/

/-- Two computations that do not depend on each other give the same `ok` results in either
order. -/
theorem sameResultOrBothFail_bind_swap {α β γ : Type} (x : SpecM α) (y : SpecM β) (k : α → β → SpecM γ) :
    SameResultOrBothFail (x >>= fun a => y >>= fun b => k a b) (y >>= fun b => x >>= fun a => k a b) := by
  intro v
  cases x <;> cases y <;> simp [bind, Except.bind]

/-- `lighthouseRowStep` keeps the row key. -/
theorem lighthouseRowStep_rowKey [CurrentPreset] (ctx : LighthouseStepContext) (base : Gwei)
    (churn : Epoch × Gwei) (r : Row)
    (x : (Epoch × Gwei) × Row) (h : lighthouseRowStep P ctx base churn r = .ok x) :
    rowKey x.2 = rowKey r := by
  unfold lighthouseRowStep at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h; rfl)

/-! ## After the pass -/

/-- The steps of `lighthouseAfterPass` from the state after the pass. -/
def lighthouseRest [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState)
    (s : BeaconState)
    (plan : LighthouseDepositPlan) (T : BeaconState) : SpecM BeaconState := do
  let s1 ← process_eth1_data_reset P T
  let s2 := { s1 with
    pending_deposits := s.pending_deposits.drop plan.next_deposit_index ++ plan.postponed
    deposit_balance_to_consume := plan.deposit_balance_to_consume }
  let s3 ← plan.new_validator_deposits.foldlM (apply_pending_deposit P o) s2
  let s4 ← (List.range' s2.validators.length (s3.validators.length - s2.validators.length)).foldlM
    updateEffectiveBalanceAt s3
  let s5 ← process_pending_consolidations P s4
  let s6 ← (validatorsInConsolidations s).foldlM updateEffectiveBalanceAt s5
  K s6

/-- The steps of `nfAfterG` from the state after the updates of the validators that are not
named. -/
def nfRest [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState) (s1 : BeaconState)
    (dec : Nat × Gwei × List Bool) (t2 : BeaconState) : SpecM BeaconState := do
  let handled := handledOfDec s1 dec
  let n := s1.validators.length
  let t3 ← process_eth1_data_reset P t2
  let t4 ← writeQueue (s1.pending_deposits.drop dec.1 ++ (handled.filter (·.2)).map (·.1))
    dec.2.1 t3
  let t5 ← (newDeposits (s1.validators.map (·.pubkey)) handled).foldlM
    (apply_pending_deposit P o) t4
  let t6 ← (List.range' n (t5.validators.length - n)).foldlM updateEffectiveBalanceAt t5
  let t7 ← process_pending_consolidations P t6
  let t8 ← (validatorsInConsolidations s1).foldlM updateEffectiveBalanceAt t7
  K t8

/-- With a state of `n` validators, the two rests are equal. -/
theorem lighthouseRest_eq_nfRest [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState)
    (s1 : BeaconState)
    (dec : Nat × Gwei × List Bool) (sums : List Gwei) (T : BeaconState)
    (hT : T.validators.length = s1.validators.length) :
    lighthouseRest o K s1 (planOf s1 dec sums) T = nfRest o K s1 dec T := by
  unfold lighthouseRest nfRest
  cases he : process_eth1_data_reset P T with
  | error e => rfl
  | ok t3 =>
    have hv := (eth1_frame T t3 he).1
    simp only [ok_bind', writeQueue]
    have hl : t3.validators.length = s1.validators.length := by rw [hv, hT]
    simp only [hl]
    rfl

/-- A fold of top-ups keeps the validators. -/
theorem increaseFold_validators (td : Nat → Gwei) :
    ∀ (l : List Nat) (T T' : BeaconState),
      l.foldlM (fun t i => increaseAt i (td i) t) T = .ok T' → T'.validators = T.validators
  | [], T, T', h => by cases h; rfl
  | i :: l, T, T', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨T1, h1, h⟩ := specM_bind_ok h
    rw [increaseFold_validators td l T1 T' h, increaseAt_validators h1]

/-- A fold of effective balance updates keeps the number of validators. -/
theorem ebFold_length [CurrentPreset] :
    ∀ (l : List Nat) (T T' : BeaconState),
      l.foldlM updateEffectiveBalanceAt T = .ok T' → T'.validators.length = T.validators.length
  | [], T, T', h => by cases h; rfl
  | i :: l, T, T', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨T1, h1, h⟩ := specM_bind_ok h
    obtain ⟨_, _, _, -, -, -, rfl⟩ := (updateEffectiveBalanceAt_ok T T1 i).mp h1
    rw [ebFold_length l _ T' h, setEB_length]

/-! ## The main theorem -/

/-- After the first pass, the second pass and the rest of `lighthouseFullTailG` give the same `ok`
results as `nfAfterG`. -/
theorem lighthouseAfter_pass2_nf [CurrentPreset] (o : Oracle) (K : BeaconState → SpecM BeaconState)
    (s1 : BeaconState)
    (downward upward : Uint64)
    (hthr : hysteresisThresholds P = .ok (downward, upward)) (hrows : ListLengthsMatch s1)
    (dec : Nat × Gwei × List Bool) (sums : List Gwei) (x : (Epoch × Gwei) × List Row)
    (hkey : x.2.map rowKey = (rowsOf s1).map rowKey) :
    SameResultOrBothFail (passM (fun _ r =>
      (fun r' => ((), r')) <$> lighthouseRowStep2 downward upward
        (sums.getD r.index 0) (decide (r.index ∈ validatorsInConsolidations s1)) r) () x.2 >>=
        fun y => lighthouseAfterPassG o K s1 (planOf s1 dec sums) (x.1, y.2))
      (nfAfterG o K s1 (s1.withRowsChurn x.1 x.2) dec sums) := by
  let S4 := s1.withRowsChurn x.1 x.2
  let td := fun i => sums.getD i 0
  let nm := fun i => decide (i ∈ validatorsInConsolidations s1)
  have hrowsS4 : rowsOf S4 = x.2 := rowsOf_withRows s1 x.2 hkey
  have hokS4 : ListLengthsMatch S4 := rowsOk_withRows_of_key s1 x.2 hrows hkey
  have hlen2 : x.2.length = s1.validators.length := by
    rw [← rowsOf_length, ← List.length_map (f := rowKey), hkey, List.length_map]
  have hlen : S4.validators.length = s1.validators.length := by
    show (x.2.map (·.validator)).length = _
    rw [List.length_map, hlen2]
  have hL : (passM (fun _ r => (fun r' => ((), r')) <$> lighthouseRowStep2 downward upward
        (td r.index) (nm r.index) r) () x.2 >>=
        fun y => lighthouseAfterPassG o K s1 (planOf s1 dec sums) (x.1, y.2)) =
      ((fun y => S4.withRows y.2) <$> passM (fun _ r => (fun r' => ((), r')) <$>
        lighthouseRowStep2 downward upward (td r.index) (nm r.index) r) () (rowsOf S4)) >>=
        lighthouseRest o K s1 (planOf s1 dec sums) := by
    rw [bind_map_left, hrowsS4]
    rfl
  have hR : nfAfterG o K s1 S4 dec sums =
      (((List.range S4.validators.length).foldlM (fun t i => increaseAt i (td i) t) S4) >>=
        fun t => ((List.range S4.validators.length).filter (fun i => !nm i)).foldlM
          updateEffectiveBalanceAt t) >>= nfRest o K s1 dec := by
    simp only [nfAfterG, addSums]
    rw [hlen, bind_assoc]
    rfl
  show SameResultOrBothFail (passM (fun _ r =>
    (fun r' => ((), r')) <$> lighthouseRowStep2 downward upward
      (td r.index) (nm r.index) r) () x.2 >>=
      fun y => lighthouseAfterPassG o K s1 (planOf s1 dec sums) (x.1, y.2))
    (nfAfterG o K s1 S4 dec sums)
  rw [hL, hR]
  refine SameResultOrBothFail.bind ((rows_pass2_fold S4 hokS4 downward upward hthr td nm).trans
    (fold_interleave td nm _ S4)) (fun T2 hT2 => SameResultOrBothFail.of_eq ?_)
  apply lighthouseRest_eq_nfRest
  obtain ⟨y, hy, rfl⟩ := (map_ok_iff' _ _ _).mp hT2
  have hyl := (passM_rows _ _ _ _ hy).1
  show (y.2.map (·.validator)).length = _
  rw [List.length_map, hyl, rowsOf_length, hlen]

/-- `lighthouseFullTailG` gives the same `ok` results as the first pass followed by `tailNFG`. -/
theorem lighthouseFullTailG_nf [CurrentPreset] (o : Oracle) (rt : Gwei → Gwei)
    (fin : Gwei → BeaconState → SpecM BeaconState) (s1 : BeaconState) (current_epoch : Epoch)
    (total_active_balance : Gwei) (rctx : RewardsContext) (adjusted per : Gwei)
    (downward upward : Uint64)
    (hcur : get_current_epoch P s1 = .ok current_epoch)
    (htab : get_total_active_balance P s1 = .ok total_active_balance)
    (hctx : rewardsContextOf P total_active_balance s1 = .ok rctx)
    (hpre : slashingsPreamble P total_active_balance s1.slashings =
      .ok (adjusted, per))
    (hthr : hysteresisThresholds P = .ok (downward, upward))
    (hrows : ListLengthsMatch s1) :
    SameResultOrBothFail (lighthouseFullTailG o rt fin s1)
      (do
        let x ← passM (fun c r => lighthouseRowStep P
            (lighthouseContextOf s1 (rt total_active_balance) current_epoch rctx per)
            (lighthouseBaseReward total_active_balance r) c r)
          (s1.earliest_exit_epoch, s1.exit_balance_to_consume) (rowsOf s1)
        tailNFG o (fin total_active_balance) s1 (s1.withRowsChurn x.1 x.2)
          (rt total_active_balance) current_epoch) := by
  let ctx := lighthouseContextOf s1 (rt total_active_balance) current_epoch rctx per
  let c0 := (s1.earliest_exit_epoch, s1.exit_balance_to_consume)
  let pass1 := passM (fun c r => lighthouseRowStep P ctx
    (lighthouseBaseReward total_active_balance r) c r) c0 (rowsOf s1)
  let K := fin total_active_balance
  rw [lighthouseFullTailG_eq o rt fin s1 current_epoch total_active_balance rctx adjusted per
    downward
    upward hcur htab hctx hpre hthr, lighthouseDepositPlan_eq]
  simp only [tailNFG_eq, bind_assoc, bind_map_left]
  refine SameResultOrBothFail.trans ?_ (sameResultOrBothFail_bind_swap (planDec s1 (rt total_active_balance) current_epoch)
    pass1 (fun dec x => sumsOfDec s1 dec >>= fun sums =>
      nfAfterG o K s1 (s1.withRowsChurn x.1 x.2) dec sums))
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun dec _ => ?_)
  refine SameResultOrBothFail.trans ?_ (sameResultOrBothFail_bind_swap (sumsOfDec s1 dec) pass1 (fun sums x =>
      nfAfterG o K s1 (s1.withRowsChurn x.1 x.2) dec sums))
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun sums _ => ?_)
  refine SameResultOrBothFail.trans
    (SameResultOrBothFail.bind (lighthouseValidatorStep_split ctx downward upward
    (lighthouseBaseReward total_active_balance) (fun i => sums.getD i 0)
    (fun i => decide (i ∈ validatorsInConsolidations s1)) c0 (rowsOf s1))
    (fun _ _ => SameResultOrBothFail.refl _)) ?_
  simp only [bind_assoc, pure_bind]
  refine SameResultOrBothFail.bind (SameResultOrBothFail.refl _) (fun x hx => ?_)
  exact lighthouseAfter_pass2_nf o K s1 downward upward hthr hrows dec sums x
    (passM_rowKey _ (fun c r y h => lighthouseRowStep_rowKey ctx _ c r y h) c0 (rowsOf s1) x hx)

/-- `lighthouseFullTail` gives the same `ok` results as the first pass followed by
`stepsAfterSinglePassCommonOrder`. -/
theorem lighthouseFullTail_nf [CurrentPreset] (o : Oracle) (s1 : BeaconState)
    (current_epoch : Epoch)
    (total_active_balance : Gwei) (rctx : RewardsContext) (adjusted per : Gwei)
    (downward upward : Uint64)
    (hcur : get_current_epoch P s1 = .ok current_epoch)
    (htab : get_total_active_balance P s1 = .ok total_active_balance)
    (hctx : rewardsContextOf P total_active_balance s1 = .ok rctx)
    (hpre : slashingsPreamble P total_active_balance s1.slashings =
      .ok (adjusted, per))
    (hthr : hysteresisThresholds P = .ok (downward, upward))
    (hrows : ListLengthsMatch s1) :
    SameResultOrBothFail (lighthouseFullTail o s1)
      (do
        let x ← passM (fun c r => lighthouseRowStep P
            (lighthouseContextOf s1 total_active_balance current_epoch rctx per)
            (lighthouseBaseReward total_active_balance r) c r)
          (s1.earliest_exit_epoch, s1.exit_balance_to_consume) (rowsOf s1)
        stepsAfterSinglePassCommonOrder o s1 (s1.withRowsChurn x.1 x.2) total_active_balance
          current_epoch) :=
  lighthouseFullTailG_nf o id (gloasFin o) s1 current_epoch total_active_balance rctx adjusted per
    downward upward hcur htab hctx hpre hthr hrows

end EpochProofs.Spec
