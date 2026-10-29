import EpochProofs.Etheorem.Resets
import EpochProofs.Sanity.EffectiveBalanceUpdates

/-!
# `process_effective_balance_updates` equals Etheorem's

The main theorem is `effective_balance_updates_etheorem`.

Etheorem runs the loop on the boxed state. `processEffectiveBalanceUpdates_run` moves it to the
plain state as a `foldl` of `ebStepView`. `ebFold` shows that after `k` steps the first `k`
validators hold `ebNew`. The reference loop is a `mapM` of `effectiveBalanceStep`
(`process_effective_balance_updates_eq`). `effectiveBalanceStep_ok` shows that each step
returns `ebNew` under the map.

Etheorem raises on a balance read past the end and on a threshold sum that overflows `uint64`,
as the reference does. `effectiveBalanceStep_cond` reads these facts off a reference step that
returns, so the theorem has no extra hypothesis.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)

variable [EthCLSpecs.Gloas.Preset]

/-- `DOWNWARD_THRESHOLD` in Etheorem. -/
abbrev ebDown : UInt64 :=
  EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Gloas.Const.hysteresisQuotient *
    UInt64.ofNat EthCLSpecs.Gloas.Const.hysteresisDownwardMultiplier

/-- `UPWARD_THRESHOLD` in Etheorem. -/
abbrev ebUp : UInt64 :=
  EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Gloas.Const.hysteresisQuotient *
    UInt64.ofNat EthCLSpecs.Gloas.Const.hysteresisUpwardMultiplier

/-- The new effective balance when the balance leaves the hysteresis band. -/
abbrev ebTarget (v : EthCLSpecs.Gloas.Validator) (b : UInt64) : UInt64 :=
  umin (b - b % EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG)
    (EthCLSpecs.Gloas.getMaxEffectiveBalance v)

/-- One step of Etheorem's loop on the plain state. -/
def ebStepView (s : EState) (i : Nat) : EState :=
  if s.balances[i]! + ebDown < s.validators[i]!.effectiveBalance ||
      s.validators[i]!.effectiveBalance + ebUp < s.balances[i]! then
    let v := s.validators[(UInt64.ofNat i).toNat]!
    let eb := ebTarget s.validators[i]! s.balances[i]!
    { s with validators := s.validators.set! (UInt64.ofNat i).toNat { v with effectiveBalance := eb } }
  else s

omit [EthCLSpecs.Gloas.Preset] in
theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id _) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

variable [HasherTag]

/-- A `foldl` that keeps the uncached box is a `foldl` on the plain state. -/
theorem foldl_pureState {α : Type} (F : EthCLSpecs.Gloas.State → α → EthCLSpecs.Gloas.State)
    (G : EState → α → EState) (hFG : ∀ s a, F (pureState s) a = pureState (G s a)) :
    ∀ (l : List α) (s : EState), l.foldl F (pureState s) = pureState (l.foldl G s) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih => intro s; simp only [List.foldl_cons, hFG, ih]

/-- The reads and sums of step `i` of Etheorem's loop succeed: the balance exists, and neither
threshold sum overflows `uint64`. The second sum runs only when the first comparison fails. -/
def EbStepOk (e : EState) (i : Nat) : Prop :=
  i < e.balances.val.size ∧ (e.balances[i]!).toNat + ebDown.toNat < 2 ^ 64 ∧
    (¬ (e.balances[i]! + ebDown < (e.validators[i]!).effectiveBalance) →
      (e.validators[i]!).effectiveBalance.toNat + ebUp.toNat < 2 ^ 64)

/-- A loop over a list on the plain state, where step `k` runs as `G` on the state that the first
`k` steps reach. -/
theorem forIn_run_foldl {α : Type} (G : EState → α → EState)
    (body : α → PUnit → GloasRun (ForInStep PUnit)) :
    ∀ (l : List α) (v : EState),
      (∀ k (hk : k < l.length), (body l[k] PUnit.unit).run (pureState ((l.take k).foldl G v)) =
        .ok (.yield PUnit.unit, pureState (G ((l.take k).foldl G v) l[k]))) →
      (forIn l PUnit.unit body).run (pureState v) = .ok (PUnit.unit, pureState (l.foldl G v)) := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons a l ih =>
    intro v hb
    rw [List.forIn_cons, run_bind]
    have h0 := hb 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at h0
    rw [h0, except_bind_ok]
    exact ih (G v a) (fun k hk => by
      have := hb (k + 1) (by simp; omega)
      simpa using this)

omit [HasherTag] in
/-- `get_max_effective_balance` equals Etheorem's. -/
theorem get_max_effective_balance_eq {p : Spec.Preset} (ht : TailPresetAgrees p)
    (v : EthCLSpecs.Gloas.Validator) :
    Spec.get_max_effective_balance p (absValidator v) =
      (EthCLSpecs.Gloas.getMaxEffectiveBalance v).toNat := by
  have hc : Spec.has_compounding_withdrawal_credential (absValidator v) =
      EthCLSpecs.Gloas.hasCompoundingWithdrawalCredential v := by
    unfold Spec.has_compounding_withdrawal_credential Spec.is_compounding_withdrawal_credential
      EthCLSpecs.Gloas.hasCompoundingWithdrawalCredential EthCLSpecs.Gloas.credPrefix vget
      absValidator
    obtain ⟨⟨l⟩, hl⟩ := v.withdrawalCredentials
    cases l with
    | nil => simp at hl
    | cons x l => simp [Vector.toList, Spec.COMPOUNDING_WITHDRAWAL_PREFIX]
  unfold Spec.get_max_effective_balance EthCLSpecs.Gloas.getMaxEffectiveBalance
  rw [hc]
  split
  · exact ht.maxEffectiveBalanceElectra.symm
  · exact ht.minActivationBalance.symm

/-- The new value of one validator in Etheorem's loop. -/
def ebNew (v : EthCLSpecs.Gloas.Validator) (b : UInt64) : EthCLSpecs.Gloas.Validator :=
  if b + ebDown < v.effectiveBalance || v.effectiveBalance + ebUp < b then
    { v with effectiveBalance := ebTarget v b }
  else v

omit [HasherTag] in
theorem ebNew_pos (v : EthCLSpecs.Gloas.Validator) (b : UInt64)
    (h : (b + ebDown < v.effectiveBalance || v.effectiveBalance + ebUp < b) = true) :
    ebNew v b = { v with effectiveBalance := ebTarget v b } :=
  if_pos h

omit [HasherTag] in
theorem ebNew_neg (v : EthCLSpecs.Gloas.Validator) (b : UInt64)
    (h : ¬ (b + ebDown < v.effectiveBalance || v.effectiveBalance + ebUp < b) = true) :
    ebNew v b = v :=
  if_neg h

omit [HasherTag] in
theorem absValidator_ebNew (v : EthCLSpecs.Gloas.Validator) (b : UInt64) :
    absValidator (ebNew v b) =
      { absValidator v with effective_balance := (ebNew v b).effectiveBalance.toNat } := by
  unfold ebNew
  split <;> rfl

omit [HasherTag] in
/-- One step writes `ebNew` at index `i`. -/
theorem ebStepView_eq (s : EState) (i : Nat) (hi : i < 2 ^ 64) :
    ebStepView s i = { s with validators := s.validators.set! i (ebNew s.validators[i]! s.balances[i]!) } := by
  unfold ebStepView
  rw [UInt64.toNat_ofNat_of_lt' hi]
  split
  · rename_i hc
    rw [ebNew_pos _ _ hc]
  · rename_i hc
    rw [ebNew_neg _ _ hc]
    have hset : s.validators.set! i s.validators[i]! = s.validators := by
      apply Subtype.ext
      rw [sszList_getElem!_val]
      change Array.set! s.validators.val i s.validators.val[i]! = s.validators.val
      by_cases hlt : i < s.validators.val.size
      · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos hlt,
          getElem!_pos s.validators.val i hlt]
        simp
      · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_neg hlt]
    rw [hset]

omit [HasherTag] in
/-- After `k` steps, Etheorem's loop has replaced the first `k` validators by `ebNew`. -/
theorem ebFold (e : EState) (hn : e.validators.val.size < 2 ^ 64) :
    ∀ k, k ≤ e.validators.val.size →
      ∃ V : SSZList EthCLSpecs.Gloas.Validator EthCLSpecs.Gloas.Const.validatorRegistryLimit,
        (List.range' 0 k).foldl ebStepView e = { e with validators := V } ∧
        V.val.toList = (List.range k).map (fun j => ebNew e.validators.val[j]! e.balances.val[j]!) ++
          e.validators.val.toList.drop k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨e.validators, rfl, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨V, hV, hVl⟩ := ih (by omega)
    have hklen : k < e.validators.val.toList.length := by simp; omega
    have hP : ((List.range k).map (fun j => ebNew e.validators.val[j]! e.balances.val[j]!)).length = k := by
      simp
    have hVk : V[k]! = e.validators.val[k]! := by
      rw [sszList_getElem!_val]
      have hsz : k < V.val.size := by
        rw [← Array.length_toList, hVl]; simp; omega
      rw [getElem!_pos V.val k hsz, getElem!_pos e.validators.val k (by omega), ← Array.getElem_toList,
        ← Array.getElem_toList]
      simp only [hVl]
      rw [List.getElem_append_right (Nat.le_of_eq hP)]
      simp [hP]
    refine ⟨V.set! k (ebNew e.validators.val[k]! e.balances.val[k]!), ?_, ?_⟩
    · rw [List.range'_concat, List.foldl_append, hV]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
      rw [ebStepView_eq _ _ (by omega)]
      simp only [hVk, sszList_getElem!_val]
    · change (V.val.set! k _).toList = _
      rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, hVl,
        List.set_append_right _ _ (Nat.le_of_eq hP), hP, Nat.sub_self,
        List.drop_eq_getElem_cons hklen, List.set_cons_zero, List.range_succ, List.map_append,
        List.append_assoc]
      simp [getElem!_pos e.validators.val k (by omega)]

omit [HasherTag] in
/-- After `k` steps, validator `k` and the balances are still those of `e`. -/
theorem ebFold_at (e : EState) (hn : e.validators.val.size < 2 ^ 64) (k : Nat)
    (hk : k < e.validators.val.size) :
    ((List.range' 0 k).foldl ebStepView e).balances = e.balances ∧
      ((List.range' 0 k).foldl ebStepView e).validators[k]! = e.validators[k]! := by
  obtain ⟨V, hV, hVl⟩ := ebFold e hn k (Nat.le_of_lt hk)
  rw [hV]
  refine ⟨rfl, ?_⟩
  have hP : ((List.range k).map (fun j => ebNew e.validators.val[j]! e.balances.val[j]!)).length = k := by
    simp
  show V[k]! = e.validators[k]!
  rw [sszList_getElem!_val, sszList_getElem!_val]
  have hsz : k < V.val.size := by
    rw [← Array.length_toList, hVl]; simp; omega
  rw [getElem!_pos V.val k hsz, getElem!_pos e.validators.val k hk, ← Array.getElem_toList,
    ← Array.getElem_toList]
  simp only [hVl]
  rw [List.getElem_append_right (Nat.le_of_eq hP)]
  simp [hP]

theorem processEffectiveBalanceUpdates_run (e : EState) (hn : e.validators.val.size < 2 ^ 64)
    (hok : ∀ i < e.validators.val.size, EbStepOk e i) :
    (EthCLSpecs.Gloas.processEffectiveBalanceUpdates (StateTransition := GloasRun)).run
        (pureState e) =
      .ok ((), pureState ((List.range' 0 e.validators.val.size).foldl ebStepView e)) := by
  unfold EthCLSpecs.Gloas.processEffectiveBalanceUpdates
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have hget : ∀ s : EthCLSpecs.Gloas.State,
      (get : GloasRun EthCLSpecs.Gloas.State).run s = .ok (s, s) := fun _ => rfl
  rw [run_bind, hget, except_bind_ok]
  simp only [view_uncachedBox]
  rw [run_bind, forIn_run_foldl ebStepView _ _ e, except_bind_ok]
  · rfl
  intro k hk
  have hk' : k < e.validators.val.size := by simpa using hk
  rw [List.take_range'_of_length_ge (by simpa using Nat.le_of_lt hk)]
  simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
  obtain ⟨hbal, hval⟩ := ebFold_at e hn k hk'
  obtain ⟨hb1, hb2, hb3⟩ := hok k hk'
  generalize (List.range' 0 k).foldl ebStepView e = w at hbal hval ⊢
  rw [← hbal] at hb1 hb2 hb3
  rw [← hval] at hb3
  have hbk : w.balances.val[k]? = some w.balances[k]! := by
    rw [sszList_getElem!_val, getElem!_pos w.balances.val k hb1]
    exact Array.getElem?_eq_getElem hb1
  rw [run_bind, hget, except_bind_ok]
  simp only [view_uncachedBox]
  rw [run_bind, run_sszGetIdx_some _ _ _ hbk, except_bind_ok]
  rw [run_bind, checkedAdd_of_lt _ _ _ hb2, run_pure, except_bind_ok]
  by_cases hlt : w.balances[k]! + ebDown < (w.validators[k]!).effectiveBalance
  · rw [if_pos hlt]
    simp only [ebStepView]
    rw [if_pos (by simp [hlt])]
    rfl
  · rw [if_neg hlt]
    rw [run_bind, checkedAdd_of_lt _ _ _ (hb3 hlt), run_pure, except_bind_ok]
    by_cases hlt2 : w.validators[k]!.effectiveBalance + ebUp < w.balances[k]!
    · simp only [hlt2, decide_true]
      simp only [ebStepView]
      rw [if_pos (by simp [hlt2])]
      rfl
    · simp only [hlt2, decide_false]
      simp only [ebStepView]
      rw [if_neg (by simp [hlt, hlt2])]
      rfl

section Thresholds

variable [EthCLSpecs.Gloas.Config] {p : Spec.Preset} (hp : PresetAgrees p) (ht : TailPresetAgrees p)
include hp ht

omit [HasherTag] in
/-- The reference thresholds equal Etheorem's. -/
theorem hysteresisThresholds_ok {down up : Nat}
    (h : Spec.hysteresisThresholds p = .ok (down, up)) :
    ebDown.toNat = down ∧ ebUp.toNat = up := by
  obtain ⟨hq, hd, hu⟩ := ht.hysteresisLt
  unfold Spec.hysteresisThresholds at h
  simp only [bind, Except.bind] at h
  cases h1 : Spec.uint64Div p.EFFECTIVE_BALANCE_INCREMENT p.HYSTERESIS_QUOTIENT with
  | error err => rw [h1] at h; cases h
  | ok inc =>
    rw [h1] at h
    simp only at h
    cases h2 : Spec.uint64Mul inc p.HYSTERESIS_DOWNWARD_MULTIPLIER with
    | error err => rw [h2] at h; cases h
    | ok d =>
      rw [h2] at h
      simp only at h
      cases h3 : Spec.uint64Mul inc p.HYSTERESIS_UPWARD_MULTIPLIER with
      | error err => rw [h3] at h; cases h
      | ok u =>
        rw [h3] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hinc : (EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG /
            UInt64.ofNat EthCLSpecs.Gloas.Const.hysteresisQuotient).toNat = inc := by
          apply uint64Div_ok
          rw [hp.effectiveBalanceIncrementG, UInt64.toNat_ofNat_of_lt' hq, ht.hysteresisQuotient]
          exact h1
        refine ⟨?_, ?_⟩
        · apply uint64Mul_ok
          rw [hinc, UInt64.toNat_ofNat_of_lt' hd, ht.hysteresisDownwardMultiplier]
          exact h2
        · apply uint64Mul_ok
          rw [hinc, UInt64.toNat_ofNat_of_lt' hu, ht.hysteresisUpwardMultiplier]
          exact h3

omit [HasherTag] in
/-- The reference result for one validator equals `ebNew`. -/
theorem newEffectiveBalance_ok (v : EthCLSpecs.Gloas.Validator) (b : UInt64) {down up eb : Nat}
    (hdown : ebDown.toNat = down) (hup : ebUp.toNat = up)
    (h : Spec.newEffectiveBalance p down up (absValidator v) b.toNat = .ok eb) :
    (ebNew v b).effectiveBalance.toNat = eb := by
  have hround : ∀ {rem rounded : Nat},
      Spec.uint64Mod b.toNat p.EFFECTIVE_BALANCE_INCREMENT = .ok rem →
      Spec.uint64Sub b.toNat rem = .ok rounded →
      (umin (b - b % EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG)
        (EthCLSpecs.Gloas.getMaxEffectiveBalance v)).toNat =
        min rounded (Spec.get_max_effective_balance p (absValidator v)) := by
    intro rem rounded hm hs
    have hr : (b % EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG).toNat = rem := by
      apply uint64Mod_ok; rw [hp.effectiveBalanceIncrementG]; exact hm
    have hs' : (b - b % EthCLSpecs.Gloas.Const.effectiveBalanceIncrementG).toNat = rounded := by
      apply uint64Sub_ok; rw [hr]; exact hs
    rw [umin_toNat, hs', get_max_effective_balance_eq ht]
  unfold Spec.newEffectiveBalance at h
  simp only [bind, Except.bind] at h
  cases hadd : Spec.uint64Add b.toNat down with
  | error err => rw [hadd] at h; cases h
  | ok below =>
    rw [hadd] at h
    simp only at h
    have hbelow : (b + ebDown).toNat = below := by
      apply uint64Add_ok; rw [hdown]; exact hadd
    have hveb : (absValidator v).effective_balance = v.effectiveBalance.toNat := rfl
    by_cases hlt : below < (absValidator v).effective_balance
    · have hc : (b + ebDown < v.effectiveBalance) := by
        rw [UInt64.lt_iff_toNat_lt, hbelow, ← hveb]; exact hlt
      simp only [hlt, ↓reduceIte, pure, Except.pure] at h
      cases hm : Spec.uint64Mod b.toNat p.EFFECTIVE_BALANCE_INCREMENT with
      | error err => rw [hm] at h; cases h
      | ok rem =>
        rw [hm] at h
        simp only at h
        cases hs : Spec.uint64Sub b.toNat rem with
        | error err => rw [hs] at h; cases h
        | ok rounded =>
          rw [hs] at h
          simp only [Except.ok.injEq] at h
          unfold ebNew
          simp only [hc, decide_true, Bool.true_or, ↓reduceIte]
          rw [hround hm hs, h]
    · have hc : ¬ (b + ebDown < v.effectiveBalance) := by
        rw [UInt64.lt_iff_toNat_lt, hbelow, ← hveb]; exact hlt
      simp only [hlt, ↓reduceIte] at h
      cases hadd2 : Spec.uint64Add (absValidator v).effective_balance up with
      | error err => rw [hadd2] at h; cases h
      | ok above =>
        rw [hadd2] at h
        simp only [pure, Except.pure] at h
        have habove : (v.effectiveBalance + ebUp).toNat = above := by
          apply uint64Add_ok; rw [hup, ← hveb]; exact hadd2
        by_cases hlt2 : above < b.toNat
        · have hc2 : v.effectiveBalance + ebUp < b := by
            rw [UInt64.lt_iff_toNat_lt, habove]; exact hlt2
          simp only [hlt2, decide_true, ↓reduceIte] at h
          cases hm : Spec.uint64Mod b.toNat p.EFFECTIVE_BALANCE_INCREMENT with
          | error err => rw [hm] at h; cases h
          | ok rem =>
            rw [hm] at h
            simp only at h
            cases hs : Spec.uint64Sub b.toNat rem with
            | error err => rw [hs] at h; cases h
            | ok rounded =>
              rw [hs] at h
              simp only [Except.ok.injEq] at h
              unfold ebNew
              simp only [hc2, decide_true, Bool.or_true, ↓reduceIte]
              rw [hround hm hs, h]
        · have hc2 : ¬ (v.effectiveBalance + ebUp < b) := by
            rw [UInt64.lt_iff_toNat_lt, habove]; exact hlt2
          simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
          unfold ebNew
          simp only [hc, hc2, decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
          exact h

omit [HasherTag] in
/-- One reference loop step returns `ebNew` under the map. -/
theorem effectiveBalanceStep_ok (e : EState) (v : EthCLSpecs.Gloas.Validator) (i : Nat)
    {w : Spec.Validator}
    (h : Spec.effectiveBalanceStep p (e.balances.toList.map UInt64.toNat) (absValidator v, i) =
      .ok w) :
    w = absValidator (ebNew v e.balances.val[i]!) := by
  unfold Spec.effectiveBalanceStep at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i b hb
    simp only [pure, Except.pure] at h
    have hb' : b = (e.balances.val[i]!).toNat := by
      rw [List.getElem?_eq_some_iff] at hb
      obtain ⟨hi, rfl⟩ := hb
      have hi' : i < e.balances.val.size := by simpa using hi
      simp only [SSZList.toList, List.getElem_map, Array.getElem_toList]
      rw [getElem!_pos e.balances.val i hi']
    subst hb'
    cases hth : Spec.hysteresisThresholds p with
    | error err => rw [hth] at h; cases h
    | ok du =>
      obtain ⟨d, u⟩ := du
      rw [hth] at h
      simp only at h
      obtain ⟨hd, hu⟩ := hysteresisThresholds_ok hp ht hth
      cases hn : Spec.newEffectiveBalance p d u (absValidator v) (e.balances.val[i]!).toNat with
      | error err => rw [hn] at h; cases h
      | ok eb =>
        rw [hn] at h
        simp only [Except.ok.injEq] at h
        rw [← h, absValidator_ebNew, newEffectiveBalance_ok hp ht v _ hd hu hn]
  · cases h

omit [HasherTag] in
/-- A reference loop step that returns reads a balance and sums its thresholds without overflow.
These are the reads and sums of Etheorem's step. -/
theorem effectiveBalanceStep_cond (e : EState) (v : EthCLSpecs.Gloas.Validator) (i : Nat)
    {w : Spec.Validator}
    (h : Spec.effectiveBalanceStep p (e.balances.toList.map UInt64.toNat) (absValidator v, i) =
      .ok w) :
    i < e.balances.val.size ∧ (e.balances[i]!).toNat + ebDown.toNat < 2 ^ 64 ∧
      (¬ (e.balances[i]! + ebDown < v.effectiveBalance) →
        v.effectiveBalance.toNat + ebUp.toNat < 2 ^ 64) := by
  unfold Spec.effectiveBalanceStep at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i b hb
    simp only [pure, Except.pure] at h
    rw [List.getElem?_eq_some_iff] at hb
    obtain ⟨hi, rfl⟩ := hb
    have hi' : i < e.balances.val.size := by simpa using hi
    have hbv : (e.balances.toList.map UInt64.toNat)[i] = (e.balances[i]!).toNat := by
      simp only [SSZList.toList, List.getElem_map, Array.getElem_toList]
      rw [sszList_getElem!_val, getElem!_pos e.balances.val i hi']
    rw [hbv] at h
    cases hth : Spec.hysteresisThresholds p with
    | error err => rw [hth] at h; cases h
    | ok du =>
      obtain ⟨d, u⟩ := du
      rw [hth] at h
      simp only at h
      obtain ⟨hd, hu⟩ := hysteresisThresholds_ok hp ht hth
      cases hn : Spec.newEffectiveBalance p d u (absValidator v) (e.balances[i]!).toNat with
      | error err => rw [hn] at h; cases h
      | ok eb =>
        unfold Spec.newEffectiveBalance at hn
        simp only [bind, Except.bind] at hn
        cases hadd : Spec.uint64Add (e.balances[i]!).toNat d with
        | error err => rw [hadd] at hn; cases hn
        | ok below =>
          rw [hadd] at hn
          have hlt1 := uint64Add_lt hadd
          have hbelow : (e.balances[i]! + ebDown).toNat = below := by
            rw [uint64Add_val hadd, UInt64.toNat_add, hd,
              Nat.mod_eq_of_lt (by simpa [UInt64.size] using hlt1)]
          refine ⟨hi', hd ▸ hlt1, fun hnlt => ?_⟩
          have hnlt' : ¬ below < (absValidator v).effective_balance := by
            rw [← hbelow]
            exact fun h' => hnlt (UInt64.lt_iff_toNat_lt.mpr h')
          simp only [hnlt', ↓reduceIte] at hn
          cases hadd2 : Spec.uint64Add (absValidator v).effective_balance u with
          | error err => rw [hadd2] at hn; cases hn
          | ok above =>
            have := uint64Add_lt hadd2
            rw [← hu] at this
            exact this
  · cases h

omit [HasherTag] in
/-- The reference loop returns `ebNew` for every validator. -/
theorem mapM_effectiveBalanceStep_ok (e : EState) :
    ∀ (l : List Nat) (vs : List Spec.Validator),
      (l.map fun i => (absValidator e.validators.val[i]!, i)).mapM
          (Spec.effectiveBalanceStep p (e.balances.toList.map UInt64.toNat)) = .ok vs →
        vs = l.map fun i => absValidator (ebNew e.validators.val[i]! e.balances.val[i]!) := by
  intro l
  induction l with
  | nil => intro vs h; simp [List.mapM_nil, pure, Except.pure] at h; simp [h]
  | cons i l ih =>
    intro vs h
    rw [List.map_cons, List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hs : Spec.effectiveBalanceStep p (e.balances.toList.map UInt64.toNat)
        (absValidator e.validators.val[i]!, i) with
    | error err => rw [hs] at h; cases h
    | ok w =>
      rw [hs] at h
      simp only at h
      cases hm : (l.map fun i => (absValidator e.validators.val[i]!, i)).mapM
          (Spec.effectiveBalanceStep p (e.balances.toList.map UInt64.toNat)) with
      | error err => rw [hm] at h; cases h
      | ok ws =>
        rw [hm] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h, effectiveBalanceStep_ok hp ht e _ i hs, ih ws hm, List.map_cons]

/-- `process_effective_balance_updates` equals Etheorem's. -/
theorem effective_balance_updates_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_effective_balance_updates p (absEState e) = .ok s') :
    ∃ e', (EthCLSpecs.Gloas.processEffectiveBalanceUpdates (StateTransition := GloasRun)).run
        (pureState e) = .ok ((), pureState e') ∧ absEState e' = s' := by
  have hn : e.validators.val.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt e.validators.property hp.validatorRegistryLimit
  obtain ⟨V, hV, hVl⟩ := ebFold e hn _ (Nat.le_refl _)
  rw [Spec.process_effective_balance_updates_eq] at h
  cases hm : (absEState e).validators.zipIdx.mapM
      (Spec.effectiveBalanceStep p (absEState e).balances) with
  | error err => rw [hm] at h; cases h
  | ok vs =>
    rw [hm] at h
    simp only [Except.map, Except.ok.injEq] at h
    rw [← h]
    simp only [absEState_validators, absEState_balances, SSZList.toList,
      zipIdx_map_eq e.validators.val absValidator] at hm
    -- Each reference step returns, so each Etheorem read and sum succeeds.
    have hok : ∀ i < e.validators.val.size, EbStepOk e i := by
      intro i hi
      obtain ⟨w, hw⟩ := mapM_ok_each _ _ hm (absValidator e.validators.val[i]!, i)
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      have := effectiveBalanceStep_cond hp ht e _ i hw
      rw [← sszList_getElem!_val] at this
      exact this
    refine ⟨_, processEffectiveBalanceUpdates_run e hn hok, ?_⟩
    rw [hV, absEState_set_validators]
    have hvs := mapM_effectiveBalanceStep_ok hp ht e _ _ hm
    rw [hvs, SSZList.toList, hVl, List.drop_eq_nil_of_le (by simp), List.append_nil, List.map_map]
    rfl

end Thresholds


end EpochProofs.Etheorem
