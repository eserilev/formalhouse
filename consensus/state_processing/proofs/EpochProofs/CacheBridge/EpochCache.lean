import EpochProofs.CacheBridge.ProgressiveBalances
import EpochProofs.Sanity.RowsRewards
import EpochProofs.Sanity.RewardsBound
import EpochProofs.Sanity.Invariants.BalanceFloor

/-!
# Bridge: the epoch cache and the epoch spec

`CacheProofs.EpochCache` proves two reads of the Lighthouse epoch cache equal to its spec model:
the floored total active balance (`total_active_balance_equiv`) and the base reward
(`get_base_reward_equiv`). This file proves those spec values equal to the values that the epoch
model uses: `get_total_active_balance` of `EpochProofs.Spec`, and `rewardsBaseReward`, which
`lhBaseReward` of the single pass model calls.

The facts left about the cache are its build invariants: the cache holds the effective balances
of the state and the sum over the active validators (`hebs`, `hinv`). `single_pass_total_active_balance`
in `CacheProofs.EpochCache` proves that the `single_pass.rs` calls build exactly that.
-/

namespace EpochProofs.CacheBridge

open CacheProofs.PB (activeAt ebAt)

/-- The validator fields that the epoch cache model reads. -/
def ecValidator (v : EpochProofs.Spec.Validator) : CacheProofs.Spec.EpochCache.Validator :=
  ⟨v.effective_balance, v.activation_epoch, v.exit_epoch⟩

/-- The state of the epoch cache model at epoch `epoch`. -/
def ecState (s : EpochProofs.Spec.BeaconState) (epoch : Nat) :
    CacheProofs.Spec.EpochCache.BeaconState :=
  ⟨s.validators.map ecValidator, epoch⟩

/-- `integer_squareroot` of the epoch spec is `Nat.sqrt`. -/
theorem integer_squareroot_eq_sqrt (n : Nat) :
    EpochProofs.Spec.integer_squareroot n = Nat.sqrt n := by
  have h1 := EpochProofs.Spec.integer_squareroot_mul_self_le n
  have h2 := EpochProofs.Spec.integer_squareroot_spec n
  exact Nat.eq_sqrt.mpr ⟨h1, h2⟩

theorem activeSumFrom_range (act : Nat → Bool) (l : List Nat) : ∀ k,
    CacheProofs.EpochCache.activeSumFrom act k l =
      (((List.range l.length).filter (fun i => act (i + k))).map (fun i => l.getD i 0)).sum := by
  induction l with
  | nil => intro k; simp [CacheProofs.EpochCache.activeSumFrom]
  | cons x l ih =>
    intro k
    rw [CacheProofs.EpochCache.activeSumFrom, ih (k + 1), List.length_cons,
      List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have hf : ((fun i => act (i + k)) ∘ Nat.succ) = (fun i => act (i + (k + 1))) := by
      funext i; simp [Function.comp]; congr 1; omega
    have hg : ((fun i => (x :: l).getD i 0) ∘ Nat.succ) = (fun i => l.getD i 0) := by
      funext i; simp [Function.comp]
    rw [hf, Nat.zero_add]
    by_cases ha : act k
    · simp only [ha, if_true, List.map_cons, List.sum_cons, List.map_map, hg]
      simp
    · simp only [ha, Bool.false_eq_true, if_false, List.map_map, hg]
      simp

theorem activeAt_ec_pb (vs : List EpochProofs.Spec.Validator) (e i : Nat) :
    CacheProofs.EpochCache.activeAt (vs.map ecValidator) e i =
      activeAt (vs.map pbValidator) e i := by
  simp only [CacheProofs.EpochCache.activeAt, activeAt, List.getElem?_map]
  cases vs[i]? <;> rfl

/-- The sum over the active validators of the epoch cache model is the sum of the progressive
balances model. Both read the same validators. -/
theorem activeSum_eq (vs : List EpochProofs.Spec.Validator) (e : Nat) :
    CacheProofs.EpochCache.activeSum (CacheProofs.EpochCache.activeAt (vs.map ecValidator) e)
        ((vs.map ecValidator).map (·.effective_balance)) =
      (((List.range vs.length).filter (activeAt (vs.map pbValidator) e)).map
        (ebAt (vs.map pbValidator))).sum := by
  unfold CacheProofs.EpochCache.activeSum
  rw [activeSumFrom_range]
  simp only [Nat.add_zero, List.length_map, activeAt_ec_pb]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < vs.length := by
    simp only [List.mem_filter, List.mem_range] at hi; exact hi.1
  simp [ebAt, hi', ecValidator, pbValidator]

/-- `get_total_active_balance` of the epoch spec in closed form. -/
theorem get_total_active_balance_closed (p : EpochProofs.Spec.Preset)
    (s : EpochProofs.Spec.BeaconState) (cur : Nat)
    (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (hfit : (((List.range s.validators.length).filter (activeAt (s.validators.map pbValidator)
      cur)).map (ebAt (s.validators.map pbValidator))).sum < 2 ^ 64) :
    EpochProofs.Spec.get_total_active_balance p s =
      .ok (max p.EFFECTIVE_BALANCE_INCREMENT
        (((List.range s.validators.length).filter (activeAt (s.validators.map pbValidator)
          cur)).map (ebAt (s.validators.map pbValidator))).sum) := by
  unfold EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.get_total_balance
  have hmem : ∀ i ∈ (List.range s.validators.length).filter
      (activeAt (s.validators.map pbValidator) cur), i < s.validators.length := fun i hi => by
    simp only [List.mem_filter, List.mem_range] at hi; exact hi.1
  have hm := mapM_eb s.validators _ hmem
  simp only [bind, Except.bind, pure, Except.pure, hcur, get_active_validator_indices_bridge]
    at hm ⊢
  rw [hm]
  have h64 : (((List.range s.validators.length).filter (activeAt (s.validators.map pbValidator)
      cur)).map (ebAt (s.validators.map pbValidator))).sum < EpochProofs.Spec.UINT64_SIZE := hfit
  simp [EpochProofs.Spec.uint64Sum, h64, pure, Except.pure]

open Aeneas Aeneas.Std Result in
/-- The floored total active balance that Lighthouse reads from the epoch cache equals the
epoch spec `get_total_active_balance`, when the cache holds the effective balances of the state
and their sum over the validators active in the current epoch. -/
theorem lh_total_active_balance_eq (p : EpochProofs.Spec.Preset)
    (s : EpochProofs.Spec.BeaconState) (cur : Nat)
    (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (ebs : List Nat) (total inc : U64)
    (hinc : inc.val = p.EFFECTIVE_BALANCE_INCREMENT)
    (hebs : ebs = s.validators.map (·.effective_balance))
    (hinv : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) cur) ebs) :
    ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
      EpochProofs.Spec.get_total_active_balance p s = .ok r.val := by
  let cfg : CacheProofs.Spec.EpochCache.Config := ⟨p.EFFECTIVE_BALANCE_INCREMENT, 0, 0⟩
  have hebs' : ebs = (s.validators.map ecValidator).map (·.effective_balance) := by
    rw [hebs, List.map_map]; rfl
  obtain ⟨r, hr, hspec⟩ := CacheProofs.EpochCache.total_active_balance_equiv cfg
    (s.validators.map ecValidator) cur ebs total inc hinc hebs' hinv
  refine ⟨r, hr, ?_⟩
  have hsum := activeSum_eq s.validators cur
  have hlt : CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) cur)
      ((s.validators.map ecValidator).map (·.effective_balance)) < 2 ^ 64 := by
    rw [← hebs', ← hinv]; exact total.hBounds
  rw [CacheProofs.EpochCache.get_total_active_balance_eq cfg _ cur hlt] at hspec
  have hval : r.val = max p.EFFECTIVE_BALANCE_INCREMENT
      (CacheProofs.EpochCache.activeSum
        (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) cur)
        ((s.validators.map ecValidator).map (·.effective_balance))) := by
    have := Except.ok.inj hspec; exact this.symm
  rw [hsum] at hlt hval
  rw [get_total_active_balance_closed p s cur hcur hlt, hval]

/-- If the altair base reward of the epoch cache model is `ok b` at total `T`, then
`rewardsBaseReward` of the epoch model is `ok b`. Both do the same `uint64` steps. -/
theorem rewardsBaseReward_of_altair (p : EpochProofs.Spec.Preset)
    (cfg : CacheProofs.Spec.EpochCache.Config) (st : CacheProofs.Spec.EpochCache.BeaconState)
    (index : Nat) (v : EpochProofs.Spec.Validator) (T b : Nat)
    (hinc : cfg.EFFECTIVE_BALANCE_INCREMENT = p.EFFECTIVE_BALANCE_INCREMENT)
    (hfactor : cfg.BASE_REWARD_FACTOR = p.BASE_REWARD_FACTOR)
    (hv : st.validators[index]? = some (ecValidator v))
    (htotal : CacheProofs.Spec.EpochCache.get_total_active_balance cfg st = .ok T)
    (hT64 : T < 2 ^ 64)
    (hb : CacheProofs.Spec.EpochCache.get_base_reward_altair cfg st index = .ok b) :
    EpochProofs.Spec.rewardsBaseReward p T v = .ok b := by
  unfold CacheProofs.Spec.EpochCache.get_base_reward_altair
    CacheProofs.Spec.EpochCache.get_base_reward_per_increment at hb
  rw [htotal] at hb
  simp only [CacheProofs.Spec.EpochCache.getValidator, hv, CacheProofs.Spec.EpochCache.uint64Mul,
    CacheProofs.Spec.EpochCache.uint64Div, CacheProofs.Spec.UINT64_SIZE,
    CacheProofs.EpochCache.integer_squareroot_eq T hT64, Bind.bind, Except.bind, Pure.pure,
    Except.pure, ecValidator, hinc, hfactor] at hb
  unfold EpochProofs.Spec.rewardsBaseReward EpochProofs.Spec.get_base_reward_per_increment
  simp only [EpochProofs.Spec.uint64Mul, EpochProofs.Spec.uint64Div,
    EpochProofs.Spec.UINT64_SIZE, integer_squareroot_eq_sqrt, Bind.bind, Except.bind, Pure.pure,
    Except.pure]
  simp only [Nat.reducePow] at hb ⊢
  split_ifs at hb ⊢
  all_goals
    dsimp only at hb ⊢
    generalize v.effective_balance / p.EFFECTIVE_BALANCE_INCREMENT *
      (p.EFFECTIVE_BALANCE_INCREMENT * p.BASE_REWARD_FACTOR / Nat.sqrt T) = X at hb ⊢
    by_cases hX : X < 18446744073709551616
    · rw [if_pos hX] at hb ⊢; rw [Except.ok.inj hb]
    · rw [if_neg hX] at hb; cases hb

open Aeneas Aeneas.Std Result in
/-- The base reward that Lighthouse reads from the epoch cache equals `rewardsBaseReward` of the
epoch model at the spec total active balance. This is the value that `lhBaseReward` of the
single pass model uses. The cache holds the effective balances of the state and their active
sum, and its table is built from that total. -/
theorem lh_base_reward_eq (p : EpochProofs.Spec.Preset) (s : EpochProofs.Spec.BeaconState)
    (cur : Nat) (hcur : EpochProofs.Spec.get_current_epoch p s = .ok cur)
    (total inc maxEb factor bpe : U64)
    (hinc : inc.val = p.EFFECTIVE_BALANCE_INCREMENT)
    (hfactor : factor.val = p.BASE_REWARD_FACTOR)
    (hinc1 : 1 ≤ inc.val) (hbpe1 : 1 ≤ bpe.val)
    (hincf : inc.val * factor.val ≤ U64.max) (hfit : maxEb.val * factor.val ≤ U64.max)
    (hcap : maxEb.val / inc.val < 4294967295)
    (hinv : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator) cur)
      (s.validators.map (·.effective_balance)))
    (ebs : Slice U64) (hebs : ebs.val.map (·.val) = s.validators.map (·.effective_balance))
    (index : Usize) (v : EpochProofs.Spec.Validator) (hv : s.validators[index.val]? = some v)
    (hmult : v.effective_balance % inc.val = 0) (hle : v.effective_balance ≤ maxEb.val)
    (T : Nat) (hT : EpochProofs.Spec.get_total_active_balance p s = .ok T) :
    ∃ tbl, types.state.base_rewards.base_rewards total inc maxEb factor bpe false =
        ok (.Ok tbl) ∧
      ∃ r, types.state.base_rewards.get_base_reward ebs (alloc.vec.Vec.deref tbl) inc
          index = ok (.Ok r) ∧
        EpochProofs.Spec.rewardsBaseReward p T v = .ok r.val := by
  let cfg : CacheProofs.Spec.EpochCache.Config :=
    ⟨p.EFFECTIVE_BALANCE_INCREMENT, p.BASE_REWARD_FACTOR, bpe.val⟩
  let vs := s.validators.map ecValidator
  have hebs' : s.validators.map (·.effective_balance) = vs.map (·.effective_balance) := by
    simp [vs, List.map_map, Function.comp_def, ecValidator]
  obtain ⟨r0, hr0, hspec0⟩ := CacheProofs.EpochCache.total_active_balance_equiv cfg vs cur
    (s.validators.map (·.effective_balance)) total inc hinc hebs' hinv
  obtain ⟨r1, hr1, hr1v⟩ := CacheProofs.EpochCache.floor_total_active_balance_spec total inc
  rw [hr0] at hr1
  cases hr1
  have htotal : CacheProofs.Spec.EpochCache.get_total_active_balance cfg ⟨vs, cur⟩ =
      .ok (max inc.val total.val) := by rw [hspec0, hr1v]
  have hv' : vs[index.val]? = some (ecValidator v) := by simp [vs, hv]
  have hebs2 : ebs.val.map (·.val) = vs.map (·.effective_balance) := by rw [hebs, hebs']
  obtain ⟨tbl, htbl, r, hr, hspec⟩ := CacheProofs.EpochCache.get_base_reward_equiv cfg vs cur
    total inc maxEb factor bpe false hinc hfactor rfl hinc1 hbpe1 hincf hfit hcap htotal ebs
    hebs2 index (ecValidator v) hv' hmult hle
  refine ⟨tbl, htbl, r, hr, ?_⟩
  obtain ⟨r2, hr2, hT2⟩ := lh_total_active_balance_eq p s cur hcur
    (s.validators.map (·.effective_balance)) total inc hinc rfl hinv
  rw [hr0] at hr2
  cases hr2
  rw [hT] at hT2
  have hTv : T = max inc.val total.val := by
    have := Except.ok.inj hT2; rw [this, hr1v]
  have hT64 : max inc.val total.val < 2 ^ 64 := by
    rw [← hr1v]; exact r0.hBounds
  simp only [Bool.false_eq_true, if_false] at hspec
  rw [hTv]
  exact rewardsBaseReward_of_altair p cfg ⟨vs, cur⟩ index.val v _ r.val rfl rfl hv' htotal hT64
    hspec

end EpochProofs.CacheBridge
