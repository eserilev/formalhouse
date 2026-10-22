import EpochProofs.Sanity.Invariants.Totality
import EpochProofs.Spec.PresetCfg

/-!
# The per-validator epoch steps and the pending deposits succeed

`process_epoch_total` takes two step facts, `MidOk` and `DepOk`. This file proves both on
mainnet, from the facts at the epoch input and `RowBounds`.

The four per-validator steps (inactivity, rewards, registry, slashings) run as passes over rows.
Each row step returns `ok` when its row and the pass state have small values, and keeps them
small for the next row.

Error sources and why they do not fire:
- Inactivity: `score + INACTIVITY_SCORE_BIAS`. `RowBounds.scores` keeps scores below `2^22`.
- Rewards: `base_reward * weight * participating_increments`. The base reward is at most
  `2048 * 2023907` Gwei because the total active balance is at least `10^9`, and the
  participating increments are at most `2^57 / 10^9` (`RowBounds.supply`). The inactivity
  penalty `effective_balance * inactivity_score` stays below `2^64` for the same reason as
  the scores (F5).
- Registry: `compute_exit_epoch_and_update_churn`. An ejected validator has at most
  `EJECTION_BALANCE` and the exit churn is at least `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA`, so
  each exit adds one epoch at most. `RowBounds.churn` and `RowBounds.count` keep the earliest
  exit epoch below `2^63`.
- Slashings: `penalty_per_increment * increments`. The penalty per increment is at most
  `2 * 10^9`.
- Pending deposits: the churn sums and `increase_balance`. `RowBounds.funds` bounds the
  balances, the pending deposits and `deposit_balance_to_consume` together.

`RowBounds.participation` bounds the reward sum: each flag's participating increments are at
most `1024` times the active increments.
-/

namespace EpochProofs.Spec

/-! ## Small arithmetic facts -/

theorem trw_bind_ok {α β : Type} (a : α) (f : α → SpecM β) : (Except.ok a >>= f) = f a := rfl

theorem trw_sub_le (a b : Nat) : @LE.le Nat _ (saturating_sub a b) a := by
  unfold saturating_sub; split <;> exact Nat.sub_le _ _

/-! ## Inactivity -/

theorem validatorEligible_total (previous_epoch : Epoch) (v : Validator)
    (hprev : previous_epoch + 1 < 2 ^ 64) : ∃ b, validatorEligible previous_epoch v = .ok b := by
  unfold validatorEligible
  split
  · exact ⟨_, rfl⟩
  · split
    · rw [tot_add hprev, trw_bind_ok]; exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem inactivityScoreStep_total (p : Preset) (participating in_leak : Bool) (score : Uint64)
    (h : score + p.INACTIVITY_SCORE_BIAS < 2 ^ 64) :
    ∃ x, inactivityScoreStep p participating in_leak score = .ok x ∧
      x ≤ score + p.INACTIVITY_SCORE_BIAS := by
  unfold inactivityScoreStep
  cases participating
  · simp only [Bool.false_eq_true, if_false]
    rw [tot_add h, trw_bind_ok]
    refine ⟨_, rfl, ?_⟩
    split
    · exact le_refl _
    · exact trw_sub_le _ _
  · simp only [if_true]
    rw [pure_bind]
    refine ⟨_, rfl, ?_⟩
    have h1 := trw_sub_le score 1
    have h2 : score ≤ score + p.INACTIVITY_SCORE_BIAS := Nat.le_add_right _ _
    split
    · exact Nat.le_trans h1 h2
    · exact Nat.le_trans (trw_sub_le _ _) (Nat.le_trans h1 h2)

theorem inactivityRowStep_total [PresetCfg] (previous_epoch : Epoch) (in_leak : Bool) (r : Row)
    (hprev : previous_epoch + 1 < 2 ^ 64) (hscore : r.inactivity_score + 4 < 2 ^ 64) :
    ∃ x, inactivityRowStep P previous_epoch in_leak () r = .ok ((), x) ∧
      x = { r with inactivity_score := x.inactivity_score } ∧
      x.inactivity_score ≤ r.inactivity_score + 4 := by
  unfold inactivityRowStep
  obtain ⟨b, hb⟩ := validatorEligible_total previous_epoch r.validator hprev
  rw [hb, trw_bind_ok]
  cases b
  · exact ⟨r, rfl, rfl, Nat.le_add_right _ _⟩
  · obtain ⟨x, hx, hle⟩ := inactivityScoreStep_total P (rowHitsTarget previous_epoch r)
      in_leak r.inactivity_score hscore
    simp only [if_true]
    rw [hx, trw_bind_ok]
    exact ⟨_, rfl, rfl, hle⟩

/-! ## Rewards -/

theorem flagDelta_total (base w : Nat) (part head leak : Bool) (inc act : Nat)
    (h1 : base * w * inc < 2 ^ 64) (h2 : act * 64 < 2 ^ 64) (h3 : 0 < act)
    (h4 : base * w < 2 ^ 64) :
    ∃ x, flagDelta base w part head leak inc act = .ok x := by
  have hw : WEIGHT_DENOMINATOR = 64 := rfl
  unfold flagDelta
  split
  · split
    · rw [tot_mul h4, trw_bind_ok, tot_mul h1, trw_bind_ok, hw, tot_mul h2, trw_bind_ok,
        tot_div (by omega), trw_bind_ok]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · split
    · rw [tot_mul h4, trw_bind_ok, hw, tot_div (by decide), trw_bind_ok]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem inactivityDelta_total [PresetCfg] (eb score : Nat) (target : Bool) (h : eb * score < 2 ^ 64) :
    ∃ x, inactivityDelta P eb score target = .ok x := by
  unfold inactivityDelta
  split
  · rw [tot_mul h, trw_bind_ok, tot_mul (by decide), trw_bind_ok, tot_div (by decide)]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- On mainnet, with a total active balance of at least one increment, the base reward of a
validator with at most `MAX_EFFECTIVE_BALANCE_ELECTRA` is at most `2048 * 2023907`. -/
theorem rewardsBaseReward_small [PresetCfg] (tab : Gwei) (v : Validator) (htab : 1000000000 ≤ tab)
    (hmax : v.effective_balance ≤ 2048000000000) :
    ∃ b, rewardsBaseReward P tab v = .ok b ∧ b ≤ 4144961536 := by
  have hroot : 31622 ≤ integer_squareroot tab :=
    le_integer_squareroot _ _ (Nat.le_trans (by decide) htab)
  obtain ⟨(r : Nat), hr⟩ : ∃ r : Nat, integer_squareroot tab = r := ⟨_, rfl⟩
  rw [hr] at hroot
  have hper : 1000000000 * 64 / r ≤ 2023907 :=
    Nat.le_trans (Nat.div_le_div_left hroot (by decide)) (by decide)
  have he : v.effective_balance / 1000000000 ≤ 2048 :=
    Nat.le_trans (Nat.div_le_div_right hmax) (by decide)
  have hprod : v.effective_balance / 1000000000 * (1000000000 * 64 / r) ≤ 4144961536 :=
    Nat.le_trans (Nat.mul_le_mul he hper) (by decide)
  have hr0 : r ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hroot)
  refine ⟨v.effective_balance / 1000000000 * (1000000000 * 64 / r), ?_, hprod⟩
  have hm : (1000000000 : Nat) * 64 < UINT64_SIZE := by decide
  have hlt : v.effective_balance / 1000000000 * (1000000000 * 64 / r) < UINT64_SIZE :=
    Nat.lt_of_le_of_lt hprod (by decide)
  simp only [rewardsBaseReward, get_base_reward_per_increment, P, Preset.ofVar, uint64Div,
    uint64Mul, hr, hr0, hm, hlt, bind, Except.bind, pure, Except.pure, if_true, if_false,
    show (1000000000 : Nat) ≠ 0 from by decide]

/-- The facts that the reward step of a row reads from the context. -/
structure RewardsCtxOk (ctx : RewardsContext) : Prop where
  tab : 1000000000 ≤ ctx.total_active_balance
  active_pos : 0 < ctx.active_increments
  active : ctx.active_increments < 2 ^ 57
  source : ctx.source_increments ≤ 144115188
  target : ctx.target_increments ≤ 144115188
  head : ctx.head_increments ≤ 144115188
  rsource : ctx.source_increments ≤ 1024 * ctx.active_increments
  rtarget : ctx.target_increments ≤ 1024 * ctx.active_increments
  rhead : ctx.head_increments ≤ 1024 * ctx.active_increments
  prev : ctx.previous_epoch + 1 < 2 ^ 64

theorem rewardsRowDeltas_total [PresetCfg] (ctx : RewardsContext) (hc : RewardsCtxOk ctx) (r : Row)
    (hmax : r.validator.effective_balance ≤ 2048000000000)
    (hscore : r.inactivity_score < 2 ^ 23) :
    ∃ ds, rewardsRowDeltas P ctx r = .ok ds := by
  unfold rewardsRowDeltas
  have hel : ∃ b, rewardsEligible ctx.previous_epoch r.validator = .ok b := by
    unfold rewardsEligible
    split
    · exact ⟨_, rfl⟩
    · split
      · rw [tot_add hc.prev, trw_bind_ok]; exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := hel
  rw [hb, trw_bind_ok]
  cases b
  · exact ⟨_, rfl⟩
  · simp only [if_true]
    obtain ⟨base, hbase, hble⟩ := rewardsBaseReward_small _ r.validator hc.tab hmax
    rw [hbase, trw_bind_ok]
    have hw1 : TIMELY_SOURCE_WEIGHT = 14 := rfl
    have hw2 : TIMELY_TARGET_WEIGHT = 26 := rfl
    have hw3 : TIMELY_HEAD_WEIGHT = 14 := rfl
    have ha64 : ctx.active_increments * 64 < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hc.active (by decide)) (by decide)
    have hbw : ∀ w inc, w ≤ 26 → inc ≤ 144115188 → base * w * inc < 2 ^ 64 := by
      intro w inc hw hi
      have : base * w * inc ≤ 4144961536 * 26 * 144115188 :=
        Nat.mul_le_mul (Nat.mul_le_mul hble hw) hi
      exact Nat.lt_of_le_of_lt this (by decide)
    have hbw' : ∀ w, w ≤ 26 → base * w < 2 ^ 64 := by
      intro w hw
      have : base * w ≤ 4144961536 * 26 := Nat.mul_le_mul hble hw
      exact Nat.lt_of_le_of_lt this (by decide)
    unfold rewardDeltas
    obtain ⟨x1, h1⟩ := flagDelta_total base TIMELY_SOURCE_WEIGHT
      (rewardsParticipating ctx.previous_epoch r TIMELY_SOURCE_FLAG_INDEX) false ctx.in_leak
      ctx.source_increments ctx.active_increments (hbw _ _ (by rw [hw1]; decide) hc.source) ha64
      hc.active_pos (hbw' _ (by rw [hw1]; decide))
    obtain ⟨x2, h2⟩ := flagDelta_total base TIMELY_TARGET_WEIGHT
      (rewardsParticipating ctx.previous_epoch r TIMELY_TARGET_FLAG_INDEX) false ctx.in_leak
      ctx.target_increments ctx.active_increments (hbw _ _ (by rw [hw2]) hc.target) ha64
      hc.active_pos (hbw' _ (by rw [hw2]))
    obtain ⟨x3, h3⟩ := flagDelta_total base TIMELY_HEAD_WEIGHT
      (rewardsParticipating ctx.previous_epoch r TIMELY_HEAD_FLAG_INDEX) true ctx.in_leak
      ctx.head_increments ctx.active_increments (hbw _ _ (by rw [hw3]; decide) hc.head) ha64
      hc.active_pos (hbw' _ (by rw [hw3]; decide))
    have hi : r.validator.effective_balance * r.inactivity_score < 2 ^ 64 := by
      have : r.validator.effective_balance * r.inactivity_score ≤ 2048000000000 * 2 ^ 23 :=
        Nat.mul_le_mul hmax (Nat.le_of_lt hscore)
      exact Nat.lt_of_le_of_lt this (by decide)
    obtain ⟨x4, h4⟩ := inactivityDelta_total r.validator.effective_balance r.inactivity_score
      (rewardsParticipating ctx.previous_epoch r TIMELY_TARGET_FLAG_INDEX) hi
    rw [h1, trw_bind_ok, h2, trw_bind_ok, h3, trw_bind_ok, h4, trw_bind_ok]
    exact ⟨_, rfl⟩

/-- `rewardsSequential` succeeds when the balance plus all rewards fits, and it adds at most
the rewards. -/
theorem rewardsSequential_total (b : Nat) (ds : List (Nat × Nat))
    (h : b + (ds.map (·.1)).sum < 2 ^ 64) :
    ∃ b' : Nat, rewardsSequential b ds = .ok b' ∧ b' ≤ b + (ds.map (·.1)).sum := by
  induction ds generalizing b with
  | nil => exact ⟨b, rfl, by simp⟩
  | cons d ds ih =>
    obtain ⟨rw, pn⟩ := d
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have hadd : b + rw < 2 ^ 64 := by omega
    have hle : @LE.le Nat _ (saturating_sub (b + rw) pn) (b + rw) := trw_sub_le _ _
    obtain ⟨b', hb', hle'⟩ := ih (saturating_sub (b + rw) pn)
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right hle _) (by omega))
    refine ⟨b', ?_, ?_⟩
    · simp only [rewardsSequential, List.foldlM_cons, bind, Except.bind] at hb' ⊢
      rw [tot_add hadd]
      exact hb'
    · generalize saturating_sub (b + rw) pn = e at hle hle'
      exact Nat.le_trans hle' (Nat.le_trans (Nat.add_le_add_right hle _)
        (Nat.le_of_eq (Nat.add_assoc _ _ _)))

theorem rewardsRowStep_total [PresetCfg] (ctx : RewardsContext) (hc : RewardsCtxOk ctx) (r : Row)
    (hmax : r.validator.effective_balance ≤ 2048000000000)
    (hscore : r.inactivity_score < 2 ^ 23)
    (hbal : r.balance + 4 * r.validator.effective_balance < 2 ^ 64) :
    ∃ x : Row, rewardsRowStep P ctx () r = .ok ((), x) ∧
      x = { r with balance := x.balance } ∧
      @LE.le Nat _ x.balance (r.balance + 4 * r.validator.effective_balance) := by
  obtain ⟨ds, hds⟩ := rewardsRowDeltas_total ctx hc r hmax hscore
  obtain ⟨st, tt, ht, i, base, rfl, hbase, -, hrew, -⟩ :=
    rewardsRowDeltas_bounds P ctx r ds hds
  have h256 : 256 * base ≤ r.validator.effective_balance := by
    rcases hbase with rfl | hb
    · exact Nat.zero_le _
    · exact rewardsBaseReward_bound_mainnet _ _ _ hc.tab hb
  have hr := hrew 1024 hc.rsource hc.rtarget hc.rhead
  have hsum : (([st, tt, ht, (0, i)] : List (Gwei × Gwei)).map (·.1)).sum ≤
      4 * r.validator.effective_balance := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    obtain ⟨(e : Nat), he⟩ : ∃ e : Nat, r.validator.effective_balance = e := ⟨_, rfl⟩
    rw [he] at h256 ⊢
    have h256' : @LE.le Nat _ (256 * base) e := h256
    generalize st.1 = a at hr ⊢
    generalize tt.1 = b at hr ⊢
    generalize ht.1 = c at hr ⊢
    show @LE.le Nat _ (a + (b + (c + (0 + 0)))) (4 * e)
    omega
  obtain ⟨b', hb', hle⟩ := rewardsSequential_total r.balance [st, tt, ht, (0, i)]
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left hsum _) hbal)
  refine ⟨{ r with balance := b' }, ?_, rfl, Nat.le_trans hle (Nat.add_le_add_left hsum _)⟩
  simp only [rewardsRowStep, hds, trw_bind_ok, hb']
  rfl

/-! ## Registry -/

theorem exit_churn_total [PresetCfg] (tab : Gwei) (htab : tab < 2 ^ 60) :
    ∃ c : Nat, get_exit_churn_limit P tab = .ok c ∧ 128000000000 ≤ c ∧ c < 2 ^ 60 := by
  unfold get_exit_churn_limit
  rw [tot_div (by decide), trw_bind_ok]
  dsimp only
  rw [tot_mod (by decide), trw_bind_ok]
  have hm : P.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA = 128000000000 := rfl
  have hq : P.CHURN_LIMIT_QUOTIENT_GLOAS = 32768 := rfl
  have hi : P.EFFECTIVE_BALANCE_INCREMENT = 1000000000 := rfl
  rw [hm, hq, hi]
  obtain ⟨(x : Nat), hx⟩ : ∃ x : Nat, max 128000000000 (tab / 32768) = x := ⟨_, rfl⟩
  have hx1 : 128000000000 ≤ x := by rw [← hx]; exact Nat.le_max_left _ _
  have hx2 : x < 2 ^ 60 := by
    rw [← hx]
    have h' : @LT.lt Nat _ tab (2 ^ 60) := htab
    exact Nat.max_lt.mpr ⟨by decide, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h'⟩
  rw [hx, tot_sub (Nat.mod_le _ _)]
  refine ⟨_, rfl, ?_, ?_⟩ <;> omega

theorem exitChurnStep_total [PresetCfg] (tab : Gwei) (cur : Nat) (eb E B c : Nat)
    (hc : get_exit_churn_limit P tab = .ok c) (hc1 : 128000000000 ≤ c)
    (hc2 : c < 2 ^ 60) (hcur : cur + 5 < 2 ^ 62) (heb : eb ≤ 16000000000)
    (hE : E < 2 ^ 63) (hB : B < 2 ^ 62) :
    ∃ e E' B' : Nat, exitChurnStep P tab cur eb E B = .ok (e, E', B') ∧
      e = E' ∧ E' ≤ max E (cur + 5) + 1 ∧ B' ≤ max B c := by
  have hact : compute_activation_exit_epoch P cur = .ok (cur + 5) := by
    have h1 : cur + 1 < 2 ^ 64 := by omega
    have h2 : cur + 1 + 4 < 2 ^ 64 := by omega
    simp [compute_activation_exit_epoch, tot_add h1, tot_add h2, P, Preset.ofVar, bind,
      Except.bind]
  have hEmax : max E (cur + 5) + 1 < 2 ^ 64 := by
    have := Nat.max_lt.mpr ⟨hE, show cur + 5 < 2 ^ 63 by omega⟩
    omega
  unfold exitChurnStep
  rw [hact, trw_bind_ok, hc, trw_bind_ok]
  dsimp only
  generalize hE' : max E (cur + 5) = E1 at hEmax ⊢
  have hE1 : E ≤ E1 := hE' ▸ Nat.le_max_left _ _
  generalize hB1 : (if E < E1 then c else B) = B1
  have hB1le : B1 ≤ max B c := by
    rw [← hB1]; split
    · exact Nat.le_max_right _ _
    · exact Nat.le_max_left _ _
  have hB1lt : B1 < 2 ^ 62 := by
    have := Nat.max_lt.mpr ⟨hB, Nat.lt_trans hc2 (by decide)⟩
    exact Nat.lt_of_le_of_lt hB1le this
  split
  · rename_i hgt
    have hgt' : B1 < eb := hgt
    have hs1 : uint64Sub eb B1 = .ok (eb - B1) := tot_sub (Nat.le_of_lt hgt')
    have hs2 : uint64Sub (eb - B1) 1 = .ok (eb - B1 - 1) := tot_sub (by omega)
    have hd : (eb - B1 - 1) / c = 0 := Nat.div_eq_of_lt (by omega)
    rw [hs1, trw_bind_ok, hs2, trw_bind_ok, tot_div (by omega), trw_bind_ok, hd,
      tot_add (by decide), trw_bind_ok, tot_add (by omega), trw_bind_ok,
      tot_mul (by omega), trw_bind_ok, tot_add (by omega), trw_bind_ok,
      tot_sub (by omega), trw_bind_ok]
    refine ⟨_, _, _, rfl, rfl, by omega, ?_⟩
    have : c ≤ max B c := Nat.le_max_right _ _
    omega
  · rename_i hle
    have hle' : eb ≤ B1 := Nat.le_of_not_lt hle
    rw [tot_sub hle', trw_bind_ok]
    exact ⟨_, _, _, rfl, rfl, by omega, by omega⟩

theorem registryRowStep_total [PresetCfg] (tab : Gwei) (cur fin act c : Nat)
    (hc : get_exit_churn_limit P tab = .ok c) (hc1 : 128000000000 ≤ c)
    (hc2 : c < 2 ^ 60) (hcur : cur + 5 < 2 ^ 62) (E B : Nat) (hE : E < 2 ^ 63)
    (hB : B < 2 ^ 62) (r : Row) :
    ∃ (E' B' : Nat) (f : RegistryFields),
      registryRowStep P tab cur fin act (E, B) r =
        .ok ((E', B'), { r with validator := r.validator.withRegistryFields f }) ∧
      E' ≤ max E (cur + 5) + 1 ∧ B' ≤ max B c := by
  have hcur1 : cur + 1 < 2 ^ 64 := by omega
  have hE0 : E ≤ max E (cur + 5) + 1 := Nat.le_succ_of_le (Nat.le_max_left _ _)
  have hB0 : B ≤ max B c := Nat.le_max_left _ _
  unfold registryRowStep registryStepExclusive
  split
  · rw [tot_add hcur1, trw_bind_ok]
    try simp only [pure_bind]
    exact ⟨_, _, _, rfl, hE0, hB0⟩
  · split
    · unfold exitStep
      split
      · simp only [registryFieldsOf, pure, Except.pure, bind, Except.bind]
        exact ⟨_, _, _, rfl, hE0, hB0⟩
      · rename_i hej _
        have heb : r.validator.effective_balance ≤ 16000000000 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hej
          exact hej.2
        obtain ⟨e, E', B', hx, rfl, hE', hB'⟩ := exitChurnStep_total tab cur
          r.validator.effective_balance E B c hc hc1 hc2 hcur heb hE hB
        have hw : e + 256 < 2 ^ 64 := by
          have := Nat.max_lt.mpr ⟨hE, show cur + 5 < 2 ^ 63 by omega⟩
          omega
        simp only [registryFieldsOf] at hx ⊢
        rw [hx, trw_bind_ok]
        have hd : P.MIN_VALIDATOR_WITHDRAWABILITY_DELAY = 256 := rfl
        simp only [hd, pure_bind]
        rw [tot_add hw, trw_bind_ok]
        try simp only [pure_bind]
        exact ⟨_, _, _, rfl, hE', hB'⟩
    · split
      · try simp only [pure_bind]
        exact ⟨_, _, _, rfl, hE0, hB0⟩
      · try simp only [pure_bind]
        exact ⟨_, _, _, rfl, hE0, hB0⟩

/-! ## Slashings -/

theorem slashingsPreamble_per [PresetCfg] (tab : Gwei) (slashings : List Gwei) (adj per : Gwei)
    (htab : 1000000000 ≤ tab)
    (h : slashingsPreamble P tab slashings = .ok (adj, per)) :
    @LE.le Nat _ per 2000000000 := by
  unfold slashingsPreamble at h
  obtain ⟨(sm : Nat), -, h⟩ := except_bind_ok h
  obtain ⟨(m : Nat), -, h⟩ := except_bind_ok h
  obtain ⟨(q : Nat), hq, h⟩ := except_bind_ok h
  obtain ⟨(d : Nat), hd, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, -⟩ := uint64Div_ok_eq hq
  obtain ⟨rfl, -⟩ := uint64Div_ok_eq hd
  have hi : P.EFFECTIVE_BALANCE_INCREMENT = 1000000000 := rfl
  rw [hi]
  have htab' : @LE.le Nat _ 1000000000 tab := htab
  obtain ⟨(t : Nat), ht⟩ : ∃ t : Nat, tab = t := ⟨_, rfl⟩
  rw [ht] at htab' ⊢
  have hq1 : 1 ≤ t / 1000000000 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have hmin : min m t ≤ t := Nat.min_le_right _ _
  apply Nat.le_trans (Nat.div_le_div_right hmin)
  apply (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr
  omega

theorem slashingsRowStep_total [PresetCfg] (target per : Nat) (hper : per ≤ 2000000000) (r : Row)
    (hmax : r.validator.effective_balance ≤ 2048000000000) :
    ∃ x : Row, slashingsRowStep P target per () r = .ok ((), x) ∧
      x = { r with balance := x.balance } ∧ @LE.le Nat _ x.balance r.balance := by
  unfold slashingsRowStep slashingBalanceStep
  split
  · rw [tot_div (by decide), trw_bind_ok]
    have he : r.validator.effective_balance / P.EFFECTIVE_BALANCE_INCREMENT ≤ 2048 :=
      Nat.le_trans (Nat.div_le_div_right hmax) (by decide)
    have hm : per * (r.validator.effective_balance / P.EFFECTIVE_BALANCE_INCREMENT) <
        2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mul_le_mul hper he) (by decide)
    rw [tot_mul hm, trw_bind_ok, pure_bind]
    exact ⟨_, rfl, rfl, trw_sub_le _ _⟩
  · rw [pure_bind]
    exact ⟨r, rfl, rfl, Nat.le_refl _⟩

/-! ## Passes with a relation between the old and the new rows -/

/-- `P` holds between each old row and its new row. -/
def RowRel (P : Row → Row → Prop) : List Row → List Row → Prop
  | [], [] => True
  | x :: xs, y :: ys => P x y ∧ RowRel P xs ys
  | _, _ => False

theorem RowRel.cons [PresetCfg] {P : Row → Row → Prop} {x y : Row} {xs ys : List Row}
    (h : RowRel P (x :: xs) (y :: ys)) : P x y ∧ RowRel P xs ys := h

theorem passM_rel [PresetCfg] {A : Type} (f : A → Row → SpecM (A × Row)) (I : Nat → A → Prop)
    (P : Row → Row → Prop) (Q : Row → Prop)
    (hf : ∀ r j a, Q r → I j a → ∃ a' r', f a r = .ok (a', r') ∧ I (j + 1) a' ∧ P r r') :
    ∀ (rows : List Row) (k : Nat) (a : A), I k a → (∀ r ∈ rows, Q r) →
      ∃ a' ys, passM f a rows = .ok (a', ys) ∧ I (k + rows.length) a' ∧ RowRel P rows ys := by
  intro rows
  induction rows with
  | nil => intro k a hI _; exact ⟨a, [], rfl, by simpa using hI, trivial⟩
  | cons r rs ih =>
    intro k a hI hQ
    obtain ⟨a1, r1, h1, hI1, hP⟩ := hf r k a (hQ r (by simp)) hI
    obtain ⟨a2, ys, h2, hI2, hR⟩ := ih (k + 1) a1 hI1 (fun x hx => hQ x (by simp [hx]))
    refine ⟨a2, r1 :: ys, ?_, ?_, ⟨hP, hR⟩⟩
    · rw [passM_cons, h1, tot_bind_ok, h2, tot_bind_ok]; rfl
    · simp only [List.length_cons]
      have : k + 1 + rs.length = k + (rs.length + 1) := by omega
      rw [← this]; exact hI2

theorem RowRel.length [PresetCfg] {P : Row → Row → Prop} :
    ∀ {xs ys : List Row}, RowRel P xs ys → ys.length = xs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨-, h2⟩ := RowRel.cons h
    simp [RowRel.length h2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem RowRel.map_eq [PresetCfg] {P : Row → Row → Prop} {β : Type} (g : Row → β)
    (hg : ∀ a b, P a b → g b = g a) :
    ∀ {xs ys : List Row}, RowRel P xs ys → ys.map g = xs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨h1, h2⟩ := RowRel.cons h
    simp only [List.map_cons, hg _ _ h1, RowRel.map_eq g hg h2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem RowRel.sum_le [PresetCfg] {P : Row → Row → Prop} (g h : Row → Nat)
    (hg : ∀ a b, P a b → g b ≤ g a + h a) :
    ∀ {xs ys : List Row}, RowRel P xs ys → (ys.map g).sum ≤ (xs.map g).sum + (xs.map h).sum
  | [], [], _ => by simp
  | a :: _, b :: _, hr => by
    obtain ⟨h1, h2⟩ := RowRel.cons hr
    simp only [List.map_cons, List.sum_cons]
    have e1 := hg a b h1
    have e2 := RowRel.sum_le g h hg h2
    omega
  | [], _ :: _, hr => hr.elim
  | _ :: _, [], hr => hr.elim

theorem RowRel.forall [PresetCfg] {P : Row → Row → Prop} (Q Q' : Row → Prop)
    (hq : ∀ a b, Q a → P a b → Q' b) :
    ∀ {xs ys : List Row}, RowRel P xs ys → (∀ r ∈ xs, Q r) → ∀ r ∈ ys, Q' r
  | [], [], _, _ => by simp
  | a :: _, b :: _, hr, hx => by
    obtain ⟨h1, h2⟩ := RowRel.cons hr
    intro r hr'
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact hq a r (hx a (by simp)) h1
    · exact RowRel.forall Q Q' hq h2 (fun x hx' => hx x (by simp [hx'])) r hr'
  | [], _ :: _, hr, _ => hr.elim
  | _ :: _, [], hr, _ => hr.elim

/-- `passM_rel` where the step may use a bound `K` on the number of rows done. -/
theorem passM_rel_bounded [PresetCfg] {A : Type} (f : A → Row → SpecM (A × Row)) (I : Nat → A → Prop)
    (P : Row → Row → Prop) (K : Nat)
    (hf : ∀ r j a, I j a → j < K → ∃ a' r', f a r = .ok (a', r') ∧ I (j + 1) a' ∧ P r r') :
    ∀ (rows : List Row) (k : Nat) (a : A), I k a → k + rows.length ≤ K →
      ∃ a' ys, passM f a rows = .ok (a', ys) ∧ I (k + rows.length) a' ∧ RowRel P rows ys := by
  intro rows
  induction rows with
  | nil => intro k a hI _; exact ⟨a, [], rfl, by simpa using hI, trivial⟩
  | cons r rs ih =>
    intro k a hI hK
    simp only [List.length_cons] at hK
    obtain ⟨a1, r1, h1, hI1, hP⟩ := hf r k a hI (by omega)
    obtain ⟨a2, ys, h2, hI2, hR⟩ := ih (k + 1) a1 hI1 (by omega)
    refine ⟨a2, r1 :: ys, ?_, ?_, ⟨hP, hR⟩⟩
    · rw [passM_cons, h1, tot_bind_ok, h2, tot_bind_ok]; rfl
    · simp only [List.length_cons]
      have : k + 1 + rs.length = k + (rs.length + 1) := by omega
      rw [← this]; exact hI2

/-! ## The four passes -/

def PInact (a b : Row) : Prop :=
  b = { a with inactivity_score := b.inactivity_score } ∧
    @LE.le Nat _ b.inactivity_score (a.inactivity_score + 4)

def PBal (a b : Row) : Prop :=
  b = { a with balance := b.balance } ∧
    @LE.le Nat _ b.balance (a.balance + 4 * a.validator.effective_balance)

def PReg (a b : Row) : Prop :=
  ∃ f : RegistryFields, b = { a with validator := a.validator.withRegistryFields f }

def PSlash (a b : Row) : Prop :=
  b = { a with balance := b.balance } ∧ @LE.le Nat _ b.balance a.balance

theorem inactivity_pass_total [PresetCfg] (rows : List Row) (prev : Epoch) (in_leak : Bool)
    (hprev : prev + 1 < 2 ^ 64) (hs : ∀ r ∈ rows, @LT.lt Nat _ r.inactivity_score (2 ^ 22)) :
    ∃ ys, passM (inactivityRowStep P prev in_leak) () rows = .ok ((), ys) ∧
      RowRel PInact rows ys := by
  obtain ⟨u, ys, h, -, hr⟩ := passM_rel (inactivityRowStep P prev in_leak)
    (fun _ _ => True) PInact (fun r => @LT.lt Nat _ r.inactivity_score (2 ^ 22))
    (fun r _ _ hq _ => by
      obtain ⟨x, hx, he, hle⟩ := inactivityRowStep_total prev in_leak r hprev
        (Nat.lt_trans (Nat.add_lt_add_right hq 4) (by decide))
      exact ⟨(), x, hx, trivial, he, hle⟩) rows 0 () trivial hs
  exact ⟨ys, h, hr⟩

theorem rewards_pass_total [PresetCfg] (rows : List Row) (ctx : RewardsContext) (hc : RewardsCtxOk ctx)
    (hs : ∀ r ∈ rows, r.validator.effective_balance ≤ 2048000000000 ∧
      @LT.lt Nat _ r.inactivity_score (2 ^ 23) ∧
      r.balance + 4 * r.validator.effective_balance < 2 ^ 64) :
    ∃ ys, passM (rewardsRowStep P ctx) () rows = .ok ((), ys) ∧
      RowRel PBal rows ys := by
  obtain ⟨u, ys, h, -, hr⟩ := passM_rel (rewardsRowStep P ctx)
    (fun _ _ => True) PBal (fun r => r.validator.effective_balance ≤ 2048000000000 ∧
      @LT.lt Nat _ r.inactivity_score (2 ^ 23) ∧
      r.balance + 4 * r.validator.effective_balance < 2 ^ 64)
    (fun r _ _ hq _ => by
      obtain ⟨x, hx, he, hle⟩ := rewardsRowStep_total ctx hc r hq.1 hq.2.1 hq.2.2
      exact ⟨(), x, hx, trivial, he, hle⟩) rows 0 () trivial hs
  exact ⟨ys, h, hr⟩

theorem registry_pass_total [PresetCfg] (rows : List Row) (tab : Gwei) (cur fin act c : Nat)
    (hc : get_exit_churn_limit P tab = .ok c) (hc1 : 128000000000 ≤ c)
    (hc2 : c < 2 ^ 60) (hcur : cur + 5 < 2 ^ 62) (E B : Nat) (hE : E < 2 ^ 62)
    (hB : B < 2 ^ 61) (hn : rows.length < 2 ^ 40) :
    ∃ E' B' ys, passM (registryRowStep P tab cur fin act) (E, B) rows =
      .ok ((E', B'), ys) ∧ RowRel PReg rows ys := by
  obtain ⟨⟨E', B'⟩, ys, h, -, hr⟩ := passM_rel_bounded
    (registryRowStep P tab cur fin act)
    (fun j a => @LE.le Nat _ a.1 (max E (cur + 5) + j) ∧ @LE.le Nat _ a.2 (max B c)) PReg
    rows.length
    (fun r j a hI hj => by
      obtain ⟨(E1 : Nat), (B1 : Nat)⟩ := a
      obtain ⟨hI1, hI2⟩ := hI
      dsimp only at hI1 hI2
      generalize hMdef : max E (cur + 5) = M at hI1
      have hM : M < 2 ^ 62 := hMdef ▸ Nat.max_lt.mpr ⟨hE, by omega⟩
      have hcM : cur + 5 ≤ M := hMdef ▸ Nat.le_max_right _ _
      generalize hBdef : max B c = Bm at hI2
      have hBm : Bm < 2 ^ 61 := hBdef ▸ Nat.max_lt.mpr ⟨hB, Nat.lt_trans hc2 (by decide)⟩
      have hcB : c ≤ Bm := hBdef ▸ Nat.le_max_right _ _
      have hE1 : E1 < 2 ^ 63 := by omega
      have hB1 : B1 < 2 ^ 62 := by omega
      obtain ⟨E2, B2, f, hx, hE2, hB2⟩ := registryRowStep_total tab cur fin act c hc hc1 hc2 hcur
        E1 B1 hE1 hB1 r
      refine ⟨(E2, B2), _, hx, ⟨?_, ?_⟩, f, rfl⟩
      · have : max E1 (cur + 5) ≤ M + j :=
          Nat.max_le.mpr ⟨hI1, Nat.le_trans hcM (Nat.le_add_right _ _)⟩
        rw [← hMdef] at this ⊢
        dsimp only
        omega
      · dsimp only
        rw [← hBdef] at hI2 hcB ⊢
        exact Nat.le_trans hB2 (Nat.max_le.mpr ⟨hI2, hcB⟩))
    rows 0 (E, B) ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩ (by omega)
  exact ⟨E', B', ys, h, hr⟩

theorem slashings_pass_total [PresetCfg] (rows : List Row) (target per : Nat) (hper : per ≤ 2000000000)
    (hs : ∀ r ∈ rows, r.validator.effective_balance ≤ 2048000000000) :
    ∃ ys, passM (slashingsRowStep P target per) () rows = .ok ((), ys) ∧
      RowRel PSlash rows ys := by
  obtain ⟨u, ys, h, -, hr⟩ := passM_rel (slashingsRowStep P target per)
    (fun _ _ => True) PSlash (fun r => r.validator.effective_balance ≤ 2048000000000)
    (fun r _ _ hq _ => by
      obtain ⟨x, hx, he, hle⟩ := slashingsRowStep_total target per hper r hq
      exact ⟨(), x, hx, trivial, he, hle⟩) rows 0 () trivial hs
  exact ⟨ys, h, hr⟩

theorem RowRel.comp [PresetCfg] {P Q : Row → Row → Prop} :
    ∀ {xs ys zs : List Row}, RowRel P xs ys → RowRel Q ys zs →
      RowRel (fun a c => ∃ b, P a b ∧ Q b c) xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, h1, h2 => by
    obtain ⟨a1, a2⟩ := RowRel.cons h1
    obtain ⟨b1, b2⟩ := RowRel.cons h2
    exact ⟨⟨_, a1, b1⟩, RowRel.comp a2 b2⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem rowsOf_map_score (s : BeaconState)
    (h : s.inactivity_scores.length = s.validators.length) :
    (rowsOf s).map (·.inactivity_score) = s.inactivity_scores := by
  apply List.ext_getElem
  · simp [rowsOf_length, h]
  · intro i h1 h2
    simp [rowsOf_getElem, List.getD_eq_getElem?_getD, h2]

theorem PInact.key {a b : Row} (h : PInact a b) : rowKey b = rowKey a := by rw [h.1]; rfl
theorem PBal.key {a b : Row} (h : PBal a b) : rowKey b = rowKey a := by rw [h.1]; rfl
theorem PReg.key {a b : Row} (h : PReg a b) : rowKey b = rowKey a := by
  obtain ⟨f, rfl⟩ := h; rfl
theorem PSlash.key {a b : Row} (h : PSlash a b) : rowKey b = rowKey a := by rw [h.1]; rfl

/-- The registry update and the slashings, on a state whose rows have small values. -/
def RegSlashOut (s3 s5 : BeaconState) : Prop :=
  ∃ (ys : List Row) (E B : Nat),
    s5 = { s3.withRows ys with earliest_exit_epoch := E, exit_balance_to_consume := B } ∧
    RowRel (fun a c => ∃ b, PReg a b ∧ PSlash b c) (rowsOf s3) ys

/-- The registry update at the churn total `rtab`, then the slashings at `tab`. Fulu runs the
registry update at a different churn total than the slashings. -/
theorem regSlash_total_g [PresetCfg] (s3 : BeaconState) (tab rtab : Gwei) (hrows : RowsOk s3)
    (hslot : s3.slot + 8192 < 2 ^ 64) (hrtab : rtab < 2 ^ 60) (htab_lo : 1000000000 ≤ tab)
    (heb : ∀ v ∈ s3.validators, v.effective_balance ≤ 2048000000000)
    (hn : s3.validators.length < 2 ^ 40) (hE : s3.earliest_exit_epoch < 2 ^ 62)
    (hB : s3.exit_balance_to_consume < 2 ^ 61) (hsl : s3.slashings.sum * 3 < 2 ^ 64) :
    OkWith (do
      let s4 ← process_registry_updates P rtab s3
      process_slashings P tab s4) (RegSlashOut s3) := by
  have hcur := tot_current_epoch s3
  have hslot' : @LT.lt Nat _ (s3.slot + 8192) (2 ^ 64) := hslot
  have he5 : @LT.lt Nat _ (s3.slot / 32 + 5) (2 ^ 62) := by omega
  have hact := compute_activation_exit_epoch_of_lt P (s3.slot / 32)
    (by show @LT.lt Nat _ (s3.slot / 32 + 1 + 4) (2 ^ 64); omega)
  obtain ⟨c, hc, hc1, hc2⟩ := exit_churn_total rtab hrtab
  obtain ⟨E', B', ys4, hp4, hr4⟩ := registry_pass_total (rowsOf s3) rtab (s3.slot / 32)
    s3.finalized_checkpoint.epoch _ c hc hc1 hc2 he5 s3.earliest_exit_epoch
    s3.exit_balance_to_consume hE hB (by rw [rowsOf_length]; exact hn)
  let s4 : BeaconState :=
    { s3.withRows ys4 with earliest_exit_epoch := E', exit_balance_to_consume := B' }
  have hreg := (process_registry_updates_rows P rtab s3 _ _ hrows hcur hact s4).mpr
    (by rw [hp4]; rfl)
  refine OkWith.bind (OkWith.of_eq hreg rfl) (fun s4' hs4 => ?_)
  subst hs4
  have hk4 : ys4.map rowKey = (rowsOf s3).map rowKey :=
    RowRel.map_eq rowKey (fun _ _ h => h.key) hr4
  have hl4 : ys4.length = s3.validators.length := by rw [RowRel.length hr4, rowsOf_length]
  have hrows4 : RowsOk s4 := rowsOk_withRows s3 ys4 hrows hl4
  have hrw4 : rowsOf s4 = ys4 := rowsOf_withRows s3 ys4 hk4
  obtain ⟨adj, per, hpre⟩ := slashingsPreamble_ok tab s3.slashings hsl htab_lo
  have hper := slashingsPreamble_per tab s3.slashings adj per htab_lo hpre
  have heb4 : ∀ r ∈ ys4, r.validator.effective_balance ≤ 2048000000000 := by
    refine RowRel.forall (fun r => r.validator.effective_balance ≤ 2048000000000)
      (fun r => r.validator.effective_balance ≤ 2048000000000) ?_ hr4 ?_
    · intro a b ha hab
      obtain ⟨f, rfl⟩ := hab
      exact ha
    · intro r hr
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      rw [rowsOf_getElem]
      exact heb _ (List.getElem_mem _)
  obtain ⟨ys5, hp5, hr5⟩ := slashings_pass_total ys4 (s3.slot / 32 + 4096) per hper heb4
  have hcur4 : get_current_epoch P s4 = .ok (s3.slot / 32) := tot_current_epoch s4
  rw [process_slashings_rows P tab s4 (s3.slot / 32) hcur4
    (by show @LT.lt Nat _ (s3.slot / 32 + 4096) (2 ^ 64); omega) adj per hpre hrows4, hrw4]
  have h4096 : P.EPOCHS_PER_SLASHINGS_VECTOR / 2 = 4096 := rfl
  rw [h4096, hp5]
  exact OkWith.of_eq rfl ⟨ys5, E', B', rfl, RowRel.comp hr4 hr5⟩

theorem regSlash_total [PresetCfg] (s3 : BeaconState) (tab : Gwei) (hrows : RowsOk s3)
    (hslot : s3.slot + 8192 < 2 ^ 64) (htab : tab < 2 ^ 60) (htab_lo : 1000000000 ≤ tab)
    (heb : ∀ v ∈ s3.validators, v.effective_balance ≤ 2048000000000)
    (hn : s3.validators.length < 2 ^ 40) (hE : s3.earliest_exit_epoch < 2 ^ 62)
    (hB : s3.exit_balance_to_consume < 2 ^ 61) (hsl : s3.slashings.sum * 3 < 2 ^ 64) :
    OkWith (do
      let s4 ← process_registry_updates P tab s3
      process_slashings P tab s4) (RegSlashOut s3) :=
  regSlash_total_g s3 tab tab hrows hslot htab htab_lo heb hn hE hB hsl

/-! ## The four steps -/

/-- Bounds on a reachable state at the epoch input that the per-validator steps and the pending
deposits need. Each one is a time or supply bound; the pyspec raises without them too.

- `scores`: inactivity scores grow by 4 per epoch of leak, so `2^22` is about one million epochs
  of leak. With a score near `2^23`, `effective_balance * inactivity_score` overflows (F5).
- `supply`: the effective balances sum to less than `2^57` Gwei (about 144M ETH).
- `funds`: the balances, the pending deposits and `deposit_balance_to_consume` sum to less than
  `2^61` Gwei. `deposit_balance_to_consume` is at most the amount of a pending deposit that did
  not fit the churn, so this is a supply bound.
- `earliest`, `exit_balance`, `count`: the exit queue and the registry are far from `2^64`.
- `participation`: each flag's participating increments of the previous epoch are at most
  `1024` times the active increments of the current epoch. Exits are churn limited, so the
  active balance cannot drop by that factor in one epoch unless almost nothing is staked. -/
structure RowBounds [PresetCfg] (t : BeaconState) : Prop where
  scores : ∀ x ∈ t.inactivity_scores, @LT.lt Nat _ x (2 ^ 22)
  supply : totalEffectiveBalance t < 2 ^ 57
  funds : t.balances.sum + (t.pending_deposits.map (·.amount)).sum +
    t.deposit_balance_to_consume < 2 ^ 61
  earliest : t.earliest_exit_epoch < 2 ^ 62
  exit_balance : t.exit_balance_to_consume < 2 ^ 61
  count : t.validators.length < 2 ^ 40
  participation : ∀ tab, get_total_active_balance P t = .ok tab →
    ∀ f, f < 3 → ∀ x, rewardsFlagIncrements P t (t.slot / 32 - 1) f = .ok x →
      @LE.le Nat _ x (1024 * (tab / 1000000000))

theorem trw_sat_one (e : Nat) (h : e ≠ 0) : saturating_sub e 1 = e - 1 := by
  unfold saturating_sub
  split
  · rfl
  · rename_i h'
    have h'' : ¬ (@LT.lt Nat _ 1 e) := h'
    have : e = 1 := by omega
    subst this; rfl

theorem trw_mem_rowsOf {s : BeaconState} (hrows : RowsOk s) {r : Row} (hr : r ∈ rowsOf s) :
    r.validator ∈ s.validators ∧ r.balance ∈ s.balances ∧
      r.inactivity_score ∈ s.inactivity_scores := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hiv : i < s.validators.length := by rw [← rowsOf_length]; exact hi
  rw [rowsOf_getElem]
  obtain ⟨h1, h2, -, -⟩ := hrows
  refine ⟨List.getElem_mem _, ?_, ?_⟩
  · have hb : i < s.balances.length := by rw [h1]; exact hiv
    rw [List.getD_eq_getElem s.balances 0 hb]; exact List.getElem_mem _
  · have hs : i < s.inactivity_scores.length := by rw [h2]; exact hiv
    rw [List.getD_eq_getElem s.inactivity_scores 0 hs]; exact List.getElem_mem _

/-- The state before the registry update: `t` with other balances and inactivity scores. -/
structure S3Facts (t s1 s3 : BeaconState) : Prop where
  slot : s3.slot = t.slot
  rows : RowsOk s3
  vals : s3.validators = t.validators
  bsum : s3.balances.sum ≤ t.balances.sum + 4 * totalEffectiveBalance t
  eee : s3.earliest_exit_epoch = t.earliest_exit_epoch
  ebtc : s3.exit_balance_to_consume = t.exit_balance_to_consume
  slashings : s3.slashings = t.slashings
  randao : s3.randao_mixes = t.randao_mixes
  cons : s3.pending_consolidations = t.pending_consolidations
  pend : s3.pending_deposits = t.pending_deposits
  dbtc : s3.deposit_balance_to_consume = t.deposit_balance_to_consume
  fin : s3.finalized_checkpoint = s1.finalized_checkpoint

theorem trw_sum_map_mul (l : List Row) (g : Row → Nat) (k : Nat) :
    (l.map (fun r => k * g r)).sum = k * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem post_of_regSlash [PresetCfg] (t s1 s3 s5 : BeaconState) (hrl : t.randao_mixes.length = 65536)
    (hsll : t.slashings.length = 8192)
    (heb : EBOk P t) (hcons : ConsolidationsInRange t) (hrb : RowBounds t)
    (hfin0 : s1.finalized_checkpoint.epoch ≤ t.slot / 32) (h3 : S3Facts t s1 s3)
    (h5 : RegSlashOut s3 s5) : TailFrame t s5 ∧ DepFrame t s5 := by
  obtain ⟨ys, E, B, rfl, hr⟩ := h5
  have hlen : ys.length = s3.validators.length := by rw [RowRel.length hr, rowsOf_length]
  have hlt : ys.length = t.validators.length := by rw [hlen, h3.vals]
  have hrows5 := rowsOk_withRows s3 ys h3.rows hlen
  -- balances
  have hbal : (ys.map (·.balance)).sum ≤ s3.balances.sum := by
    have := RowRel.sum_le (·.balance) (fun _ => 0) (fun a c hq => by
      obtain ⟨b, ⟨f, rfl⟩, hs⟩ := hq
      exact hs.2) hr
    rw [rowsOf_map_balance s3 h3.rows.1] at this
    simpa using this
  have hbsum : @LE.le Nat _ (ys.map (·.balance)).sum
      (t.balances.sum + 4 * totalEffectiveBalance t) := Nat.le_trans hbal h3.bsum
  -- effective balances
  have hvmap : (ys.map (fun r => r.validator.effective_balance)) =
      (rowsOf s3).map (fun r => r.validator.effective_balance) :=
    RowRel.map_eq (fun r => r.validator.effective_balance) (fun a c hq => by
      obtain ⟨b, ⟨f, rfl⟩, hs⟩ := hq
      rw [hs.1]; rfl) hr
  have hteb : totalEffectiveBalance (s3.withRows ys) = totalEffectiveBalance t := by
    unfold totalEffectiveBalance
    simp only [BeaconState.withRows, List.map_map, Function.comp_def]
    rw [hvmap, ← h3.vals, ← rowsOf_map_validator s3, List.map_map]
    rfl
  have hmax : ∀ v ∈ (ys.map (·.validator)), v.effective_balance ≤ 2048000000000 := by
    intro v hv
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hv
    refine RowRel.forall (fun r => r.validator.effective_balance ≤ 2048000000000)
      (fun r => r.validator.effective_balance ≤ 2048000000000) ?_ hr ?_ r hr'
    · intro a c ha hq
      obtain ⟨b, ⟨f, rfl⟩, hs⟩ := hq
      rw [hs.1]; exact ha
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [rowsOf_getElem]
      have hmem : s3.validators[i]'(by rw [← rowsOf_length]; exact hi) ∈ t.validators := by
        rw [← h3.vals]; exact List.getElem_mem _
      exact (heb _ hmem).2
  have hsup : @LT.lt Nat _ (totalEffectiveBalance t) (2 ^ 57) := hrb.supply
  have hfunds : @LT.lt Nat _ (t.balances.sum + (t.pending_deposits.map (·.amount)).sum +
      t.deposit_balance_to_consume) (2 ^ 61) := hrb.funds
  have hbt : @LT.lt Nat _ t.balances.sum (2 ^ 61) := by omega
  refine ⟨⟨h3.slot, hrows5, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨h3.pend, h3.dbtc, ?_, hbsum, hteb, h3.fin ▸ hfin0⟩⟩
  · show s3.randao_mixes.length = 65536
    rw [h3.randao]; exact hrl
  · show s3.slashings.length = 8192
    rw [h3.slashings]; exact hsll
  · intro c hc
    have hc' : c ∈ t.pending_consolidations := h3.cons ▸ hc
    have := hcons c hc'
    show c.source_index < (ys.map (·.validator)).length ∧
      c.target_index < (ys.map (·.validator)).length
    rw [List.length_map, hlt]; exact this
  · show @LT.lt Nat _ (ys.map (·.balance)).sum (2 ^ 62)
    omega
  · intro v hv
    exact Nat.lt_of_le_of_lt (hmax v hv) (by decide)
  · show @LT.lt Nat _ (totalEffectiveBalance (s3.withRows ys)) (2 ^ 62)
    rw [hteb]; omega
  · show (ys.map (·.validator)).length = t.validators.length
    rw [List.length_map, hlt]

theorem trw_inact_genesis [PresetCfg] (s : BeaconState) (h : s.slot / 32 = 0) :
    process_inactivity_updates P s = .ok s := by
  unfold process_inactivity_updates
  rw [tot_current_epoch, trw_bind_ok, h]
  rfl

theorem trw_rewards_genesis [PresetCfg] (tab : Gwei) (s : BeaconState) (h : s.slot / 32 = 0) :
    process_rewards_and_penalties P tab s = .ok s := by
  unfold process_rewards_and_penalties
  rw [tot_current_epoch, trw_bind_ok, h]
  rfl

/-- The inactivity, rewards, registry and slashings steps after justification and
finalization, with one total active balance `tab` and the registry update at the churn total
`g tab`. Gloas uses `g = id`. Fulu uses `fuluTabM`. -/
def MidCore [PresetCfg] (g : Gwei → Gwei) (t : BeaconState) : Prop :=
  ∀ s1, JFShape t s1 → s1.finalized_checkpoint.epoch ≤ t.slot / 32 →
    (t.slot / 32 ≠ 0 → s1.finalized_checkpoint.epoch + 1 ≤ t.slot / 32) →
    ∀ tab, get_total_active_balance P s1 = .ok tab →
    OkWith (do
      let s2 ← process_inactivity_updates P s1
      let s3 ← process_rewards_and_penalties P tab s2
      let s4 ← process_registry_updates P (g tab) s3
      process_slashings P tab s4) (fun s => TailFrame t s ∧ DepFrame t s)

/-- On mainnet, the inactivity, rewards, registry and slashings steps succeed after
justification and finalization, under `RowBounds`, for any churn total `g tab` below `2^60`. -/
theorem midCore_of_rowBounds [PresetCfg] (g : Gwei → Gwei) (hg : ∀ x, x < 2 ^ 57 → g x < 2 ^ 60)
    (t : BeaconState) (hrows : RowsOk t) (hslot : t.slot + 8192 < 2 ^ 64)
    (heb : EBOk P t) (hrl : t.randao_mixes.length = 65536)
    (hsll : t.slashings.length = 8192)
    (hcons : ConsolidationsInRange t) (hsl : t.slashings.sum * 3 < 2 ^ 64)
    (hrb : RowBounds t) : MidCore g t := by
  intro s1 hshape hfin0 hfin tab htab
  obtain ⟨cp1, cp2, cp3, bits, hs1⟩ := hshape
  have hv1 : s1.validators = t.validators := by rw [hs1]
  have hrows1 : RowsOk s1 := by rw [hs1]; exact hrows
  have hslot1 : s1.slot = t.slot := by rw [hs1]
  have htabeq : get_total_active_balance P s1 =
      get_total_active_balance P t := by rw [hs1]; rfl
  have hincq : ∀ e f, rewardsFlagIncrements P s1 e f =
      rewardsFlagIncrements P t e f := by intro e f; rw [hs1]; rfl
  have hteb1 : totalEffectiveBalance s1 = totalEffectiveBalance t := by rw [hs1]; rfl
  have hslot' : @LT.lt Nat _ (t.slot + 8192) (2 ^ 64) := hslot
  have hsup : @LT.lt Nat _ (totalEffectiveBalance t) (2 ^ 57) := hrb.supply
  have hfunds : @LT.lt Nat _ (t.balances.sum + (t.pending_deposits.map (·.amount)).sum +
      t.deposit_balance_to_consume) (2 ^ 61) := hrb.funds
  have hcur : get_current_epoch P s1 = .ok (t.slot / 32) := by
    rw [← hslot1]; exact tot_current_epoch s1
  obtain ⟨tab', htab', htab_lo, htab_hi⟩ := get_total_active_balance_bounds P s1
    (t.slot / 32) hcur (by rw [hteb1]; exact Nat.lt_trans hsup (by decide))
  rw [htab] at htab'
  cases htab'
  have htab_lo' : @LE.le Nat _ 1000000000 tab := htab_lo
  have htab57 : @LT.lt Nat _ tab (2 ^ 57) := by
    have h' : @LE.le Nat _ tab (max 1000000000 (totalEffectiveBalance t)) := by
      rw [← hteb1]; exact htab_hi
    exact Nat.lt_of_le_of_lt h' (Nat.max_lt.mpr ⟨by decide, hsup⟩)
  have hn : t.validators.length < 2 ^ 40 := hrb.count
  have hebmax : ∀ v ∈ t.validators, v.effective_balance ≤ 2048000000000 :=
    fun v hv => (heb v hv).2
  -- the last two steps from a state with the facts `S3Facts`
  have hlast : ∀ s3, S3Facts t s1 s3 → OkWith (do
      let s4 ← process_registry_updates P (g tab) s3
      process_slashings P tab s4) (fun s => TailFrame t s ∧ DepFrame t s) := by
    intro s3 h3
    refine OkWith.mono (regSlash_total_g s3 tab (g tab) h3.rows (by rw [h3.slot]; exact hslot)
      (hg tab htab57) htab_lo' (by rw [h3.vals]; exact hebmax)
      (by rw [h3.vals]; exact hn) (by rw [h3.eee]; exact hrb.earliest)
      (by rw [h3.ebtc]; exact hrb.exit_balance) (by rw [h3.slashings]; exact hsl)) ?_
    intro s5 h5
    exact post_of_regSlash t s1 s3 s5 hrl hsll heb hcons hrb hfin0 h3 h5
  have hb1 : s1.balances = t.balances := by rw [hs1]
  have hbase : S3Facts t s1 s1 := by
    refine ⟨hslot1, hrows1, hv1, ?_, by rw [hs1], by rw [hs1], by rw [hs1], by rw [hs1],
      by rw [hs1], by rw [hs1], by rw [hs1], rfl⟩
    rw [hb1]; exact Nat.le_add_right _ _
  by_cases hgen : t.slot / 32 = 0
  · -- genesis: no inactivity and no rewards
    have hg1 : s1.slot / 32 = 0 := by rw [hslot1]; exact hgen
    rw [trw_inact_genesis s1 hg1, trw_bind_ok, trw_rewards_genesis tab s1 hg1, trw_bind_ok]
    exact hlast s1 hbase
  · have he : t.slot / 32 ≠ 0 := hgen
    have heN : ¬ (@Eq Nat (t.slot / 32) 0) := hgen
    have hgen' : t.slot / 32 ≠ GENESIS_EPOCH := by simpa [GENESIS_EPOCH] using he
    have hprev : get_previous_epoch P s1 = .ok (t.slot / 32 - 1) := by
      rw [tot_previous_epoch, hslot1, trw_sat_one _ he]
    have hfinp : @LE.le Nat _ s1.finalized_checkpoint.epoch (t.slot / 32 - 1) := by
      have h' : @LE.le Nat _ (s1.finalized_checkpoint.epoch + 1) (t.slot / 32) := hfin he
      omega
    have hleak : ∃ b, is_in_inactivity_leak P s1 = .ok b := by
      unfold is_in_inactivity_leak get_finality_delay
      rw [hprev, trw_bind_ok, tot_sub hfinp, trw_bind_ok]
      exact ⟨_, rfl⟩
    obtain ⟨lk, hlk⟩ := hleak
    -- inactivity
    have hQ1 : ∀ r ∈ rowsOf s1, r.validator.effective_balance ≤ 2048000000000 ∧
        @LT.lt Nat _ r.inactivity_score (2 ^ 22) ∧ @LT.lt Nat _ r.balance (2 ^ 61) := by
      intro r hr
      obtain ⟨m1, m2, m3⟩ := trw_mem_rowsOf hrows1 hr
      rw [hs1] at m1 m2 m3
      have hbt : @LT.lt Nat _ t.balances.sum (2 ^ 61) := by omega
      exact ⟨hebmax _ m1, hrb.scores _ m3, Nat.lt_of_le_of_lt (tot_mem_le_sum m2) hbt⟩
    obtain ⟨ys2, hp2, hr2⟩ := inactivity_pass_total (rowsOf s1) (t.slot / 32 - 1) lk
      (by show @LT.lt Nat _ (t.slot / 32 - 1 + 1) (2 ^ 64); omega) (fun r hr => (hQ1 r hr).2.1)
    have hi := (process_inactivity_updates_rows P s1 (t.slot / 32) (t.slot / 32 - 1)
      lk hrows1 hcur hgen' hprev hlk (s1.withRows ys2)).mpr (by rw [hp2]; rfl)
    rw [hi, trw_bind_ok]
    have hk2 : ys2.map rowKey = (rowsOf s1).map rowKey :=
      RowRel.map_eq rowKey (fun _ _ h => h.key) hr2
    have hvr2 : ys2.map (·.validator) = s1.validators := by
      rw [RowRel.map_eq (·.validator) (fun a b h => by rw [h.1]) hr2, rowsOf_map_validator]
    have hbr2 : ys2.map (·.balance) = s1.balances := by
      rw [RowRel.map_eq (·.balance) (fun a b h => by rw [h.1]) hr2,
        rowsOf_map_balance s1 hrows1.1]
    have hl2 : ys2.length = s1.validators.length := by rw [RowRel.length hr2, rowsOf_length]
    have hrows2 : RowsOk (s1.withRows ys2) := rowsOk_withRows s1 ys2 hrows1 hl2
    have hrw2 : rowsOf (s1.withRows ys2) = ys2 := rowsOf_withRows s1 ys2 hk2
    -- the rewards context
    obtain ⟨ctx, hctx, hsrc, htgt, hhd⟩ := rewardsContextOf_bounds P tab s1 hrows1
      (t.slot / 32) (t.slot / 32 - 1) hcur hprev
      (by show @Ne Nat (t.slot / 32 - 1) (t.slot / 32); omega) (by decide)
      (by rw [hteb1]; exact Nat.lt_trans hsup (by decide)) hfinp
    obtain ⟨hcp, hcs, hct, hch, hca, -, hctot⟩ := rewardsContextOf_ok P tab s1 ctx hctx
    have hpe : ctx.previous_epoch = t.slot / 32 - 1 := by
      rw [hprev] at hcp; exact (Except.ok.inj hcp).symm
    have hact_eq : ctx.active_increments = tab / 1000000000 := by
      simp only [uint64Div] at hca
      split at hca
      · cases hca
      · exact (Except.ok.inj hca).symm
    have htab_t : get_total_active_balance P t = .ok tab := htabeq ▸ htab
    have hratio : ∀ f, f < 3 → ∀ x, rewardsFlagIncrements P s1 ctx.previous_epoch f =
        .ok x → @LE.le Nat _ x (1024 * ctx.active_increments) := by
      intro f hf x hx
      rw [hincq, hpe] at hx
      rw [hact_eq]
      exact hrb.participation tab htab_t f hf x hx
    have hmaxinc : @LE.le Nat _ (max P.EFFECTIVE_BALANCE_INCREMENT
        (totalEffectiveBalance s1) / P.EFFECTIVE_BALANCE_INCREMENT) 144115188 := by
      rw [hteb1]
      have hm : @LT.lt Nat _ (max 1000000000 (totalEffectiveBalance t)) (2 ^ 57) :=
        Nat.max_lt.mpr ⟨by decide, hsup⟩
      show @LE.le Nat _ (max 1000000000 (totalEffectiveBalance t) / 1000000000) 144115188
      generalize max 1000000000 (totalEffectiveBalance t) = m at hm ⊢
      omega
    have hc : RewardsCtxOk ctx := by
      refine ⟨by rw [hctot]; exact htab_lo', by rw [hact_eq]; exact Nat.div_pos htab_lo' (by decide),
        by rw [hact_eq]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) htab57,
        Nat.le_trans hsrc hmaxinc, Nat.le_trans htgt hmaxinc, Nat.le_trans hhd hmaxinc,
        hratio _ (by decide) _ hcs, hratio _ (by decide) _ hct, hratio _ (by decide) _ hch, ?_⟩
      rw [hpe]; show @LT.lt Nat _ (t.slot / 32 - 1 + 1) (2 ^ 64); omega
    have hctx2 : rewardsContextOf P tab (s1.withRows ys2) = .ok ctx := by
      rw [rewardsContextOf_withRows _ _ _ _ hvr2]; exact hctx
    have hQ2 : ∀ r ∈ ys2, r.validator.effective_balance ≤ 2048000000000 ∧
        @LT.lt Nat _ r.inactivity_score (2 ^ 23) ∧
        r.balance + 4 * r.validator.effective_balance < 2 ^ 64 := by
      refine RowRel.forall _ _ ?_ hr2 hQ1
      intro a b ha hab
      obtain ⟨hq1, hq2, hq3⟩ := ha
      rw [hab.1]
      refine ⟨hq1, ?_, ?_⟩
      · have := hab.2; show @LT.lt Nat _ b.inactivity_score (2 ^ 23); omega
      · show @LT.lt Nat _ (a.balance + 4 * a.validator.effective_balance) (2 ^ 64)
        have h1 : @LE.le Nat _ a.validator.effective_balance 2048000000000 := hq1
        omega
    obtain ⟨ys3, hp3, hr3⟩ := rewards_pass_total ys2 ctx hc hQ2
    have hcur2 : get_current_epoch P (s1.withRows ys2) = .ok (t.slot / 32) := hcur
    have hrw := (process_rewards_and_penalties_rows P tab (s1.withRows ys2) hrows2
      (t.slot / 32) hcur2 hgen' ctx hctx2 ((s1.withRows ys2).withRows ys3)).mpr
      (by rw [hrw2, hp3]; rfl)
    rw [hrw, trw_bind_ok]
    have hl3 : ys3.length = (s1.withRows ys2).validators.length := by
      rw [RowRel.length hr3]; simp [BeaconState.withRows, hl2]
    have hvr3 : ys3.map (·.validator) = ys2.map (·.validator) :=
      RowRel.map_eq (·.validator) (fun a b h => by rw [h.1]) hr3
    have hb3 := RowRel.sum_le (·.balance) (fun r => 4 * r.validator.effective_balance)
      (fun a b h => h.2) hr3
    have h4 : (ys2.map (fun r => 4 * r.validator.effective_balance)).sum =
        4 * totalEffectiveBalance t := by
      rw [trw_sum_map_mul, ← hteb1]
      unfold totalEffectiveBalance
      rw [← hvr2, List.map_map]
      rfl
    refine hlast _ ⟨hslot1, rowsOk_withRows _ ys3 hrows2 hl3, ?_, ?_, by rw [hs1]; rfl,
      by rw [hs1]; rfl, by rw [hs1]; rfl, by rw [hs1]; rfl, by rw [hs1]; rfl, by rw [hs1]; rfl,
      by rw [hs1]; rfl, rfl⟩
    · show ys3.map (·.validator) = t.validators
      rw [hvr3, hvr2, hv1]
    · show @LE.le Nat _ (ys3.map (·.balance)).sum (t.balances.sum + 4 * totalEffectiveBalance t)
      rw [hbr2, h4, hb1] at hb3
      exact hb3

/-- On mainnet, the inactivity, rewards, registry and slashings steps succeed after
justification and finalization, under `RowBounds`. -/
theorem midOk_of_rowBounds [PresetCfg] (t : BeaconState) (hrows : RowsOk t) (hslot : t.slot + 8192 < 2 ^ 64)
    (heb : EBOk P t) (hvec : t.VectorLengths P)
    (hcons : ConsolidationsInRange t) (hsl : t.slashings.sum * 3 < 2 ^ 64)
    (hrb : RowBounds t) : MidOk t := by
  intro s1 hshape hfin0 hfin
  have hcore := midCore_of_rowBounds id (fun x hx => Nat.lt_trans hx (by decide)) t hrows hslot
    heb hvec.2.2.1 hvec.2.2.2.1 hcons hsl hrb s1 hshape hfin0 hfin
  obtain ⟨cp1, cp2, cp3, bits, hs1⟩ := hshape
  have hrows1 : RowsOk s1 := by rw [hs1]; exact hrows
  have hslot1 : s1.slot = t.slot := by rw [hs1]
  have hteb1 : totalEffectiveBalance s1 = totalEffectiveBalance t := by rw [hs1]; rfl
  have hslot' : @LT.lt Nat _ (t.slot + 8192) (2 ^ 64) := hslot
  have hcur : get_current_epoch P s1 = .ok (t.slot / 32) := by
    rw [← hslot1]; exact tot_current_epoch s1
  obtain ⟨tab, htab, -, -⟩ := get_total_active_balance_bounds P s1
    (t.slot / 32) hcur (by rw [hteb1]; exact Nat.lt_trans hrb.supply (by decide))
  have hact := compute_activation_exit_epoch_of_lt P (t.slot / 32)
    (by show @LT.lt Nat _ (t.slot / 32 + 1 + 4) (2 ^ 64); omega)
  have hfar : t.slot / 32 < FAR_FUTURE_EPOCH := by
    show @LT.lt Nat _ (t.slot / 32) (2 ^ 64 - 1); omega
  have hsame := specFourSteps_sameOk P s1 tab htab hrows1 (t.slot / 32) _ hcur
    hact hfar
  obtain ⟨v, hv, hp⟩ := hcore tab htab
  exact ⟨v, (hsame v).mpr hv, hp⟩

/-! ## Pending deposits -/

/-- A `for` loop with an invariant on the rest of the list. `F` holds at the end, whether the
loop stops early or runs to the end. -/
theorem forIn_total_rest {α β : Type} (I : List α → β → Prop) (F : β → Prop)
    (f : α → β → SpecM (ForInStep β))
    (hf : ∀ a rest b, I (a :: rest) b → ∃ r, f a b = .ok r ∧
      (∀ c, r = .done c → F c) ∧ (∀ c, r = .yield c → I rest c))
    (hend : ∀ b, I [] b → F b) :
    ∀ (l : List α) (b : β), I l b → ∃ r, forIn l b f = .ok r ∧ F r := by
  intro l
  induction l with
  | nil => intro b hb; exact ⟨b, rfl, hend b hb⟩
  | cons x xs ih =>
    intro b hb
    rw [List.forIn_cons]
    obtain ⟨r, hr, hdone, hyield⟩ := hf x xs b hb
    rw [hr]
    cases r with
    | done c => exact ⟨c, rfl, hdone c rfl⟩
    | yield c => exact ih c (hyield c rfl)

theorem act_churn_total [PresetCfg] (tab : Gwei) :
    ∃ c : Nat, get_activation_churn_limit P tab = .ok c ∧ c ≤ 256000000000 := by
  unfold get_activation_churn_limit
  rw [tot_div (by decide), trw_bind_ok]
  dsimp only
  rw [tot_mod (by decide), trw_bind_ok, tot_sub (Nat.mod_le _ _), trw_bind_ok]
  exact ⟨_, rfl, Nat.min_le_left _ _⟩

/-- The loop state of `process_pending_deposits` while `rest` is still to come. -/
def DepInv (s : BeaconState) (avail : Nat) (rest : List PendingDeposit)
    (r : MProd (List PendingDeposit) (MProd Bool (MProd Uint64 (MProd Uint64 BeaconState)))) :
    Prop :=
  @LE.le Nat _ r.2.2.2.1 avail ∧
  @LE.le Nat _ (r.2.2.2.2.balances.sum + (rest.map (·.amount)).sum)
    (s.balances.sum + (s.pending_deposits.map (·.amount)).sum) ∧
  @LE.le Nat _ (totalEffectiveBalance r.2.2.2.2 + (rest.map (·.amount)).sum)
    (totalEffectiveBalance s + (s.pending_deposits.map (·.amount)).sum) ∧
  RowsOk r.2.2.2.2 ∧
  (∀ v ∈ r.2.2.2.2.validators, @LT.lt Nat _ v.effective_balance (2 ^ 62)) ∧
  r.2.2.2.2.slot = s.slot ∧ r.2.2.2.2.randao_mixes = s.randao_mixes ∧
  r.2.2.2.2.slashings = s.slashings ∧
  r.2.2.2.2.pending_consolidations = s.pending_consolidations ∧
  s.validators.length ≤ r.2.2.2.2.validators.length

theorem DepInv.weaken {s : BeaconState} {avail : Nat} {a : PendingDeposit}
    {rest : List PendingDeposit} {r : MProd (List PendingDeposit)
      (MProd Bool (MProd Uint64 (MProd Uint64 BeaconState)))}
    (h : DepInv s avail (a :: rest) r) : DepInv s avail [] r := by
  unfold DepInv at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at h2 h3 ⊢
  exact ⟨h1, by omega, by omega, h4⟩

/-- `apply_pending_deposit` keeps `DepInv` when the deposit leaves the rest. -/
theorem DepInv.apply {s : BeaconState} {avail : Nat} {a : PendingDeposit}
    {rest : List PendingDeposit} {pp : List PendingDeposit} {b : Bool} {n p p' : Uint64}
    {st st' : BeaconState} (hP : @LT.lt Nat _ (s.balances.sum +
      (s.pending_deposits.map (·.amount)).sum) (2 ^ 62))
    (h : DepInv s avail (a :: rest) ⟨pp, b, n, p, st⟩) (hp : @LE.le Nat _ p' avail)
    (hstep : DepStep st st' a.amount) : DepInv s avail rest ⟨pp, b, n + 1, p', st'⟩ := by
  unfold DepInv at h ⊢
  obtain ⟨-, h2, h3, -, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [List.map_cons, List.sum_cons] at h2 h3
  refine ⟨hp, ?_, ?_, hstep.rows, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : @LE.le Nat _ st'.balances.sum (st.balances.sum + a.amount) := hstep.bsum
    dsimp only; omega
  · have hb : @LE.le Nat _ (totalEffectiveBalance st')
        (totalEffectiveBalance st + a.amount) := hstep.teb
    dsimp only; omega
  · intro v hv
    rcases hstep.ebs v hv with hv' | hv'
    · exact h5 v hv'
    · have : @LE.le Nat _ v.effective_balance a.amount := hv'
      omega
  · dsimp only; rw [hstep.slot]; exact h6
  · dsimp only; rw [hstep.randao]; exact h7
  · dsimp only; rw [hstep.slashings]; exact h8
  · dsimp only; rw [hstep.cons]; exact h9
  · exact Nat.le_trans h10 hstep.vlen

/-- A step that keeps the state keeps `DepInv` without the deposit. -/
theorem DepInv.skip {s : BeaconState} {avail : Nat} {a : PendingDeposit}
    {rest : List PendingDeposit} {pp pp' : List PendingDeposit} {b : Bool} {n p : Uint64}
    {st : BeaconState} (h : DepInv s avail (a :: rest) ⟨pp, b, n, p, st⟩) :
    DepInv s avail rest ⟨pp', b, n + 1, p, st⟩ := by
  unfold DepInv at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.map_cons, List.sum_cons] at h2 h3
  exact ⟨h1, by dsimp only; omega, by dsimp only; omega, h4⟩

/-- `process_pending_deposits` at the churn total `g tab` succeeds after the eth1 data reset.
Gloas uses `g = id`. Fulu uses `fuluTabM`. -/
def DepCore [PresetCfg] (g : Gwei → Gwei) (o : Oracle) (t : BeaconState) : Prop :=
  ∀ s tab, TailFrame t s → DepFrame t s → get_total_active_balance P s = .ok tab →
    OkWith (process_pending_deposits P (g tab) (apply_pending_deposit P o)
      s) (TailFrame t)

theorem depCore_of_rowBounds [PresetCfg] (g : Gwei → Gwei) (o : Oracle) (t : BeaconState)
    (hslot0 : t.slot + 8192 < 2 ^ 64) (hrb : RowBounds t) : DepCore g o t := by
  intro s tab hf hd htab
  have hteb : @LT.lt Nat _ (totalEffectiveBalance t) (2 ^ 57) := hrb.supply
  have hfunds : @LT.lt Nat _ (t.balances.sum + (t.pending_deposits.map (·.amount)).sum +
      t.deposit_balance_to_consume) (2 ^ 61) := hrb.funds
  obtain ⟨tab', htab', -, htab_hi⟩ := get_total_active_balance_bounds P s _
    (tot_current_epoch s) (Nat.lt_trans hf.teb (by decide))
  rw [htab] at htab'
  cases htab'
  have htab60 : tab < 2 ^ 60 := by
    have h' : @LE.le Nat _ tab (max 1000000000 (totalEffectiveBalance s)) := htab_hi
    rw [hd.teb] at h'
    exact Nat.lt_of_le_of_lt h' (Nat.max_lt.mpr ⟨by decide, Nat.lt_trans hteb (by decide)⟩)
  have hslot : @LT.lt Nat _ (s.slot + 8192) (2 ^ 64) := by rw [hf.slot]; exact hslot0
  have hdbtc : @LT.lt Nat _ s.deposit_balance_to_consume (2 ^ 61) := by rw [hd.dbtc]; omega
  have hfin : @LE.le Nat _ s.finalized_checkpoint.epoch (s.slot / 32) := by
    rw [hf.slot]; exact hd.fin
  unfold process_pending_deposits
  rw [tot_current_epoch, tot_bind_ok, tot_add (by omega), tot_bind_ok]
  obtain ⟨c, hc, hcle⟩ := act_churn_total (g tab)
  rw [hc, trw_bind_ok,
    tot_add (show @LT.lt Nat _ (s.deposit_balance_to_consume + c) (2 ^ 64) by omega), trw_bind_ok]
  dsimp only
  have hfs : compute_start_slot_at_epoch P s.finalized_checkpoint.epoch =
      .ok (s.finalized_checkpoint.epoch * 32) := by
    unfold compute_start_slot_at_epoch
    have h32 : P.SLOTS_PER_EPOCH = 32 := rfl
    rw [h32]
    exact tot_mul (show @LT.lt Nat _ (s.finalized_checkpoint.epoch * 32) (2 ^ 64) by omega)
  rw [hfs, trw_bind_ok]
  try dsimp only
  have hsb : @LE.le Nat _ s.balances.sum (t.balances.sum + 4 * totalEffectiveBalance t) := hd.bsum
  have hPt : (s.pending_deposits.map (·.amount)).sum = (t.pending_deposits.map (·.amount)).sum := by
    rw [hd.pend]
  have hP : @LT.lt Nat _ (s.balances.sum + (s.pending_deposits.map (·.amount)).sum) (2 ^ 62) := by
    rw [hPt]; omega
  refine OkWith.bind (forIn_total_rest (DepInv s (s.deposit_balance_to_consume + c))
    (DepInv s (s.deposit_balance_to_consume + c) []) _ ?_ (fun _ h => h) s.pending_deposits
    ⟨[], false, 0, 0, s⟩ ?_) (fun r hr => ?_)
  · intro a rest r hI
    obtain ⟨pp, b, n, p, st⟩ := r
    dsimp only
    have hI' := hI
    unfold DepInv at hI'
    obtain ⟨hp, hb, -, hrows', -⟩ := hI'
    dsimp only at hp hb hrows'
    simp only [List.map_cons, List.sum_cons] at hb
    have hsum : @LT.lt Nat _ (st.balances.sum + a.amount) (2 ^ 64) := by omega
    have hamt : @LT.lt Nat _ (p + a.amount) (2 ^ 64) := by omega
    split
    · exact ⟨_, rfl, fun c' hc' => (by cases hc'; exact hI.weaken), fun c' hc' => (by cases hc')⟩
    try simp only [pure_bind]
    split
    · exact ⟨_, rfl, fun c' hc' => (by cases hc'; exact hI.weaken), fun c' hc' => (by cases hc')⟩
    split
    · rename_i hmem
      have hidx : (st.validators.map (·.pubkey)).idxOf a.pubkey < st.validators.length := by
        rw [← List.length_map (f := fun x => x.pubkey)]
        exact List.idxOf_lt_length_iff.mpr hmem
      rw [tot_get hidx, trw_bind_ok]
      try simp only [pure_bind]
      split
      · obtain ⟨st', hst', hstep⟩ := apply_pending_deposit_total o st a hrows' hsum
        rw [hst', trw_bind_ok]
        try simp only [pure_bind]
        exact ⟨_, rfl, fun c' hc' => (by cases hc'),
          fun c' hc' => (by cases hc'; exact DepInv.apply hP hI hp hstep)⟩
      split
      · exact ⟨_, rfl, fun c' hc' => (by cases hc'), fun c' hc' => (by cases hc'; exact DepInv.skip hI)⟩
      rw [tot_add hamt, trw_bind_ok]
      split
      · exact ⟨_, rfl, fun c' hc' => (by cases hc'; exact hI.weaken), fun c' hc' => (by cases hc')⟩
      · rename_i hnot
        have hle : ¬ (@LT.lt Nat _ (s.deposit_balance_to_consume + c) (p + a.amount)) := by
          simpa using hnot
        try simp only [pure_bind]
        rw [trw_bind_ok]
        obtain ⟨st', hst', hstep⟩ := apply_pending_deposit_total o st a hrows' hsum
        rw [hst', trw_bind_ok]
        try simp only [pure_bind]
        exact ⟨_, rfl, fun c' hc' => (by cases hc'),
          fun c' hc' => (by cases hc'; exact DepInv.apply hP hI (Nat.le_of_not_lt hle) hstep)⟩
    · simp only [pure_bind, Bool.false_eq_true, if_false]
      rw [tot_add hamt, trw_bind_ok]
      split
      · exact ⟨_, rfl, fun c' hc' => (by cases hc'; exact hI.weaken), fun c' hc' => (by cases hc')⟩
      · rename_i hnot
        have hle : ¬ (@LT.lt Nat _ (s.deposit_balance_to_consume + c) (p + a.amount)) := by
          simpa using hnot
        try simp only [pure_bind]
        rw [trw_bind_ok]
        obtain ⟨st', hst', hstep⟩ := apply_pending_deposit_total o st a hrows' hsum
        rw [hst', trw_bind_ok]
        try simp only [pure_bind]
        exact ⟨_, rfl, fun c' hc' => (by cases hc'),
          fun c' hc' => (by cases hc'; exact DepInv.apply hP hI (Nat.le_of_not_lt hle) hstep)⟩
  · unfold DepInv
    exact ⟨Nat.zero_le _, Nat.le_refl _, Nat.le_refl _, hf.rows, fun v hv => hf.ebs v hv, rfl, rfl,
      rfl, rfl, Nat.le_refl _⟩
  · obtain ⟨pp, b, n, p, st⟩ := r
    unfold DepInv at hr
    obtain ⟨hp, hb, htb, hrows', hebs', hsl', hra', hss', hpc', hvl'⟩ := hr
    dsimp only at hp hb htb hrows' hebs' hsl' hra' hss' hpc' hvl'
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hb htb
    have htebs : @LE.le Nat _ (totalEffectiveBalance s) (totalEffectiveBalance t) :=
      Nat.le_of_eq hd.teb
    have hframe : ∀ st2 : BeaconState, st2.slot = st.slot → st2.validators = st.validators →
        st2.balances = st.balances → st2.inactivity_scores = st.inactivity_scores →
        st2.previous_epoch_participation = st.previous_epoch_participation →
        st2.current_epoch_participation = st.current_epoch_participation →
        st2.randao_mixes = st.randao_mixes → st2.slashings = st.slashings →
        st2.pending_consolidations = st.pending_consolidations → TailFrame t st2 := by
      intro st2 e1 e2 e3 e4 e5 e6 e7 e8 e9
      obtain ⟨r1, r2, r3, r4⟩ := hrows'
      refine ⟨by rw [e1, hsl', hf.slot], ⟨by rw [e3, e2, r1], by rw [e4, e2, r2], by rw [e5, e2, r3],
        by rw [e6, e2, r4]⟩, by rw [e7, hra', hf.randao], by rw [e8, hss', hf.slashings], ?_, ?_, ?_,
        ?_⟩
      · intro c' hc'
        rw [e9, hpc'] at hc'
        obtain ⟨h1, h2⟩ := hf.cons c' hc'
        rw [e2]
        exact ⟨Nat.lt_of_lt_of_le h1 hvl', Nat.lt_of_lt_of_le h2 hvl'⟩
      · rw [e3]; show @LT.lt Nat _ st.balances.sum (2 ^ 62); omega
      · rw [e2]; exact hebs'
      · have : totalEffectiveBalance st2 = totalEffectiveBalance st := by
          unfold totalEffectiveBalance; rw [e2]
        rw [this]
        show @LT.lt Nat _ (totalEffectiveBalance st) (2 ^ 62)
        rw [hPt] at htb
        omega
    dsimp only
    split
    · rw [tot_sub hp, trw_bind_ok]
      try simp only [pure_bind]
      exact OkWith.pure (hframe _ rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    · exact OkWith.pure (hframe _ rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem depOk_of_rowBounds (o : Oracle) (t : BeaconState) (hslot0 : t.slot + 8192 < 2 ^ 64)
    (hrb : RowBounds t) : DepOk o t :=
  depCore_of_rowBounds id o t hslot0 hrb

/-! ## The whole epoch -/

/-- `process_epoch_total` with the per-validator steps and the pending deposits proved: on
mainnet, the spec `process_epoch` succeeds from the facts at its input, `RowBounds`, and the
committee steps (`CommitteesOk`). -/
theorem process_epoch_total_rows [PresetCfg] (o : Oracle) (t : BeaconState) (hrows : RowsOk t)
    (hslot : t.slot + 8192 < 2 ^ 64) (hlast : (t.slot + 1) % 32 = 0)
    (hvec : t.VectorLengths P) (hffg : FfgInvariant P t)
    (heb : EBOk P t) (hcons : ConsolidationsInRange t)
    (hsl : t.slashings.sum * 3 < 2 ^ 64) (hrb : RowBounds t) (hcomm : CommitteesOk o t) :
    ∃ s', process_epoch P o t = .ok s' :=
  process_epoch_total o t hrows hslot hlast hvec hffg
    (Nat.lt_trans hrb.supply (by decide))
    (midOk_of_rowBounds t hrows hslot heb hvec hcons hsl hrb)
    (depOk_of_rowBounds o t hslot hrb) hcomm

end EpochProofs.Spec
