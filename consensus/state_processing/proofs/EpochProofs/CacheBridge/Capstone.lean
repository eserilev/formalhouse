import EpochProofs.Caches
import EpochProofs.Sanity.Invariants.LighthouseEpoch
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.PresetBounds
import EpochProofs.CacheBridge.EpochCache

/-!
# The cache reads of the epoch give the spec values

The epoch model computes the participation totals and the total active balance with the spec
functions. Lighthouse reads them from the progressive balances cache and the epoch cache. When the
caches are correct at the epoch start state, each value that Lighthouse reads is the spec value.
-/

namespace EpochProofs.CacheBridge

open CacheProofs.ProgressiveBalances (unslashedFlagBalance)

/-- A flag total is at most the sum of all effective balances. -/
theorem unslashedFlagBalance_le (vs : List CacheProofs.Spec.Validator) (ps : List Nat) (e f : Nat) :
    unslashedFlagBalance vs ps e f ≤ (vs.map (·.effective_balance)).sum := by
  induction vs generalizing ps with
  | nil => simp [unslashedFlagBalance]
  | cons v vs ih =>
    cases ps with
    | nil => simp [unslashedFlagBalance]
    | cons q ps =>
      simp only [unslashedFlagBalance, List.map_cons, List.sum_cons]
      have := ih ps
      split <;> omega

theorem unslashedFlagBalance_lt [EpochProofs.Spec.CurrentPreset] (s : EpochProofs.Spec.BeaconState)
    (ps : List Nat) (e f : Nat)
    (h : EpochProofs.Spec.totalEffectiveBalance s < 2 ^ 60) :
    max EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (unslashedFlagBalance (s.validators.map progressiveBalancesValidatorOf) ps e f) < 2 ^ 64 := by
  have h1 := unslashedFlagBalance_le (s.validators.map progressiveBalancesValidatorOf) ps e f
  have h2 : ((s.validators.map progressiveBalancesValidatorOf).map (·.effective_balance)).sum =
      EpochProofs.Spec.totalEffectiveBalance s := by
    simp [EpochProofs.Spec.totalEffectiveBalance, List.map_map, Function.comp_def,
      progressiveBalancesValidatorOf]
  have hinc : EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT < 2 ^ 64 := by
    show (1000000000 : Nat) < 2 ^ 64
    decide
  rw [h2] at h1
  have h6064 : (2 : Nat) ^ 60 < 2 ^ 64 := by norm_num
  exact Nat.max_lt.mpr ⟨hinc, Nat.lt_of_le_of_lt h1 (Nat.lt_trans h h6064)⟩

theorem current_epoch_mainnet [EpochProofs.Spec.CurrentPreset] [EpochProofs.Spec.CurrentPreset.Valid]
    (s : EpochProofs.Spec.BeaconState) :
    EpochProofs.Spec.get_current_epoch EpochProofs.Spec.P s =
      .ok (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) := by
  have h : EpochProofs.Spec.P.SLOTS_PER_EPOCH ≠ 0 := EpochProofs.Spec.P_slots_ne
  simp [EpochProofs.Spec.get_current_epoch, EpochProofs.Spec.compute_epoch_at_slot,
    EpochProofs.Spec.uint64Div, h, pure, Except.pure]

theorem previous_epoch_mainnet [EpochProofs.Spec.CurrentPreset] [EpochProofs.Spec.CurrentPreset.Valid] (s : EpochProofs.Spec.BeaconState) :
    EpochProofs.Spec.get_previous_epoch EpochProofs.Spec.P s =
      .ok (EpochProofs.Spec.saturating_sub
        (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) 1) := by
  simp [EpochProofs.Spec.get_previous_epoch, current_epoch_mainnet, bind, Except.bind, pure,
    Except.pure]

open Aeneas Aeneas.Std Result in
open CacheProofs.ProgressiveBalances (LighthouseProgressiveBalancesCache
  ProgressiveBalancesCacheCorrect lighthousePreviousEpochFlagBalance
  lighthouseCurrentEpochFlagBalance) in
/-- The cache reads that Lighthouse epoch processing makes, at the epoch start state `s` on
mainnet, equal the spec values that the epoch model computes:

- the current and previous epoch flag totals of the progressive balances cache equal
  `get_total_balance(state, get_unslashed_participating_indices(state, flag, epoch))`;
- the floored total active balance of the epoch cache equals `get_total_active_balance`.

The caches satisfy their build invariants: the progressive balances cache is
`ProgressiveBalancesCacheCorrect` with the state, and the epoch cache total is the sum of the
effective balances of the validators active in the current epoch. -/
theorem lighthouse_cache_reads_correct [EpochProofs.Spec.CurrentPreset]
    [EpochProofs.Spec.CurrentPreset.Valid] (s : EpochProofs.Spec.BeaconState)
    (hrows : EpochProofs.Spec.ListLengthsMatch s) (hsupply : EpochProofs.Spec.BalancesFarFromOverflow s)
    (c : LighthouseProgressiveBalancesCache)
    (hc : ProgressiveBalancesCacheCorrect EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (progressiveBalancesStateOf s (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)) c)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (s.validators.map epochCacheValidatorOf)
        (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      (s.validators.map (·.effective_balance))) :
    (∀ f : Usize, f.val < 3 → ∃ x : U64, lighthouseCurrentEpochFlagBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
          f.val (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) >>=
        EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
    (∀ f : Usize, f.val < 3 → 0 < s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH →
      ∃ x : U64, lighthousePreviousEpochFlagBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
          f.val (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH - 1) >>=
        EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
    (∀ inc : U64, inc.val = EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT →
      ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
        EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.P s =
          .ok r.val) := by
  obtain ⟨-, -, hpl, hcl⟩ := hrows
  obtain ⟨-, hteb, -⟩ := hsupply
  have hcur := current_epoch_mainnet s
  have hprev := previous_epoch_mainnet s
  generalize s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH = cur at hc htotal hcur hprev ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact lighthouse_current_flag_balance_eq _ s f hf cur _ hcur hprev hcl
      (unslashedFlagBalance_lt s _ _ _ hteb) c hc.1
  · intro f hf hpos
    have hsat : EpochProofs.Spec.saturating_sub cur 1 = cur - 1 := by
      simp only [EpochProofs.Spec.saturating_sub]
      by_cases h1 : cur > 1
      · rw [if_pos h1]
      · rw [if_neg h1]
        have h1' : ¬ 1 < cur := h1
        have : cur = 1 := Nat.le_antisymm (Nat.not_lt.mp h1') hpos
        rw [this]
    rw [hsat] at hprev
    exact lighthouse_previous_flag_balance_eq _ s f hf cur (cur - 1) hcur hprev
      (Nat.sub_lt hpos Nat.one_pos).ne hpl
      (unslashedFlagBalance_lt s _ _ _ hteb) c hc.2
  · intro inc hinc
    exact lighthouse_total_active_balance_eq _ s cur hcur _ total inc hinc rfl htotal

end EpochProofs.CacheBridge
