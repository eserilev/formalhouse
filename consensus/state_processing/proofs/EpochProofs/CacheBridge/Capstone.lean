import EpochProofs.Caches
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.PresetBounds
import EpochProofs.CacheBridge.EpochCache

/-!
# The Lighthouse epoch equals Etheorem, with the cache reads checked

`lighthouse_order_epoch_etheorem_reachable` (`Etheorem/Final.lean`) is about the epoch model.
The model computes the participation totals and the total active balance with the spec
functions. Lighthouse reads them from the progressive balances cache and the epoch cache.

This file adds the cache side. When the caches are built from the epoch start state (the cache
build invariants `Coherent` and the active sum), each value that Lighthouse reads from them
equals the spec value that the model computes. The build invariants are what the cache proofs
of `CacheProofs` give for the cache build code (`build_coherent`,
`single_pass_total_active_balance`).
-/

namespace EpochProofs.CacheBridge

open CacheProofs.PB (flagSum)

/-- A flag total is at most the sum of all effective balances. -/
theorem flagSum_le (vs : List CacheProofs.Spec.Validator) (ps : List Nat) (e f : Nat) :
    flagSum vs ps e f ≤ (vs.map (·.effective_balance)).sum := by
  induction vs generalizing ps with
  | nil => simp [flagSum]
  | cons v vs ih =>
    cases ps with
    | nil => simp [flagSum]
    | cons q ps =>
      simp only [flagSum, List.map_cons, List.sum_cons]
      have := ih ps
      split <;> omega

theorem flagSum_lt [EpochProofs.Spec.PresetCfg] (s : EpochProofs.Spec.BeaconState) (ps : List Nat) (e f : Nat)
    (h : EpochProofs.Spec.totalEffectiveBalance s < 2 ^ 60) :
    max EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (flagSum (s.validators.map pbValidator) ps e f) < 2 ^ 64 := by
  have h1 := flagSum_le (s.validators.map pbValidator) ps e f
  have h2 : ((s.validators.map pbValidator).map (·.effective_balance)).sum =
      EpochProofs.Spec.totalEffectiveBalance s := by
    simp [EpochProofs.Spec.totalEffectiveBalance, List.map_map, Function.comp_def, pbValidator]
  have hinc : EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT < 2 ^ 64 := by
    show (1000000000 : Nat) < 2 ^ 64
    decide
  rw [h2] at h1
  have h6064 : (2 : Nat) ^ 60 < 2 ^ 64 := by norm_num
  exact Nat.max_lt.mpr ⟨hinc, Nat.lt_of_le_of_lt h1 (Nat.lt_trans h h6064)⟩

theorem current_epoch_mainnet [EpochProofs.Spec.PresetCfg] [EpochProofs.Spec.PresetCfg.Ok]
    (s : EpochProofs.Spec.BeaconState) :
    EpochProofs.Spec.get_current_epoch EpochProofs.Spec.P s =
      .ok (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) := by
  have h : EpochProofs.Spec.P.SLOTS_PER_EPOCH ≠ 0 := EpochProofs.Spec.P_slots_ne
  simp [EpochProofs.Spec.get_current_epoch, EpochProofs.Spec.compute_epoch_at_slot,
    EpochProofs.Spec.uint64Div, h, pure, Except.pure]

theorem previous_epoch_mainnet [EpochProofs.Spec.PresetCfg] [EpochProofs.Spec.PresetCfg.Ok] (s : EpochProofs.Spec.BeaconState) :
    EpochProofs.Spec.get_previous_epoch EpochProofs.Spec.P s =
      .ok (EpochProofs.Spec.saturating_sub
        (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) 1) := by
  simp [EpochProofs.Spec.get_previous_epoch, current_epoch_mainnet, bind, Except.bind, pure,
    Except.pure]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- The cache reads that Lighthouse epoch processing makes, at the epoch start state `s` on
mainnet, equal the spec values that the epoch model computes:

- the current and previous epoch flag totals of the progressive balances cache equal
  `get_total_balance(state, get_unslashed_participating_indices(state, flag, epoch))`;
- the floored total active balance of the epoch cache equals `get_total_active_balance`.

The caches satisfy their build invariants: the progressive balances cache is `Coherent` with
the state, and the epoch cache total is the sum of the effective balances of the validators
active in the current epoch. -/
theorem lh_cache_reads_mainnet [EpochProofs.Spec.PresetCfg] [EpochProofs.Spec.PresetCfg.Ok] (s : EpochProofs.Spec.BeaconState)
    (hrows : EpochProofs.Spec.RowsOk s) (hsupply : EpochProofs.Spec.EpochSupply s)
    (c : LhCache)
    (hc : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState s (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH)) c)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt (s.validators.map ecValidator)
        (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      (s.validators.map (·.effective_balance))) :
    (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
          f.val (s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH) >>=
        EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
    (∀ f : Usize, f.val < 3 → 0 < s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH →
      ∃ x : U64, lhPreviousEpochFlagAttestingBalance c f = ok (.Ok x) ∧
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
    exact lh_current_flag_balance_eq _ s f hf cur _ hcur hprev hcl
      (flagSum_lt s _ _ _ hteb) c hc.1
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
    exact lh_previous_flag_balance_eq _ s f hf cur (cur - 1) hcur hprev (Nat.sub_lt hpos Nat.one_pos).ne hpl
      (flagSum_lt s _ _ _ hteb) c hc.2
  · intro inc hinc
    exact lh_total_active_balance_eq _ s cur hcur _ total inc hinc rfl htotal

section Generic

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [EthCLLib.Spec.HasherTag]
  [EthCLLib.Spec.CryptoBackend]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- Lighthouse's epoch processing equals Etheorem's Gloas `processEpoch` at an epoch boundary of
a reachable run, on mainnet (`lighthouse_order_epoch_etheorem_reachable`), and the cache reads
that it makes equal the spec values of the model (`lh_cache_reads_mainnet`). The caches satisfy
their build invariants at the epoch start state. -/
theorem lighthouse_order_epoch_etheorem_reachable_cached [EpochProofs.Spec.PresetCfg]
    [EpochProofs.Spec.PresetCfg.Ok] (hpa : EpochProofs.Etheorem.EpochPresetAgrees Spec.P)
    (hhr : Spec.LH_HISTORICAL_ROOTS_LIMIT ≤ EthCLSpecs.Gloas.Const.historicalRootsLimit)
    (o : Spec.Oracle)
    (ho : EpochProofs.Etheorem.OracleAgrees o)
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) (e : EpochProofs.Etheorem.EState)
    (hin : Spec.EpochInputOk'' Spec.EpochSupply (EpochProofs.Etheorem.absEState e))
    (hpre : Spec.TailPre (EpochProofs.Etheorem.absEState e))
    (hcond : EpochProofs.Etheorem.EpochCondsIn e) (hsel : EpochProofs.Etheorem.SelectionsFull e)
    {s' : Spec.BeaconState}
    (h : Spec.process_epoch_lh_order o (EpochProofs.Etheorem.absEState e) = .ok s')
    (c : LhCache)
    (hc : Coherent EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT
      (pbState (EpochProofs.Etheorem.absEState e)
        ((EpochProofs.Etheorem.absEState e).slot /
          EpochProofs.Spec.P.SLOTS_PER_EPOCH)) c)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        ((EpochProofs.Etheorem.absEState e).validators.map ecValidator)
        ((EpochProofs.Etheorem.absEState e).slot /
          EpochProofs.Spec.P.SLOTS_PER_EPOCH))
      ((EpochProofs.Etheorem.absEState e).validators.map (·.effective_balance))) :
    (∃ e', (EthCLSpecs.Gloas.processEpoch
        (StateTransition := GloasRun)).run (EthCLLib.Proofs.pureState e) =
      .ok ((), EthCLLib.Proofs.pureState e') ∧ EpochProofs.Etheorem.absEState e' = s') ∧
    let s := EpochProofs.Etheorem.absEState e
    let cur := s.slot / EpochProofs.Spec.P.SLOTS_PER_EPOCH
    (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
          f.val cur >>=
        EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
    (∀ f : Usize, f.val < 3 → 0 < cur →
      ∃ x : U64, lhPreviousEpochFlagAttestingBalance c f = ok (.Ok x) ∧
      (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.P s
          f.val (cur - 1) >>=
        EpochProofs.Spec.get_total_balance EpochProofs.Spec.P s) = .ok x.val) ∧
    (∀ inc : U64, inc.val = EpochProofs.Spec.P.EFFECTIVE_BALANCE_INCREMENT →
      ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
        EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.P s =
          .ok r.val) :=
  ⟨EpochProofs.Etheorem.lighthouse_order_epoch_etheorem_reachable hpa hhr o ho hsha e hin hpre
    hcond hsel
    h,
   lh_cache_reads_mainnet _ hin.1.1.1.2.1 hin.1.1.2.2.2.2 c hc total htotal⟩

end Generic

end EpochProofs.CacheBridge
