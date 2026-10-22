import EpochProofs.Sanity.Fulu
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.FuluCfg

/-!
# The Fulu churn as the Gloas churn of a smaller total

Fulu reads `get_activation_exit_churn_limit` for exits and for pending deposits. On mainnet and
on minimal, the Fulu quotient is twice the Gloas quotient, and the Fulu cap is the Gloas
activation cap. So the Fulu churn of `total_active_balance` is the Gloas churn of
`fuluTab p f total_active_balance = min (total_active_balance / 2) (cap * quotient)`, for the
exit churn (`get_exit_churn_limit`, no cap) and for the activation churn
(`get_activation_churn_limit`).

- `fulu_exit_churn_eq`, `fulu_activation_churn_eq`: the two churn equalities.
- `process_registry_updates_fulu_eq`: Fulu `process_registry_updates` is the Gloas function at
  `fuluTab`.
- `process_pending_deposits_fulu_tab_eq`: Fulu `process_pending_deposits` is the Gloas function
  at `fuluTab`, with the same preset.

The Gloas functions read `total_active_balance` only through the churn. So the Gloas proofs
apply to Fulu with `fuluTab` in place of the total, and the same preset.
-/

namespace EpochProofs.Spec

/-- The relations between the Fulu config and the Gloas preset that `fuluTab` needs. They hold
on mainnet and on minimal (`fuluCompat`, `fuluCompat_minimal`). -/
structure FuluCompat (p : Preset) (f : FuluConfig) : Prop where
  quotient : f.CHURN_LIMIT_QUOTIENT = 2 * p.CHURN_LIMIT_QUOTIENT_GLOAS
  quotient_pos : 0 < p.CHURN_LIMIT_QUOTIENT_GLOAS
  min_le_cap : p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA ≤ f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
  cap_mod : f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT % p.EFFECTIVE_BALANCE_INCREMENT = 0
  increment_pos : 0 < p.EFFECTIVE_BALANCE_INCREMENT
  cap_le : f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT ≤ p.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS

theorem fuluCompat_mainnet : FuluCompat (Preset.ofVar PresetVar.mainnet) FuluConfig.mainnet :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The Fulu config and the preset agree, for the configs of the generic proofs. -/
class FuluCfg.Ok [PresetCfg] [FuluCfg] : Prop where
  compat : FuluCompat P FC

theorem fuluCompat [PresetCfg] [FuluCfg] [FuluCfg.Ok] : FuluCompat P FC := FuluCfg.Ok.compat

theorem fuluCompat_minimal : FuluCompat Preset.minimal FuluConfig.minimal :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The total whose Gloas churn is the Fulu churn of `total_active_balance`. -/
def fuluTab (p : Preset) (f : FuluConfig) (total_active_balance : Gwei) : Gwei :=
  min (total_active_balance / 2) (f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT *
    p.CHURN_LIMIT_QUOTIENT_GLOAS)

theorem div_min_eq (a b c : Nat) : min a b / c = min (a / c) (b / c) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.div_le_div_right h)]
  · rw [Nat.min_eq_right h, Nat.min_eq_right (Nat.div_le_div_right h)]

/-- Rounding down to a multiple of `inc` commutes with `min` against a multiple of `inc`. -/
theorem round_min_eq (w C inc : Nat) (hinc : 0 < inc) (hC : C % inc = 0) :
    min w C - min w C % inc = min (w - w % inc) C := by
  rcases Nat.le_total w C with h | h
  · rw [Nat.min_eq_left h]
    exact (Nat.min_eq_left (Nat.le_trans (Nat.sub_le _ _) h)).symm
  · rw [Nat.min_eq_right h, hC, Nat.sub_zero]
    have hw := Nat.div_add_mod w inc
    have hc := Nat.div_add_mod C inc
    rw [hC, Nat.add_zero] at hc
    have hd : C / inc ≤ w / inc := Nat.div_le_div_right h
    have hm : inc * (C / inc) ≤ inc * (w / inc) := Nat.mul_le_mul_left _ hd
    have : C ≤ w - w % inc := by omega
    exact (Nat.min_eq_right this).symm

theorem max_min_of_le (m y c : Nat) (h : m ≤ c) : max m (min y c) = min (max m y) c := by
  omega

theorem quotient_pos_of (a b : Nat) (h : a = 2 * b) (hb : 0 < b) : 0 < a := by omega

theorem min_min_of_le (c g x : Nat) (h : c ≤ g) : min g (min c x) = min c x := by omega

/-- The Nat value of both churns. -/
theorem fulu_churn_value (p : Preset) (f : FuluConfig) (hc : FuluCompat p f) (tab : Nat) :
    let w := max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA (fuluTab p f tab / p.CHURN_LIMIT_QUOTIENT_GLOAS)
    let v := max p.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA (tab / f.CHURN_LIMIT_QUOTIENT)
    w - w % p.EFFECTIVE_BALANCE_INCREMENT =
      min f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT (v - v % p.EFFECTIVE_BALANCE_INCREMENT) := by
  intro w v
  have hdiv : fuluTab p f tab / p.CHURN_LIMIT_QUOTIENT_GLOAS =
      min (tab / f.CHURN_LIMIT_QUOTIENT) f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
    unfold fuluTab
    rw [div_min_eq, Nat.div_div_eq_div_mul,
      show (2 : Nat) * p.CHURN_LIMIT_QUOTIENT_GLOAS = f.CHURN_LIMIT_QUOTIENT from hc.quotient.symm,
      Nat.mul_div_cancel _ hc.quotient_pos]
  have hw : w = min v f.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
    show max _ _ = _
    rw [hdiv]
    exact max_min_of_le _ _ _ hc.min_le_cap
  rw [hw, round_min_eq _ _ _ hc.increment_pos hc.cap_mod, Nat.min_comm]

theorem uint64Div_ok (a b : Nat) (h : 0 < b) : uint64Div a b = .ok (a / b) := by
  simp [uint64Div, Nat.pos_iff_ne_zero.mp h, pure, Except.pure]

theorem uint64Mod_ok (a b : Nat) (h : 0 < b) : uint64Mod a b = .ok (a % b) := by
  simp [uint64Mod, Nat.pos_iff_ne_zero.mp h, pure, Except.pure]

theorem uint64Sub_mod_ok (a b : Nat) : uint64Sub a (a % b) = .ok (a - a % b) := by
  simp [uint64Sub, Nat.mod_le, pure, Except.pure]

/-- The Fulu churn is the Gloas exit churn at `fuluTab`. -/
theorem fulu_exit_churn_eq (p : Preset) (f : FuluConfig) (hc : FuluCompat p f) (tab : Gwei) :
    get_activation_exit_churn_limit p f tab = get_exit_churn_limit p (fuluTab p f tab) := by
  have hq : 0 < f.CHURN_LIMIT_QUOTIENT := quotient_pos_of _ _ hc.quotient hc.quotient_pos
  have hv := fulu_churn_value p f hc tab
  simp only at hv
  simp only [get_activation_exit_churn_limit, get_balance_churn_limit, get_exit_churn_limit,
    uint64Div_ok _ _ hq, uint64Div_ok _ _ hc.quotient_pos, uint64Mod_ok _ _ hc.increment_pos,
    uint64Sub_mod_ok, bind, Except.bind, pure, Except.pure, hv]

/-- The Fulu churn is the Gloas activation churn at `fuluTab`. -/
theorem fulu_activation_churn_eq (p : Preset) (f : FuluConfig) (hc : FuluCompat p f) (tab : Gwei) :
    get_activation_exit_churn_limit p f tab = get_activation_churn_limit p (fuluTab p f tab) := by
  have hq : 0 < f.CHURN_LIMIT_QUOTIENT := quotient_pos_of _ _ hc.quotient hc.quotient_pos
  have hv := fulu_churn_value p f hc tab
  simp only at hv
  simp only [get_activation_exit_churn_limit, get_balance_churn_limit, get_activation_churn_limit,
    uint64Div_ok _ _ hq, uint64Div_ok _ _ hc.quotient_pos, uint64Mod_ok _ _ hc.increment_pos,
    uint64Sub_mod_ok, bind, Except.bind, pure, Except.pure, hv]
  rw [min_min_of_le _ _ _ hc.cap_le]

theorem compute_exit_epoch_and_update_churn_fulu_eq (p : Preset) (f : FuluConfig)
    (hc : FuluCompat p f) (tab : Gwei) (state : BeaconState) (exit_balance : Gwei) :
    compute_exit_epoch_and_update_churn_fulu p f tab state exit_balance =
      compute_exit_epoch_and_update_churn p (fuluTab p f tab) state exit_balance := by
  unfold compute_exit_epoch_and_update_churn_fulu compute_exit_epoch_and_update_churn
  rw [fulu_exit_churn_eq p f hc]

theorem initiate_validator_exit_fulu_eq (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (tab : Gwei) (state : BeaconState) (index : ValidatorIndex) :
    initiate_validator_exit_fulu p f tab state index =
      initiate_validator_exit p (fuluTab p f tab) state index := by
  unfold initiate_validator_exit_fulu initiate_validator_exit
  simp only [compute_exit_epoch_and_update_churn_fulu_eq p f hc]

/-- Fulu `process_registry_updates` is the Gloas function at `fuluTab`. -/
theorem process_registry_updates_fulu_eq (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (tab : Gwei) (state : BeaconState) :
    process_registry_updates_fulu p f tab state =
      process_registry_updates p (fuluTab p f tab) state := by
  unfold process_registry_updates_fulu process_registry_updates
  simp only [initiate_validator_exit_fulu_eq p f hc]

/-- Fulu `process_pending_deposits` is the Gloas function at `fuluTab`, with the same preset. -/
theorem process_pending_deposits_fulu_tab_eq (p : Preset) (f : FuluConfig) (hc : FuluCompat p f)
    (tab : Gwei) (apply_pending_deposit : BeaconState → PendingDeposit → SpecM BeaconState)
    (state : BeaconState) :
    process_pending_deposits_fulu p f tab apply_pending_deposit state =
      process_pending_deposits p (fuluTab p f tab) apply_pending_deposit state := by
  unfold process_pending_deposits_fulu process_pending_deposits
  rw [fulu_activation_churn_eq p f hc]

end EpochProofs.Spec
