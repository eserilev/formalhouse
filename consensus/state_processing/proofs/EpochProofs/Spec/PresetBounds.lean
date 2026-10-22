import EpochProofs.Spec.PresetCfg

/-!
# More facts about the preset values

`PresetCfg.Ok` holds the facts that the epoch proofs up to `Totality` use. The totality proofs
for the per-validator steps and the committee steps need more facts: bounds on the churn
values, the committee sizes and the window lengths. `PresetCfg.Bounds` holds them. Both
presets satisfy them by `decide`.
-/

namespace EpochProofs.Spec

/-- The bounds on the preset values that the totality proofs use. -/
class PresetCfg.Bounds [c : PresetCfg] : Prop where
  slots_le : c.v.SLOTS_PER_EPOCH ≤ 32
  min_churn_ge : 64000000000 ≤ c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  min_churn_le : c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA ≤ 128000000000
  min_churn_inc : c.v.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA % 1000000000 = 0
  churn_quot_pos : 0 < c.v.CHURN_LIMIT_QUOTIENT_GLOAS
  max_act_churn_ge : 128000000000 ≤ c.v.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
  max_act_churn_le : c.v.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS ≤ 256000000000
  consolidation_quot_pos : 0 < c.v.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
  target_committee_pos : 0 < c.v.TARGET_COMMITTEE_SIZE
  target_committee_le : c.v.TARGET_COMMITTEE_SIZE ≤ 128
  max_committees_pos : 0 < c.v.MAX_COMMITTEES_PER_SLOT
  max_committees_le : c.v.MAX_COMMITTEES_PER_SLOT ≤ 64
  shuffle_rounds_le : c.v.SHUFFLE_ROUND_COUNT ≤ 256
  ptc_pos : 0 < c.v.PTC_SIZE
  ptc_le : c.v.PTC_SIZE ≤ 512
  sync_le : c.v.SYNC_COMMITTEE_SIZE ≤ 512
  sync_period_pos : 0 < c.v.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
  sync_period_le : c.v.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≤ 256

theorem mainnetCfg_bounds : @PresetCfg.Bounds mainnetCfg :=
  letI := mainnetCfg
  { slots_le := by decide, min_churn_ge := by decide, min_churn_le := by decide,
    min_churn_inc := by decide, churn_quot_pos := by decide, max_act_churn_ge := by decide,
    max_act_churn_le := by decide, consolidation_quot_pos := by decide,
    target_committee_pos := by decide, target_committee_le := by decide,
    max_committees_pos := by decide, max_committees_le := by decide,
    shuffle_rounds_le := by decide, ptc_pos := by decide, ptc_le := by decide,
    sync_le := by decide, sync_period_pos := by decide, sync_period_le := by decide }

theorem minimalCfg_bounds : @PresetCfg.Bounds minimalCfg :=
  letI := minimalCfg
  { slots_le := by decide, min_churn_ge := by decide, min_churn_le := by decide,
    min_churn_inc := by decide, churn_quot_pos := by decide, max_act_churn_ge := by decide,
    max_act_churn_le := by decide, consolidation_quot_pos := by decide,
    target_committee_pos := by decide, target_committee_le := by decide,
    max_committees_pos := by decide, max_committees_le := by decide,
    shuffle_rounds_le := by decide, ptc_pos := by decide, ptc_le := by decide,
    sync_le := by decide, sync_period_pos := by decide, sync_period_le := by decide }

/-- The slots per epoch as a `Nat` with its bounds. -/
theorem P_slots_bounds [PresetCfg] [h : PresetCfg.Ok] [b : PresetCfg.Bounds] :
    ∃ S : Nat, P.SLOTS_PER_EPOCH = S ∧ 6 ≤ S ∧ S ≤ 32 :=
  ⟨_, rfl, h.slots_ge_six, b.slots_le⟩

/-- The epoch of a slot is at most the slot divided by 6. -/
theorem P_epoch_le_div6 [PresetCfg] [PresetCfg.Ok] (x : Nat) : x / P.SLOTS_PER_EPOCH ≤ x / 6 :=
  Nat.div_le_div_left (PresetCfg.Ok.slots_ge_six) (by decide)

/-- The epoch of a slot times the slots per epoch is at most the slot. -/
theorem P_epoch_mul_le [PresetCfg] (x : Nat) : x / P.SLOTS_PER_EPOCH * P.SLOTS_PER_EPOCH ≤ x :=
  Nat.div_mul_le_self _ _

end EpochProofs.Spec
