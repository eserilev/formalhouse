import Mathlib.Tactic.Attr.Register

/-! # The simp sets that read `toSpecPreset` and `toSpecState` -/

/-- Reads one value of `toSpecPreset`. -/
register_simp_attr spec_preset

/-- Reads one field of `toSpecState`. -/
register_simp_attr spec_state
