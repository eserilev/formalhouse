import EpochProofs.Trusted.CacheUpkeep

/-!
# The progressive balances cache stays coherent inside an epoch

`PBStep.coherent` proves each hook of `Trusted/CacheUpkeep.lean` correct from the Aeneas-checked
update functions (#64). `PBTrace.coherent` chains them. `lighthouse_model_gloas_epoch_eq_etheorem_upkeep` (`Headline.lean`) uses them to ask for a coherent cache at
a state `start` of the epoch, not at the epoch input.
-/

namespace EpochProofs.CacheBridge

open Aeneas Aeneas.Std Result
open CacheProofs.PB

theorem PBStep.coherent {incr : Nat} {x y : CacheProofs.Spec.BeaconState × LhCache}
    (h : PBStep incr x y) (hc : Coherent incr x.1 x.2) : Coherent incr y.1 y.2 := by
  cases h with
  | attest s s' c c' e j f is_slashed eb v p hspec he hepoch hv hp hnew hactive hf hslashed
      heb hfit hlh =>
    obtain ⟨c'', h1, h2⟩ := attestation_coherent incr s s' c e j f is_slashed eb v p hc hspec he
      hepoch hv hp hnew hactive hf hslashed heb hfit
    rw [hlh] at h1
    cases h1
    exact h2
  | slash s s' c c' j pflags cflags eb v hspec hv hs hpp hcp hpact hcact heb hlh =>
    obtain ⟨c'', h1, h2⟩ := slashing_coherent incr s s' c j pflags cflags eb v hc hspec hv hs
      hpp hcp hpact hcact heb
    rw [hlh] at h1
    cases h1
    exact h2
  | view s c vs' hprev hcur => exact registry_change_coherent incr s c vs' hc hprev hcur
  | addValidator s c v hplen hclen => exact add_validator_coherent incr s c v hc hplen hclen

theorem PBTrace.coherent {incr : Nat} {x y : CacheProofs.Spec.BeaconState × LhCache}
    (h : PBTrace incr x y) (hc : Coherent incr x.1 x.2) : Coherent incr y.1 y.2 := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hs.coherent hc)

/-- The upkeep fact moves a coherent cache from `start` to `finish`. -/
theorem coherent_of_upkeep {incr : Nat} {start finish : CacheProofs.Spec.BeaconState}
    {c0 c : LhCache} (hc0 : Coherent incr start c0) (hup : CacheUpkeep incr start finish c0 c) :
    Coherent incr finish c :=
  PBTrace.coherent hup hc0

end EpochProofs.CacheBridge
