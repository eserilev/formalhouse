import EpochProofs.Trusted.CacheUpkeep

/-!
# The progressive balances cache stays correct inside an epoch

`ProgressiveBalancesUpdate.coherent` proves each hook of `Trusted/CacheUpkeep.lean` correct from
the Aeneas-checked update functions (#64). `ProgressiveBalancesUpdates.coherent` chains them. A
theorem that uses them asks for a correct cache at a state `start` of the epoch, not at the epoch
input.
-/

namespace EpochProofs.CacheBridge

open Aeneas Aeneas.Std Result
open CacheProofs.PB

theorem ProgressiveBalancesUpdate.coherent {incr : Nat}
    {x y : CacheProofs.Spec.BeaconState × LhCache}
    (h : ProgressiveBalancesUpdate incr x y)
    (hc : Coherent incr x.1 x.2) : Coherent incr y.1 y.2 := by
  cases h with
  | attestation s s' c c' e j f is_slashed eb v p hspec he hepoch hv hp hnew hactive hf hslashed
      heb hfit hlh =>
    obtain ⟨c'', h1, h2⟩ := attestation_coherent incr s s' c e j f is_slashed eb v p hc hspec he
      hepoch hv hp hnew hactive hf hslashed heb hfit
    rw [hlh, ok.injEq, core.result.Result.Ok.injEq] at h1
    subst h1
    exact h2
  | slashing s s' c c' j pflags cflags eb v hspec hv hs hpp hcp hpact hcact heb hlh =>
    obtain ⟨c'', h1, h2⟩ := slashing_coherent incr s s' c j pflags cflags eb v hc hspec hv hs
      hpp hcp hpact hcact heb
    rw [hlh, ok.injEq, core.result.Result.Ok.injEq] at h1
    subst h1
    exact h2
  | otherWrite s c vs' hprev hcur => exact registry_change_coherent incr s c vs' hc hprev hcur
  | newValidator s c v hplen hclen => exact add_validator_coherent incr s c v hc hplen hclen

theorem ProgressiveBalancesUpdates.coherent {incr : Nat}
    {x y : CacheProofs.Spec.BeaconState × LhCache}
    (h : ProgressiveBalancesUpdates incr x y)
    (hc : Coherent incr x.1 x.2) : Coherent incr y.1 y.2 := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hs.coherent hc)

/-- The upkeep fact moves a correct cache from `start` to `finish`. -/
theorem progressive_balances_correct_after_updates {incr : Nat}
    {start finish : CacheProofs.Spec.BeaconState}
    {c0 c : LhCache} (hc0 : Coherent incr start c0) (hup : CacheUpkeep incr start finish c0 c) :
    Coherent incr finish c :=
  ProgressiveBalancesUpdates.coherent hup hc0

end EpochProofs.CacheBridge
