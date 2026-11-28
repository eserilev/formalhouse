import EpochProofs.Trusted.ProgressiveBalancesUpdates

/-!
# The progressive balances cache stays correct inside an epoch

`ProgressiveBalancesUpdate.correct` proves that each update of
`Trusted/ProgressiveBalancesUpdates.lean` keeps the cache correct. It uses the proofs about the
translated update functions. `ProgressiveBalancesUpdates.correct` chains the updates. A theorem
that uses them asks for a correct cache at a state `start` of the epoch, not at the epoch input.
-/

namespace EpochProofs.CacheReads

open Aeneas Aeneas.Std Result
open CacheProofs.ProgressiveBalances

theorem ProgressiveBalancesUpdate.correct {incr : Nat}
    {x y : CacheProofs.Spec.BeaconState × LighthouseProgressiveBalancesCache}
    (h : ProgressiveBalancesUpdate incr x y)
    (hc : ProgressiveBalancesCacheCorrect incr x.1 x.2) : ProgressiveBalancesCacheCorrect incr y.1
    y.2 := by
  cases h with
  | attestation s s' c c' e j f is_slashed eb v p hspec he hepoch hv hp hnew hactive hf hslashed
      heb hfit hlh =>
    obtain ⟨c'', h1, h2⟩ := attestation_correct incr s s' c e j f is_slashed eb v p hc hspec he
      hepoch hv hp hnew hactive hf hslashed heb hfit
    rw [hlh, ok.injEq, core.result.Result.Ok.injEq] at h1
    subst h1
    exact h2
  | slashing s s' c c' j pflags cflags eb v hspec hv hs hpp hcp hpact hcact heb hlh =>
    obtain ⟨c'', h1, h2⟩ := slashing_correct incr s s' c j pflags cflags eb v hc hspec hv hs
      hpp hcp hpact hcact heb
    rw [hlh, ok.injEq, core.result.Result.Ok.injEq] at h1
    subst h1
    exact h2
  | otherWrite s c vs' hprev hcur => exact registry_change_correct incr s c vs' hc hprev hcur
  | newValidator s c v hplen hclen => exact add_validator_correct incr s c v hc hplen hclen

theorem ProgressiveBalancesUpdates.correct {incr : Nat}
    {x y : CacheProofs.Spec.BeaconState × LighthouseProgressiveBalancesCache}
    (h : ProgressiveBalancesUpdates incr x y)
    (hc : ProgressiveBalancesCacheCorrect incr x.1 x.2) : ProgressiveBalancesCacheCorrect incr y.1
    y.2 := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hs.correct hc)

/-- A run of cache updates keeps the cache correct. -/
theorem progressive_balances_correct_after_updates {incr : Nat}
    {start finish : CacheProofs.Spec.BeaconState}
    {c0 c : LighthouseProgressiveBalancesCache}
    (hc0 : ProgressiveBalancesCacheCorrect incr start c0)
    (hup : ProgressiveBalancesUpdates incr (start, c0) (finish, c)) :
    ProgressiveBalancesCacheCorrect incr finish c :=
  ProgressiveBalancesUpdates.correct hup hc0

end EpochProofs.CacheReads
