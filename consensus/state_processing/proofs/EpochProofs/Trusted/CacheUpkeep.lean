import EpochProofs.CacheBridge.ProgressiveBalances

/-!
# The upkeep of the progressive balances cache inside one epoch

Lighthouse keeps `ProgressiveBalancesCache` up to date with hooks, not by a rebuild. This file
names the hooks as the steps of `PBStep`. A run of the steps is a `PBTrace`.

The trusted part is one fact: between two states of one epoch, Lighthouse runs exactly the hooks
of a `PBTrace` that follows the spec changes. The audit of sigp unstable `ec2442d24b`
(2026-10-22) found these call sites, and no other write to a field that the cache reads:

- U1 `attest`: `process_operations.rs` (Altair to Fulu `process_attestation`, and the Gloas
  `process_attestation`) calls `update_progressive_balances_on_attestation` for each flag that the
  attestation newly sets. The effective balance comes from the epoch cache, which equals the
  validator's effective balance inside the epoch.
- U2 `slash`: `slash_validator.rs` calls `update_progressive_balances_on_slashing` with the flags
  of both epochs, before any other change to the validator.
- U3 `view`: every other block operation, and every slot inside an epoch, keeps each effective
  balance, each `slashed` flag, and the activity in the previous and current epochs. Exits and
  activations set epochs after the current epoch. Withdrawals, deposits, execution requests,
  the sync aggregate, payload attestations and builder operations do not write these fields.
- U4 `addValidator`: a new validator joins with empty participation. Since Electra this happens
  only in epoch processing, so a block run inside an epoch does not use this step.

The effective balance hook and the epoch transition hook are outside the epoch. The proofs of
#64 cover them (`effective_balance_change_coherent`, `epoch_transition_coherent`).
-/

namespace EpochProofs.CacheBridge

open Aeneas Aeneas.Std Result
open CacheProofs.PB

/-- One cache hook together with the spec change that it follows. -/
inductive PBStep (incr : Nat) :
    CacheProofs.Spec.BeaconState × LhCache → CacheProofs.Spec.BeaconState × LhCache → Prop
  | attest (s s' : CacheProofs.Spec.BeaconState) (c c' : LhCache) (e j : Nat) (f : Usize)
      (is_slashed : Bool) (eb : U64) (v : CacheProofs.Spec.Validator) (p : Nat)
      (hspec : CacheProofs.Spec.set_participation_flag s e j f.val = .ok s')
      (he : e = CacheProofs.Spec.get_previous_epoch s ∨ e = CacheProofs.Spec.get_current_epoch s)
      (hepoch : s.current_epoch ≤ U64.max)
      (hv : s.validators[j]? = some v) (hp : (partAt s e)[j]? = some p)
      (hnew : CacheProofs.Spec.has_flag p f.val = false)
      (hactive : CacheProofs.Spec.is_active_validator v e = true)
      (hf : f.val < 3) (hslashed : is_slashed = v.slashed) (heb : eb.val = v.effective_balance)
      (hfit : flagSum s'.validators (partAt s' e) e f.val ≤ U64.max)
      (hlh : lhOnNewAttestation c e is_slashed f eb = ok (.Ok c')) :
      PBStep incr (s, c) (s', c')
  | slash (s s' : CacheProofs.Spec.BeaconState) (c c' : LhCache) (j : Nat)
      (pflags cflags : U8) (eb : U64) (v : CacheProofs.Spec.Validator)
      (hspec : CacheProofs.Spec.set_slashed s j = .ok s')
      (hv : s.validators[j]? = some v) (hs : v.slashed = false)
      (hpp : s.previous_epoch_participation[j]? = some pflags.val)
      (hcp : s.current_epoch_participation[j]? = some cflags.val)
      (hpact : ∀ f < 3, CacheProofs.Spec.has_flag pflags.val f = true →
        CacheProofs.Spec.is_active_validator v (CacheProofs.Spec.get_previous_epoch s) = true)
      (hcact : ∀ f < 3, CacheProofs.Spec.has_flag cflags.val f = true →
        CacheProofs.Spec.is_active_validator v s.current_epoch = true)
      (heb : eb.val = v.effective_balance)
      (hlh : lhOnSlashing c pflags cflags eb = ok (.Ok c')) :
      PBStep incr (s, c) (s', c')
  | view (s : CacheProofs.Spec.BeaconState) (c : LhCache) (vs' : List CacheProofs.Spec.Validator)
      (hprev : SameView s.validators vs' (CacheProofs.Spec.get_previous_epoch s))
      (hcur : SameView s.validators vs' s.current_epoch) :
      PBStep incr (s, c) ({ s with validators := vs' }, c)
  | addValidator (s : CacheProofs.Spec.BeaconState) (c : LhCache) (v : CacheProofs.Spec.Validator)
      (hplen : s.previous_epoch_participation.length = s.validators.length)
      (hclen : s.current_epoch_participation.length = s.validators.length) :
      PBStep incr (s, c) ({ s with
        validators := s.validators ++ [v]
        previous_epoch_participation := s.previous_epoch_participation ++ [0]
        current_epoch_participation := s.current_epoch_participation ++ [0] }, c)

/-- A run of cache hooks. -/
inductive PBTrace (incr : Nat) :
    CacheProofs.Spec.BeaconState × LhCache → CacheProofs.Spec.BeaconState × LhCache → Prop
  | refl (x) : PBTrace incr x x
  | step {x y z} : PBStep incr x y → PBTrace incr y z → PBTrace incr x z

/-- The trusted upkeep fact (U1 to U4): between the state `start` and the state `finish` of one
epoch, with caches `c0` and `c`, Lighthouse runs the hooks of a `PBTrace`. -/
def CacheUpkeep (incr : Nat) (start finish : CacheProofs.Spec.BeaconState) (c0 c : LhCache) :
    Prop :=
  PBTrace incr (start, c0) (finish, c)

end EpochProofs.CacheBridge
