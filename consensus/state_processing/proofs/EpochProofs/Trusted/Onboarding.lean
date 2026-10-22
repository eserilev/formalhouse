import EpochProofs.Sanity.Invariants.ForkUpgrade
import EpochProofs.Generated

/-!
# The contract of the builder onboarding glue

`onboard` in `upgrade/builder_onboarding.rs` is generic over the `Onboarding` trait. Aeneas
translates it, but not `StateOnboarding` in `upgrade/gloas.rs`, which reads the state, the
pubkey cache and the signature cache, and keeps two hash tables. `OnboardingContract` says what
each trait method does, in spec terms. `pubkeys` is the list of validator pubkeys, `absDep` and
`absB` give the spec value of a deposit and of a builder, `table` is the builder pubkey table
and `pending` is the set of pubkeys with a valid kept deposit:

- `is_validator` says whether the deposit pubkey is a validator pubkey. It does not change the
  tables. The pubkey cache it can update is not part of the spec state.
- `is_builder_credential` is the spec `is_builder_withdrawal_credential`.
- `is_valid_signature` is the spec `is_valid_deposit_signature`. Lighthouse reads it from the
  signature cache, which holds the result of the same check.
- `new_builder` is the builder that `add_builder_to_registry` adds for the deposit.
- `top_up` adds the deposit amount to the builder balance, and fails on a `u64` overflow.
- `builder_index` looks up the deposit pubkey in the table. `add_builder_index` adds an entry
  that hides any older entry for the same pubkey, as `HashMap::insert` does.
- `is_pending_validator` and `add_pending_validator` read and grow the pubkey set, as `HashSet`
  does.
- `clone` copies a deposit.

This is the only statement the proofs trust about this glue.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev LhOnboarding (S D B E : Type) := upgrade.builder_onboarding.Onboarding S D B E

/-- The builder that `add_builder_to_registry` adds for a deposit. -/
def onboardedBuilder (p : Spec.Preset) (d : Spec.PendingDeposit) : Spec.Builder where
  pubkey := d.pubkey
  version := Spec.PAYLOAD_BUILDER_VERSION
  execution_address := Spec.withdrawalAddress d.withdrawal_credentials
  balance := d.amount
  deposit_epoch := d.slot / p.SLOTS_PER_EPOCH
  withdrawable_epoch := Spec.FAR_FUTURE_EPOCH

/-- Trusted: what the `Onboarding` implementation in `upgrade/gloas.rs` does. -/
structure OnboardingContract {S D B E : Type} (inst : LhOnboarding S D B E)
    (cloneInst : core.clone.Clone D) (p : Spec.Preset) (o : Spec.Oracle)
    (pubkeys : List Spec.BLSPubkey) (absDep : D → Spec.PendingDeposit) (absB : B → Spec.Builder)
    (table : S → List (Spec.BLSPubkey × Nat)) (pending : S → List Spec.BLSPubkey) : Prop where
  clone : ∀ (d : D), ∃ d', cloneInst.clone d = ok d' ∧ absDep d' = absDep d
  is_validator : ∀ (s : S) (d : D), ∃ s', inst.is_validator s d =
      ok (.Ok (decide ((absDep d).pubkey ∈ pubkeys)), s') ∧
    table s' = table s ∧ pending s' = pending s
  is_builder_credential : ∀ (s : S) (d : D), inst.is_builder_credential s d =
    ok (Spec.is_builder_withdrawal_credential (absDep d).withdrawal_credentials)
  is_valid_signature : ∀ (s : S) (d : D), inst.is_valid_signature s d =
    ok (Spec.is_valid_deposit_signature p o (absDep d).pubkey (absDep d).withdrawal_credentials
      (absDep d).amount (absDep d).signature)
  new_builder : ∀ (s : S) (d : D), ∃ b, inst.new_builder s d = ok (.Ok b) ∧
    absB b = onboardedBuilder p (absDep d)
  top_up : ∀ (s : S) (b : B) (d : D),
    (∀ v, Spec.uint64Add (absB b).balance (absDep d).amount = .ok v →
      ∃ b', inst.top_up s b d = ok (.Ok (), b') ∧ absB b' = { absB b with balance := v }) ∧
    (∀ e, Spec.uint64Add (absB b).balance (absDep d).amount = .error e →
      ∃ e' b', inst.top_up s b d = ok (.Err e', b'))
  builder_index : ∀ (s : S) (d : D), ∃ r : Option U64, inst.builder_index s d = ok r ∧
    r.map (·.val) = (table s).lookup (absDep d).pubkey
  add_builder_index : ∀ (s : S) (d : D) (i : U64), ∃ s', inst.add_builder_index s d i = ok s' ∧
    table s' = ((absDep d).pubkey, i.val) :: table s ∧ pending s' = pending s
  is_pending_validator : ∀ (s : S) (d : D), inst.is_pending_validator s d =
    ok (decide ((absDep d).pubkey ∈ pending s))
  add_pending_validator : ∀ (s : S) (d : D), ∃ s', inst.add_pending_validator s d = ok s' ∧
    table s' = table s ∧ pending s' = (absDep d).pubkey :: pending s

end EpochProofs
