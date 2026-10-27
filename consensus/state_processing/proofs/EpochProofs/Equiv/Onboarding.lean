import EpochProofs.Trusted.Onboarding
import EpochProofs.Sanity.Onboarding
import EpochProofs.Equiv.ConsolidationTable
import Mathlib.Data.List.Basic

/-!
# Lighthouse builder onboarding equals the reference

`onboard_spec` relates `onboard` in `upgrade/builder_onboarding.rs` to the spec
`onboard_builders_from_pending_deposits`, on a state with an empty builder registry. It assumes
`OnboardingContract`. If the spec succeeds, Lighthouse returns the kept deposits and the new
builders of the spec result. If the spec fails, Lighthouse fails.

Lighthouse differs from the spec in three ways, and the proof covers each one:

- It keeps the set of pubkeys with a valid kept deposit, where the spec scans the kept deposits
  (`is_pending_validator`). The set equals the scan for every pubkey that is not a validator
  pubkey, and the walk asks only about such pubkeys.
- It keeps a pubkey table of the builders, where the spec scans the registry.
- It appends every new builder, where the spec asks `get_index_for_new_builder`. At the fork
  every builder has `withdrawable_epoch = FAR_FUTURE_EPOCH`, so the spec appends too.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

theorem is_pending_validator_append (p : Spec.Preset) (o : Spec.Oracle)
    (l : List Spec.PendingDeposit) (d : Spec.PendingDeposit) (pk : Spec.BLSPubkey) :
    Spec.is_pending_validator p o (l ++ [d]) pk =
      (Spec.is_pending_validator p o l pk ||
        (d.pubkey == pk && Spec.is_valid_deposit_signature p o d.pubkey d.withdrawal_credentials
          d.amount d.signature)) := by
  simp [Spec.is_pending_validator, List.any_append]

/-- The builder pubkey table matches the builder registry. -/
def TableOk (table : List (Spec.BLSPubkey × Nat)) (builders : List Spec.Builder) : Prop :=
  ∀ pk, table.lookup pk =
    if pk ∈ builders.map (·.pubkey) then some ((builders.map (·.pubkey)).idxOf pk) else none

/-- The pending pubkey set matches the spec scan, for every pubkey that is not a validator. -/
def PendingOk (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (set : List Spec.BLSPubkey) (kept : List Spec.PendingDeposit) : Prop :=
  ∀ pk, pk ∉ pubkeys → (pk ∈ set ↔ Spec.is_pending_validator p o kept pk = true)

theorem tableOk_add (table : List (Spec.BLSPubkey × Nat)) (builders : List Spec.Builder)
    (h : TableOk table builders) (b : Spec.Builder) (hb : b.pubkey ∉ builders.map (·.pubkey)) :
    TableOk ((b.pubkey, builders.length) :: table) (builders ++ [b]) := by
  intro pk
  by_cases hpk : pk = b.pubkey
  · subst hpk
    simp only [List.lookup_cons, beq_self_eq_true, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton, or_true, if_true]
    rw [List.idxOf_append_of_notMem hb]
    simp
  · have hne : (pk == b.pubkey) = false := by simpa using hpk
    simp only [List.lookup_cons, hne, h pk, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton, hpk, or_false]
    split
    · rename_i hin
      rw [List.idxOf_append_of_mem hin]
    · rfl

theorem tableOk_set (table : List (Spec.BLSPubkey × Nat)) (builders : List Spec.Builder)
    (h : TableOk table builders) (i : Nat) (b : Spec.Builder) (hi : i < builders.length)
    (hb : b.pubkey = builders[i].pubkey) : TableOk table (builders.set i b) := by
  have : (builders.set i b).map (·.pubkey) = builders.map (·.pubkey) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_set]
    split
    · subst_vars; exact hb
    · rfl
  intro pk
  rw [h pk, this]

/-- The spec loop over a prefix of the deposits. -/
def specFold (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (state0 : Spec.BeaconState) (l : List Spec.PendingDeposit) :
    Spec.SpecM (Spec.BeaconState × List Spec.PendingDeposit) :=
  l.foldlM (Spec.onboard_step p o pubkeys) (state0, [])

theorem specFold_snoc (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (state0 : Spec.BeaconState) (l : List Spec.PendingDeposit) (d : Spec.PendingDeposit)
    (acc : Spec.BeaconState × List Spec.PendingDeposit) (h : specFold p o pubkeys state0 l = .ok acc) :
    specFold p o pubkeys state0 (l ++ [d]) = Spec.onboard_step p o pubkeys acc d := by
  unfold specFold at h ⊢
  rw [List.foldlM_append, h]
  simp [Bind.bind, Except.bind, List.foldlM_cons, List.foldlM_nil, Pure.pure, Except.pure]
  cases Spec.onboard_step p o pubkeys acc d <;> rfl

theorem specFold_error_append (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (state0 : Spec.BeaconState) (l1 l2 : List Spec.PendingDeposit) (e : Spec.SpecError)
    (h : specFold p o pubkeys state0 l1 = .error e) :
    specFold p o pubkeys state0 (l1 ++ l2) = .error e := by
  unfold specFold at h ⊢
  rw [List.foldlM_append, h]
  rfl

theorem onboard_step_validator (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (acc : Spec.BeaconState × List Spec.PendingDeposit) (dep : Spec.PendingDeposit)
    (hv : dep.pubkey ∈ pubkeys) :
    Spec.onboard_step p o pubkeys acc dep = .ok (acc.1, acc.2 ++ [dep]) := by
  unfold Spec.onboard_step
  rw [if_pos hv]
  rfl

theorem onboard_step_new (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (acc : Spec.BeaconState × List Spec.PendingDeposit) (dep : Spec.PendingDeposit)
    (hv : dep.pubkey ∉ pubkeys) (hb : dep.pubkey ∉ acc.1.builders.map (·.pubkey)) :
    Spec.onboard_step p o pubkeys acc dep =
      if !Spec.is_builder_withdrawal_credential dep.withdrawal_credentials then
        .ok (acc.1, acc.2 ++ [dep])
      else if Spec.is_pending_validator p o acc.2 dep.pubkey then .ok (acc.1, acc.2 ++ [dep])
      else if !Spec.is_valid_deposit_signature p o dep.pubkey dep.withdrawal_credentials
          dep.amount dep.signature then .ok (acc.1, acc.2)
      else (do
        let state ← Spec.add_builder_to_registry p acc.1 dep.pubkey Spec.PAYLOAD_BUILDER_VERSION
          (Spec.withdrawalAddress dep.withdrawal_credentials) dep.amount dep.slot
        pure (state, acc.2)) := by
  unfold Spec.onboard_step
  rw [if_neg hv, if_pos hb]
  rfl

theorem onboard_step_builder (p : Spec.Preset) (o : Spec.Oracle) (pubkeys : List Spec.BLSPubkey)
    (acc : Spec.BeaconState × List Spec.PendingDeposit) (dep : Spec.PendingDeposit)
    (hv : dep.pubkey ∉ pubkeys) (hb : dep.pubkey ∈ acc.1.builders.map (·.pubkey)) :
    Spec.onboard_step p o pubkeys acc dep = (do
      let builder_index := (acc.1.builders.map (·.pubkey)).idxOf dep.pubkey
      let builder ← Spec.listGet acc.1.builders builder_index
      let balance ← Spec.uint64Add builder.balance dep.amount
      let builders ← Spec.listSet acc.1.builders builder_index { builder with balance }
      pure ({ acc.1 with builders }, acc.2)) := by
  unfold Spec.onboard_step
  rw [if_neg hv, if_neg (not_not.mpr hb)]

/-- The loop invariant. -/
structure OnbInv {S D B : Type} (p : Spec.Preset) (o : Spec.Oracle)
    (pubkeys : List Spec.BLSPubkey) (absDep : D → Spec.PendingDeposit) (absB : B → Spec.Builder)
    (table : S → List (Spec.BLSPubkey × Nat)) (pending : S → List Spec.BLSPubkey)
    (state0 : Spec.BeaconState) (deps : Slice D)
    (y : S × alloc.vec.Vec D × alloc.vec.Vec B × Usize) : Prop where
  le : y.2.2.2.val ≤ deps.val.length
  fold : specFold p o pubkeys state0 ((deps.val.take y.2.2.2.val).map absDep) =
    .ok ({ state0 with builders := y.2.2.1.val.map absB }, y.2.1.val.map absDep)
  table : TableOk (table y.1) (y.2.2.1.val.map absB)
  pending : PendingOk p o pubkeys (pending y.1) (y.2.1.val.map absDep)
  far : ∀ b ∈ y.2.2.1.val, (absB b).withdrawable_epoch = Spec.FAR_FUTURE_EPOCH
  count : y.2.2.1.val.length ≤ y.2.2.2.val
  kept : y.2.1.val.length ≤ y.2.2.2.val

theorem get_current_epoch_builders (p : Spec.Preset) (state : Spec.BeaconState)
    (bs : List Spec.Builder) :
    Spec.get_current_epoch p { state with builders := bs } = Spec.get_current_epoch p state := rfl

theorem cast_u64_usize (hus : Usize.max = U64.max) (x : Usize) :
    (UScalar.cast UScalarTy.U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h2 : x.val ≤ Usize.max := by scalar_tac
  have h3 : U64.max + 1 = 2 ^ UScalarTy.U64.numBits := by
    rw [U64.max_def]; simp [U64.numBits]
  omega

/-- What the loop returns, in spec terms. -/
def OnbPost {S D B E : Type} (p : Spec.Preset) (o : Spec.Oracle)
    (pubkeys : List Spec.BLSPubkey) (absDep : D → Spec.PendingDeposit) (absB : B → Spec.Builder)
    (state0 : Spec.BeaconState) (deps : Slice D)
    (r : S × alloc.vec.Vec D × alloc.vec.Vec B ×
      Option (upgrade.builder_onboarding.OnboardingError E)) : Prop :=
  (r.2.2.2 = none → specFold p o pubkeys state0 (deps.val.map absDep) =
    .ok ({ state0 with builders := r.2.2.1.val.map absB }, r.2.1.val.map absDep)) ∧
  (∀ err, r.2.2.2 = some err → ∃ e, specFold p o pubkeys state0 (deps.val.map absDep) = .error e)

theorem onboard_loop_spec {S D B E : Type} (inst : LhOnboarding S D B E)
    (cloneInst : core.clone.Clone D) (p : Spec.Preset) (o : Spec.Oracle)
    (pubkeys : List Spec.BLSPubkey) (absDep : D → Spec.PendingDeposit) (absB : B → Spec.Builder)
    (table : S → List (Spec.BLSPubkey × Nat)) (pending : S → List Spec.BLSPubkey)
    (hc : OnboardingContract inst cloneInst p o pubkeys absDep absB table pending)
    (hus : Usize.max = U64.max) (state0 : Spec.BeaconState) (ce : Nat)
    (hce : Spec.get_current_epoch p state0 = .ok ce) (hlt : ce < Spec.FAR_FUTURE_EPOCH)
    (hspe : p.SLOTS_PER_EPOCH ≠ 0) (deps : Slice D)
    (s : S) (pend : alloc.vec.Vec D) (bs : alloc.vec.Vec B) (i : Usize)
    (hinv : OnbInv p o pubkeys absDep absB table pending state0 deps (s, pend, bs, i)) :
    upgrade.builder_onboarding.onboard_loop cloneInst inst s deps pend bs i ⦃ r =>
      OnbPost p o pubkeys absDep absB state0 deps r ⦄ := by
  unfold upgrade.builder_onboarding.onboard_loop
  apply loop.spec_decr_nat
    (measure := fun (y : S × alloc.vec.Vec D × alloc.vec.Vec B × Usize) =>
      deps.val.length - y.2.2.2.val)
    (inv := OnbInv p o pubkeys absDep absB table pending state0 deps)
  · rintro ⟨s1, pend1, bs1, i1⟩ hinv1
    obtain ⟨hle, hfold, htab, hpen, hfar, hcount, hkept⟩ := hinv1
    dsimp only at hle hfold htab hpen hfar hcount hkept ⊢
    unfold upgrade.builder_onboarding.onboard_loop.body
    dsimp only
    split
    · rename_i hlt1
      have hil : i1.val < deps.val.length := by scalar_tac
      rw [slice_get_some deps i1 hil, bind_tc_ok]
      dsimp only
      generalize hd : deps.val[i1.val] = d
      have hmax : i1.val < Usize.max := by have := deps.property; scalar_tac
      have hsat := usize_saturating_add_one i1 hmax
      have htake : (deps.val.take (i1.val + 1)).map absDep =
          (deps.val.take i1.val).map absDep ++ [absDep d] := by
        rw [List.take_succ_eq_append_getElem hil, List.map_append, hd]; rfl
      have hstep := specFold_snoc p o pubkeys state0 _ (absDep d) _ hfold
      rw [← htake] at hstep
      have hpendlen : pend1.val.length < Usize.max := by omega
      obtain ⟨s2, hiv, ht2, hp2⟩ := hc.is_validator s1 d
      rw [hiv, bind_tc_ok]
      simp only [uncurry_apply_pair]
      by_cases hpk : (absDep d).pubkey ∈ pubkeys
      · -- A validator pubkey: the deposit stays.
        simp only [hpk, decide_true, if_true]
        obtain ⟨d', hcl, hd'⟩ := hc.clone d
        rw [hcl, bind_tc_ok]
        obtain ⟨pend2, hpu, hpend2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec pend1 d' hpendlen)
        rw [hpu, bind_tc_ok]
        simp only [lift, bind_tc_ok, spec_ok]
        try dsimp only
        rw [hsat]
        refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, ?_, hfar, by (try dsimp only); (try rw [hsat]); omega, by (try dsimp only); (try rw [hsat]); rw [hpend2]; simp; omega⟩, by (try dsimp only); (try rw [hsat]); omega⟩
        · (try dsimp only)
          try rw [hsat]
          rw [hstep, onboard_step_validator p o pubkeys _ _ hpk]
          simp [hpend2, hd']
        · (try dsimp only)
          try rw [hsat]
          rw [ht2]; exact htab
        · (try dsimp only)
          try rw [hsat]
          intro pk hpk'
          have hne : (absDep d).pubkey ≠ pk := fun h => hpk' (h ▸ hpk)
          rw [hp2, hpen pk hpk', hpend2, List.map_append, List.map_singleton, hd',
            is_pending_validator_append]
          simp [hne]
      · simp only [hpk, decide_false, Bool.false_eq_true, if_false]
        obtain ⟨ro, hbi, hro⟩ := hc.builder_index s2 d
        rw [hbi, bind_tc_ok]
        have hL := htab (absDep d).pubkey
        rw [← ht2] at hL
        cases ro with
        | none =>
          -- A pubkey with no builder.
          have hnot : (absDep d).pubkey ∉ (bs1.val.map absB).map (·.pubkey) := by
            intro hin
            rw [hL, if_pos hin] at hro
            simp at hro
          dsimp only
          rw [hc.is_builder_credential s2 d, bind_tc_ok]
          by_cases hcred : Spec.is_builder_withdrawal_credential (absDep d).withdrawal_credentials
          · simp only [hcred, if_true]
            rw [hc.is_pending_validator s2 d, bind_tc_ok]
            have hpv := hpen (absDep d).pubkey hpk
            rw [← hp2] at hpv
            by_cases hpending : (absDep d).pubkey ∈ pending s2
            · -- A valid kept deposit has the pubkey: the deposit stays.
              simp only [hpending, decide_true, if_true]
              obtain ⟨d', hcl, hd'⟩ := hc.clone d
              rw [hcl, bind_tc_ok]
              obtain ⟨pend2, hpu, hpend2⟩ :=
                spec_imp_exists (alloc.vec.Vec.push_spec pend1 d' hpendlen)
              rw [hpu, bind_tc_ok]
              simp only [lift, bind_tc_ok, spec_ok]
              try dsimp only
              rw [hsat]
              have hspv : Spec.is_pending_validator p o (pend1.val.map absDep) (absDep d).pubkey =
                  true := hpv.mp hpending
              refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, ?_, hfar, by (try dsimp only); (try rw [hsat]); omega, by (try dsimp only); (try rw [hsat]); rw [hpend2]; simp; omega⟩, by (try dsimp only); (try rw [hsat]); omega⟩
              · (try dsimp only)
                try rw [hsat]
                rw [hstep, onboard_step_new p o pubkeys _ _ hpk hnot]
                simp [hcred, hspv, hpend2, hd']
              · (try dsimp only)
                try rw [hsat]
                rw [ht2]; exact htab
              · (try dsimp only)
                try rw [hsat]
                intro pk hpk'
                rw [hp2, hpen pk hpk', hpend2, List.map_append, List.map_singleton, hd',
                  is_pending_validator_append]
                by_cases hpe : (absDep d).pubkey = pk
                · subst hpe; simp [hspv]
                · simp [hpe]
            · have hspv : Spec.is_pending_validator p o (pend1.val.map absDep) (absDep d).pubkey =
                  false := by
                cases h : Spec.is_pending_validator p o (pend1.val.map absDep) (absDep d).pubkey
                · rfl
                · exact absurd (hpv.mpr h) hpending
              simp only [hpending, decide_false, Bool.false_eq_true, if_false]
              rw [hc.is_valid_signature s2 d, bind_tc_ok]
              by_cases hsig : Spec.is_valid_deposit_signature p o (absDep d).pubkey
                  (absDep d).withdrawal_credentials (absDep d).amount (absDep d).signature = true
              · -- A new builder.
                simp only [hsig, if_true]
                obtain ⟨b, hnb, hb⟩ := hc.new_builder s2 d
                rw [hnb, bind_tc_ok]
                dsimp only
                have hcast := cast_u64_usize hus (alloc.vec.Vec.len bs1)
                simp only [lift, bind_tc_ok]
                generalize hci : UScalar.cast UScalarTy.U64 (alloc.vec.Vec.len bs1) = ci at hcast
                obtain ⟨s3, hab, ht3, hp3⟩ := hc.add_builder_index s2 d ci
                rw [hab, bind_tc_ok]
                have hbslen : bs1.val.length < Usize.max := by omega
                obtain ⟨bs2, hpb, hbs2⟩ := spec_imp_exists (alloc.vec.Vec.push_spec bs1 b hbslen)
                rw [hpb, bind_tc_ok]
                simp only [lift, bind_tc_ok, spec_ok]
                try dsimp only
                rw [hsat]
                have hstate : { state0 with builders := bs1.val.map absB } =
                    { state0 with builders := bs1.val.map absB } := rfl
                have hall : ∀ b' ∈ ({ state0 with builders := bs1.val.map absB } : Spec.BeaconState).builders,
                    b'.withdrawable_epoch = Spec.FAR_FUTURE_EPOCH := by
                  intro b' hb'
                  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb'
                  exact hfar x hx
                have hadd := Spec.add_builder_to_registry_far p
                  { state0 with builders := bs1.val.map absB } ce
                  (by rw [get_current_epoch_builders]; exact hce) hlt hall hspe
                  (absDep d).pubkey Spec.PAYLOAD_BUILDER_VERSION
                  (Spec.withdrawalAddress (absDep d).withdrawal_credentials) (absDep d).amount
                  (absDep d).slot
                refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, ?_, ?_, ?_, by (try dsimp only); (try rw [hsat]); omega⟩, by (try dsimp only); (try rw [hsat]); omega⟩
                · (try dsimp only)
                  try rw [hsat]
                  rw [hstep, onboard_step_new p o pubkeys _ _ hpk hnot]
                  simp only [hcred, hspv, hsig, Bool.not_true, Bool.false_eq_true, if_false]
                  rw [hadd]
                  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                  rw [hbs2, List.map_append, List.map_singleton, hb]
                  rfl
                · (try dsimp only)
                  try rw [hsat]
                  rw [ht3, hbs2, List.map_append, List.map_singleton, hb, hcast]
                  have : (alloc.vec.Vec.len bs1).val = (bs1.val.map absB).length := by simp
                  rw [this]
                  exact tableOk_add (table s2) (bs1.val.map absB) (by rw [ht2]; exact htab)
                    (onboardedBuilder p (absDep d)) hnot
                · (try dsimp only)
                  try rw [hsat]
                  intro pk hpk'
                  rw [hp3, hp2, hpen pk hpk']
                · (try dsimp only)
                  try rw [hsat]
                  intro b' hb'
                  rw [hbs2] at hb'
                  rcases List.mem_append.mp hb' with h | h
                  · exact hfar b' h
                  · simp at h; subst h; rw [hb]; rfl
                · (try dsimp only)
                  try rw [hsat]
                  rw [hbs2]; simp; omega
              · -- An invalid signature: the deposit is dropped.
                simp only [hsig, Bool.false_eq_true, if_false]
                simp only [lift, bind_tc_ok, spec_ok]
                try dsimp only
                rw [hsat]
                have hsig' : Spec.is_valid_deposit_signature p o (absDep d).pubkey
                    (absDep d).withdrawal_credentials (absDep d).amount (absDep d).signature =
                    false := by simpa using hsig
                refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, ?_, hfar, by (try dsimp only); (try rw [hsat]); omega, by (try dsimp only); (try rw [hsat]); omega⟩, by (try dsimp only); (try rw [hsat]); omega⟩
                · (try dsimp only)
                  try rw [hsat]
                  rw [hstep, onboard_step_new p o pubkeys _ _ hpk hnot]
                  simp [hcred, hspv, hsig']
                · (try dsimp only)
                  try rw [hsat]
                  rw [ht2]; exact htab
                · (try dsimp only)
                  try rw [hsat]
                  intro pk hpk'; rw [hp2]; exact hpen pk hpk'
          · -- Not a builder credential: the deposit stays.
            have hcred' : Spec.is_builder_withdrawal_credential
                (absDep d).withdrawal_credentials = false := by simpa using hcred
            simp only [hcred', Bool.false_eq_true, if_false]
            obtain ⟨d', hcl, hd'⟩ := hc.clone d
            rw [hcl, bind_tc_ok]
            obtain ⟨pend2, hpu, hpend2⟩ :=
              spec_imp_exists (alloc.vec.Vec.push_spec pend1 d' hpendlen)
            rw [hpu, bind_tc_ok]
            rw [hc.is_valid_signature s2 d, bind_tc_ok]
            have hrest : ∀ s3, table s3 = table s1 →
                (∀ pk, pk ∉ pubkeys → (pk ∈ pending s3 ↔
                  Spec.is_pending_validator p o (pend2.val.map absDep) pk = true)) →
                (do
                  let i2 ← lift (core.num.Usize.saturating_add i1 1#usize)
                  ok (ControlFlow.cont (s3, pend2, bs1, i2)) :
                  Result (ControlFlow (S × alloc.vec.Vec D × alloc.vec.Vec B × Usize)
                    (S × alloc.vec.Vec D × alloc.vec.Vec B ×
                      Option (upgrade.builder_onboarding.OnboardingError E)))) ⦃ r =>
                  match r with
                  | ControlFlow.done y => OnbPost p o pubkeys absDep absB state0 deps y
                  | ControlFlow.cont x' =>
                    OnbInv p o pubkeys absDep absB table pending state0 deps x' ∧
                      deps.val.length - x'.2.2.2.val < deps.val.length - i1.val ⦄ := by
              intro s3 ht3 hp3
              simp only [lift, bind_tc_ok, spec_ok]
              try dsimp only
              rw [hsat]
              refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, hp3, hfar, by (try dsimp only); (try rw [hsat]); omega, by (try dsimp only); (try rw [hsat]); rw [hpend2]; simp; omega⟩, by (try dsimp only); (try rw [hsat]); omega⟩
              · (try dsimp only)
                try rw [hsat]
                rw [hstep, onboard_step_new p o pubkeys _ _ hpk hnot]
                simp [hcred', hpend2, hd']
              · (try dsimp only)
                try rw [hsat]
                rw [ht3]; exact htab
            by_cases hsig : Spec.is_valid_deposit_signature p o (absDep d).pubkey
                (absDep d).withdrawal_credentials (absDep d).amount (absDep d).signature = true
            · simp only [hsig, if_true]
              obtain ⟨s3, hap, ht3, hp3⟩ := hc.add_pending_validator s2 d
              rw [hap, bind_tc_ok]
              apply hrest s3 (ht3.trans ht2)
              intro pk hpk'
              rw [hp3, hpend2, List.map_append, List.map_singleton, hd',
                is_pending_validator_append, List.mem_cons, hp2, hpen pk hpk']
              by_cases hpe : (absDep d).pubkey = pk
              · subst hpe; simp [hsig]
              · simp [hpe, Ne.symm hpe]
            · have hsig' : Spec.is_valid_deposit_signature p o (absDep d).pubkey
                  (absDep d).withdrawal_credentials (absDep d).amount (absDep d).signature =
                  false := by simpa using hsig
              simp only [hsig', Bool.false_eq_true, if_false, bind_tc_ok]
              apply hrest s2 ht2
              intro pk hpk'
              rw [hp2, hpend2, List.map_append, List.map_singleton, hd',
                is_pending_validator_append, hpen pk hpk']
              simp [hsig']
        | some idx =>
          -- A builder with the pubkey: top up.
          have hin : (absDep d).pubkey ∈ (bs1.val.map absB).map (·.pubkey) := by
            by_contra hin
            rw [hL, if_neg hin] at hro
            simp at hro
          rw [hL, if_pos hin] at hro
          simp only [Option.map_some, Option.some.injEq] at hro
          have hidxlt : idx.val < bs1.val.length := by
            rw [hro]
            have := List.idxOf_lt_length_of_mem hin
            simpa using this
          dsimp only
          simp only [lift, alloc.vec.Vec.deref_mut, core.slice.Slice.get_mut,
            core.slice.index.Usize.get_mut, bind_tc_ok, uncurry_apply_pair,
            Slice.getElem?_Usize_eq]
          have hcidx : (UScalar.cast UScalarTy.Usize idx).val = idx.val := cast_usize_u64 hus idx
          have hget : bs1.val[(UScalar.cast UScalarTy.Usize idx).val]? = some bs1.val[idx.val] := by
            rw [hcidx, List.getElem?_eq_getElem hidxlt]
          rw [hget]
          dsimp only
          have hspec := onboard_step_builder p o pubkeys
            ({ state0 with builders := bs1.val.map absB }, pend1.val.map absDep) (absDep d) hpk hin
          rw [hspec] at hstep
          have hsidx : ((bs1.val.map absB).map (·.pubkey)).idxOf (absDep d).pubkey = idx.val :=
            hro.symm
          have hgetb : Spec.listGet (bs1.val.map absB) idx.val = .ok (absB bs1.val[idx.val]) := by
            simp [Spec.listGet, List.getElem?_eq_getElem hidxlt, Pure.pure, Except.pure]
          obtain ⟨htu_ok, htu_err⟩ := hc.top_up s2 bs1.val[idx.val] d
          cases hadd : Spec.uint64Add (absB bs1.val[idx.val]).balance (absDep d).amount with
          | error e =>
            obtain ⟨e', b', htu⟩ := htu_err e hadd
            rw [htu, bind_tc_ok]
            simp only [uncurry_apply_pair, spec_ok]
            refine ⟨fun h => by simp at h, fun err _ => ⟨e, ?_⟩⟩
            have herr : specFold p o pubkeys state0
                ((deps.val.take (i1.val + 1)).map absDep) = .error e := by
              rw [hstep]
              simp only [hsidx, hgetb, hadd, Bind.bind, Except.bind]
            have hsplit : deps.val.map absDep = (deps.val.take (i1.val + 1)).map absDep ++
                (deps.val.drop (i1.val + 1)).map absDep := by
              rw [← List.map_append, List.take_append_drop]
            rw [hsplit]
            exact specFold_error_append p o pubkeys state0 _ _ e herr
          | ok v =>
            obtain ⟨b', htu, hb'⟩ := htu_ok v hadd
            rw [htu, bind_tc_ok]
            simp only [uncurry_apply_pair, lift, bind_tc_ok, spec_ok]
            have hset : (Slice.set_opt ⟨bs1.val, bs1.property⟩ (UScalar.cast UScalarTy.Usize idx)
                (some b')).val = bs1.val.set idx.val b' := by
              simp [Slice.set_opt, list_set_opt_some, hcidx]
            refine ⟨⟨by (try dsimp only); (try rw [hsat]); omega, ?_, ?_, ?_, ?_,
              by (try dsimp only); (try rw [hsat]); rw [hset]; simp; omega,
              by (try dsimp only); (try rw [hsat]); omega⟩,
              by (try dsimp only); (try rw [hsat]); omega⟩
            · (try dsimp only)
              try rw [hsat]
              rw [hset, hstep]
              simp only [hsidx, hgetb, hadd, Bind.bind, Except.bind, Spec.listSet,
                List.length_map, hidxlt, if_true, Pure.pure, Except.pure, List.map_set, hb']
            · (try dsimp only)
              rw [hset, List.map_set]
              exact tableOk_set _ _ (by rw [ht2]; exact htab) idx.val (absB b')
                (by simpa using hidxlt) (by rw [hb']; simp)
            · (try dsimp only)
              intro pk hpk'
              rw [hp2]; exact hpen pk hpk'
            · (try dsimp only)
              intro x hx
              rw [hset] at hx
              rcases List.mem_or_eq_of_mem_set hx with h | h
              · exact hfar x h
              · subst h; rw [hb']; exact hfar _ (List.getElem_mem hidxlt)
    · rename_i hge
      have hil : i1.val = deps.val.length := by scalar_tac
      simp only [spec_ok]
      refine ⟨fun _ => ?_, fun err h => by simp at h⟩
      rw [hil, List.take_length] at hfold
      exact hfold
  · exact hinv

/-- Lighthouse's builder onboarding at the Gloas fork equals the spec
`onboard_builders_from_pending_deposits` on a state with an empty builder registry: if the spec
succeeds, Lighthouse returns the kept deposits and the builders of the spec result, and if the
spec fails, Lighthouse fails. -/
theorem onboard_spec {S D B E : Type} (inst : LhOnboarding S D B E)
    (cloneInst : core.clone.Clone D) (p : Spec.Preset) (o : Spec.Oracle)
    (pubkeys : List Spec.BLSPubkey) (absDep : D → Spec.PendingDeposit) (absB : B → Spec.Builder)
    (table : S → List (Spec.BLSPubkey × Nat)) (pending : S → List Spec.BLSPubkey)
    (hc : OnboardingContract inst cloneInst p o pubkeys absDep absB table pending)
    (hus : Usize.max = U64.max) (state0 : Spec.BeaconState) (ce : Nat)
    (hce : Spec.get_current_epoch p state0 = .ok ce) (hlt : ce < Spec.FAR_FUTURE_EPOCH)
    (hspe : p.SLOTS_PER_EPOCH ≠ 0) (deps : Slice D) (s : S)
    (hdeps : deps.val.map absDep = state0.pending_deposits)
    (hpk : pubkeys = state0.validators.map (·.pubkey)) (hb0 : state0.builders = [])
    (ht0 : table s = []) (hp0 : pending s = []) :
    upgrade.builder_onboarding.onboard cloneInst inst s deps ⦃ r =>
      (∀ t, Spec.onboard_builders_from_pending_deposits p o state0 = .ok t →
        ∃ kept bs, r.1 = .Ok (kept, bs) ∧
          t = { state0 with builders := bs.val.map absB, pending_deposits := kept.val.map absDep }) ∧
      (∀ e, Spec.onboard_builders_from_pending_deposits p o state0 = .error e →
        ∃ e', r.1 = .Err e') ⦄ := by
  have hspecdef : Spec.onboard_builders_from_pending_deposits p o state0 = (do
      let r ← specFold p o pubkeys state0 (deps.val.map absDep)
      pure { r.1 with pending_deposits := r.2 }) := by
    unfold Spec.onboard_builders_from_pending_deposits specFold
    rw [hdeps, hpk]
  rw [hspecdef]
  unfold upgrade.builder_onboarding.onboard
  apply exists_imp_spec
  have hinit : OnbInv p o pubkeys absDep absB table pending state0 deps
      (s, alloc.vec.Vec.new D, alloc.vec.Vec.new B, 0#usize) := by
    refine ⟨by simp, ?_, ?_, ?_, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.new]⟩
    · have : ({ state0 with builders := ([] : List B).map absB } : Spec.BeaconState) = state0 := by
        rw [List.map_nil, ← hb0]
      have hv0 : (alloc.vec.Vec.new B).val = [] := rfl
      have hd0 : (alloc.vec.Vec.new D).val = [] := rfl
      show specFold p o pubkeys state0 ((deps.val.take 0).map absDep) =
        .ok ({ state0 with builders := (alloc.vec.Vec.new B).val.map absB },
          (alloc.vec.Vec.new D).val.map absDep)
      rw [hv0, hd0, this]
      rfl
    · intro pk; simp [ht0, alloc.vec.Vec.new]
    · intro pk _; simp [hp0, alloc.vec.Vec.new, Spec.is_pending_validator]
  obtain ⟨res, hres, hpost⟩ := spec_imp_exists (onboard_loop_spec inst cloneInst p o pubkeys absDep
    absB table pending hc hus state0 ce hce hlt hspe deps s _ _ 0#usize hinit)
  rw [hres]
  obtain ⟨s', kept, bs, err⟩ := res
  simp only [uncurry_apply_pair, bind_tc_ok]
  cases err with
  | none =>
    have hf := hpost.1 rfl
    refine ⟨_, rfl, fun t ht => ⟨kept, bs, rfl, ?_⟩, fun e he => ?_⟩
    · simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at ht
      rw [← ht]
    · simp [hf, Bind.bind, Except.bind, Pure.pure, Except.pure] at he
  | some err =>
    obtain ⟨e, hf⟩ := hpost.2 err rfl
    refine ⟨_, rfl, fun t ht => ?_, fun _ _ => ⟨err, rfl⟩⟩
    simp [hf, Bind.bind, Except.bind] at ht

end EpochProofs
