import EpochProofs.Equiv.SelectionBytes
import EpochProofs.Equiv.RegistryUpdates
import EpochProofs.Equiv.EffectiveBalanceUpdates
import EpochProofs.Sanity.SelectionPass

/-!
# Lighthouse `compute_balance_weighted_selection` equals the reference

`selection_pass_spec`: one pass of the Lighthouse loop returns the candidate of
`Spec.selectionPass`. `compute_balance_weighted_selection_spec`: if the reference returns
`selected`, Lighthouse returns `Ok selected`.

`EBLink inst balances ebs` says that `inst.effective_balance balances i` returns the effective
balance `ebs[i]` of validator `i`, or `None` past the end of the registry.
-/

namespace EpochProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result state_processing

abbrev EBInst (B : Type) := types.state.balance_weighted_selection.EffectiveBalances B
abbrev SelErr := types.state.balance_weighted_selection.SelectionError

/-- `inst.effective_balance balances i` reads the effective balance `ebs[i]`. -/
def EBLink {B : Type} (inst : EBInst B) (balances : B) (ebs : List Nat) : Prop :=
  ∀ i : Usize, ∃ r, inst.effective_balance balances i = ok r ∧ r.map (·.val) = ebs[i.val]?

theorem except_bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind]
  | ok a => simp [Bind.bind, Except.bind]

theorem max_random_value_val :
    types.state.balance_weighted_selection.MAX_RANDOM_VALUE.val = 2 ^ 16 - 1 := by
  unfold types.state.balance_weighted_selection.MAX_RANDOM_VALUE; simp

theorem slice_get_usize (s : Slice Usize) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice Usize) s i = ok s.val[i.val]? :=
  rfl

theorem usize_safe_rem_ok (a b : Usize) (hb : b.val ≠ 0) :
    ∃ v : Usize, Usize.Insts.Safe_arithSafeArithUsize.safe_rem a b = ok (.Ok v) ∧
      v.val = a.val % b.val := by
  unfold Usize.Insts.Safe_arithSafeArithUsize.safe_rem
  have h := Usize.checked_rem_bv_spec a b
  cases hc : a.checked_rem b <;> simp only [hc] at h
  · exact absurd h hb
  · rename_i v
    exact ⟨v, by simp [lift, core.option.Option.ok_or], h.2.1⟩

theorem u64_safe_mul_ok (a b : U64) (h : a.val * b.val < 2 ^ 64) :
    ∃ v : U64, U64.Insts.Safe_arithSafeArithU64.safe_mul a b = ok (.Ok v) ∧
      v.val = a.val * b.val := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (safe_mul_spec a b)
  cases r with
  | Ok v => exact ⟨v, hr, (hp.1 v rfl).1⟩
  | Err e => exact absurd h (hp.2 e rfl).2

/-- Before pass `i`, the reference holds the hash of block `i // 16` unless pass `i` computes
it. -/
def RandomBytesOk (o : Spec.Oracle) (seedSpec : Spec.Bytes32) (i : Nat) (rb : Spec.Bytes32) :
    Prop :=
  i % 16 ≠ 0 → rb = o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i / 16))

theorem selection_pass_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (reg : List Nat) (hEB : EBLink ebi balances reg)
    (indices : Slice Usize) (seed : Array U8 32#usize) (seedSpec : Spec.Bytes32)
    (hseed : u8s seed.val = seedSpec.toList)
    (shuffle : Bool) (R : U8) (hR : R.val = p.SHUFFLE_ROUND_COUNT)
    (maxeb : U64) (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn : 0 < indices.val.length) (hn24 : indices.val.length ≤ 2 ^ 24)
    (hreg : ∀ j ∈ indices.val, j.val < reg.length)
    (i : Usize) (rb : Spec.Bytes32) (hrb : RandomBytesOk o seedSpec i.val rb)
    (c : Option Nat) (rb' : Spec.Bytes32)
    (hpass : Spec.selectionPass p o (indices.val.map (·.val)) seedSpec shuffle
      indices.val.length ((indices.val.map (·.val)).map (fun j => reg[j]!)) i.val rb =
        .ok (c, rb')) :
    types.state.balance_weighted_selection.selection_pass inst ebi balances indices seed shuffle
      R maxeb i ⦃ r => ∃ c' : Option Usize, r = .Ok c' ∧ c'.map (·.val) = c ⦄ := by
  unfold Spec.selectionPass at hpass
  simp only [except_bind_ok_iff] at hpass
  obtain ⟨m16, hm16, off, hoff, nx0, hnx0, hrest⟩ := hpass
  have hm16' : m16 = i.val % 16 := by
    simp only [Spec.uint64Mod, show (16 : Nat) ≠ 0 by decide, if_false] at hm16
    exact (Except.ok.inj hm16).symm
  subst hm16'
  have hoff' : off = i.val % 16 * 2 := by
    have : i.val % 16 * 2 < Spec.UINT64_SIZE := by unfold Spec.UINT64_SIZE; omega
    simp only [Spec.uint64Mul, this, if_true] at hoff
    exact (Except.ok.inj hoff).symm
  have hnx0' : nx0 = i.val % indices.val.length := by
    simp only [Spec.uint64Mod, show indices.val.length ≠ 0 by omega, if_false] at hnx0
    exact (Except.ok.inj hnx0).symm
  have hrbv : (if (off == 0) = true then
      o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i.val / 16)) else rb) =
      o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i.val / 16)) := by
    split
    · rfl
    · rename_i h
      apply hrb
      intro h0
      apply h
      rw [hoff', h0]
      rfl
  simp only [hrbv] at hrest
  unfold types.state.balance_weighted_selection.selection_pass
  have hlen : (Slice.len indices).val = indices.val.length := Slice.len_val indices
  obtain ⟨v, hv, hvv⟩ := usize_safe_rem_ok i (Slice.len indices) (by omega)
  simp only [hv, bind_tc_ok, branch_ok]
  cases shuffle
  · simp only [Bool.false_eq_true, if_false, pure_bind, except_bind_ok_iff] at hrest ⊢
    obtain ⟨eb, heb, w, hw, rv, hrv, th, hth, hfin⟩ := hrest
    have hvlt : v.val < indices.val.length := by rw [hvv, hlen]; exact Nat.mod_lt _ hn
    have hnx : nx0 = v.val := by rw [hvv, hlen, hnx0']
    subst hnx
    rw [slice_get_usize, List.getElem?_eq_getElem hvlt]
    simp only [bind_tc_ok, core.option.Option.ok_or, branch_ok]
    generalize hcand : indices.val[v.val] = cand
    have hcreg : cand.val < reg.length := by
      rw [← hcand]; exact hreg _ (List.getElem_mem _)
    obtain ⟨r, hr, hrr⟩ := hEB cand
    rw [List.getElem?_eq_getElem hcreg] at hrr
    cases r with
    | none => simp at hrr
    | some e =>
    simp only [Option.map_some, Option.some.injEq] at hrr
    have heb' : eb = reg[cand.val] := by
      simp only [Spec.listGet, List.getElem?_map, List.getElem?_eq_getElem hvlt, Option.map_some,
        hcand] at heb
      rw [← (Except.ok.inj heb), getElem!_pos reg cand.val hcreg]
    subst heb'
    have hwlt : reg[cand.val] * (2 ^ 16 - 1) < 2 ^ 64 := by
      unfold Spec.uint64Mul at hw; split at hw
      · rename_i h; unfold Spec.UINT64_SIZE at h; exact h
      · simp [throw, throwThe, MonadExceptOf.throw] at hw
    have hwv : w = reg[cand.val] * (2 ^ 16 - 1) := by
      unfold Spec.uint64Mul at hw; rw [if_pos (by unfold Spec.UINT64_SIZE; exact hwlt)] at hw
      exact (Except.ok.inj hw).symm
    obtain ⟨w', hw', hw'v⟩ := u64_safe_mul_ok e types.state.balance_weighted_selection.MAX_RANDOM_VALUE
      (by rw [hrr, max_random_value_val]; exact hwlt)
    rw [hr]
    simp only [bind_tc_ok, core.option.Option.ok_or, branch_ok, hw']
    step with random_value_spec inst o hH seed i as ⟨rv', hrv'⟩
    rw [hseed] at hrv'
    have hrvv : rv'.val = rv := by
      rw [hrv', ← hoff']
      simp only [Spec.bytes_to_uint64] at hrv
      split at hrv
      · exact (Except.ok.inj hrv)
      · simp [throw, throwThe, MonadExceptOf.throw] at hrv
    have hthlt : p.MAX_EFFECTIVE_BALANCE_ELECTRA * rv < 2 ^ 64 := by
      unfold Spec.uint64Mul at hth; split at hth
      · rename_i h; unfold Spec.UINT64_SIZE at h; exact h
      · simp [throw, throwThe, MonadExceptOf.throw] at hth
    have hthv : th = p.MAX_EFFECTIVE_BALANCE_ELECTRA * rv := by
      unfold Spec.uint64Mul at hth; rw [if_pos (by unfold Spec.UINT64_SIZE; exact hthlt)] at hth
      exact (Except.ok.inj hth).symm
    obtain ⟨th', hth', hth'v⟩ := u64_safe_mul_ok maxeb rv' (by rw [hmaxeb, hrvv]; exact hthlt)
    simp only [hth', bind_tc_ok, branch_ok]
    have hw'n : w'.val = w := by rw [hw'v, hrr, max_random_value_val, hwv]
    have hth'n : th'.val = th := by rw [hth'v, hmaxeb, hrvv, hthv]
    have hcmp : (w' ≥ th') ↔ (w ≥ th) := by
      simp only [ge_iff_le, UScalar.le_equiv, hw'n, hth'n]
    by_cases hge : w ≥ th
    · have hge' : w' ≥ th' := hcmp.2 hge
      simp only [hge', if_true, spec_ok]
      simp only [hge, if_true, except_bind_ok_iff] at hfin
      obtain ⟨x, hx, hfin⟩ := hfin
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      refine ⟨some cand, rfl, ?_⟩
      rw [← hfin.1]
      simp only [Spec.listGet, List.getElem?_map, List.getElem?_eq_getElem hvlt, Option.map_some,
        hcand] at hx
      simp [← (Except.ok.inj hx)]
    · have hge' : ¬ w' ≥ th' := fun h => hge (hcmp.1 h)
      simp only [hge', if_false, spec_ok]
      simp only [hge, if_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      exact ⟨none, rfl, by simp [← hfin.1]⟩
  · simp only [if_true, pure_bind, except_bind_ok_iff] at hrest ⊢
    obtain ⟨nx, hcsi, eb, heb, w, hw, rv, hrv, th, hth, hfin⟩ := hrest
    have hvlt0 : v.val < indices.val.length := by rw [hvv, hlen]; exact Nat.mod_lt _ hn
    apply spec_bind (compute_shuffled_index_with_eq inst p o hH v (Slice.len indices) seed seedSpec
      hseed R hR (by rw [hlen]; exact hn24) (by rw [hlen]; exact hvlt0))
    intro o1 hpost
    obtain ⟨x, ho1, hx⟩ := hpost
    simp only [ho1]
    rw [hlen, hvv, hlen, ← hnx0', hcsi] at hx
    have hxn : nx = x.val := Except.ok.inj hx
    subst hxn
    simp only [core.option.Option.ok_or, bind_tc_ok, branch_ok]
    have hxlt : x.val < indices.val.length := by
      simp only [Spec.listGet] at heb
      split at heb
      · rename_i a ha
        have := (List.getElem?_eq_some_iff.mp ha).1
        simpa using this
      · simp [throw, throwThe, MonadExceptOf.throw] at heb
    rw [slice_get_usize, List.getElem?_eq_getElem hxlt]
    simp only [bind_tc_ok, core.option.Option.ok_or, branch_ok]
    generalize hcand : indices.val[x.val] = cand
    have hcreg : cand.val < reg.length := by
      rw [← hcand]; exact hreg _ (List.getElem_mem _)
    obtain ⟨r, hr, hrr⟩ := hEB cand
    rw [List.getElem?_eq_getElem hcreg] at hrr
    cases r with
    | none => simp at hrr
    | some e =>
    simp only [Option.map_some, Option.some.injEq] at hrr
    have heb' : eb = reg[cand.val] := by
      simp only [Spec.listGet, List.getElem?_map, List.getElem?_eq_getElem hxlt, Option.map_some,
        hcand] at heb
      rw [← (Except.ok.inj heb), getElem!_pos reg cand.val hcreg]
    subst heb'
    have hwlt : reg[cand.val] * (2 ^ 16 - 1) < 2 ^ 64 := by
      unfold Spec.uint64Mul at hw; split at hw
      · rename_i h; unfold Spec.UINT64_SIZE at h; exact h
      · simp [throw, throwThe, MonadExceptOf.throw] at hw
    have hwv : w = reg[cand.val] * (2 ^ 16 - 1) := by
      unfold Spec.uint64Mul at hw; rw [if_pos (by unfold Spec.UINT64_SIZE; exact hwlt)] at hw
      exact (Except.ok.inj hw).symm
    obtain ⟨w', hw', hw'v⟩ := u64_safe_mul_ok e types.state.balance_weighted_selection.MAX_RANDOM_VALUE
      (by rw [hrr, max_random_value_val]; exact hwlt)
    rw [hr]
    simp only [bind_tc_ok, core.option.Option.ok_or, branch_ok, hw']
    step with random_value_spec inst o hH seed i as ⟨rv', hrv'⟩
    rw [hseed] at hrv'
    have hrvv : rv'.val = rv := by
      rw [hrv', ← hoff']
      simp only [Spec.bytes_to_uint64] at hrv
      split at hrv
      · exact (Except.ok.inj hrv)
      · simp [throw, throwThe, MonadExceptOf.throw] at hrv
    have hthlt : p.MAX_EFFECTIVE_BALANCE_ELECTRA * rv < 2 ^ 64 := by
      unfold Spec.uint64Mul at hth; split at hth
      · rename_i h; unfold Spec.UINT64_SIZE at h; exact h
      · simp [throw, throwThe, MonadExceptOf.throw] at hth
    have hthv : th = p.MAX_EFFECTIVE_BALANCE_ELECTRA * rv := by
      unfold Spec.uint64Mul at hth; rw [if_pos (by unfold Spec.UINT64_SIZE; exact hthlt)] at hth
      exact (Except.ok.inj hth).symm
    obtain ⟨th', hth', hth'v⟩ := u64_safe_mul_ok maxeb rv' (by rw [hmaxeb, hrvv]; exact hthlt)
    simp only [hth', bind_tc_ok, branch_ok]
    have hw'n : w'.val = w := by rw [hw'v, hrr, max_random_value_val, hwv]
    have hth'n : th'.val = th := by rw [hth'v, hmaxeb, hrvv, hthv]
    have hcmp : (w' ≥ th') ↔ (w ≥ th) := by
      simp only [ge_iff_le, UScalar.le_equiv, hw'n, hth'n]
    by_cases hge : w ≥ th
    · have hge' : w' ≥ th' := hcmp.2 hge
      simp only [hge', if_true, spec_ok]
      simp only [hge, if_true, except_bind_ok_iff] at hfin
      obtain ⟨x, hx, hfin⟩ := hfin
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      refine ⟨some cand, rfl, ?_⟩
      rw [← hfin.1]
      simp only [Spec.listGet, List.getElem?_map, List.getElem?_eq_getElem hxlt, Option.map_some,
        hcand] at hx
      simp [← (Except.ok.inj hx)]
    · have hge' : ¬ w' ≥ th' := fun h => hge (hcmp.1 h)
      simp only [hge', if_false, spec_ok]
      simp only [hge, if_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      exact ⟨none, rfl, by simp [← hfin.1]⟩


theorem selectionPass_rb (p : Spec.Preset) (o : Spec.Oracle) (indices : List Nat)
    (seedSpec : Spec.Bytes32) (shuffle : Bool) (total : Nat) (ebs : List Nat) (i : Nat)
    (rb : Spec.Bytes32) (hrb : RandomBytesOk o seedSpec i rb) (c : Option Nat)
    (rb' : Spec.Bytes32)
    (hpass : Spec.selectionPass p o indices seedSpec shuffle total ebs i rb = .ok (c, rb')) :
    rb' = o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i / 16)) := by
  unfold Spec.selectionPass at hpass
  simp only [except_bind_ok_iff] at hpass
  obtain ⟨m16, hm16, off, hoff, nx0, hnx0, hrest⟩ := hpass
  have hm16' : m16 = i % 16 := by
    simp only [Spec.uint64Mod, show (16 : Nat) ≠ 0 by decide, if_false] at hm16
    exact (Except.ok.inj hm16).symm
  subst hm16'
  have hoff' : off = i % 16 * 2 := by
    have : i % 16 * 2 < Spec.UINT64_SIZE := by unfold Spec.UINT64_SIZE; omega
    simp only [Spec.uint64Mul, this, if_true] at hoff
    exact (Except.ok.inj hoff).symm
  have hrbv : (if (off == 0) = true then
      o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i / 16)) else rb) =
      o.hash (seedSpec.toList ++ Spec.uint_to_bytes 8 (i / 16)) := by
    split
    · rfl
    · rename_i h
      apply hrb
      intro h0
      apply h
      rw [hoff', h0]
      rfl
  simp only [hrbv] at hrest
  cases shuffle
  · simp only [Bool.false_eq_true, if_false, pure_bind, except_bind_ok_iff] at hrest
    obtain ⟨_, _, _, _, _, _, _, _, hfin⟩ := hrest
    split at hfin
    · simp only [except_bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      obtain ⟨_, _, _, h⟩ := hfin
      exact h.symm
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      exact hfin.2.symm
  · simp only [if_true, pure_bind, except_bind_ok_iff] at hrest
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hfin⟩ := hrest
    split at hfin
    · simp only [except_bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      obtain ⟨_, _, _, h⟩ := hfin
      exact h.symm
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfin
      exact hfin.2.symm

theorem selection_loop_zero (p : Spec.Preset) (o : Spec.Oracle) (indices : List Nat)
    (seedSpec : Spec.Bytes32) (size : Nat) (shuffle : Bool) (total : Nat) (ebs : List Nat)
    (sel : List Nat) (i : Nat) (rb : Spec.Bytes32) (res : List Nat) :
    Spec.compute_balance_weighted_selection_loop p o indices seedSpec size shuffle total ebs 0
      sel i rb ≠ .ok res := by
  simp [Spec.compute_balance_weighted_selection_loop, throw, throwThe, MonadExceptOf.throw]

theorem selection_loop_spec {H B : Type} (inst : ShuffleHashInst H) (ebi : EBInst B)
    (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (reg : List Nat) (hEB : EBLink ebi balances reg)
    (indices : Slice Usize) (seed : Array U8 32#usize) (seedSpec : Spec.Bytes32)
    (hseed : u8s seed.val = seedSpec.toList)
    (shuffle : Bool) (R : U8) (hR : R.val = p.SHUFFLE_ROUND_COUNT)
    (maxeb : U64) (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn : 0 < indices.val.length) (hn24 : indices.val.length ≤ 2 ^ 24)
    (hreg : ∀ j ∈ indices.val, j.val < reg.length) (size : Usize)
    (hus : Usize.max = U64.max)
    (selected : alloc.vec.Vec Usize) (i : Usize) (rb : Spec.Bytes32) (fuel : Nat)
    (res : List Nat) (hrb : RandomBytesOk o seedSpec i.val rb)
    (hrun : Spec.compute_balance_weighted_selection_loop p o (indices.val.map (·.val)) seedSpec
      size.val shuffle indices.val.length ((indices.val.map (·.val)).map (fun j => reg[j]!)) fuel
      (selected.val.map (·.val)) i.val rb = .ok res) :
    types.state.balance_weighted_selection.compute_balance_weighted_selection_loop inst ebi
      balances indices seed size shuffle R maxeb selected i ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ := by
  unfold types.state.balance_weighted_selection.compute_balance_weighted_selection_loop
  apply loop.spec_decr_nat
    (measure := fun (x : alloc.vec.Vec Usize × Usize) => Usize.max + 1 - x.2.val)
    (inv := fun (x : alloc.vec.Vec Usize × Usize) => ∃ fuel rb,
      RandomBytesOk o seedSpec x.2.val rb ∧
      Spec.compute_balance_weighted_selection_loop p o (indices.val.map (·.val)) seedSpec
        size.val shuffle indices.val.length ((indices.val.map (·.val)).map (fun j => reg[j]!))
        fuel (x.1.val.map (·.val)) x.2.val rb = .ok res)
  · rintro ⟨sel, j⟩ ⟨fuel, rb, hrb, hrun⟩
    dsimp only at hrb hrun ⊢
    unfold types.state.balance_weighted_selection.compute_balance_weighted_selection_loop.body
    cases fuel with
    | zero => exact absurd hrun (selection_loop_zero _ _ _ _ _ _ _ _ _ _ _ _)
    | succ fuel =>
    rw [Spec.selection_loop_succ] at hrun
    have hlenv : (alloc.vec.Vec.len sel).val = (sel.val.map (·.val)).length := by simp
    dsimp only
    split
    · rename_i hlt
      have hlt' : (sel.val.map (·.val)).length < size.val := by rw [← hlenv]; scalar_tac
      rw [if_pos hlt'] at hrun
      simp only [except_bind_ok_iff] at hrun
      obtain ⟨⟨c, rb'⟩, hpass, j', hj', hrun'⟩ := hrun
      apply spec_bind (selection_pass_spec inst ebi balances p o hH reg hEB indices seed seedSpec
        hseed shuffle R hR maxeb hmaxeb hn hn24 hreg j rb hrb c rb' hpass)
      intro r hr
      obtain ⟨c', hrc, hc'⟩ := hr
      simp only [hrc]
      have hj1 : j.val + 1 < 2 ^ 64 := by
        simp only [Spec.uint64Add] at hj'
        split at hj'
        · rename_i h; unfold Spec.UINT64_SIZE at h; exact h
        · simp [throw, throwThe, MonadExceptOf.throw] at hj'
      have hj'v : j' = j.val + 1 := by
        simp only [Spec.uint64Add, show j.val + 1 < Spec.UINT64_SIZE by
          unfold Spec.UINT64_SIZE; exact hj1, if_true] at hj'
        exact (Except.ok.inj hj').symm
      have hrb' := selectionPass_rb p o _ seedSpec shuffle _ _ j.val rb hrb c rb' hpass
      have hselmax : sel.val.length < Usize.max := by
        have h1 : sel.val.length < size.val := by simpa using hlt'
        scalar_tac
      have hjmax : j.val + 1 ≤ Usize.max := by rw [hus, U64.max_eq]; omega
      clear hrc
      cases c' with
      | none =>
        simp only [Option.map_none] at hc'
        subst hc'
        simp only [bind_tc_ok]
        have hs1 : sel.val.map (·.val) = sel.val.map (·.val) ++ (none : Option Nat).toList := by
          simp
        have hca := Usize.checked_add_bv_spec j 1#usize
        cases hcj : j.checked_add 1#usize with
        | none =>
          simp only [hcj] at hca
          simp at hca; omega
        | some nxt =>
          simp only [hcj] at hca
          simp only [lift, bind_tc_ok, hcj, spec_ok]
          have hnxt : nxt.val = j.val + 1 := by simpa using hca.2.1
          refine ⟨⟨fuel, rb', ?_, ?_⟩, by omega⟩
          · intro h
            rw [hrb', hnxt]
            rw [hnxt] at h
            congr 3
            omega
          · rw [hnxt, ← hj'v, hs1]
            exact hrun'
      | some x =>
        simp only [Option.map_some] at hc'
        subst hc'
        step with alloc.vec.Vec.push_spec as ⟨s1, hs1v⟩
        have hs1 : s1.val.map (·.val) = sel.val.map (·.val) ++ (some x.val).toList := by
          simp [hs1v]
        have hca := Usize.checked_add_bv_spec j 1#usize
        cases hcj : j.checked_add 1#usize with
        | none =>
          simp only [hcj] at hca
          simp at hca; omega
        | some nxt =>
          simp only [hcj] at hca
          simp only [lift, bind_tc_ok, hcj, spec_ok]
          have hnxt : nxt.val = j.val + 1 := by simpa using hca.2.1
          refine ⟨⟨fuel, rb', ?_, ?_⟩, by omega⟩
          · intro h
            rw [hrb', hnxt]
            rw [hnxt] at h
            congr 3
            omega
          · rw [hnxt, ← hj'v, hs1]
            exact hrun'
    · rename_i hge
      have hge' : ¬ (sel.val.map (·.val)).length < size.val := by rw [← hlenv]; scalar_tac
      rw [if_neg hge'] at hrun
      simp only [spec_ok]
      exact ⟨sel, rfl, Except.ok.inj hrun⟩
  · exact ⟨fuel, rb, hrb, hrun⟩

theorem mapM_effective_balances (vals : List Spec.Validator) (indices : List Nat)
    (ebs : List Nat)
    (h : indices.mapM (fun index => do
      let v ← Spec.listGet vals index
      pure v.effective_balance) = .ok ebs) :
    ebs = indices.map (fun j => (vals.map (·.effective_balance))[j]!) ∧
      ∀ j ∈ indices, j < vals.length := by
  induction indices generalizing ebs with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons j rest ih =>
    simp only [List.mapM_cons, except_bind_ok_iff] at h
    obtain ⟨e, he, ebs', hrest, hfin⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at hfin
    obtain ⟨v, hv, he⟩ := he
    simp only [pure, Except.pure, Except.ok.injEq] at he
    have hj : j < vals.length ∧ vals[j]? = some v := by
      simp only [Spec.listGet] at hv
      split at hv
      · rename_i a ha
        have := List.getElem?_eq_some_iff.mp ha
        exact ⟨this.1, by rw [ha, Except.ok.inj hv]⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at hv
    obtain ⟨ih1, ih2⟩ := ih ebs' hrest
    subst hfin
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, ih1, List.cons.injEq, and_true]
      rw [getElem!_pos _ j (by simp; exact hj.1), ← he]
      simp [(List.getElem?_eq_some_iff.mp hj.2).2]
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hj.1
      · exact ih2 k hk

/-- Lighthouse `compute_balance_weighted_selection` equals the reference. -/
theorem compute_balance_weighted_selection_spec {H B : Type} (inst : ShuffleHashInst H)
    (ebi : EBInst B) (balances : B) (p : Spec.Preset) (o : Spec.Oracle) (hH : HashLink inst o)
    (state : Spec.BeaconState)
    (hEB : EBLink ebi balances (state.validators.map (·.effective_balance)))
    (indices : Slice Usize) (seed : Array U8 32#usize) (seedSpec : Spec.Bytes32)
    (hseed : u8s seed.val = seedSpec.toList)
    (shuffle : Bool) (R : U8) (hR : R.val = p.SHUFFLE_ROUND_COUNT)
    (maxeb : U64) (hmaxeb : maxeb.val = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hn24 : indices.val.length ≤ 2 ^ 24) (size : Usize) (hus : Usize.max = U64.max)
    (res : List Nat)
    (hspec : Spec.compute_balance_weighted_selection p o state (indices.val.map (·.val)) seedSpec
      size.val shuffle = .ok res) :
    types.state.balance_weighted_selection.compute_balance_weighted_selection inst ebi balances
      indices seed size shuffle R maxeb ⦃ r =>
        ∃ v : alloc.vec.Vec Usize, r = .Ok v ∧ v.val.map (·.val) = res ⦄ := by
  unfold Spec.compute_balance_weighted_selection at hspec
  simp only [List.length_map] at hspec
  have hn : 0 < indices.val.length := by
    by_contra h0
    simp [h0, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hspec
  simp only [gt_iff_lt, hn, not_true_eq_false, if_false, except_bind_ok_iff] at hspec
  obtain ⟨_, _, ebs, hebs, hrun⟩ := hspec
  obtain ⟨hebs', hreg0⟩ := mapM_effective_balances _ _ _ hebs
  subst hebs'
  have hreg : ∀ j ∈ indices.val, j.val < (state.validators.map (·.effective_balance)).length := by
    intro j hj
    simpa using hreg0 j.val (List.mem_map.mpr ⟨j, hj, rfl⟩)
  unfold types.state.balance_weighted_selection.compute_balance_weighted_selection
  have hne : ¬ indices.val.isEmpty := by
    cases h : indices.val with
    | nil => rw [h] at hn; simp at hn
    | cons _ _ => simp
  step*
  have hreg' : ∀ j ∈ indices.val, j.val < (state.validators.map (·.effective_balance)).length :=
    hreg
  exact selection_loop_spec inst ebi balances p o hH _ hEB indices seed seedSpec hseed shuffle R hR
    maxeb hmaxeb hn hn24 hreg' size hus _ 0#usize Spec.Bytes32.zero Spec.UINT64_SIZE res
    (by intro h; simp at h) (by simpa using hrun)

end EpochProofs
