import EthLib.Consensus.Participation
import EthLib.Consensus.Proofs.Accessors
import EpochProofs.EthLib.Preset
import EpochProofs.EthLib.Results
import EpochProofs.EthLib.State
import EpochProofs.Spec.Helpers
import EpochProofs.Spec.TotalActiveBalance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The accessors that the epoch steps share

Each theorem says that an EthLib accessor and the reference accessor have the same outcome.

Two hypotheses occur:

- `hslots : preset.SLOTS_PER_EPOCH ≠ 0`. The reference fails on a division by zero. EthLib divides
  by a preset value without this check. Mainnet and minimal satisfy it.
- `hregistry : s.RegistryWithinLimit`. EthLib reads a registry position as a `UInt64` index, and
  the reference does not. A Fulu state always satisfies it, see `registryWithinLimit_of_fulu`.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- Before Gloas, the type of the registry holds the limit. -/
theorem registryWithinLimit_of_fulu (s : BeaconState preset .fusaka) : s.RegistryWithinLimit :=
  s.validators.bound (by decide)

/-- The reference state is the EthLib state. -/
abbrev SameState (a : BeaconState preset fork) (b : Spec.BeaconState) : Prop := b = toSpecState a

/-! ## Epochs -/

theorem get_current_epoch_eq (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset fork) :
    Spec.get_current_epoch (toSpecPreset preset config) (toSpecState s) =
      .ok (getCurrentEpoch s).toNat := by
  have hslots' : preset.SLOTS_PER_EPOCH.toNat ≠ 0 := fun h => hslots (UInt64.toNat_inj.mp h)
  rw [getCurrentEpoch_toNat]
  simp [Spec.get_current_epoch, Spec.compute_epoch_at_slot, Spec.uint64Div, toSpecPreset,
    toSpecState, hslots', pure, Except.pure]

theorem get_previous_epoch_eq (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    (s : BeaconState preset fork) :
    Spec.get_previous_epoch (toSpecPreset preset config) (toSpecState s) =
      .ok (getPreviousEpoch s).toNat := by
  rw [getPreviousEpoch_toNat]
  simp only [Spec.get_previous_epoch, get_current_epoch_eq hslots, bind, Except.bind, pure,
    Except.pure, Spec.saturating_sub, Except.ok.injEq]
  generalize (getCurrentEpoch s).toNat = epoch
  by_cases h : epoch > 1
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Nat.sub_self]
    exact (Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)).symm

theorem next_epoch_same (s : BeaconState preset fork) :
    SameOutcome SameNumber (liftAccessor (liftArith (addChecked (getCurrentEpoch s) 1)))
      (Spec.uint64Add (getCurrentEpoch s).toNat 1) :=
  (addChecked_same (getCurrentEpoch s) 1).liftArith.liftAccessor

/-! ## Circular buffers -/

theorem toNat_mod_lt_length {α : Type} {n i : UInt64} (buffer : Vector α n.toNat) (hn : n ≠ 0) :
    (i % n).toNat < buffer.toList.length := by
  rw [Vector.length_toList]
  exact toNat_mod_lt hn

theorem readCircular_same {α : Type} {n : UInt64} (buffer : Vector α n.toNat) (i : UInt64) :
    SameOutcome (fun a b => b = a) (readCircular buffer i)
      (do Spec.listGet buffer.toList (← Spec.uint64Mod i.toNat n.toNat)) := by
  unfold readCircular
  by_cases hn : n = 0
  · subst hn
    exact .failed
  · rw [dite_eq_right hn, uint64Mod_eq hn]
    have hlt := toNat_mod_lt_length (i := i) buffer hn
    simp only [bind_ok, Spec.listGet, List.getElem?_eq_getElem hlt]
    exact .returned (by simp)

theorem writeCircularRooted_same {α β : Type} [SszType α] {n : UInt64}
    (read : α → β) (buffer : RootedVector α n.toNat) (i : UInt64) (value : α) :
    SameOutcome (fun a b => b = a.elements.toList.map read)
      (writeCircularRooted buffer i value)
      (do
        let position ← Spec.uint64Mod i.toNat n.toNat
        Spec.listSet (buffer.elements.toList.map read) position (read value)) := by
  unfold writeCircularRooted
  by_cases hn : n = 0
  · subst hn
    exact .failed
  · rw [dite_eq_right hn, uint64Mod_eq hn]
    have hlt := toNat_mod_lt_length (i := i) buffer.elements hn
    simp only [bind_ok, Spec.listSet, List.length_map, hlt, ite_true]
    refine .returned ?_
    simp [RootedVector.set, Vector.toList_set, List.map_set]

/-! ## Block roots -/

theorem get_block_root_at_slot_same (s : BeaconState preset fork) (slot : UInt64) :
    SameOutcome (fun a b => b = a) (getBlockRootAtSlot s slot)
      (Spec.get_block_root_at_slot (toSpecPreset preset config) (toSpecState s) slot.toNat) := by
  unfold getBlockRootAtSlot Spec.get_block_root_at_slot
  have hslot : (toSpecState s).slot = s.slot.toNat := rfl
  rw [hslot]
  by_cases hlt : slot < s.slot
  · rw [ite_eq_left hlt, ite_eq_right (by simpa using UInt64.lt_iff_toNat_lt.mp hlt)]
    refine .bind (addChecked_same slot preset.SLOTS_PER_HISTORICAL_ROOT).liftArith ?_
    rintro last _ rfl -
    by_cases hle : s.slot ≤ last
    · rw [ite_eq_left hle, ite_eq_right (by simpa using UInt64.le_iff_toNat_le.mp hle)]
      unfold _root_.EthLib.Consensus.readCircular Spec.listGet
      by_cases hzero : preset.SLOTS_PER_HISTORICAL_ROOT = 0
      · have hlength : s.blockRoots.elements.toList.length = 0 := by simp [hzero]
        have hnone : (toSpecState s).block_roots = [] := List.length_eq_zero_iff.mp hlength
        simp only [hzero, dite_true, hnone, List.getElem?_nil]
        exact .failed
      · have hlt : slot.toNat % preset.SLOTS_PER_HISTORICAL_ROOT.toNat <
            preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
          rw [← UInt64.toNat_mod]
          exact toNat_mod_lt hzero
        simp only [hzero, dite_false, toSpecState, toSpecPreset, Vector.getElem?_toList,
          Vector.getElem?_eq_getElem hlt]
        exact .returned (by simp [UInt64.toNat_mod])
    · rw [ite_eq_right hle, ite_eq_left (by simpa [UInt64.le_iff_toNat_le] using hle)]
      exact .failed
  · rw [ite_eq_right hlt, ite_eq_left (by simpa [UInt64.lt_iff_toNat_lt] using hlt)]
    exact .failed

theorem get_block_root_same (s : BeaconState preset fork) (epoch : UInt64) :
    SameOutcome (fun a b => b = a) (getBlockRoot s epoch)
      (Spec.get_block_root (toSpecPreset preset config) (toSpecState s) epoch.toNat) := by
  unfold getBlockRoot Spec.get_block_root
  refine .bind (mulChecked_same epoch preset.SLOTS_PER_EPOCH).liftArith ?_
  rintro slot _ rfl -
  exact get_block_root_at_slot_same s slot

/-! ## Sets of validator indices -/

/-- The reference list holds the same validator indices as the EthLib list. The indices are
distinct, and each one names a validator of the state. -/
structure SameIndices (s : BeaconState preset fork) (indices : List UInt64)
    (specIndices : List Nat) : Prop where
  eq : specIndices = indices.map UInt64.toNat
  nodup : indices.Nodup
  inside : ∀ index ∈ indices, index.toNat < s.validators.data.size

theorem is_active_validator_eq (v : Validator) (epoch : UInt64) :
    Spec.is_active_validator (toSpecValidator v) epoch.toNat = isActiveValidator v epoch := by
  simp only [Spec.is_active_validator, isActiveValidator, toSpecValidator, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt]
  rfl

theorem get_active_validator_indices_same {s : BeaconState preset fork}
    (hregistry : s.RegistryWithinLimit) (epoch : UInt64) :
    SameIndices s (getActiveValidatorIndices s epoch)
      (Spec.get_active_validator_indices (toSpecState s) epoch.toNat) where
  eq := by
    unfold Spec.get_active_validator_indices getActiveValidatorIndices
    simp only [toSpecState, readList, List.zipIdx_map, List.filter_map, List.map_map,
      List.map_filterMap]
    rw [← List.filterMap_eq_filter, ← List.filterMap_eq_map, List.filterMap_filterMap]
    refine List.filterMap_congr ?_
    rintro ⟨v, i⟩ hmem
    have hi : i < s.validators.data.size := by simpa using (List.mem_zipIdx' hmem).1
    simp only [Function.comp, Prod.map, is_active_validator_eq, Option.guard, id]
    split <;> simp_all [toNat_toUInt64_of_lt hregistry hi]
  nodup := (getActiveValidatorIndices_sorted hregistry epoch).imp UInt64.ne_of_lt
  inside := fun _ => lt_size_of_mem_getActiveValidatorIndices

theorem listGet_validators {s : BeaconState preset fork} {i : Nat}
    (hi : i < s.validators.data.size) :
    Spec.listGet (toSpecState s).validators i = .ok (toSpecValidator s.validators.data[i]) := by
  simp [Spec.listGet, toSpecState, readList, hi, pure, Except.pure]

theorem mapM_ok {ε α β : Type} {f : α → Except ε β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = .ok (g a)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_ok fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem mapM_error {ε α β : Type} {f : α → Except ε β} {a : α} {e : ε} :
    ∀ {l : List α}, a ∈ l → f a = .error e → ∃ e', l.mapM f = .error e'
  | b :: l, hmem, h => by
    rw [List.mapM_cons]
    cases hb : f b with
    | error e' => exact ⟨e', rfl⟩
    | ok c =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [h] at hb
        cases hb
      · obtain ⟨e', h'⟩ := mapM_error hmem h
        exact ⟨e', by rw [h']; rfl⟩

/-- A loop that appends each element that passes a test. -/
theorem forIn_filter_ok {α : Type} {body : α → List α → Spec.SpecM (ForInStep (List α))}
    {test : α → Bool} :
    ∀ {l : List α} {acc : List α},
      (∀ a ∈ l, ∀ acc, body a acc = .ok (.yield (if test a then acc ++ [a] else acc))) →
      forIn l acc body = .ok (acc ++ l.filter test)
  | [], acc, _ => by simp [pure, Except.pure]
  | a :: l, acc, h => by
    rw [List.forIn_cons, h a List.mem_cons_self]
    simp only [bind, Except.bind]
    rw [forIn_filter_ok fun b hb => h b (List.mem_cons_of_mem _ hb)]
    by_cases ha : test a = true <;> simp [ha]

/-- A loop that never stops early fails if its body fails on some element. -/
theorem forIn_error {α β : Type} {body : α → β → Spec.SpecM (ForInStep β)} {a : α}
    (hyield : ∀ a acc r, body a acc = .ok r → ∃ acc', r = .yield acc')
    (ha : ∀ acc, ∃ e, body a acc = .error e) :
    ∀ {l : List α} {acc : β}, a ∈ l → ∃ e, forIn l acc body = .error e
  | b :: l, acc, hmem => by
    rw [List.forIn_cons]
    cases hb : body b acc with
    | error e => exact ⟨e, rfl⟩
    | ok r =>
      obtain ⟨acc', rfl⟩ := hyield _ _ _ hb
      rcases List.mem_cons.mp hmem with rfl | hmem
      · obtain ⟨e, he⟩ := ha acc
        rw [he] at hb
        cases hb
      · exact forIn_error hyield ha hmem

theorem has_flag_eq (flags : UInt8) (flag : UInt64) (hflag : flag.toNat < 3) :
    Spec.has_flag flags flag.toNat = .ok (hasFlag flags flag) := by
  have h : flag = 0 ∨ flag = 1 ∨ flag = 2 := by
    simp only [← UInt64.toNat_inj]
    simp
    omega
  rcases h with rfl | rfl | rfl <;> rfl

/-- The loops of `get_unslashed_participating_indices` over the active indices. -/
theorem unslashed_participating_same {s : BeaconState preset fork}
    {participation : Array ParticipationFlags} {active : List UInt64} (flag : UInt64)
    (hflag : flag.toNat < 3) (hnodup : active.Nodup)
    (hinside : ∀ index ∈ active, index.toNat < s.validators.data.size) :
    SameOutcome (SameIndices s)
      (do
        let read ← active.mapM fun index => do
          let some flags := participation[index.toNat]?
            | throw (AccessorError.indexOutOfRange index)
          return (index, hasFlag flags flag && !(← getValidator s index).slashed)
        return (read.filter (·.2)).map (·.1))
      (do
        let mut participating_indices := []
        for i in active.map UInt64.toNat do
          if (← Spec.has_flag (← Spec.listGet participation.toList i) flag.toNat) then
            participating_indices := participating_indices ++ [i]
        let mut unslashed := []
        for index in participating_indices do
          if !(← Spec.listGet (toSpecState s).validators index).slashed then
            unslashed := unslashed ++ [index]
        Pure.pure unslashed) := by
  have hbody (i : Nat) (acc : List Nat) :
      (do
        if (← Spec.has_flag (← Spec.listGet participation.toList i) flag.toNat) then
          Pure.pure (ForInStep.yield (acc ++ [i]))
        else Pure.pure (ForInStep.yield acc) : Spec.SpecM (ForInStep (List Nat))) =
      match participation[i]? with
      | some flags => .ok (.yield (if hasFlag flags flag then acc ++ [i] else acc))
      | none => .error .indexOutOfRange := by
    cases hflags : participation[i]? with
    | none => simp [Spec.listGet, hflags, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    | some flags =>
      simp only [Spec.listGet, Array.getElem?_toList, hflags, Pure.pure, Except.pure, bind_ok,
        has_flag_eq flags flag hflag]
      split <;> rfl
  simp only [hbody]
  by_cases hall : ∀ index ∈ active, index.toNat < participation.size
  case neg =>
    obtain ⟨index, hmem, hout⟩ : ∃ index ∈ active, ¬index.toNat < participation.size := by
      simpa using hall
    have hnone := Array.getElem?_eq_none (Nat.not_lt.mp hout)
    obtain ⟨e, he⟩ := mapM_error (f := fun index : UInt64 => do
      let some flags := participation[index.toNat]?
        | throw (AccessorError.indexOutOfRange index)
      return (index, hasFlag flags flag && !(← getValidator s index).slashed)) hmem
      (show _ = Except.error (AccessorError.indexOutOfRange index) by rw [hnone]; rfl)
    obtain ⟨e', he'⟩ := forIn_error (l := active.map UInt64.toNat) (acc := [])
      (a := index.toNat) (body := fun i acc =>
        match participation[i]? with
        | some flags => .ok (.yield (if hasFlag flags flag then acc ++ [i] else acc))
        | none => .error .indexOutOfRange)
      (fun i acc r h => by
        split at h <;> cases h
        exact ⟨_, rfl⟩)
      (fun acc => ⟨.indexOutOfRange, by simp only [hnone]⟩)
      (List.mem_map_of_mem hmem)
    rw [he, he']
    exact .failed
  have hread := mapM_ok (l := active) (f := fun index : UInt64 => do
      let some flags := participation[index.toNat]?
        | throw (AccessorError.indexOutOfRange index)
      return (index, hasFlag flags flag && !(← getValidator s index).slashed))
    (g := fun index => (index, hasFlag (participation.getD index.toNat 0) flag &&
      !((s.validators.data[index.toNat]?.map (·.slashed)).getD false)))
    (fun index hmem => by
      simp [getValidator, hall index hmem, hinside index hmem, Array.getD, bind, Except.bind,
        Pure.pure, Except.pure])
  have hloop := forIn_filter_ok (l := active.map UInt64.toNat) (acc := [])
    (test := fun i => hasFlag (participation.getD i 0) flag) (body := fun i acc =>
      match participation[i]? with
      | some flags => .ok (.yield (if hasFlag flags flag then acc ++ [i] else acc))
      | none => .error .indexOutOfRange)
    (fun i hmem acc => by
      obtain ⟨index, hmem', rfl⟩ := List.mem_map.mp hmem
      simp [hall index hmem', Array.getD])
  rw [hread, hloop]
  simp only [bind_ok, List.nil_append]
  have hslashed := forIn_filter_ok
    (l := (active.map UInt64.toNat).filter fun i => hasFlag (participation.getD i 0) flag)
    (acc := [])
    (test := fun i => !((s.validators.data[i]?.map (·.slashed)).getD false))
    (body := fun index acc => do
      if !(← Spec.listGet (toSpecState s).validators index).slashed then
        Pure.pure (.yield (acc ++ [index]))
      else Pure.pure (.yield acc))
    (fun i hmem acc => by
      obtain ⟨index, hmem', rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
      have hlt := hinside index hmem'
      rw [listGet_validators hlt]
      cases hs : s.validators.data[index.toNat].slashed <;>
        simp [toSpecValidator, hlt, hs, Pure.pure, Except.pure, bind, Except.bind])
  rw [hslashed]
  refine .returned ⟨?_, ?_, ?_⟩
  · simp [List.filter_map, List.filter_filter, Function.comp_def, Bool.and_comm]
  · simpa [List.filter_map, Function.comp_def] using hnodup.filter _
  · intro index hmem
    simp only [List.mem_map, List.mem_filter] at hmem
    obtain ⟨_, ⟨⟨index, hmem, rfl⟩, -⟩, rfl⟩ := hmem
    exact hinside index hmem

theorem get_unslashed_participating_indices_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    {s : BeaconState preset fork} (altair : .altair ≤ fork) (hregistry : s.RegistryWithinLimit)
    (flag : UInt64) (hflag : flag.toNat < 3) (epoch : UInt64) :
    SameOutcome (SameIndices s) (getUnslashedParticipatingIndices s altair flag epoch)
      (Spec.get_unslashed_participating_indices (toSpecPreset preset config) (toSpecState s)
        flag.toNat epoch.toNat) := by
  unfold getUnslashedParticipatingIndices Spec.get_unslashed_participating_indices
  rw [get_previous_epoch_eq hslots, get_current_epoch_eq hslots]
  simp only [bind_ok]
  by_cases hrecent : epoch = getPreviousEpoch s ∨ epoch = getCurrentEpoch s
  case neg =>
    rw [ite_eq_right hrecent, ite_eq_left (by simpa [UInt64.toNat_inj] using hrecent)]
    exact .failed
  rw [ite_eq_left hrecent]
  have hrecent' : (!(epoch.toNat == (getPreviousEpoch s).toNat ||
      epoch.toNat == (getCurrentEpoch s).toNat)) = false := by
    simpa [UInt64.toNat_inj, Decidable.or_iff_not_imp_left] using hrecent
  have hparticipation : (if (epoch.toNat == (getCurrentEpoch s).toNat) = true then
      (toSpecState s).current_epoch_participation
      else (toSpecState s).previous_epoch_participation) =
      (if epoch = getCurrentEpoch s then (s.currentEpochParticipation altair).data
      else (s.previousEpochParticipation altair).data).toList := by
    rw [toSpecState_current_epoch_participation s altair,
      toSpecState_previous_epoch_participation s altair]
    by_cases h : epoch = getCurrentEpoch s <;> simp [h, UInt64.toNat_inj]
  obtain ⟨heq, hnodup, hinside⟩ := get_active_validator_indices_same hregistry epoch
  rw [heq, getActiveValidatorIndicesChecked_of_within hregistry]
  simp only [bind_ok, hrecent', Bool.false_eq_true, ite_false, hparticipation]
  generalize (if epoch = getCurrentEpoch s then (s.currentEpochParticipation altair).data
      else (s.previousEpochParticipation altair).data) = participation
  generalize getActiveValidatorIndices s epoch = active at hnodup hinside ⊢
  exact unslashed_participating_same flag hflag hnodup hinside

/-! ## Balances -/

theorem sumMarked_eq {s : BeaconState preset fork} {indices : List UInt64}
    (hnodup : indices.Nodup)
    (hinside : ∀ index ∈ indices, index.toNat < s.validators.data.size) :
    sumMarked s.validators.data (markIndices s.validators.data.size indices) =
      (indices.map fun index =>
        ((s.validators.data[index.toNat]?).map (·.effectiveBalance.toNat)).getD 0).sum := by
  rw [sumMarked_eq_sum]
  have hnodup' : (indices.map UInt64.toNat).Nodup :=
    hnodup.map fun _ _ => UInt64.toNat_inj.mp
  rw [← List.sum_toFinset _ List.nodup_range]
  have hmap := List.map_map (l := indices) (f := UInt64.toNat) (g := fun j =>
    ((s.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0)
  simp only [Function.comp_def] at hmap
  rw [← hmap, ← List.sum_toFinset _ hnodup', ← Finset.sum_filter]
  refine Finset.sum_congr (Finset.ext fun j => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range, List.mem_map,
    getElem?_markIndices]
  constructor
  · rintro ⟨hj, hmark⟩
    simpa [hj] using hmark
  · rintro ⟨index, hmem, rfl⟩
    have hlt := hinside index hmem
    exact ⟨hlt, by simpa [hlt] using ⟨index, hmem, rfl⟩⟩

theorem get_total_balance_same {s : BeaconState preset fork} {indices : List UInt64}
    {specIndices : List Nat} (h : SameIndices s indices specIndices) :
    SameOutcome SameNumber (getTotalBalance s indices)
      (Spec.get_total_balance (toSpecPreset preset config) (toSpecState s) specIndices) := by
  obtain ⟨rfl, hnodup, hinside⟩ := h
  have hfind : indices.find? (s.validators.data.size ≤ ·.toNat) = none :=
    List.find?_eq_none.mpr fun index hmem => by simpa using hinside index hmem
  have hbalances : ((indices.map UInt64.toNat).mapM fun index => do
      Pure.pure (← Spec.listGet (toSpecState s).validators index).effective_balance) =
      (.ok ((indices.map UInt64.toNat).map fun index =>
        ((s.validators.data[index]?).map (·.effectiveBalance.toNat)).getD 0) :
        Spec.SpecM (List Nat)) := by
    refine mapM_ok fun index hmem => ?_
    obtain ⟨index, hmem', rfl⟩ := List.mem_map.mp hmem
    have hlt := hinside index hmem'
    rw [listGet_validators hlt]
    simp [toSpecValidator, hlt, bind, Except.bind, Pure.pure, Except.pure]
  unfold getTotalBalance Spec.get_total_balance
  rw [hbalances, List.map_map]
  unfold Spec.uint64Sum Spec.UINT64_SIZE
  simp only [hfind, Function.comp_def, bind_ok, sumMarked_eq hnodup hinside]
  generalize (indices.map fun index =>
    ((s.validators.data[index.toNat]?).map (·.effectiveBalance.toNat)).getD 0).sum = total
  by_cases htotal : total < 2 ^ 64
  · rw [ite_eq_right (Nat.not_le.mpr htotal), ite_eq_left htotal]
    refine .returned ?_
    have hnat : total.toUInt64.toNat = total := UInt64.toNat_ofNat_of_lt' htotal
    show max preset.EFFECTIVE_BALANCE_INCREMENT.toNat total = _
    rw [UInt64.max_def]
    split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le, hnat] at h <;> omega
  · rw [ite_eq_left (Nat.not_lt.mp htotal), ite_eq_right htotal]
    exact .failed

theorem get_total_active_balance_same (hslots : preset.SLOTS_PER_EPOCH ≠ 0)
    {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    SameOutcome SameNumber (getTotalActiveBalance s)
      (Spec.get_total_active_balance (toSpecPreset preset config) (toSpecState s)) := by
  unfold getTotalActiveBalance Spec.get_total_active_balance
  rw [get_current_epoch_eq hslots, getActiveValidatorIndicesChecked_of_within hregistry]
  exact get_total_balance_same (get_active_validator_indices_same hregistry _)

end EpochProofs.EthLib
