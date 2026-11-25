import EthLib.Consensus.Mutators
import EpochProofs.EthLib.Accessors
import EpochProofs.Spec.RewardsAndPenalties

/-!
# Balance changes: the reference and EthLib agree

EthLib changes the balances inside a state. The reference changes the list of balances.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64
open _root_.EthLib.Consensus

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

theorem listGet_readList {data : Array UInt64} {i : Nat} (h : i < data.size) :
    Spec.listGet (readList UInt64.toNat data) i = .ok data[i].toNat := by
  simp [Spec.listGet, readList, h, pure, Except.pure]

theorem listSet_readList {data : Array UInt64} {i : Nat} (h : i < data.size) (value : UInt64) :
    Spec.listSet (readList UInt64.toNat data) i value.toNat =
      .ok (readList UInt64.toNat (data.set i value h)) := by
  simp [Spec.listSet, readList, h, pure, Except.pure, List.map_set]

theorem listGet_readList_error {data : Array UInt64} {i : Nat} (h : ¬i < data.size) :
    Spec.listGet (readList UInt64.toNat data) i = .error .indexOutOfRange := by
  simp [Spec.listGet, readList, h, throw, throwThe, MonadExceptOf.throw]

/-- The EthLib state has the balances of the reference list. No other field differs from `s`. -/
def OnlyBalancesChanged (s : BeaconState preset fork) (st : BeaconState preset fork)
    (balances : List Nat) : Prop :=
  ∃ l : Balances preset fork, st = { s with balances := l } ∧
    l.data.size = s.balances.data.size ∧ balances = readList UInt64.toNat l.data

theorem OnlyBalancesChanged.refl (s : BeaconState preset fork) :
    OnlyBalancesChanged s s (toSpecState s).balances := ⟨s.balances, rfl, rfl, rfl⟩

theorem OnlyBalancesChanged.toSpecState_eq {s st : BeaconState preset fork} {balances : List Nat}
    (h : OnlyBalancesChanged s st balances) :
    { toSpecState s with balances := balances } = toSpecState st := by
  obtain ⟨l, rfl, -, rfl⟩ := h
  rfl

theorem ofNatChecked_ok {n : Nat} (h : n < 2 ^ 64) :
    ∃ i : UInt64, ofNatChecked n = .ok i ∧ i.toNat = n := by
  refine ⟨UInt64.ofNatLT n h, ?_, UInt64.toNat_ofNatLT⟩
  rw [ofNatChecked, dite_eq_left h]

theorem registry_lt {s : BeaconState preset fork} (hregistry : s.RegistryWithinLimit) :
    s.validators.data.size < 2 ^ 64 :=
  Nat.lt_of_le_of_lt hregistry preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt

/-- A change of one balance: EthLib changes the state, and the reference changes the list. -/
theorem change_balance_same {s st : BeaconState preset fork} {balances : List Nat}
    (h : OnlyBalancesChanged s st balances) (index : UInt64)
    {change : UInt64 → Except ArithError UInt64} {specChange : Nat → Spec.SpecM Nat}
    (hchange : ∀ b, SameOutcome SameNumber (change b) (specChange b.toNat)) :
    SameOutcome (OnlyBalancesChanged s)
      (do
        let balance ← getBalance st index
        let balance ← liftArith (change balance)
        st.setBalance index balance)
      (do
        let balance ← Spec.listGet balances index.toNat
        let balance ← specChange balance
        Spec.listSet balances index.toNat balance) := by
  obtain ⟨l, rfl, hsize, rfl⟩ := h
  by_cases hlt : index.toNat < l.data.size
  · have hget : getBalance { s with balances := l } index = .ok l.data[index.toNat] := by
      simp [getBalance, hlt]
    have hspec : Spec.listGet (readList UInt64.toNat l.data) index.toNat =
        .ok l.data[index.toNat].toNat := by
      simp [Spec.listGet, readList, hlt, pure, Except.pure]
    rw [hget, hspec, bind_ok, bind_ok]
    refine .bind (hchange _).liftArith ?_
    rintro balance _ rfl -
    rw [BeaconState.setBalance, dite_eq_left hlt, Spec.listSet,
      ite_eq_left (by simpa [readList] using hlt)]
    refine .returned ⟨_, rfl, ?_, ?_⟩
    · simpa using hsize
    · simp [readList, List.map_set]
  · have hget : getBalance { s with balances := l } index = .error (.indexOutOfRange index) := by
      simp [getBalance, hlt]
    have hspec : Spec.listGet (readList UInt64.toNat l.data) index.toNat =
        .error .indexOutOfRange := by
      simp [Spec.listGet, readList, hlt, throw, throwThe, MonadExceptOf.throw]
    rw [hget, hspec]
    exact .failed

theorem saturatingSub_eq (a b : UInt64) :
    (saturatingSub a b).toNat = Spec.saturating_sub a.toNat b.toNat := by
  unfold saturatingSub Spec.saturating_sub
  by_cases h : b < a
  · have h' : a.toNat > b.toNat := UInt64.lt_iff_toNat_lt.mp h
    rw [ite_eq_left h, ite_eq_left h', UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
  · have h' : ¬a.toNat > b.toNat := fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')
    rw [ite_eq_right h, ite_eq_right h', Nat.sub_self]
    rfl

theorem increase_balance_same {s st : BeaconState preset fork} {balances : List Nat}
    (h : OnlyBalancesChanged s st balances) (index delta : UInt64) :
    SameOutcome (OnlyBalancesChanged s) (increaseBalance st index delta)
      (Spec.increase_balance balances index.toNat delta.toNat) :=
  change_balance_same h index fun b => addChecked_same b delta

theorem decrease_balance_same {s st : BeaconState preset fork} {balances : List Nat}
    (h : OnlyBalancesChanged s st balances) (index delta : UInt64) :
    SameOutcome (OnlyBalancesChanged s) (decreaseBalance st index delta)
      (Spec.decrease_balance balances index.toNat delta.toNat) :=
  change_balance_same h index (change := fun b => .ok (saturatingSub b delta))
    (specChange := fun b => .ok (Spec.saturating_sub b delta.toNat)) fun b =>
    .returned (saturatingSub_eq b delta).symm

end EpochProofs.EthLib
