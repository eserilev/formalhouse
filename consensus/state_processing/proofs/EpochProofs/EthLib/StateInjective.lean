import EpochProofs.EthLib.State

/-!
# The state maps lose no field

Two different EthLib states never map to the same reference state, on Gloas
(`toSpecState_injective`) and on Fulu (`toSpecFuluState_injective`).
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Serialization.Ssz
open _root_.EthLib.Consensus
open Function (Injective)

theorem toNat_injective : Injective UInt64.toNat := fun _ _ => UInt64.toNat_inj.mp

/-- Equal reads come from equal fields. A field that the fork does not have has only one value. -/
theorem fieldOr_injective {present : Prop} [Decidable present] {α β : Type} {absent : β}
    {read : α → β} (hread : Injective read) {f g : present → α}
    (heq : fieldOr absent read f = fieldOr absent read g) : f = g := by
  funext h
  rw [fieldOr_present _ _ _ h, fieldOr_present _ _ _ h] at heq
  exact hread heq

/-- Two values of a field that the fork does not have are equal. -/
theorem absentField_eq {present : Prop} {α : Type} (h : ¬present) (f g : present → α) : f = g :=
  funext fun h' => absurd h' h

theorem readList_injective {α β : Type} {read : α → β} (hread : Injective read) :
    Injective (readList read) := fun _ _ h =>
  Array.toList_inj.mp ((List.map_inj_right fun _ _ => @hread _ _).mp h)

theorem vector_injective {α β : Type} {n : Nat} {read : α → β} (hread : Injective read) :
    Injective (fun v : Vector α n => v.toList.map read) := fun _ _ h =>
  Vector.toList_inj.mp ((List.map_inj_right fun _ _ => @hread _ _).mp h)

theorem vector_toList_injective {α : Type} {n : Nat} :
    Injective (fun v : Vector α n => v.toList) := fun _ _ h => Vector.toList_inj.mp h

theorem rootedVector_injective {α β : Type} [SszType α] {n : Nat} {read : Vector α n → β}
    (hread : Injective read) : Injective (fun v : RootedVector α n => read v.elements) :=
  fun _ _ h => RootedVector.ext (hread h)

theorem sszList_injective {α β : Type} {limit : Nat} {read : Array α → β}
    (hread : Injective read) : Injective (fun l : SszList α limit => read l.data) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  cases hread h
  rfl

theorem progressiveList_injective {α β : Type} {read : Array α → β} (hread : Injective read) :
    Injective (fun l : ProgressiveList α => read l.data) := by
  rintro ⟨_⟩ ⟨_⟩ h
  cases hread h
  rfl

theorem forkList_injective {switch fork : _root_.EthLib.Base.Fork} {α β : Type} {limit : Nat}
    {read : Array α → β} (hread : Injective read) :
    Injective (fun l : ForkList switch fork α limit => read l.data) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  cases hread h
  rfl

theorem bitvector_injective {n : Nat} :
    Injective (fun b : Bitvector n => b.bits.toList) := by
  rintro ⟨_⟩ ⟨_⟩ h
  cases Vector.toList_inj.mp h
  rfl

theorem array_toList_injective {α : Type} : Injective (Array.toList : Array α → List α) :=
  fun _ _ => Array.toList_inj.mp

theorem toSpecValidator_injective : Injective toSpecValidator := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecValidator, UInt64.toNat_inj] using h

theorem toSpecPendingDeposit_injective : Injective toSpecPendingDeposit := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecPendingDeposit, UInt64.toNat_inj] using h

theorem toSpecPendingPartialWithdrawal_injective : Injective toSpecPendingPartialWithdrawal := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecPendingPartialWithdrawal, UInt64.toNat_inj] using h

theorem toSpecPendingConsolidation_injective : Injective toSpecPendingConsolidation := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecPendingConsolidation, UInt64.toNat_inj] using h

theorem toSpecCheckpoint_injective : Injective toSpecCheckpoint := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecCheckpoint, UInt64.toNat_inj] using h

theorem toSpecFork_injective : Injective toSpecFork := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecFork, UInt64.toNat_inj] using h

theorem toSpecBeaconBlockHeader_injective : Injective toSpecBeaconBlockHeader := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecBeaconBlockHeader, UInt64.toNat_inj] using h

theorem toSpecEth1Data_injective : Injective toSpecEth1Data := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecEth1Data, UInt64.toNat_inj] using h

theorem toSpecSyncCommittee_injective {preset : Preset} :
    Injective (toSpecSyncCommittee (preset := preset)) := by
  intro c c' h
  simp only [toSpecSyncCommittee, Spec.SyncCommittee.mk.injEq] at h
  apply Rooted.ext
  rcases hc : c.value with ⟨keys, aggregate⟩
  rcases hc' : c'.value with ⟨keys', aggregate'⟩
  rw [hc, hc'] at h
  cases Vector.toList_inj.mp h.1
  cases h.2
  rfl

theorem toSpecHistoricalSummary_injective : Injective toSpecHistoricalSummary := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecHistoricalSummary] using h

theorem toSpecBuilder_injective : Injective toSpecBuilder := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecBuilder, UInt64.toNat_inj] using h

theorem toSpecWithdrawal_injective : Injective toSpecWithdrawal := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecWithdrawal, UInt64.toNat_inj] using h

theorem toSpecBuilderPendingWithdrawal_injective : Injective toSpecBuilderPendingWithdrawal := by
  rintro ⟨⟩ ⟨⟩ h
  simpa [toSpecBuilderPendingWithdrawal, UInt64.toNat_inj] using h

theorem toSpecBuilderPendingPayment_injective : Injective toSpecBuilderPendingPayment := by
  rintro ⟨_, ⟨⟩, _⟩ ⟨_, ⟨⟩, _⟩ h
  simpa [toSpecBuilderPendingPayment, toSpecBuilderPendingWithdrawal, UInt64.toNat_inj] using h

theorem kzgCommitment_injective :
    Injective (fun c : _root_.EthLib.Cryptography.Kzg.KZGCommitment => c.bytes) := by
  rintro ⟨_⟩ ⟨_⟩ h
  cases h
  rfl

/-- Heze adds a field to the bid that the reference does not have. -/
theorem toSpecExecutionPayloadBid_injective {preset : Preset} {fork : _root_.EthLib.Base.Fork}
    (beforeHeze : fork < .hegota) :
    Injective (toSpecExecutionPayloadBid (preset := preset) (fork := fork)) := by
  rintro ⟨⟩ ⟨⟩ h
  simp only [toSpecExecutionPayloadBid, Spec.ExecutionPayloadBid.mk.injEq, UInt64.toNat_inj] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcommitments, rfl⟩ := h
  cases forkList_injective (readList_injective kzgCommitment_injective) hcommitments
  congr 1
  exact absentField_eq (Nat.not_le_of_lt beforeHeze) _ _

theorem toSpecExecutionPayloadHeader_injective {preset : Preset}
    {fork : _root_.EthLib.Base.Fork} :
    Injective (toSpecExecutionPayloadHeader (preset := preset) (fork := fork)) := by
  rintro ⟨⟩ ⟨⟩ h
  simp only [toSpecExecutionPayloadHeader, Spec.ExecutionPayloadHeader.mk.injEq, UInt64.toNat_inj,
    BitVec.toNat_inj, Vector.toList_inj] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextra, rfl, rfl, rfl, hwithdrawals,
    hused, hexcess⟩ := h
  cases sszList_injective array_toList_injective hextra
  congr 1
  · exact fieldOr_injective (fun _ _ => id) hwithdrawals
  · exact fieldOr_injective toNat_injective hused
  · exact fieldOr_injective toNat_injective hexcess

/-- Between Altair and Gloas, `toSpecState` and the payload header together keep every field. -/
theorem eq_of_toSpecState_eq {preset : Preset} {fork : _root_.EthLib.Base.Fork}
    (altair : .altair ≤ fork) (beforeHeze : fork < .hegota) {s s' : BeaconState preset fork}
    (hheader : s.latestExecutionPayloadHeader = s'.latestExecutionPayloadHeader)
    (h : toSpecState s = toSpecState s') : s = s' := by
  have hblockHash : s.latestBlockHash = s'.latestBlockHash := by
    have h' := congrArg Spec.BeaconState.latest_block_hash h
    simp only [toSpecState, hheader] at h'
    exact fieldOr_injective (fun _ _ => id) h'
  simp only [toSpecState, Spec.BeaconState.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, -, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44, h45, h46⟩ := h
  have nat : Injective UInt64.toNat := toNat_injective
  have list {α : Type} : Injective (Array.toList : Array α → List α) := array_toList_injective
  cases s
  cases s'
  congr 1
  · exact nat h1
  · exact nat h3
  · exact toSpecFork_injective h4
  · exact toSpecBeaconBlockHeader_injective h5
  · exact rootedVector_injective vector_toList_injective h6
  · exact rootedVector_injective vector_toList_injective h7
  · exact sszList_injective list h8
  · exact fieldOr_injective toSpecEth1Data_injective h9
  · exact fieldOr_injective (sszList_injective (readList_injective toSpecEth1Data_injective)) h10
  · exact fieldOr_injective nat h11
  · exact RootedForkList.ext (readList_injective toSpecValidator_injective h12)
  · exact forkList_injective (readList_injective nat) h13
  · exact rootedVector_injective vector_toList_injective h14
  · exact rootedVector_injective (vector_injective nat) h15
  · exact absentField_eq (Nat.not_lt_of_le altair) _ _
  · exact absentField_eq (Nat.not_lt_of_le altair) _ _
  · exact fieldOr_injective (forkList_injective list) h16
  · exact fieldOr_injective (forkList_injective list) h17
  · exact bitvector_injective h18
  · exact toSpecCheckpoint_injective h19
  · exact toSpecCheckpoint_injective h20
  · exact toSpecCheckpoint_injective h21
  · exact fieldOr_injective (forkList_injective (readList_injective nat)) h22
  · exact fieldOr_injective toSpecSyncCommittee_injective h23
  · exact fieldOr_injective toSpecSyncCommittee_injective h24
  · exact fieldOr_injective nat h26
  · exact fieldOr_injective nat h27
  · exact fieldOr_injective
      (sszList_injective (readList_injective toSpecHistoricalSummary_injective)) h28
  · exact fieldOr_injective nat h29
  · exact fieldOr_injective nat h30
  · exact fieldOr_injective nat h31
  · exact fieldOr_injective nat h32
  · exact fieldOr_injective nat h33
  · exact fieldOr_injective nat h34
  · exact fieldOr_injective
      (forkList_injective (readList_injective toSpecPendingDeposit_injective)) h35
  · exact fieldOr_injective
      (forkList_injective (readList_injective toSpecPendingPartialWithdrawal_injective)) h36
  · exact fieldOr_injective
      (forkList_injective (readList_injective toSpecPendingConsolidation_injective)) h37
  · exact fieldOr_injective (vector_injective nat) h38
  · exact fieldOr_injective
      (progressiveList_injective (readList_injective toSpecBuilder_injective)) h39
  · exact fieldOr_injective nat h40
  · exact fieldOr_injective bitvector_injective h41
  · exact fieldOr_injective
      (rootedVector_injective (vector_injective toSpecBuilderPendingPayment_injective)) h42
  · exact fieldOr_injective
      (progressiveList_injective (readList_injective toSpecBuilderPendingWithdrawal_injective)) h43
  · exact fieldOr_injective (toSpecExecutionPayloadBid_injective beforeHeze) h44
  · exact fieldOr_injective
      (forkList_injective (readList_injective toSpecWithdrawal_injective)) h45
  · exact fieldOr_injective (rootedVector_injective (vector_injective (vector_injective nat))) h46

/-- Two different Gloas states of EthLib never map to the same reference state. -/
theorem toSpecState_injective {preset : Preset} :
    Injective (toSpecState (preset := preset) (fork := .glamsterdam)) := fun _ _ h =>
  eq_of_toSpecState_eq (by decide) (by decide) (absentField_eq (by decide) _ _) h

/-- Two different Fulu states of EthLib never map to the same Fulu reference state. -/
theorem toSpecFuluState_injective {preset : Preset} :
    Injective (toSpecFuluState (preset := preset)) := by
  intro s s' h
  simp only [toSpecFuluState, Spec.FuluState.mk.injEq] at h
  exact eq_of_toSpecState_eq (by decide) (by decide)
    (funext fun _ => toSpecExecutionPayloadHeader_injective h.2) h.1

end EpochProofs.EthLib
