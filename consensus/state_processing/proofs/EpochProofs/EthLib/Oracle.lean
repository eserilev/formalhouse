import EthLib.Consensus.Proofs.Containers.Misc
import EthLib.Consensus.Proofs.Containers.Signing
import EthLib.Consensus.SyncCommittee
import EthLib.Consensus.Transition.BuilderRequests
import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EpochProofs.EthLib.Accessors
import EpochProofs.Spec.Block.SyncAggregate
import EpochProofs.Spec.Epoch

/-!
# The reference oracle and the EthLib functions

The reference takes SHA-256, `hash_tree_root` and BLS as the fields of an `Oracle`. EthLib computes
them. `OracleMatches` says that each field that an epoch reads is the EthLib function.
`exists_oracle` proves that such an oracle exists.

The check of one signature is the parameter `SignatureChecks` of EthLib.
-/

namespace EpochProofs.EthLib

open _root_.EthLib.Base _root_.EthLib.Base.Uint64 _root_.EthLib.Cryptography.Bls
open _root_.EthLib.Consensus _root_.EthLib.Serialization.Ssz
open _root_.EthLib.Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {fork : _root_.EthLib.Base.Fork}

/-- Each oracle field that an epoch reads is the EthLib function. -/
structure OracleMatches (preset : Preset) (checks : SignatureChecks) (o : Spec.Oracle) : Prop where
  hash : ∀ bytes : List UInt8,
    o.hash bytes = _root_.EthLib.Cryptography.Hash.Sha256.hash32 ⟨bytes.toArray⟩
  blockRoots : ∀ roots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat,
    hashTreeRoot roots = .ok (o.hash_tree_root_BlockRoots roots.elements.toList)
  stateRoots : ∀ roots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat,
    hashTreeRoot roots = .ok (o.hash_tree_root_StateRoots roots.elements.toList)
  forkData : ∀ version root,
    hashTreeRoot (ForkData.mk version root) =
      .ok (o.hash_tree_root_ForkData
        { current_version := version, genesis_validators_root := root })
  signingData : ∀ root domain,
    hashTreeRoot (SigningData.mk root domain) =
      .ok (o.hash_tree_root_SigningData { object_root := root, domain := domain })
  depositMessage : ∀ pubkey credentials (amount : UInt64),
    hashTreeRoot (DepositMessage.mk pubkey credentials amount) =
      .ok (o.hash_tree_root_DepositMessage
        { pubkey := pubkey, withdrawal_credentials := credentials, amount := amount.toNat })
  verify : ∀ pubkey message signature,
    o.bls_Verify pubkey message signature = checks.verify pubkey (packBytes message) signature
  keyValidate : ∀ pubkey, o.bls_KeyValidate pubkey = true ↔ G1.keyValidate pubkey = .ok ()
  aggregate : ∀ (pubkeys : List BLSPubkey) key,
    Signatures.ethAggregatePubkeys pubkeys.toArray = .ok key → o.bls_AggregatePKs pubkeys = key

/-- The value of a result, or `absent` if it is an error. -/
def valueOr {ε α : Type} (absent : α) : Except ε α → α
  | .ok a => a
  | .error _ => absent

theorem eq_ok_valueOr {ε α : Type} {absent : α} {x : Except ε α} (h : ∃ a, x = .ok a) :
    x = .ok (valueOr absent x) := by
  obtain ⟨a, rfl⟩ := h
  rfl

/-- The roots of a list of the length that the preset gives. -/
def rootOfRoots (length : Nat) (roots : List Root) : Root :=
  if h : roots.toArray.size = length then
    valueOr Spec.Bytes32.zero (hashTreeRoot (RootedVector.ofVector (length := length) ⟨_, h⟩))
  else Spec.Bytes32.zero

/-- An oracle that matches EthLib exists. -/
theorem exists_oracle (checks : SignatureChecks) (hroots : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0) :
    ∃ o, OracleMatches preset checks o := by
  have : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat :=
    ⟨fun h => hroots (UInt64.toNat_inj.mp h)⟩
  have hrootOfRoots (roots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
      hashTreeRoot roots =
        .ok (rootOfRoots preset.SLOTS_PER_HISTORICAL_ROOT.toNat roots.elements.toList) := by
    have hsize : roots.elements.toList.toArray.size = preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
      simp
    have heq : RootedVector.ofVector ⟨roots.elements.toList.toArray, hsize⟩ = roots :=
      RootedVector.ext rfl
    rw [rootOfRoots, dite_eq_left hsize, heq]
    exact eq_ok_valueOr (hashTreeRoot_total roots)
  let zero := Spec.Bytes32.zero
  refine ⟨{
    hash := fun bytes => _root_.EthLib.Cryptography.Hash.Sha256.hash32 ⟨bytes.toArray⟩
    hash_tree_root_BeaconState := fun _ => zero
    hash_tree_root_BeaconBlockHeader := fun _ => zero
    hash_tree_root_BeaconBlock := fun _ => zero
    hash_tree_root_BeaconBlockBody := fun _ => zero
    hash_tree_root_BlockRoots := rootOfRoots preset.SLOTS_PER_HISTORICAL_ROOT.toNat
    hash_tree_root_StateRoots := rootOfRoots preset.SLOTS_PER_HISTORICAL_ROOT.toNat
    hash_tree_root_Epoch := fun _ => zero
    hash_tree_root_SigningData := fun data =>
      valueOr zero (hashTreeRoot (SigningData.mk data.object_root data.domain))
    hash_tree_root_ForkData := fun data =>
      valueOr zero (hashTreeRoot (ForkData.mk data.current_version data.genesis_validators_root))
    hash_tree_root_AttestationData := fun _ => zero
    hash_tree_root_VoluntaryExit := fun _ => zero
    hash_tree_root_DepositMessage := fun message => valueOr zero (hashTreeRoot (DepositMessage.mk
      message.pubkey message.withdrawal_credentials (UInt64.ofNat message.amount)))
    hash_tree_root_BLSToExecutionChange := fun _ => zero
    hash_tree_root_ExecutionPayloadBid := fun _ => zero
    hash_tree_root_ExecutionPayloadEnvelope := fun _ => zero
    hash_tree_root_PayloadAttestationData := fun _ => zero
    hash_tree_root_ExecutionRequests := fun _ => zero
    hash_tree_root_Withdrawals := fun _ => zero
    bls_Verify := fun pubkey message signature =>
      checks.verify pubkey (packBytes message) signature
    bls_FastAggregateVerify := fun _ _ _ => false
    bls_AggregateVerify := fun _ _ _ => false
    bls_AggregatePKs := fun pubkeys =>
      valueOr Spec.BLSPubkey.zero (Signatures.ethAggregatePubkeys pubkeys.toArray)
    bls_KeyValidate := fun pubkey => match G1.keyValidate pubkey with
      | .ok _ => true
      | .error _ => false
    bls_SubtractPK := fun a _ => a }, ?_⟩
  exact {
    hash := fun _ => rfl
    blockRoots := hrootOfRoots
    stateRoots := hrootOfRoots
    forkData := fun _ _ => eq_ok_valueOr (hashTreeRoot_total _)
    signingData := fun _ _ => eq_ok_valueOr (hashTreeRoot_total _)
    depositMessage := fun pubkey credentials amount => by
      simp only [UInt64.ofNat_toNat]
      exact eq_ok_valueOr (hashTreeRoot_total _)
    verify := fun _ _ _ => rfl
    keyValidate := fun pubkey => by
      simp only
      cases G1.keyValidate pubkey <;> simp
    aggregate := fun _ _ h => by simp only [h, valueOr] }

/-! ## Deposit signatures -/

theorem compute_domain_eq {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) :
    computeDomain config DOMAIN_DEPOSIT =
      .ok (Spec.compute_domain (toSpecPreset preset config) o Spec.DOMAIN_DEPOSIT) := by
  unfold computeDomain computeForkDataRoot
  rw [ho.forkData, bind_ok]
  refine congrArg Except.ok (Vector.ext fun i hi => ?_)
  simp only [Vector.getElem_ofFn, Spec.compute_domain, Spec.compute_fork_data_root,
    Vector.getElem_cast, Vector.getElem_append]
  split
  · rfl
  · rw [Vector.getElem_extract]
    simp only [Nat.zero_add]
    rfl

theorem is_valid_deposit_signature_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (pubkey : BLSPubkey) (credentials : Bytes32)
    (amount : UInt64) (signature : BLSSignature) :
    isValidDepositSignature config checks pubkey credentials amount signature =
      .ok (Spec.is_valid_deposit_signature (toSpecPreset preset config) o pubkey credentials
        amount.toNat signature) := by
  unfold isValidDepositSignature isValidDepositMessageSignature computeSigningRoot
  rw [compute_domain_eq ho]
  simp only [ho.depositMessage, bind_ok, liftSsz, Except.mapError, ho.signingData, ← ho.verify]
  rfl

/-! ## Aggregate public keys -/

theorem addPubkeyPoints_ok_iff :
    ∀ (entries : List (BLSPubkey × Nat)) (start : G1),
      (∃ point, entries.foldlM Signatures.addPubkeyPoint start = .ok point) ↔
        ∀ entry ∈ entries, G1.keyValidate entry.1 = .ok ()
  | [], start => by simp [pure, Except.pure]
  | (pubkey, i) :: entries, start => by
    rw [List.foldlM_cons, Signatures.addPubkeyPoint]
    cases h : G1.keyValidatePoint pubkey with
    | error e =>
      have hinvalid : G1.keyValidate pubkey ≠ .ok () := by
        simp [G1.keyValidate, h, bind, Except.bind]
      simp [hinvalid, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    | ok point =>
      have hvalid : G1.keyValidate pubkey = .ok () := by
        simp [G1.keyValidate, h, bind, Except.bind, pure, Except.pure]
      simp only [pure_eq_ok, bind_ok, addPubkeyPoints_ok_iff entries]
      simp [hvalid]

theorem eth_aggregate_pubkeys_same {checks : SignatureChecks} {o : Spec.Oracle}
    (ho : OracleMatches preset checks o) (pubkeys : List BLSPubkey) :
    SameOutcome (fun a b => b = a) (aggregatePubkeys pubkeys.toArray)
      (Spec.eth_aggregate_pubkeys o pubkeys) := by
  unfold aggregatePubkeys Spec.eth_aggregate_pubkeys
  refine .mapError _ ?_
  have hpoint : Signatures.ethAggregatePubkeys pubkeys.toArray =
      if pubkeys = [] then .error .emptyPubkeyList
      else pubkeys.zipIdx.foldlM Signatures.addPubkeyPoint G1.zero >>= fun point =>
        pure (Signatures.pointToPubkey point) := by
    unfold Signatures.ethAggregatePubkeys Signatures.aggregatePubkeyPoint
    cases pubkeys with
    | nil => rfl
    | cons pubkey pubkeys =>
      simp
  have hvalid : (∃ point, pubkeys.zipIdx.foldlM Signatures.addPubkeyPoint G1.zero = .ok point) ↔
      pubkeys.all o.bls_KeyValidate = true := by
    rw [addPubkeyPoints_ok_iff, List.all_eq_true]
    simp only [ho.keyValidate]
    constructor
    · intro h pubkey hmem
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
      exact h (pubkeys[i], i) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi]))
    · rintro h ⟨pubkey, i⟩ hmem
      exact h pubkey (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hmem))
  by_cases hempty : pubkeys = []
  · subst hempty
    exact .failed
  · have hlength : ¬¬pubkeys.length > 0 := by simpa using hempty
    rw [ite_eq_right hlength]
    cases hkeys : Signatures.ethAggregatePubkeys pubkeys.toArray with
    | ok key =>
      have hkeys' := hkeys
      rw [hpoint, ite_eq_right hempty] at hkeys'
      have hall := hvalid.mp (by
        obtain ⟨point, hpoint, -⟩ := bind_ok_iff.mp hkeys'
        exact ⟨point, hpoint⟩)
      rw [ite_eq_right (by simp [hall])]
      exact .returned (ho.aggregate _ _ hkeys)
    | error e =>
      have hall : ¬pubkeys.all o.bls_KeyValidate = true := fun hall => by
        obtain ⟨point, hp⟩ := hvalid.mpr hall
        rw [hpoint, ite_eq_right hempty, hp] at hkeys
        cases hkeys
      rw [ite_eq_left hall]
      exact .failed

end EpochProofs.EthLib
