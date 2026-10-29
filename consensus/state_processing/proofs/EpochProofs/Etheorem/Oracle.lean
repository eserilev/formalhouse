import EpochProofs.Etheorem.State
import EpochProofs.Spec.Epoch

/-!
# The reference `Oracle` and Etheorem's hash, SSZ and BLS functions

The reference takes SHA-256, `hash_tree_root` and BLS as fields of an `Oracle`. Etheorem
computes them: SHA-256 and `hash_tree_root` through `[HasherTag]`, BLS through
`[CryptoBackend]`.

`OracleAgrees o` says that each field the epoch reads equals the Etheorem function.
`etheoremOracle base` is an `Oracle` that takes these fields from Etheorem and the rest from
`base`. `etheoremOracle_agrees` proves `OracleAgrees` for it, so the hypothesis holds for at
least one oracle.

With `pureHasherTag`, SHA-256 is the pure Lean `Sha256Spec` and adds no axiom. BLS stays a
parameter. The `CryptoBackend.ffi` instance calls blst through the FFI.
-/

forkproof EpochEtheorem

open EthCLLib.Spec

/-- A list of roots as a `Vector` of length `n`. The list has length `n` in a reachable state.
Past the end of the list the vector holds zero roots. -/
def rootsVector (n : Nat) (roots : List Spec.Root) : Vector Spec.Root n :=
  Vector.ofFn fun i => roots.getD i.val Spec.Bytes32.zero

/-- The block roots of a state read back as the Etheorem vector. -/
theorem rootsVector_toList {n : Nat} (v : Vector Spec.Root n) : rootsVector n v.toList = v := by
  apply Vector.ext
  intro i hi
  simp [rootsVector]

variable [EthCLSpecs.Gloas.Preset] [HasherTag] [CryptoBackend]

/-- `sha256(data)` in Etheorem, as a `Bytes32`. -/
def etheoremHash (data : List UInt8) : Spec.Bytes32 :=
  bytesToRoot (sha ⟨data.toArray⟩)

/-- Each `Oracle` field the epoch reads equals the Etheorem function.

`hash` is `get_seed`, the shuffle, proposer and sync committee selection, and `compute_ptc`.
`blockRoots` and `stateRoots` are `process_historical_summaries_update`. `forkData`,
`signingData`, `depositMessage` and `verify` are the deposit signature in
`apply_pending_deposit`. `aggregate` is the sync committee `aggregate_pubkey`. -/
structure OracleAgrees (o : Spec.Oracle) : Prop where
  hash : ∀ data, o.hash data = etheoremHash data
  blockRoots : ∀ roots, o.hash_tree_root_BlockRoots roots =
    htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
  stateRoots : ∀ roots, o.hash_tree_root_StateRoots roots =
    htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
  forkData : ∀ d : Spec.ForkData,
    o.hash_tree_root_ForkData d = computeForkDataRoot d.current_version d.genesis_validators_root
  signingData : ∀ d : Spec.SigningData,
    o.hash_tree_root_SigningData d = htr ({ objectRoot := d.object_root, domain := d.domain } : SigningData)
  depositMessage : ∀ m : Spec.DepositMessage,
    o.hash_tree_root_DepositMessage m =
      htr ({ pubkey := m.pubkey, withdrawalCredentials := m.withdrawal_credentials,
             amount := UInt64.ofNat m.amount } : EthCLSpecs.Gloas.DepositMessage)
  verify : ∀ pubkey root signature, o.bls_Verify pubkey root signature =
    blsVerify pubkey root signature
  aggregate : ∀ pubkeys, o.bls_AggregatePKs pubkeys = blsAggregatePubkeys pubkeys.toArray

/-- The `Oracle` that takes the epoch fields from Etheorem and the other fields from `base`. -/
def etheoremOracle (base : Spec.Oracle) : Spec.Oracle :=
  { base with
    hash := etheoremHash
    hash_tree_root_BlockRoots := fun roots =>
      htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
    hash_tree_root_StateRoots := fun roots =>
      htr (rootsVector EthCLSpecs.Gloas.Const.slotsPerHistoricalRoot roots)
    hash_tree_root_ForkData := fun d =>
      computeForkDataRoot d.current_version d.genesis_validators_root
    hash_tree_root_SigningData := fun d =>
      htr ({ objectRoot := d.object_root, domain := d.domain } : SigningData)
    hash_tree_root_DepositMessage := fun m =>
      htr ({ pubkey := m.pubkey, withdrawalCredentials := m.withdrawal_credentials,
             amount := UInt64.ofNat m.amount } : EthCLSpecs.Gloas.DepositMessage)
    bls_Verify := fun pubkey root signature => blsVerify pubkey root signature
    bls_AggregatePKs := fun pubkeys => blsAggregatePubkeys pubkeys.toArray }

theorem etheoremOracle_agrees (base : Spec.Oracle) : OracleAgrees (etheoremOracle base) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl⟩

end forkproof

