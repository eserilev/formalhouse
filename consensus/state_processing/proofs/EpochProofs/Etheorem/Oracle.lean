import EpochProofs.Assumptions.Etheorem
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


/-- The block roots of a state read back as the Etheorem vector. -/
theorem rootsVector_toList {n : Nat} (v : Vector Spec.Root n) : rootsVector n v.toList = v := by
  apply Vector.ext
  intro i hi
  simp [rootsVector]

variable [EthCLSpecs.Gloas.Preset] [HasherTag] [CryptoBackend]


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

