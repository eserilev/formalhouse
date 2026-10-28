import EpochProofs.FormalhouseRust

/-!
# The hypotheses of the final theorems can hold together

A theorem with hypotheses that cannot hold together proves nothing. The final theorems had this
bug: `committees` stated the committee conditions at every state `s` with `CommFrame t s`.
`CommFrame` fixes only the slot, the list lengths and the RANDAO length, so it admits `t` with
every validator list emptied, where `CommPreconds.syncActive` fails. That hypothesis was false
for every input. It now holds at the one state that the epoch passes to the committee steps
(`Spec.CommAt`, `Spec.CommAtFulu`).

This file gives a witness: `wt`, a minimal-preset state at the last slot of epoch 0 with eight
active compounding validators at `2048 ETH`, and `we`, `wef`, the Etheorem states that map to
it. Lean computes the epoch steps on it.

- `gloasAssumptions_witness`: every field of `GloasAssumptions` holds at `we`, with an oracle
  that agrees with Etheorem, given `SelectionsFull we` (F3) and that SHA-256 returns 32 bytes.
- `fuluAssumptions_witness`: the same for `FuluAssumptions` at `wef`, given also the run bounds
  (`supply`, `econ`) and `FuluEpochConds`.
- `gloas_spec_witness`, `fulu_spec_witness`: at the same state, the start-state facts
  (`FuluStartOk`) and the reachable-state facts that the run hypotheses give (`EpochInputOk''`)
  hold too, the epoch reaches its committee steps (so `committees` is not vacuous), and the spec
  `process_epoch` returns `ok`.
- `selFin_full`: the selection facts in `CommPreconds` hold for every hash when every candidate
  has the maximum effective balance.

Not covered: the run hypotheses (`GloasEpochInput`, `FuluEpochInput`, the supply and economic
bounds over all runs), the facts about Etheorem's output (`SelectionsFull`, `FuluEpochConds`),
the hash backend (`sha`), the cache facts and the Rust glue (`EpochLinks`).
-/

namespace EpochProofs.Spec

/-- Every pass of the balance weighted selection accepts when every candidate has the maximum
effective balance, whatever the hash values. -/
theorem bwsAccept_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (i : Nat) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    bwsAccept p o seed ebs shuffle i = true := by
  have hk : bwsNext p o seed ebs.length shuffle i < ebs.length := by
    unfold bwsNext; split
    · exact csiFold_lt o seed.toList ebs.length p.SHUFFLE_ROUND_COUNT _ hpos (Nat.mod_lt _ hpos)
    · exact Nat.mod_lt _ hpos
  unfold bwsAccept
  rw [List.getD_eq_getElem _ _ hk, hall _ (List.getElem_mem hk)]
  have := leNat_take2_lt ((bwsBytes o seed i).toList.drop (i % 16 * 2))
  simp only [decide_eq_true_eq, ge_iff_le]
  exact Nat.mul_le_mul_left _ (by omega)

theorem bwsCount_full (p : Preset) (o : Oracle) (seed : Bytes32) (ebs : List Gwei)
    (shuffle : Bool) (hpos : 0 < ebs.length)
    (hall : ∀ x ∈ ebs, x = p.MAX_EFFECTIVE_BALANCE_ELECTRA) (m : Nat) :
    bwsCount p o seed ebs shuffle m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bwsCount_succ, ih, bwsAccept_full p o seed ebs shuffle m hpos hall]; rfl

/-- `SelFin` holds for every seed when the candidates are validators with the maximum effective
balance. -/
theorem selFin_full (p : Preset) (o : Oracle) (s : BeaconState) (indices : List ValidatorIndex)
    (seed : Bytes32) (size : Nat) (shuffle : Bool) (hne : indices ≠ [])
    (hin : ∀ j ∈ indices, j < s.validators.length)
    (heb : ∀ v ∈ s.validators, v.effective_balance = p.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (hsize : size < 2 ^ 64) : SelFin p o s indices seed size shuffle := by
  refine ⟨size, hsize, ?_⟩
  rw [bwsCount_full]
  · simpa [ebsOf, List.length_pos_iff] using hne
  · intro x hx
    simp only [ebsOf, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.getElem?_eq_getElem (hin j hj)]
    exact heb _ (List.getElem_mem _)

end EpochProofs.Spec

namespace EpochProofs.Witness

open EpochProofs.Spec


/-- `ev` as a reference validator. -/
def wv (k : Nat) : Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawal_credentials := Bytes32.zero.set 0 2
    effective_balance := 2048000000000, slashed := false
    activation_eligibility_epoch := 0, activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- The witness as a reference state. -/
def wt : BeaconState :=
  { slot := 7
    block_roots := List.replicate 64 Bytes32.zero
    state_roots := List.replicate 64 Bytes32.zero
    validators := (List.range 8).map wv
    balances := List.replicate 8 2048000000000
    randao_mixes := List.replicate 64 Bytes32.zero
    slashings := List.replicate 64 0
    previous_epoch_participation := List.replicate 8 0
    current_epoch_participation := List.replicate 8 0
    justification_bits := List.replicate 4 false
    inactivity_scores := List.replicate 8 0
    current_sync_committee := { pubkeys := List.replicate 32 BLSPubkey.zero }
    next_sync_committee := { pubkeys := List.replicate 32 BLSPubkey.zero }
    proposer_lookahead := List.replicate 16 0
    execution_payload_availability := List.replicate 64 false
    builder_pending_payments := List.replicate 16 BuilderPendingPayment.empty
    builder_pending_withdrawals := []
    ptc_window := List.replicate 24 (List.replicate 16 0) }

/-- `wt` without the Gloas fields: the witness as a Fulu reference state. -/
def wtf : BeaconState :=
  { wt with execution_payload_availability := [], builder_pending_payments := [],
            ptc_window := [] }

section Minimal

attribute [local instance] minimalCfg fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- The steps before the committee steps return `wt` itself: at epoch 0 the justification,
inactivity and rewards steps skip, and nothing else changes on this state. -/
theorem wt_epochToCommittees (o : Oracle) : epochToCommittees P o wt = .ok wt := by rfl

theorem wtf_epochToCommitteesFulu (o : Oracle) : epochToCommitteesFulu P FC o wtf = .ok wtf := by
  rfl

theorem wt_eb : ∀ v ∈ wt.validators, v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide +kernel

theorem wt_active_lt (e j : Nat) (h : j ∈ get_active_validator_indices wt e) :
    j < wt.validators.length := active_lt wt e j h

theorem wt_commConds (o : Oracle) (hk : ∀ v ∈ wt.validators, o.bls_KeyValidate v.pubkey = true) :
    CommConds o wt :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, hk⟩

theorem wt_commPreconds (o : Oracle) : CommPreconds o wt where
  syncActive := by decide +kernel
  proposers := by decide +kernel
  ptc32 := by decide +kernel
  selSync seed := selFin_full P o wt _ seed _ true (by decide +kernel)
    (wt_active_lt _) wt_eb (by decide +kernel)
  selProp seed := selFin_full P o wt _ seed _ true (by decide +kernel)
    (fun j hj => wt_active_lt _ j (List.mem_of_mem_filter hj)) wt_eb (by decide +kernel)
  selPtc slot hslot l hl seed := by
    have he : slot / P.SLOTS_PER_EPOCH = 2 := hslot
    have h32 : P.SLOTS_PER_EPOCH ≤
        (get_active_validator_indices wt (slot / P.SLOTS_PER_EPOCH)).length := by
      rw [he]; decide +kernel
    obtain ⟨l', hl1, hl2, hl3⟩ := ptcIndices_total o wt slot
      (by rw [he]; decide +kernel) (by decide +kernel)
      ((active_len_le _ _).trans (by decide +kernel))
    have hll : l' = l := by rw [hl1] at hl; exact Except.ok.inj hl
    rw [← hll]
    have hne : l' ≠ [] := by
      intro h; rw [h] at hl2
      have := ptc_len_pos _ (slot % P.SLOTS_PER_EPOCH) _ P_slots_pos h32
      simp at hl2; omega
    exact selFin_full P o wt l' seed _ false hne (fun j hj => wt_active_lt _ j (hl3 j hj)) wt_eb
      (by decide +kernel)

/-- The Gloas committee hypothesis holds at `wt`, for every oracle that accepts the eight keys. -/
theorem wt_commAt (o : Oracle) (hk : ∀ v ∈ wt.validators, o.bls_KeyValidate v.pubkey = true) :
    CommAt o wt := by
  intro s hs
  rw [wt_epochToCommittees] at hs
  cases hs
  exact ⟨wt_commConds o hk, wt_commPreconds o⟩

theorem wt_rowsOk : RowsOk wt := by unfold RowsOk; decide +kernel

theorem wt_pubkeys : PubkeysUnique wt := by unfold PubkeysUnique; decide +kernel

theorem wt_vectors : wt.VectorLengths P := by unfold BeaconState.VectorLengths; decide +kernel

theorem wt_fuluVectors : wt.FuluVectorLengths P := by
  unfold BeaconState.FuluVectorLengths; decide +kernel

theorem wt_tailPre : TailPre wt := by unfold TailPre; decide +kernel

theorem wt_rowBounds : RowBounds wt where
  scores := by decide +kernel
  supply := by decide +kernel
  funds := by decide +kernel
  earliest := by decide +kernel
  exit_balance := by decide +kernel
  count := by decide +kernel
  participation tab htab f hf x hx := by
    rw [show get_total_active_balance P wt = .ok 16384000000000 from rfl] at htab
    cases htab
    have h0 : rewardsFlagIncrements P wt (wt.slot / P.SLOTS_PER_EPOCH - 1) 0 = .ok 1 := rfl
    have h1 : rewardsFlagIncrements P wt (wt.slot / P.SLOTS_PER_EPOCH - 1) 1 = .ok 1 := rfl
    have h2 : rewardsFlagIncrements P wt (wt.slot / P.SLOTS_PER_EPOCH - 1) 2 = .ok 1 := rfl
    interval_cases f
    · rw [h0] at hx; cases hx; decide
    · rw [h1] at hx; cases hx; decide
    · rw [h2] at hx; cases hx; decide

theorem wt_startOk : FuluStartOk wt where
  ffg := by unfold FfgInvariant CheckpointOrder epochOf; decide +kernel
  rows := wt_rowsOk
  exitDelay := by unfold ExitDelay ExitDelayV; decide +kernel
  exitEpochs := by unfold ExitEpochsU64; decide +kernel
  afterEB := by unfold AfterEB; decide +kernel
  pubkeys := wt_pubkeys
  consolidations := by unfold ConsolidationsInRange; decide +kernel
  withdrawable := by unfold WithdrawableU64; decide +kernel

theorem wt_epochInputOk : EpochInputOk'' EpochSupply wt := by
  unfold EpochInputOk'' EpochInputOk' EpochInputOk BoundaryOk EpochSupply
  refine ⟨⟨⟨⟨wt_startOk.ffg, wt_rowsOk, ?_⟩, by decide +kernel, ?_, wt_startOk.exitEpochs,
    by decide +kernel, by decide +kernel, by decide +kernel⟩, wt_pubkeys,
    wt_startOk.consolidations⟩, wt_startOk.withdrawable, ?_⟩
  · unfold EntryEB; decide +kernel
  · unfold EBOk EBOkV; decide +kernel
  · unfold WithdrawableValid; decide +kernel

/-- The Gloas witness. At `wt`, for every oracle that accepts the eight keys: the spec-state
fields of `GloasAssumptions`, the start-state facts and the reachable-state facts hold
together, the epoch reaches its committee steps, and the spec `process_epoch` returns `ok`. -/
theorem gloas_spec_witness (o : Oracle)
    (hk : ∀ v ∈ wt.validators, o.bls_KeyValidate v.pubkey = true) :
    FuluStartOk wt ∧ EpochInputOk'' EpochSupply wt ∧ PubkeysUnique wt ∧ wt.VectorLengths P ∧
      TailPre wt ∧ wt.slot + 8192 < 2 ^ 64 ∧ RowBounds wt ∧ CommAt o wt ∧
      epochToCommittees P o wt = .ok wt ∧ ∃ s', process_epoch P o wt = .ok s' := by
  have hc := wt_commAt o hk
  have hokc := committeesOk_of o wt (by decide +kernel) hc wt (wt_epochToCommittees o)
    ⟨rfl, wt_rowsOk, by decide +kernel⟩
  obtain ⟨s', hs', -⟩ := hokc
  refine ⟨wt_startOk, wt_epochInputOk, wt_pubkeys, wt_vectors, wt_tailPre,
    by decide +kernel, wt_rowBounds, hc, wt_epochToCommittees o, s', ?_⟩
  rw [process_epoch_committees, wt_epochToCommittees, tot_bind_ok]
  exact hs'

theorem wtf_eb : ∀ v ∈ wtf.validators, v.effective_balance = P.MAX_EFFECTIVE_BALANCE_ELECTRA :=
  wt_eb

theorem wtf_fuluCommAt (o : Oracle)
    (hk : ∀ v ∈ wtf.validators, o.bls_KeyValidate v.pubkey = true) : CommAtFulu o wtf := by
  intro s hs
  rw [wtf_epochToCommitteesFulu] at hs
  cases hs
  exact ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, hk⟩,
    ⟨by decide +kernel, by decide +kernel,
      fun seed => selFin_full P o wtf _ seed _ true (by decide +kernel)
        (fun j hj => active_lt wtf _ j hj) wtf_eb (by decide +kernel),
      fun seed => selFin_full P o wtf _ seed _ true (by decide +kernel)
        (fun j hj => active_lt wtf _ j hj) wtf_eb (by decide +kernel)⟩⟩

theorem wtf_rowsOk : RowsOk wtf := wt_rowsOk

theorem wtf_rowBounds : RowBounds wtf where
  scores := by decide +kernel
  supply := by decide +kernel
  funds := by decide +kernel
  earliest := by decide +kernel
  exit_balance := by decide +kernel
  count := by decide +kernel
  participation tab htab f hf x hx := wt_rowBounds.participation tab htab f hf x hx

theorem wtf_startOk : FuluStartOk wtf where
  ffg := wt_startOk.ffg
  rows := wt_rowsOk
  exitDelay := wt_startOk.exitDelay
  exitEpochs := wt_startOk.exitEpochs
  afterEB := wt_startOk.afterEB
  pubkeys := wt_pubkeys
  consolidations := wt_startOk.consolidations
  withdrawable := wt_startOk.withdrawable

theorem wtf_epochInputOk : EpochInputOk'' EpochSupply wtf := wt_epochInputOk

theorem wtf_fuluVectors : wtf.FuluVectorLengths P := wt_fuluVectors

/-- The Fulu witness: at `wtf`, for every oracle that accepts the eight keys, the spec-state
fields of `FuluAssumptions`, the start-state facts and the reachable-state facts hold together,
the epoch reaches its committee steps, and the Fulu spec `process_epoch` returns `ok`. -/
theorem fulu_spec_witness (o : Oracle)
    (hk : ∀ v ∈ wtf.validators, o.bls_KeyValidate v.pubkey = true) :
    FuluStartOk wtf ∧ EpochInputOk'' EpochSupply wtf ∧ wtf.FuluVectorLengths P ∧ TailPre wtf ∧
      wtf.slot + 8192 < 2 ^ 64 ∧ RowBounds wtf ∧ CommAtFulu o wtf ∧
      epochToCommitteesFulu P FC o wtf = .ok wtf ∧
      ∃ s', process_epoch_fulu P FC o wtf = .ok s' := by
  have hc := wtf_fuluCommAt o hk
  obtain ⟨s', hs', -⟩ := committeesOkFulu_of o wtf (by decide +kernel) hc wtf
    (wtf_epochToCommitteesFulu o) ⟨rfl, wtf_rowsOk, by decide +kernel⟩
  refine ⟨wtf_startOk, wtf_epochInputOk, wtf_fuluVectors, wt_tailPre, by decide +kernel,
    wtf_rowBounds, hc, wtf_epochToCommitteesFulu o, s', ?_⟩
  rw [process_epoch_fulu_committees, wtf_epochToCommitteesFulu, tot_bind_ok]
  exact hs'

end Minimal

/-! ## The assumption structures

The witnesses above are reference states. Here they are the `absEState` of Etheorem states, so
they give the fields of `GloasAssumptions` and `FuluAssumptions` directly. -/

/-- An `Oracle` that accepts every key. Its other fields are constants. -/
def keyOracle : Oracle where
  hash _ := default
  hash_tree_root_BeaconState _ := default
  hash_tree_root_BeaconBlockHeader _ := default
  hash_tree_root_BeaconBlock _ := default
  hash_tree_root_BeaconBlockBody _ := default
  hash_tree_root_BlockRoots _ := default
  hash_tree_root_StateRoots _ := default
  hash_tree_root_Epoch _ := default
  hash_tree_root_SigningData _ := default
  hash_tree_root_ForkData _ := default
  hash_tree_root_AttestationData _ := default
  hash_tree_root_VoluntaryExit _ := default
  hash_tree_root_DepositMessage _ := default
  hash_tree_root_BLSToExecutionChange _ := default
  hash_tree_root_ExecutionPayloadBid _ := default
  hash_tree_root_ExecutionPayloadEnvelope _ := default
  hash_tree_root_PayloadAttestationData _ := default
  hash_tree_root_ExecutionRequests _ := default
  hash_tree_root_Withdrawals _ := default
  bls_Verify _ _ _ := false
  bls_FastAggregateVerify _ _ _ := false
  bls_AggregateVerify _ _ _ := false
  bls_AggregatePKs _ := default
  bls_KeyValidate _ := true
  bls_SubtractPK _ _ := default

section GloasEState

attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩


/-- A validator of the witness: active from epoch 0, never exits, compounding credentials, the
maximum effective balance. -/
def ev (k : Nat) : EthCLSpecs.Gloas.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The witness as an Etheorem state on the minimal preset: the last slot of epoch 0, eight
validators, every other field at its default. -/
def we : EthCLSpecs.Gloas.BeaconState :=
  { (default : EthCLSpecs.Gloas.BeaconState) with
    slot := 7
    validators := ⟨#[ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, ev 6, ev 7], by decide⟩
    balances := ⟨Array.replicate 8 2048000000000, by decide⟩
    previousEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    currentEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    inactivityScores := ⟨Array.replicate 8 0, by decide⟩ }


theorem we_abs : Etheorem.absEState we = wt := by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

/-- The oracle hypotheses hold for an oracle that accepts every key (`etheoremOracle_agrees`). -/
theorem oracle_witness : ∃ o, Etheorem.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.etheoremOracle keyOracle, Etheorem.etheoremOracle_agrees _, fun _ => rfl⟩

/-- Every field of `GloasAssumptions` holds at `we` on the minimal preset, given the two facts
about the hash backend that the structure takes as they are: Etheorem's selections return all
their items (`SelectionsFull`, F3) and SHA-256 returns 32 bytes. -/
theorem gloasAssumptions_witness (hsel : Etheorem.SelectionsFull we)
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, Formalhouse.GloasAssumptions o { state := wt } we := by
  obtain ⟨o, ho, hk⟩ := oracle_witness
  exact ⟨o, {
    start := wt_startOk
    pubkeys := we_abs ▸ wt_pubkeys
    vectors := we_abs ▸ wt_vectors
    boundary := we_abs ▸ wt_tailPre
    slot := by rw [we_abs]; decide +kernel
    rows := we_abs ▸ wt_rowBounds
    committees := we_abs ▸ wt_commAt o (fun v _ => hk _)
    selections := hsel
    etheoremRoom := ⟨by rw [we_abs]; decide +kernel, by decide +kernel⟩
    oracle := ho
    sha := hsha }⟩

end GloasEState

section FuluEState

attribute [local instance] EthCLSpecs.Fulu.minimal EthCLSpecs.Fulu.minimalConfig minimalCfg
  fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- `ev` as a Fulu validator. -/
def evf (k : Nat) : EthCLSpecs.Fulu.Validator :=
  { pubkey := Vector.replicate 48 (UInt8.ofNat k)
    withdrawalCredentials := Bytes32.zero.set 0 2
    effectiveBalance := 2048000000000, slashed := false
    activationEligibilityEpoch := 0, activationEpoch := 0
    exitEpoch := UInt64.ofNat FAR_FUTURE_EPOCH, withdrawableEpoch := UInt64.ofNat FAR_FUTURE_EPOCH }

/-- The Fulu witness as an Etheorem Fulu state. -/
def wef : EthCLSpecs.Fulu.BeaconState :=
  { (default : EthCLSpecs.Fulu.BeaconState) with
    slot := 7
    validators := ⟨#[evf 0, evf 1, evf 2, evf 3, evf 4, evf 5, evf 6, evf 7], by decide⟩
    balances := ⟨Array.replicate 8 2048000000000, by decide⟩
    previousEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    currentEpochParticipation := ⟨Array.replicate 8 0, by decide⟩
    inactivityScores := ⟨Array.replicate 8 0, by decide⟩ }

theorem wef_abs : Etheorem.Fulu.absEState wef = wtf := by decide +kernel

variable [EthCLLib.Spec.HasherTag] [EthCLLib.Spec.CryptoBackend]

theorem fulu_oracle_witness :
    ∃ o, Etheorem.Fulu.OracleAgrees o ∧ ∀ pk, o.bls_KeyValidate pk = true :=
  ⟨Etheorem.Fulu.etheoremOracle keyOracle, Etheorem.Fulu.etheoremOracle_agrees _, fun _ => rfl⟩

/-- Every field of `FuluAssumptions` that is about the epoch input holds at `wef` on the minimal
preset, with an oracle that agrees with Etheorem. Taken as they are: the supply and economic
bounds over every run from the start state (`supply`, `econ`), the facts about Etheorem's Fulu
output (`FuluEpochConds`) and SHA-256 returning 32 bytes. -/
theorem fuluAssumptions_witness (fo : FuluOracle) (c : FuluBlockConfig)
    (hsha : ∀ b : ByteArray, (EthCLLib.Spec.sha b).size = 32) :
    ∃ o, (SupplyBoundFulu o fo c { state := wtf } →
      EpochEconFulu o fo c { state := wtf } EpochSupply →
      Etheorem.Fulu.FuluEpochConds P o wef →
      Formalhouse.FuluAssumptions o fo c { state := wtf } wef) := by
  obtain ⟨o, ho, hk⟩ := fulu_oracle_witness
  exact ⟨o, fun hsup hecon hconds => {
    start := wtf_startOk
    supply := hsup
    econ := hecon
    boundary := wef_abs ▸ wt_tailPre
    slot := by rw [wef_abs]; decide +kernel
    vectors := wef_abs ▸ wtf_fuluVectors
    rows := wef_abs ▸ wtf_rowBounds
    committees := wef_abs ▸ wtf_fuluCommAt o (fun v _ => hk _)
    etheorem := hconds
    oracle := ho
    sha := hsha }⟩

end FuluEState

end EpochProofs.Witness
