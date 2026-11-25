import EthLib.Consensus.Proofs.Containers.State
import EthLib.Consensus.Proofs.Transition.Totality.Slot
import EpochProofs.AssumptionsHoldForExample
import EpochProofs.EthLib.ResultsFromEthLibRun

/-!
# The assumptions about an EthLib run hold together for an example

The run starts one slot before the end of epoch 0, at `exampleEthLibState`, and takes one slot. This
file proves that the assumptions of the theorems for an EthLib run hold at its epoch input, on the
minimal preset, for Gloas and for Fulu.

Not covered: a run with a block, a run from genesis, the caches and the untranslated Rust.
-/

namespace EpochProofs.Example

open EpochProofs.EthLib EpochProofs.Formalhouse EpochProofs.Formalhouse.FromEthLibRun
open EpochProofs.Spec hiding Fork Preset Validator
open _root_.EthLib.Base (Fork)
open _root_.EthLib.Consensus (Config Preset SignatureChecks processEpoch processSlot Run Step
  ForkedBeaconState Validator advanceSlotAcross)

attribute [local instance] minimalCfg fuluMinimalCfg
local instance : @PresetCfg.Ok minimalCfg := minimalCfg_ok
local instance : @PresetCfg.Bounds minimalCfg := minimalCfg_bounds
local instance : FuluCfg.Ok := ⟨fuluCompat_minimal⟩

/-- The start of the run: the example state, one slot earlier. -/
def exampleStart (fork : Fork) : _root_.EthLib.Consensus.BeaconState Preset.minimal fork :=
  { exampleEthLibState fork with slot := 6 }

theorem exampleStart_validators {fork : Fork} {P : Validator → Prop}
    (each : ∀ k < 8, P (exampleEthLibValidator k)) :
    ∀ validator ∈ (exampleStart fork).validators.data, P validator := by
  intro validator member
  change validator ∈ #[exampleEthLibValidator 0, exampleEthLibValidator 1,
    exampleEthLibValidator 2, exampleEthLibValidator 3, exampleEthLibValidator 4,
    exampleEthLibValidator 5, exampleEthLibValidator 6, exampleEthLibValidator 7] at member
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact each _ (by decide)

/-- The start has the facts of a chain state. -/
theorem exampleStart_facts {config : Config} {fork : Fork} (fulu : .fusaka ≤ fork) :
    ChainFacts config (exampleStart fork) where
  invariant :=
    { balancesMatch := by rfl
      exitsOrdered := exampleStart_validators fun _ _ => by exact UInt64.le_refl _
      ordered := ⟨UInt64.le_refl _, UInt64.le_refl _⟩
      settled := UInt64.zero_le
      aligned := fun _ => exampleStart_validators fun _ _ => by
        change (2048000000000 : UInt64) %
          _root_.EthLib.Consensus.Preset.minimal.EFFECTIVE_BALANCE_INCREMENT = 0
        decide }
  shaped :=
    { balancesMatch := by rfl
      participationMatches := fun _ => ⟨rfl, rfl⟩
      inactivityScoresMatch := fun _ => rfl
      capped := exampleStart_validators fun k _ => by
        have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) fulu
        simp only [_root_.EthLib.Consensus.withdrawalMaxEffectiveBalance, electra, ↓reduceIte]
        change (2048000000000 : UInt64) ≤
          if _root_.EthLib.Consensus.hasCompoundingWithdrawalCredential (exampleEthLibValidator k)
          then _root_.EthLib.Consensus.Preset.minimal.MAX_EFFECTIVE_BALANCE_ELECTRA
          else _root_.EthLib.Consensus.Preset.minimal.MIN_ACTIVATION_BALANCE
        rw [ite_eq_left (by rfl)]
        decide
      inside := fun _ consolidation member => by
        change consolidation ∈ #[] at member
        simp at member }
  keys := by
    change ((List.range 8).map examplePubkey).Nodup
    exact examplePubkeys_unique
  exitDelay := exampleStart_validators fun _ _ exits => absurd rfl exits

/-- The start is a start state. -/
theorem exampleStart_chainStart {config : Config} {fork : Fork} (fulu : .fusaka ≤ fork) :
    ChainStart config ⟨fork, exampleStart fork⟩ where
  facts := exampleStart_facts fulu
  balanceFloor _ i validator balance found read := by
    have effective : validator.effectiveBalance = 2048000000000 :=
      exampleStart_validators (P := (·.effectiveBalance = 2048000000000)) (fun _ _ => rfl) validator
        (Array.mem_of_getElem? found)
    have value : balance = 2048000000000 := by
      have member := Array.mem_of_getElem? read
      change balance ∈ Array.replicate 8 (2048000000000 : UInt64) at member
      exact (Array.mem_replicate.mp member).2
    rw [effective, value]
    decide

/-- A state like the example state. Only the roots, the latest block header and the payload
availability can differ. -/
def LikeExample {fork : Fork} (input : _root_.EthLib.Consensus.BeaconState Preset.minimal fork) :
    Prop :=
  ∃ stateRoots blockRoots header availability, input = { exampleEthLibState fork with
    stateRoots := stateRoots
    blockRoots := blockRoots
    latestBlockHeader := header
    executionPayloadAvailability := availability }

/-- `processSlot` succeeds at slot 6 and at slot 7. -/
theorem exampleSlots (fork : Fork) :
    ∃ cached input : _root_.EthLib.Consensus.BeaconState Preset.minimal fork,
      processSlot (exampleStart fork) = .ok cached ∧
      processSlot { cached with slot := 7 } = .ok input ∧ LikeExample input := by
  obtain ⟨cached, cachedOk⟩ := _root_.EthLib.Consensus.processSlot_total
    (state := exampleStart fork) (by change 6 + 1 < 2 ^ 64; decide)
  obtain ⟨input, inputOk⟩ := _root_.EthLib.Consensus.processSlot_total
    (state := ({ cached with slot := 7 } :
      _root_.EthLib.Consensus.BeaconState Preset.minimal fork)) (by change 7 + 1 < 2 ^ 64; decide)
  refine ⟨cached, input, cachedOk, inputOk, ?_⟩
  obtain ⟨_, _, _, _, rfl⟩ := _root_.EthLib.Consensus.processSlot_ok cachedOk
  obtain ⟨_, _, _, _, rfl⟩ := _root_.EthLib.Consensus.processSlot_ok inputOk
  exact ⟨_, _, _, _, rfl⟩

/-- The epoch input of the example run. -/
noncomputable def exampleInput (fork : Fork) :
    _root_.EthLib.Consensus.BeaconState Preset.minimal fork :=
  (exampleSlots fork).choose_spec.choose

theorem exampleInput_like (fork : Fork) : LikeExample (exampleInput fork) :=
  (exampleSlots fork).choose_spec.choose_spec.2.2

/-- The example run reaches the epoch input. -/
theorem exampleRun {config : Config} {checks : SignatureChecks} {fork : Fork}
    (fulu : .fusaka ≤ fork) (noUpgrade : ∀ next ∈ config.nextFork fork, 1 ≤ next.2.toNat) :
    Nonempty (RunToEpochInput config checks ⟨fork, exampleStart fork⟩ (exampleInput fork)) := by
  obtain ⟨cached, cachedOk, inputOk⟩ :
      ∃ cached : _root_.EthLib.Consensus.BeaconState Preset.minimal fork,
        processSlot (exampleStart fork) = .ok cached ∧
        processSlot { cached with slot := 7 } = .ok (exampleInput fork) :=
    have both := (exampleSlots fork).choose_spec.choose_spec
    ⟨_, both.1, both.2.1⟩
  -- The slot step from slot 6 to slot 7.
  have advanced : _root_.EthLib.Consensus.advanceSlot config checks (exampleStart fork) =
      .ok { cached with slot := 7 } := by
    unfold _root_.EthLib.Consensus.advanceSlot
    rw [cachedOk]
    rfl
  have across : advanceSlotAcross config checks ⟨fork, exampleStart fork⟩ =
      .ok ⟨fork, { cached with slot := 7 }⟩ := by
    rw [_root_.EthLib.Consensus.advanceSlotAcross_of_before (fun next scheduled => by
      have later := noUpgrade next scheduled
      change 6 + 1 < next.2.toNat * 8
      omega), advanced]
    rfl
  have slot : (exampleInput fork).slot = 7 := by
    obtain ⟨_, _, _, _, same⟩ := exampleInput_like fork
    rw [same]
    rfl
  exact ⟨⟨.inr (exampleStart_chainStart fulu), _, Run.nil.snoc (.slot across), inputOk,
    by rw [slot]; decide, by rw [slot]; decide⟩⟩

theorem LikeExample.supply {fork : Fork}
    {input : _root_.EthLib.Consensus.BeaconState Preset.minimal fork} (like : LikeExample input) :
    SupplyAtInput (toSpecState input) := by
  obtain ⟨_, _, _, _, rfl⟩ := like
  refine ⟨exampleGloasState_reachableInvariants.1.1.2.2.2.2, fun total totalOk => ?_⟩
  have value : get_total_active_balance P exampleGloasState = .ok 16384000000000 := rfl
  change get_total_active_balance P exampleGloasState = .ok total at totalOk
  rw [value] at totalOk
  cases totalOk
  decide

theorem LikeExample.roomForDeposits {fork : Fork} {electra : .pectra ≤ fork}
    {input : _root_.EthLib.Consensus.BeaconState Preset.minimal fork} (like : LikeExample input) :
    RoomForDeposits electra input := by
  obtain ⟨_, _, _, _, rfl⟩ := like
  unfold RoomForDeposits
  change 8 + min 0 _ ≤ Preset.minimal.VALIDATOR_REGISTRY_LIMIT.toNat
  decide

/-! ## Gloas -/

/-- `exampleGloasState`, with other roots, block header and payload availability. -/
def likeGloasState (blockRoots stateRoots : List Root) (header : BeaconBlockHeader)
    (availability : List Bool) : BeaconState :=
  { exampleGloasState with
    block_roots := blockRoots
    state_roots := stateRoots
    latest_block_header := header
    execution_payload_availability := availability }

theorem gloasInput_exists : ∃ blockRoots stateRoots header availability,
    toSpecState (exampleInput .glamsterdam) =
      likeGloasState blockRoots stateRoots header availability := by
  obtain ⟨_, _, _, _, same⟩ := exampleInput_like .glamsterdam
  rw [same]
  exact ⟨_, _, _, _, rfl⟩

/-- The epoch input of the Gloas run, as a reference state. The term has no variables, so Lean
computes with it. -/
noncomputable def gloasInput : BeaconState :=
  likeGloasState gloasInput_exists.choose gloasInput_exists.choose_spec.choose
    gloasInput_exists.choose_spec.choose_spec.choose
    gloasInput_exists.choose_spec.choose_spec.choose_spec.choose

theorem toSpecState_gloasInput : toSpecState (exampleInput .glamsterdam) = gloasInput :=
  gloasInput_exists.choose_spec.choose_spec.choose_spec.choose_spec

/-- The steps before the committee steps return the state itself, as for `exampleGloasState`. -/
theorem gloasInput_epochToCommittees (oracle : Oracle) :
    epochToCommittees P oracle gloasInput = .ok gloasInput := by rfl

theorem gloasChain {checks : SignatureChecks} {oracle : Oracle}
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    GloasChainAssumptions oracle (toSpecState (exampleInput .glamsterdam)) := by
  rw [toSpecState_gloasInput]
  have keys := exampleGloasState_keys oracleMatches
  have preconditions := exampleGloasState_committeeStepPreconds oracle
  have limits := exampleGloasState_physicalLimits
  refine ⟨fun committeeInput steps => ?_,
    ⟨limits.1, limits.2, limits.3, limits.4, limits.5, limits.6, limits.7⟩, ?_,
    exampleGloasState_atEpochBoundary.2.2⟩
  · rw [gloasInput_epochToCommittees] at steps
    cases steps
    exact ⟨⟨preconditions.1, preconditions.2, preconditions.3, preconditions.4, preconditions.5,
      preconditions.6⟩, ⟨by change 8 ≤ 2 ^ 40; decide, keys⟩⟩
  · change 7 + 8192 < 2 ^ 64
    decide

/-- The Gloas assumptions about the run, the supply, the chain, the room and the oracle hold
together, for every fork schedule. At that epoch input, the model and EthLib give the same state. -/
theorem gloas_run_assumptions_hold_for_example (checks : SignatureChecks)
    (forkEpochs : ForkEpochs) :
    ∃ (oracle : Oracle) (input : _root_.EthLib.Consensus.BeaconState Preset.minimal .glamsterdam),
      Nonempty (RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks
        ⟨.glamsterdam, exampleStart .glamsterdam⟩ input) ∧
      SupplyAtInput (toSpecState input) ∧ GloasChainAssumptions oracle (toSpecState input) ∧
      RoomForDeposits (by decide) input ∧ OracleMatches Preset.minimal checks oracle ∧
      ∃ result, process_epoch_lighthouse oracle (toSpecState input) = .ok (toSpecState result) ∧
        processEpoch (withForkEpochs Config.minimal forkEpochs) checks input = .ok result := by
  obtain ⟨oracle, oracleMatches⟩ := exists_oracle (preset := Preset.minimal) checks (by decide)
  obtain ⟨run⟩ := exampleRun (checks := checks)
    (config := withForkEpochs Config.minimal forkEpochs) (fork := .glamsterdam) (by decide)
    (fun next scheduled => by
      cases scheduled
      change 1 ≤ Config.minimal.HEZE_FORK_EPOCH.toNat
      decide)
  have like := exampleInput_like .glamsterdam
  have supply := like.supply
  have chain := gloasChain oracleMatches
  have room : RoomForDeposits (by decide) (exampleInput .glamsterdam) := like.roomForDeposits
  refine ⟨oracle, _, ⟨run⟩, supply, chain, room, oracleMatches, ?_⟩
  exact Formalhouse.lighthouse_model_gloas_epoch_eq_ethlib_of_invariants presetMatches_minimal
    (run.invariants presetMatches_minimal maxEffectiveBalance_minimal (by decide)
      (registryWithinLimit room) supply)
    (run.atEpochBoundary presetMatches_minimal chain.historicalSummariesBelowLimit) chain room
    oracleMatches

/-! ## Fulu -/

/-- `exampleFuluState`, with other roots, block header and payload availability. -/
def likeFuluState (blockRoots stateRoots : List Root) (header : BeaconBlockHeader)
    (availability : List Bool) : BeaconState :=
  { exampleFuluState with
    block_roots := blockRoots
    state_roots := stateRoots
    latest_block_header := header
    execution_payload_availability := availability }

theorem fuluInput_exists : ∃ blockRoots stateRoots header availability,
    toSpecState (exampleInput .fusaka) =
      likeFuluState blockRoots stateRoots header availability := by
  obtain ⟨_, _, _, _, same⟩ := exampleInput_like .fusaka
  rw [same]
  exact ⟨_, _, _, _, rfl⟩

/-- The epoch input of the Fulu run, as a reference state. The term has no variables, so Lean
computes with it. -/
noncomputable def fuluInput : BeaconState :=
  likeFuluState fuluInput_exists.choose fuluInput_exists.choose_spec.choose
    fuluInput_exists.choose_spec.choose_spec.choose
    fuluInput_exists.choose_spec.choose_spec.choose_spec.choose

theorem toSpecState_fuluInput : toSpecState (exampleInput .fusaka) = fuluInput :=
  fuluInput_exists.choose_spec.choose_spec.choose_spec.choose_spec

/-- The steps before the committee steps return the state itself, as for `exampleFuluState`. -/
theorem fuluInput_epochToCommittees (oracle : Oracle) :
    epochToCommitteesFulu P FC oracle fuluInput = .ok fuluInput := by rfl

theorem fuluChain {checks : SignatureChecks} {oracle : Oracle}
    (oracleMatches : OracleMatches Preset.minimal checks oracle) :
    FuluChainAssumptions oracle (toSpecState (exampleInput .fusaka)) := by
  rw [toSpecState_fuluInput]
  have keys := exampleGloasState_keys oracleMatches
  have preconditions := (exampleFuluState_atCommitteeStepState oracle keys _
    (exampleFuluState_epochToCommitteesFulu oracle)).2
  have limits := exampleFuluState_physicalLimits
  refine ⟨fun committeeInput steps => ?_,
    ⟨limits.1, limits.2, limits.3, limits.4, limits.5, limits.6, limits.7⟩, ?_,
    exampleGloasState_atEpochBoundary.2.2⟩
  · rw [fuluInput_epochToCommittees] at steps
    cases steps
    exact ⟨⟨preconditions.1, preconditions.2, preconditions.3, preconditions.4⟩,
      ⟨by change 8 ≤ 2 ^ 40; decide, keys⟩⟩
  · change 7 + 8192 < 2 ^ 64
    decide

/-- The Fulu assumptions about the run, the supply, the chain, the room and the oracle hold
together, for every fork schedule with Gloas after epoch 0. At that epoch input, the model and
EthLib give the same state. -/
theorem fulu_run_assumptions_hold_for_example (checks : SignatureChecks) (forkEpochs : ForkEpochs)
    (gloasLater : 1 ≤ forkEpochs.gloas.toNat) :
    ∃ (oracle : Oracle) (input : _root_.EthLib.Consensus.BeaconState Preset.minimal .fusaka),
      Nonempty (RunToEpochInput (withForkEpochs Config.minimal forkEpochs) checks
        ⟨.fusaka, exampleStart .fusaka⟩ input) ∧
      SupplyAtInput (toSpecState input) ∧ FuluChainAssumptions oracle (toSpecState input) ∧
      RoomForDeposits (by decide) input ∧ OracleMatches Preset.minimal checks oracle ∧
      ∃ result,
        process_epoch_lighthouse_fulu oracle (toSpecState input) = .ok (toSpecState result) ∧
        processEpoch (withForkEpochs Config.minimal forkEpochs) checks input = .ok result := by
  obtain ⟨oracle, oracleMatches⟩ := exists_oracle (preset := Preset.minimal) checks (by decide)
  obtain ⟨run⟩ := exampleRun (checks := checks)
    (config := withForkEpochs Config.minimal forkEpochs) (fork := .fusaka) (by decide)
    (fun next scheduled => by
      cases scheduled
      exact gloasLater)
  have like := exampleInput_like .fusaka
  have supply := like.supply
  have chain := fuluChain oracleMatches
  have room : RoomForDeposits (by decide) (exampleInput .fusaka) := like.roomForDeposits
  obtain ⟨result, model, ethLib, -⟩ := lighthouse_model_fulu_epoch_eq_ethlib_minimal run supply
    chain room oracleMatches
  exact ⟨oracle, _, ⟨run⟩, supply, chain, room, oracleMatches, result, model, ethLib⟩

end EpochProofs.Example
