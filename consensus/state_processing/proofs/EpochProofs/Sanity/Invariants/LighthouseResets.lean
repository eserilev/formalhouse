import EpochProofs.Equiv.TailUpdates
import EpochProofs.Spec.PresetCfg
import EpochProofs.Spec.EpochRest

/-!
# The Lighthouse reset steps equal the spec steps

`resets.rs` and `historical_summaries_update.rs` run the eth1, slashings and randao resets and
the historical summaries update with the checks in `tail_updates.rs`. Each `lh*` function here is
that glue on mainnet: the checks are the models of `Equiv/TailUpdates.lean`, and the writes are
the list writes of the glue. The participation rotation is plain glue with the same writes as
the spec, so it has no model of its own.

The eth1 reset of Lighthouse reads the slot, not the epoch:
`(slot + 1) % SLOTS_PER_ETH1_VOTING_PERIOD == 0`. It equals the spec test
`next_epoch % EPOCHS_PER_ETH1_VOTING_PERIOD == 0` at the last slot of an epoch, where
`process_epoch` runs.
-/

namespace EpochProofs.Spec

/-- `E::HistoricalRootsLimit`: the limit of `historical_summaries` in Lighthouse. It is the same
on mainnet and minimal. -/
def LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT : Nat := 16777216

/-- `E::SlotsPerEth1VotingPeriod`: `EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`. -/
def LH_SLOTS_PER_ETH1_VOTING_PERIOD [PresetCfg] : Nat :=
  P.EPOCHS_PER_ETH1_VOTING_PERIOD * P.SLOTS_PER_EPOCH

/-- `process_eth1_data_reset` in `resets.rs`. -/
def lhEth1DataReset [PresetCfg] (s : BeaconState) : SpecM BeaconState := do
  if ← lhEth1ResetDue s.slot LH_SLOTS_PER_ETH1_VOTING_PERIOD then
    pure { s with eth1_data_votes := [] }
  else
    pure s

/-- `process_slashings_reset` in `resets.rs`. `state.current_epoch()` is `slot / SLOTS_PER_EPOCH`. -/
def lhSlashingsReset [PresetCfg] (s : BeaconState) : SpecM BeaconState := do
  match ← slashingsResetIndex (s.slot / P.SLOTS_PER_EPOCH)
      P.EPOCHS_PER_SLASHINGS_VECTOR with
  | none => throw .indexOutOfRange
  | some i => pure { s with slashings := ← listSet s.slashings i 0 }

/-- `process_randao_mixes_reset` in `resets.rs`. -/
def lhRandaoMixesReset [PresetCfg] (s : BeaconState) : SpecM BeaconState := do
  match ← randaoMixesResetIndices (s.slot / P.SLOTS_PER_EPOCH)
      P.EPOCHS_PER_HISTORICAL_VECTOR with
  | none => throw .indexOutOfRange
  | some (source, target) =>
    let mix ← listGet s.randao_mixes source
    pure { s with randao_mixes := ← listSet s.randao_mixes target mix }

/-- `process_historical_summaries_update` in `historical_summaries_update.rs`. The push fails
when the list holds `LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT` items. -/
def lhHistoricalSummariesUpdate [PresetCfg] (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let next_epoch ← uint64Add (s.slot / P.SLOTS_PER_EPOCH) 1
  if ← historicalSummaryDue next_epoch P.SLOTS_PER_HISTORICAL_ROOT
      P.SLOTS_PER_EPOCH then
    if s.historical_summaries.length < LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT then
      let historical_summary : HistoricalSummary := {
        block_summary_root := o.hash_tree_root_BlockRoots s.block_roots
        state_summary_root := o.hash_tree_root_StateRoots s.state_roots }
      pure { s with historical_summaries := s.historical_summaries ++ [historical_summary] }
    else
      throw .indexOutOfRange
  else
    pure s

/-- `get_current_epoch` is `slot / SLOTS_PER_EPOCH`. -/
theorem get_current_epoch_mainnet [PresetCfg] [PresetCfg.Ok] (s : BeaconState) :
    get_current_epoch P s = .ok (s.slot / P.SLOTS_PER_EPOCH) := by
  simp [get_current_epoch, compute_epoch_at_slot, uint64Div, Nat.ne_of_gt P_slots_pos, pure,
    Except.pure]

/-- With `S ∣ n + 1`: `E * S ∣ n + 1` exactly when `E ∣ n / S + 1`. -/
theorem eth1_due_iff (n S E : Nat) (hS : 0 < S) (hl : (n + 1) % S = 0) :
    ((n + 1) % (E * S) == 0) = ((n / S + 1) % E == 0) := by
  have h1 : (n + 1) / S = n / S + 1 := by
    rw [Nat.succ_div]; simp [Nat.dvd_iff_mod_eq_zero.mpr hl]
  have hq : n + 1 = S * (n / S + 1) := by
    have := Nat.div_add_mod (n + 1) S
    rw [hl, Nat.add_zero, h1] at this; omega
  rw [hq, Nat.mul_comm E S, Nat.mul_mod_mul_left]
  by_cases h : (n / S + 1) % E = 0
  · simp [h]
  · have : S * ((n / S + 1) % E) ≠ 0 := Nat.mul_ne_zero (by omega) h
    simp [h, this]

/-- At the last slot of an epoch, the Lighthouse eth1 reset is the spec eth1 reset. -/
theorem lhEth1DataReset_eq [PresetCfg] [PresetCfg.Ok] (s : BeaconState)
    (hslot : s.slot + 1 < 2 ^ 64) (hlast : (s.slot + 1) % P.SLOTS_PER_EPOCH = 0) :
    lhEth1DataReset s = process_eth1_data_reset P s := by
  obtain ⟨S, hS⟩ : ∃ S : Nat, P.SLOTS_PER_EPOCH = S := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Nat, P.EPOCHS_PER_ETH1_VOTING_PERIOD = E := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot = n := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [← hS]; exact P_slots_pos
  have hE0 : 0 < E := by rw [← hE]; exact P_eth1_period_pos
  have hl : (n + 1) % S = 0 := by rw [← hn, ← hS]; exact hlast
  have hslot' : n + 1 < 2 ^ 64 := by rw [← hn]; exact hslot
  have hES : E * S ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hEn : E ≠ 0 := by omega
  have hfit : n / S + 1 < 2 ^ 64 := by
    have := Nat.div_le_self n S; omega
  have hdue := eth1_due_iff n S E hS0 hl
  simp only [lhEth1DataReset, process_eth1_data_reset, lhEth1ResetDue, get_current_epoch_mainnet,
    LH_SLOTS_PER_ETH1_VOTING_PERIOD, hS, hE, hn, uint64Add, uint64Mod, UINT64_SIZE, hslot', hfit,
    hES, hEn, if_true, if_false, pure, Except.pure, Bind.bind, Except.bind]
  rw [hdue]

/-- Away from `u64` overflow, the Lighthouse slashings reset is the spec slashings reset. -/
theorem lhSlashingsReset_eq [PresetCfg] [PresetCfg.Ok] (s : BeaconState)
    (hfit : s.slot / P.SLOTS_PER_EPOCH + 1 +
      P.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64) :
    lhSlashingsReset s = process_slashings_reset P s := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot / P.SLOTS_PER_EPOCH = n := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Nat, P.EPOCHS_PER_SLASHINGS_VECTOR = V := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [← hV]; exact P_slashings_vector_pos
  have hf : n + 1 + V < 2 ^ 64 := by rw [← hn, ← hV]; exact hfit
  have hVn : V ≠ 0 := by omega
  have h1 : n + 1 < 2 ^ 64 := by omega
  have hlt : ¬ n ≥ n + 1 + V := by omega
  have hle : ¬ n + 1 > n + 1 := by omega
  simp only [lhSlashingsReset, process_slashings_reset, slashingsResetIndex, epochVectorIndex,
    get_current_epoch_mainnet, hn, hV, uint64Add, uint64Mod, UINT64_SIZE, h1, hf, hVn, if_true,
    if_false, pure, Except.pure, Bind.bind, Except.bind, hlt, hle]

/-- Away from `u64` overflow, the Lighthouse randao reset is the spec randao reset. -/
theorem lhRandaoMixesReset_eq [PresetCfg] [PresetCfg.Ok] (s : BeaconState)
    (hfit : s.slot / P.SLOTS_PER_EPOCH + 1 +
      P.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64) :
    lhRandaoMixesReset s = process_randao_mixes_reset P s := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot / P.SLOTS_PER_EPOCH = n := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Nat, P.EPOCHS_PER_HISTORICAL_VECTOR = V := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [← hV]; exact P_historical_vector_pos
  have hf : n + 1 + V < 2 ^ 64 := by rw [← hn, ← hV]; exact hfit
  have hVn : V ≠ 0 := by omega
  have h1 : n + 1 < 2 ^ 64 := by omega
  have h0 : n + V < 2 ^ 64 := by omega
  have ha : ¬ n ≥ n + V := by omega
  have hb : ¬ n ≥ n + 1 + V := by omega
  have hc : ¬ n > n := by omega
  have hd : ¬ n + 1 > n + 1 := by omega
  simp only [lhRandaoMixesReset, process_randao_mixes_reset, randaoMixesResetIndices,
    epochVectorIndex, get_randao_mix, get_current_epoch_mainnet, hn, hV, uint64Add, uint64Mod,
    UINT64_SIZE, h1, hf, h0, hVn, if_true, if_false, pure, Except.pure, Bind.bind, Except.bind,
    ha, hb, hc, hd, Bool.false_eq_true]

/-- Below the Lighthouse list limit, the Lighthouse historical summaries update is the spec
update. -/
theorem lhHistoricalSummariesUpdate_eq [PresetCfg] [PresetCfg.Ok] (o : Oracle) (s : BeaconState)
    (hroom : s.historical_summaries.length < LIGHTHOUSE_HISTORICAL_ROOTS_LIMIT) :
    lhHistoricalSummariesUpdate o s = process_historical_summaries_update P o s := by
  simp only [lhHistoricalSummariesUpdate, process_historical_summaries_update,
    historicalSummaryDue, get_current_epoch_mainnet]
  simp only [uint64Div, Nat.ne_of_gt P_slots_pos, if_false, hroom, if_true]
  simp only [pure, Except.pure, Bind.bind, Except.bind]
  cases uint64Add (s.slot / P.SLOTS_PER_EPOCH) 1 with
  | error e => rfl
  | ok a =>
    simp only []
    cases uint64Mod a (P.SLOTS_PER_HISTORICAL_ROOT / P.SLOTS_PER_EPOCH) with
    | error e => rfl
    | ok v => by_cases hv : v = 0 <;> simp [hv]

end EpochProofs.Spec
