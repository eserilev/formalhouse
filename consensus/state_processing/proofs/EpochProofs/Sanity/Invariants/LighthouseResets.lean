import EpochProofs.Equiv.TailUpdates
import EpochProofs.Spec.EpochRest

/-!
# The Lighthouse reset steps equal the spec steps

`resets.rs` and `historical_summaries_update.rs` run the eth1, slashings and randao resets and
the historical summaries update with the checks in `tail_updates.rs`. Each `lh*` function here is
that glue on mainnet: the checks are the models of `Equiv/TailUpdates.lean`, and the writes are
the list writes of the glue. The participation rotation is plain glue with the same writes as
the spec, so it has no model of its own.

The eth1 reset of Lighthouse reads the slot, not the epoch: `(slot + 1) % 2048 == 0`. It equals
the spec test `next_epoch % 64 == 0` at the last slot of an epoch, where `process_epoch` runs.
-/

namespace EpochProofs.Spec

/-- `E::HistoricalRootsLimit` on mainnet: the limit of `historical_summaries` in Lighthouse. -/
def LH_HISTORICAL_ROOTS_LIMIT : Nat := 16777216

/-- `E::SlotsPerEth1VotingPeriod` on mainnet: `EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`. -/
def LH_SLOTS_PER_ETH1_VOTING_PERIOD : Nat := 2048

/-- `process_eth1_data_reset` in `resets.rs`. -/
def lhEth1DataReset (s : BeaconState) : SpecM BeaconState := do
  if ← lhEth1ResetDue s.slot LH_SLOTS_PER_ETH1_VOTING_PERIOD then
    pure { s with eth1_data_votes := [] }
  else
    pure s

/-- `process_slashings_reset` in `resets.rs`. `state.current_epoch()` is `slot / 32`. -/
def lhSlashingsReset (s : BeaconState) : SpecM BeaconState := do
  match ← slashingsResetIndex (s.slot / Preset.mainnet.SLOTS_PER_EPOCH)
      Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR with
  | none => throw .indexOutOfRange
  | some i => pure { s with slashings := ← listSet s.slashings i 0 }

/-- `process_randao_mixes_reset` in `resets.rs`. -/
def lhRandaoMixesReset (s : BeaconState) : SpecM BeaconState := do
  match ← randaoMixesResetIndices (s.slot / Preset.mainnet.SLOTS_PER_EPOCH)
      Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR with
  | none => throw .indexOutOfRange
  | some (source, target) =>
    let mix ← listGet s.randao_mixes source
    pure { s with randao_mixes := ← listSet s.randao_mixes target mix }

/-- `process_historical_summaries_update` in `historical_summaries_update.rs`. The push fails
when the list holds `LH_HISTORICAL_ROOTS_LIMIT` items. -/
def lhHistoricalSummariesUpdate (o : Oracle) (s : BeaconState) : SpecM BeaconState := do
  let next_epoch ← uint64Add (s.slot / Preset.mainnet.SLOTS_PER_EPOCH) 1
  if ← historicalSummaryDue next_epoch Preset.mainnet.SLOTS_PER_HISTORICAL_ROOT
      Preset.mainnet.SLOTS_PER_EPOCH then
    if s.historical_summaries.length < LH_HISTORICAL_ROOTS_LIMIT then
      let historical_summary : HistoricalSummary := {
        block_summary_root := o.hash_tree_root_BlockRoots s.block_roots
        state_summary_root := o.hash_tree_root_StateRoots s.state_roots }
      pure { s with historical_summaries := s.historical_summaries ++ [historical_summary] }
    else
      throw .indexOutOfRange
  else
    pure s

/-- `get_current_epoch` on mainnet is `slot / 32`. -/
theorem get_current_epoch_mainnet (s : BeaconState) :
    get_current_epoch Preset.mainnet s = .ok (s.slot / Preset.mainnet.SLOTS_PER_EPOCH) := by
  simp [get_current_epoch, compute_epoch_at_slot, uint64Div, Preset.mainnet, pure, Except.pure]

/-- At the last slot of an epoch, the Lighthouse eth1 reset is the spec eth1 reset. -/
theorem lhEth1DataReset_eq (s : BeaconState) (hslot : s.slot + 1 < 2 ^ 64)
    (hlast : (s.slot + 1) % Preset.mainnet.SLOTS_PER_EPOCH = 0) :
    lhEth1DataReset s = process_eth1_data_reset Preset.mainnet s := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot = n := ⟨_, rfl⟩
  have hl : (n + 1) % 32 = 0 := by rw [← hn]; exact hlast
  have hslot' : n + 1 < 2 ^ 64 := by rw [← hn]; exact hslot
  have hdue : ((n + 1) % 2048 == 0) = ((n / 32 + 1) % 64 == 0) := by
    have h1 : n / 32 + 1 = (n + 1) / 32 := by omega
    rw [h1]
    by_cases h : (n + 1) % 2048 = 0
    · have : (n + 1) / 32 % 64 = 0 := by omega
      simp [h, this]
    · have : (n + 1) / 32 % 64 ≠ 0 := by omega
      simp [h, this]
  have hfit : n / 32 + 1 < 2 ^ 64 := by omega
  simp only [lhEth1DataReset, process_eth1_data_reset, lhEth1ResetDue, get_current_epoch_mainnet]
  simp only [uint64Add, uint64Mod, UINT64_SIZE, LH_SLOTS_PER_ETH1_VOTING_PERIOD, Preset.mainnet, hn]
  simp only [hslot', if_true]
  simp only [show (2048 : Nat) ≠ 0 by decide, show (64 : Nat) ≠ 0 by decide, if_false]
  simp only [pure, Except.pure, Bind.bind, Except.bind]
  rw [hdue]
  simp only [hfit, if_true]

/-- Away from `u64` overflow, the Lighthouse slashings reset is the spec slashings reset. -/
theorem lhSlashingsReset_eq (s : BeaconState)
    (hfit : s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 +
      Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR < 2 ^ 64) :
    lhSlashingsReset s = process_slashings_reset Preset.mainnet s := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot = n := ⟨_, rfl⟩
  have hf : n / 32 + 1 + 8192 < 2 ^ 64 := by rw [← hn]; exact hfit
  have h1 : n / 32 + 1 < 2 ^ 64 := by omega
  have hlt : ¬ n / 32 ≥ n / 32 + 1 + 8192 := by omega
  have hle : ¬ n / 32 + 1 > n / 32 + 1 := by omega
  simp only [lhSlashingsReset, process_slashings_reset, slashingsResetIndex, epochVectorIndex,
    get_current_epoch_mainnet]
  simp only [uint64Add, uint64Mod, UINT64_SIZE, Preset.mainnet, hn]
  simp only [h1, hf, if_true, show (8192 : Nat) ≠ 0 by decide, if_false,
    pure, Except.pure, Bind.bind, Except.bind, hlt, hle]

/-- Away from `u64` overflow, the Lighthouse randao reset is the spec randao reset. -/
theorem lhRandaoMixesReset_eq (s : BeaconState)
    (hfit : s.slot / Preset.mainnet.SLOTS_PER_EPOCH + 1 +
      Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR < 2 ^ 64) :
    lhRandaoMixesReset s = process_randao_mixes_reset Preset.mainnet s := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, s.slot = n := ⟨_, rfl⟩
  have hf : n / 32 + 1 + 65536 < 2 ^ 64 := by rw [← hn]; exact hfit
  have h1 : n / 32 + 1 < 2 ^ 64 := by omega
  have h0 : n / 32 + 65536 < 2 ^ 64 := by omega
  have ha : ¬ n / 32 ≥ n / 32 + 65536 := by omega
  have hb : ¬ n / 32 ≥ n / 32 + 1 + 65536 := by omega
  have hc : ¬ n / 32 > n / 32 := by omega
  have hd : ¬ n / 32 + 1 > n / 32 + 1 := by omega
  simp only [lhRandaoMixesReset, process_randao_mixes_reset, randaoMixesResetIndices,
    epochVectorIndex, get_randao_mix, get_current_epoch_mainnet]
  simp only [uint64Add, uint64Mod, UINT64_SIZE, Preset.mainnet, hn]
  simp only [h1, hf, h0, if_true, show (65536 : Nat) ≠ 0 by decide, if_false,
    pure, Except.pure, Bind.bind, Except.bind, ha, hb, hc, hd, Bool.false_eq_true]

/-- Below the Lighthouse list limit, the Lighthouse historical summaries update is the spec
update. -/
theorem lhHistoricalSummariesUpdate_eq (o : Oracle) (s : BeaconState)
    (hroom : s.historical_summaries.length < LH_HISTORICAL_ROOTS_LIMIT) :
    lhHistoricalSummariesUpdate o s = process_historical_summaries_update Preset.mainnet o s := by
  simp only [lhHistoricalSummariesUpdate, process_historical_summaries_update,
    historicalSummaryDue, get_current_epoch_mainnet]
  simp only [uint64Div, Preset.mainnet,
    show (32 : Nat) ≠ 0 by decide, if_false, hroom, if_true]
  rfl

end EpochProofs.Spec
