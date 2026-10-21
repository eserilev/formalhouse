import EpochProofs.Etheorem.Helpers

/-!
# The reset and rotation steps equal Etheorem's

Four steps of `process_epoch`: `process_eth1_data_reset`, `process_slashings_reset`,
`process_randao_mixes_reset` and `process_participation_flag_updates`. Each theorem reads "if the
reference returns `s'`, then Etheorem's run succeeds and its result maps to `s'`".

`TailPresetAgrees p` holds the preset values that these steps, the effective balance update and
the historical summaries read, and that `PresetAgrees` does not hold.
-/

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Repr SizzLean.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)

section WithPreset

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config]

open EthCLSpecs.Gloas in
/-- The Etheorem preset holds the values of `p` that the tail steps read. -/
structure TailPresetAgrees (p : Spec.Preset) : Prop where
  epochsPerEth1VotingPeriod : Const.epochsPerEth1VotingPeriod = p.EPOCHS_PER_ETH1_VOTING_PERIOD
  epochsPerEth1VotingPeriodLt : Const.epochsPerEth1VotingPeriod < 2 ^ 64
  epochsPerSlashingsVector : Const.epochsPerSlashingsVector = p.EPOCHS_PER_SLASHINGS_VECTOR
  epochsPerSlashingsVectorLt : Const.epochsPerSlashingsVector < 2 ^ 64
  slotsPerHistoricalRoot : Const.slotsPerHistoricalRoot = p.SLOTS_PER_HISTORICAL_ROOT
  hysteresisQuotient : Const.hysteresisQuotient = p.HYSTERESIS_QUOTIENT
  hysteresisDownwardMultiplier :
    Const.hysteresisDownwardMultiplier = p.HYSTERESIS_DOWNWARD_MULTIPLIER
  hysteresisUpwardMultiplier : Const.hysteresisUpwardMultiplier = p.HYSTERESIS_UPWARD_MULTIPLIER
  hysteresisLt : Const.hysteresisQuotient < 2 ^ 64 ∧ Const.hysteresisDownwardMultiplier < 2 ^ 64 ∧
    Const.hysteresisUpwardMultiplier < 2 ^ 64
  maxEffectiveBalanceElectra : Const.maxEffectiveBalanceElectraG.toNat = p.MAX_EFFECTIVE_BALANCE_ELECTRA
  minActivationBalance : Const.minActivationBalance.toNat = p.MIN_ACTIVATION_BALANCE

omit [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] in
/-- `(x + 1) % k` in Etheorem reads as the reference value. -/
theorem next_mod_ok {x : UInt64} {k m n r : Nat} (hk : k = m) (hlt : k < 2 ^ 64)
    (hadd : Spec.uint64Add x.toNat 1 = .ok n) (hmod : Spec.uint64Mod n m = .ok r) :
    ((x + 1) % UInt64.ofNat k).toNat = r := by
  have hn : (x + 1).toNat = n := uint64Add_ok (a := x) (b := 1) (by simpa using hadd)
  apply uint64Mod_ok
  rw [hn, UInt64.toNat_ofNat_of_lt' hlt, hk]
  exact hmod

omit [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] in
theorem uint64_eq_zero_iff (x : UInt64) : x = 0 ↔ x.toNat = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; exact UInt64.toNat_inj.mp (by simpa using h)

omit [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] in
/-- `Vector.set!` is `List.set` under the map. Past the end both leave the list unchanged. -/
theorem map_toList_vset! {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) (i : Nat) (a : α) :
    (v.set! i a).toList.map f = (v.toList.map f).set i (f a) := by
  rw [← Vector.toList_toArray, Vector.toArray_set!, Array.set!_eq_setIfInBounds,
    Array.toList_setIfInBounds, List.map_set, Vector.toList_toArray]

variable [HasherTag]

omit [EthCLSpecs.Gloas.Config] in
theorem currentEpochOf_pureState (e : EState) :
    EthCLSpecs.Gloas.currentEpochOf (pureState e) = EthCLSpecs.Gloas.computeEpochAtSlot e.slot :=
  rfl

/-! ## The four Etheorem runs -/

omit [EthCLSpecs.Gloas.Config] in
theorem processEth1DataReset_run (e : EState) :
    runPure (EthCLSpecs.Gloas.processEth1DataReset (StateTransition := GloasRun)) e =
      .ok ((), if (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1) %
          UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerEth1VotingPeriod = 0
        then { e with eth1DataVotes := sszOfArray #[] } else e) := by
  unfold EthCLSpecs.Gloas.processEth1DataReset EthCLSpecs.Gloas.getCurrentEpoch
  by_cases h : (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1) %
      UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerEth1VotingPeriod = 0
  · rw [if_pos h]
    simp [runPure, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.pure, Except.bind, view_uncachedBox, h]
    rfl
  · rw [if_neg h]
    simp [runPure, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.pure, Except.bind, view_uncachedBox, h]
    rfl

omit [EthCLSpecs.Gloas.Config] in
theorem processSlashingsReset_run (e : EState) :
    runPure (EthCLSpecs.Gloas.processSlashingsReset (StateTransition := GloasRun)) e =
      .ok ((), { e with slashings := (e.slashings.set!
        (umodIdx (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1)
          EthCLSpecs.Gloas.Const.epochsPerSlashingsVector) 0) }) := by
  unfold EthCLSpecs.Gloas.processSlashingsReset EthCLSpecs.Gloas.getCurrentEpoch
  simp [runPure, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind, view_uncachedBox]
  rfl

omit [EthCLSpecs.Gloas.Config] in
theorem processRandaoMixesReset_run (e : EState) :
    runPure (EthCLSpecs.Gloas.processRandaoMixesReset (StateTransition := GloasRun)) e =
      .ok ((), { e with randaoMixes := (e.randaoMixes.set!
        (umodIdx (EthCLSpecs.Gloas.computeEpochAtSlot e.slot + 1)
          EthCLSpecs.Gloas.Const.epochsPerHistoricalVector)
        (vget e.randaoMixes (EthCLSpecs.Gloas.computeEpochAtSlot e.slot %
          UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerHistoricalVector).toNat)) }) := by
  unfold EthCLSpecs.Gloas.processRandaoMixesReset EthCLSpecs.Gloas.getCurrentEpoch
    EthCLSpecs.Gloas.getRandaoMix
  simp [runPure, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind, view_uncachedBox]
  rfl

omit [EthCLSpecs.Gloas.Config] in
theorem processParticipationFlagUpdates_run (e : EState) :
    runPure (EthCLSpecs.Gloas.processParticipationFlagUpdates (StateTransition := GloasRun)) e =
      .ok ((), { e with previousEpochParticipation := e.currentEpochParticipation,
                        currentEpochParticipation :=
                          sszOfArray (Array.replicate e.validators.val.size 0) }) := by
  unfold EthCLSpecs.Gloas.processParticipationFlagUpdates
  simp [runPure, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.pure, Except.bind, view_uncachedBox]
  rfl

/-! ## The reference equals Etheorem -/

section Steps

variable {p : Spec.Preset} (hp : PresetAgrees p) (ht : TailPresetAgrees p)

include hp ht in
/-- `process_eth1_data_reset` equals Etheorem's. -/
theorem eth1_data_reset_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_eth1_data_reset p (absEState e) = .ok s') :
    ∃ e', runPure (EthCLSpecs.Gloas.processEth1DataReset (StateTransition := GloasRun)) e =
        .ok ((), e') ∧ absEState e' = s' := by
  refine ⟨_, processEth1DataReset_run e, ?_⟩
  unfold Spec.process_eth1_data_reset at h
  rw [get_current_epoch_eq hp, currentEpochOf_pureState] at h
  simp only [bind, Except.bind] at h
  generalize hc : EthCLSpecs.Gloas.computeEpochAtSlot e.slot = c at h ⊢
  cases hadd : Spec.uint64Add c.toNat 1 with
  | error err => rw [hadd] at h; cases h
  | ok n =>
    rw [hadd] at h
    simp only at h
    cases hmod : Spec.uint64Mod n p.EPOCHS_PER_ETH1_VOTING_PERIOD with
    | error err => rw [hmod] at h; cases h
    | ok r =>
      rw [hmod] at h
      have hr := next_mod_ok ht.epochsPerEth1VotingPeriod ht.epochsPerEth1VotingPeriodLt hadd hmod
      simp only [pure, Except.pure] at h
      by_cases h0 : r = 0
      · rw [if_pos (by rw [uint64_eq_zero_iff, hr, h0])]
        simp only [h0, beq_self_eq_true, if_true, Except.ok.injEq] at h
        rw [← h, absEState_set_eth1DataVotes]
        simp [sszOfArray]
      · rw [if_neg (by rw [uint64_eq_zero_iff, hr]; exact h0)]
        simp only [beq_iff_eq, h0, if_false, Except.ok.injEq] at h
        exact h

include hp ht in
/-- `process_slashings_reset` equals Etheorem's. -/
theorem slashings_reset_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_slashings_reset p (absEState e) = .ok s') :
    ∃ e', runPure (EthCLSpecs.Gloas.processSlashingsReset (StateTransition := GloasRun)) e =
        .ok ((), e') ∧ absEState e' = s' := by
  refine ⟨_, processSlashingsReset_run e, ?_⟩
  unfold Spec.process_slashings_reset at h
  rw [get_current_epoch_eq hp, currentEpochOf_pureState] at h
  simp only [bind, Except.bind] at h
  generalize hc : EthCLSpecs.Gloas.computeEpochAtSlot e.slot = c at h ⊢
  cases hadd : Spec.uint64Add c.toNat 1 with
  | error err => rw [hadd] at h; cases h
  | ok n =>
    rw [hadd] at h
    simp only at h
    cases hmod : Spec.uint64Mod n p.EPOCHS_PER_SLASHINGS_VECTOR with
    | error err => rw [hmod] at h; cases h
    | ok r =>
      rw [hmod] at h
      have hr := next_mod_ok ht.epochsPerSlashingsVector ht.epochsPerSlashingsVectorLt hadd hmod
      simp only at h
      cases hs : Spec.listSet (absEState e).slashings r 0 with
      | error err => rw [hs] at h; cases h
      | ok l =>
        rw [hs] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        unfold Spec.listSet at hs
        split at hs
        · cases hs
          rw [← h, absEState_set_slashings, umodIdx, hr, map_toList_vset!]
          rfl
        · cases hs

include hp in
/-- `process_randao_mixes_reset` equals Etheorem's. -/
theorem randao_mixes_reset_etheorem (e : EState) {s' : Spec.BeaconState}
    (h : Spec.process_randao_mixes_reset p (absEState e) = .ok s') :
    ∃ e', runPure (EthCLSpecs.Gloas.processRandaoMixesReset (StateTransition := GloasRun)) e =
        .ok ((), e') ∧ absEState e' = s' := by
  refine ⟨_, processRandaoMixesReset_run e, ?_⟩
  have hk := hp.epochsPerHistoricalVector
  have hlt := EthCLSpecs.Gloas.Const.epochsPerHistoricalVectorLt
  unfold Spec.process_randao_mixes_reset Spec.get_randao_mix at h
  rw [get_current_epoch_eq hp, currentEpochOf_pureState] at h
  simp only [bind, Except.bind] at h
  generalize hc : EthCLSpecs.Gloas.computeEpochAtSlot e.slot = c at h ⊢
  cases hadd : Spec.uint64Add c.toNat 1 with
  | error err => rw [hadd] at h; cases h
  | ok n =>
    rw [hadd] at h
    simp only at h
    cases hm1 : Spec.uint64Mod c.toNat p.EPOCHS_PER_HISTORICAL_VECTOR with
    | error err => rw [hm1] at h; cases h
    | ok j =>
      rw [hm1] at h
      simp only at h
      have hj : (c % UInt64.ofNat EthCLSpecs.Gloas.Const.epochsPerHistoricalVector).toNat = j := by
        apply uint64Mod_ok
        rw [UInt64.toNat_ofNat_of_lt' hlt, hk]
        exact hm1
      cases hg : Spec.listGet (absEState e).randao_mixes j with
      | error err => rw [hg] at h; cases h
      | ok mix =>
        rw [hg] at h
        simp only at h
        have hmix : mix = vget e.randaoMixes j := by
          unfold Spec.listGet at hg
          simp only [absEState_randao_mixes] at hg
          split at hg
          · rename_i a ha
            cases hg
            rw [List.getElem?_eq_some_iff] at ha
            obtain ⟨hj', rfl⟩ := ha
            unfold vget
            rw [getElem!_pos _ _ (by simpa using hj')]
            simp
          · cases hg
        cases hm2 : Spec.uint64Mod n p.EPOCHS_PER_HISTORICAL_VECTOR with
        | error err => rw [hm2] at h; cases h
        | ok r =>
          rw [hm2] at h
          have hr := next_mod_ok hk hlt hadd hm2
          simp only at h
          cases hs : Spec.listSet (absEState e).randao_mixes r mix with
          | error err => rw [hs] at h; cases h
          | ok l =>
            rw [hs] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            unfold Spec.listSet at hs
            split at hs
            · cases hs
              rw [← h, absEState_set_randaoMixes, umodIdx, hr, hj, ← hmix]
              have := map_toList_vset! id e.randaoMixes r mix
              simp only [List.map_id_fun, id_eq] at this
              rw [this]
              rfl
            · cases hs

omit [EthCLSpecs.Gloas.Config] in
/-- `process_participation_flag_updates` equals Etheorem's. -/
theorem participation_flag_updates_etheorem (e : EState) :
    ∃ e', runPure (EthCLSpecs.Gloas.processParticipationFlagUpdates (StateTransition := GloasRun))
        e = .ok ((), e') ∧ absEState e' = Spec.process_participation_flag_updates (absEState e) := by
  refine ⟨_, processParticipationFlagUpdates_run e, ?_⟩
  have hcap := e.validators.property
  rw [absEState_set_participation]
  simp [Spec.process_participation_flag_updates, sszOfArray, hcap, SSZList.toList]

end Steps

end WithPreset

end EpochProofs.Etheorem

namespace EpochProofs.Etheorem

section
attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig
theorem tailPresetAgrees_mainnet : TailPresetAgrees Spec.Preset.mainnet := by
  constructor <;> first | rfl | decide
end

section
attribute [local instance] EthCLSpecs.Gloas.minimal EthCLSpecs.Gloas.minimalConfig
theorem tailPresetAgrees_minimal : TailPresetAgrees Spec.Preset.minimal := by
  constructor <;> first | rfl | decide
end

end EpochProofs.Etheorem
