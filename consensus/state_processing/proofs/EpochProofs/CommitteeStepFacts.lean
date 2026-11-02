import EpochProofs.AgreesEtheorem.Epoch

/-!
# The committee step facts that follow from the epoch input

The committee steps read five facts of the state that the epoch passes to them
(`Spec.CommitteeStepFacts`, Fulu: `Spec.FuluCommitteeStepFacts`). Three of them follow from the
epoch input, so the chain bundles do not assume them:

- each effective balance is at most 2048 ETH: `EBOk` holds at the epoch input
  (`ReachableInvariants`), and the steps before the committee steps keep the cap
  (`epochToCommittees_ebMax`, `epochToCommitteesFulu_ebMax`);
- the lengths of `proposer_lookahead` and, for Gloas, `ptc_window`: the state is the image of an
  Etheorem state (`epochToCommittees_etheorem`), and Etheorem holds these fields as fixed-size
  vectors (`vectorLengths_toSpecState`).

The other two, at most `2^40` validators and valid pubkeys, remain assumptions: the fields
`registrySizeAtCommitteeStepState` and `pubkeysValidAtCommitteeStepState` of the chain bundles.
-/

namespace EpochProofs.Spec

/-- The steps of the Gloas epoch before the committee steps keep each effective balance at most
`MAX_EFFECTIVE_BALANCE_ELECTRA`, from `EBOk` at the epoch input. -/
theorem epochToCommittees_ebMax [PresetCfg] (o : Oracle) (s t : BeaconState)
    (h : epochToCommittees P o s = .ok t) (hs : EBOk P s) :
    ∀ v ∈ t.validators, v.effective_balance ≤ 2048000000000 := by
  have hp := ebPresetOk_mainnet
  unfold epochToCommittees at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  obtain ⟨s8, h8, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  obtain ⟨s13, h13, h⟩ := specM_bind_ok h
  have ht : process_participation_flag_updates s13 = t := by
    simpa [pure, Except.pure] using h
  have e1 : EBOk _ s1 :=
    hs.of_validators (process_justification_and_finalization_frame _ _ _ h1).1.1
  have e2 : EBOk _ s2 := e1.of_validators (process_inactivity_updates_validators _ _ _ h2)
  have e3 : EBOk _ s3 := e2.of_validators (process_rewards_and_penalties_validators _ _ _ _ h3)
  have e4 : EBOk _ s4 := process_registry_updates_ebOk _ _ _ _ h4 e3
  have e5 : EBOk _ s5 := e4.of_validators (process_slashings_validators _ _ _ _ h5)
  have e6 : EBOk _ s6 := e5.of_validators (process_eth1_data_reset_frame _ _ _ h6).1.1
  have e7 : EBOk _ s7 := process_pending_deposits_ebOk _ o hp _ _ _ h7 e6
  have e8 : EBOk _ s8 := e7.of_validators (process_pending_consolidations_validators _ _ _ h8)
  have e9 : EBOk _ s9 :=
    e8.of_validators (process_builder_pending_payments_validators _ _ _ _ h9)
  have hmax := process_effective_balance_updates_le_max _ hp _ _ hysteresisThresholds_mainnet
    s9 s10 h10 fun v hv => (e9 v hv).2
  have f : RegistryFrame s10 t := ht ▸
    (process_slashings_reset_frame _ _ _ h11).1.trans
    ((process_randao_mixes_reset_frame _ _ _ h12).1.trans
    ((process_historical_summaries_update_frame _ o _ _ h13).1.trans
    (process_participation_flag_updates_frame _).1))
  intro v hv
  rw [← P_maxeb]
  exact hmax v (f.1 ▸ hv)

/-- The steps of the Fulu epoch before the committee steps keep each effective balance at most
`MAX_EFFECTIVE_BALANCE_ELECTRA`, from `EBOk` at the epoch input. -/
theorem epochToCommitteesFulu_ebMax [PresetCfg] [FuluCfg] [FuluCfg.Ok] (o : Oracle)
    (s t : BeaconState) (h : epochToCommitteesFulu P FC o s = .ok t) (hs : EBOk P s) :
    ∀ v ∈ t.validators, v.effective_balance ≤ 2048000000000 := by
  have hp := ebPresetOk_mainnet
  unfold epochToCommitteesFulu at h
  simp only [process_registry_updates_fulu_eq P FC fuluCompat,
    process_pending_deposits_fulu_tab_eq P FC fuluCompat] at h
  obtain ⟨s1, h1, h⟩ := specM_bind_ok h
  obtain ⟨s2, h2, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s3, h3, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s4, h4, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s5, h5, h⟩ := specM_bind_ok h
  obtain ⟨s6, h6, h⟩ := specM_bind_ok h
  obtain ⟨_, -, h⟩ := specM_bind_ok h
  obtain ⟨s7, h7, h⟩ := specM_bind_ok h
  obtain ⟨s8, h8, h⟩ := specM_bind_ok h
  obtain ⟨s9, h9, h⟩ := specM_bind_ok h
  obtain ⟨s10, h10, h⟩ := specM_bind_ok h
  obtain ⟨s11, h11, h⟩ := specM_bind_ok h
  obtain ⟨s12, h12, h⟩ := specM_bind_ok h
  have ht : process_participation_flag_updates s12 = t := by
    simpa [pure, Except.pure] using h
  have e1 : EBOk _ s1 :=
    hs.of_validators (process_justification_and_finalization_frame _ _ _ h1).1.1
  have e2 : EBOk _ s2 := e1.of_validators (process_inactivity_updates_validators _ _ _ h2)
  have e3 : EBOk _ s3 := e2.of_validators (process_rewards_and_penalties_validators _ _ _ _ h3)
  have e4 : EBOk _ s4 := process_registry_updates_ebOk _ _ _ _ h4 e3
  have e5 : EBOk _ s5 := e4.of_validators (process_slashings_validators _ _ _ _ h5)
  have e6 : EBOk _ s6 := e5.of_validators (process_eth1_data_reset_frame _ _ _ h6).1.1
  have e7 : EBOk _ s7 := process_pending_deposits_ebOk _ o hp _ _ _ h7 e6
  have e8 : EBOk _ s8 := e7.of_validators (process_pending_consolidations_validators _ _ _ h8)
  have hmax := process_effective_balance_updates_le_max _ hp _ _ hysteresisThresholds_mainnet
    s8 s9 h9 fun v hv => (e8 v hv).2
  have f : RegistryFrame s9 t := ht ▸
    (process_slashings_reset_frame _ _ _ h10).1.trans
    ((process_randao_mixes_reset_frame _ _ _ h11).1.trans
    ((process_historical_summaries_update_frame _ o _ _ h12).1.trans
    (process_participation_flag_updates_frame _).1))
  intro v hv
  rw [← P_maxeb]
  exact hmax v (f.1 ▸ hv)

end EpochProofs.Spec

namespace EpochProofs.Etheorem

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Gloas

variable [EthCLSpecs.Gloas.Preset] [EthCLSpecs.Gloas.Config] [HasherTag] [CryptoBackend]

/-- Gloas: the committee step facts at the state that the epoch passes to the committee steps,
from the epoch input, the validator count and the pubkeys. The effective balance cap is carried from the
input (`epochToCommittees_ebMax`), and the lookahead and PTC window lengths hold because that
state is the image of an Etheorem state (`epochToCommittees_etheorem`). -/
theorem committeeStepFacts_of_etheorem [Spec.PresetCfg] [Spec.PresetCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P) (o : Spec.Oracle) (ho : OracleAgrees o) (e : EtheoremState)
    (hb0 : Spec.BoundaryOk (toSpecState e)) (hslot : (toSpecState e).slot < 2 ^ 64)
    (heb : Spec.EBOk Spec.P (toSpecState e))
    (hin : GloasEtheoremDivergenceAssumptions e)
    (hhist : (toSpecState e).historical_summaries.length < EthCLSpecs.Gloas.Const.historicalRootsLimit)
    {t : Spec.BeaconState} (ht : Spec.epochToCommittees Spec.P o (toSpecState e) = .ok t)
    (hregLen : t.validators.length ≤ 2 ^ 40)
    (hkeys : ∀ v ∈ t.validators, o.bls_KeyValidate v.pubkey = true) : Spec.CommitteeStepFacts o t := by
  obtain ⟨e14, -, rfl⟩ := epochToCommittees_etheorem hpa o ho e hb0 hslot hin hhist ht
  have hvec := vectorLengths_toSpecState hpa e14
  unfold Spec.BeaconState.VectorLengths at hvec
  obtain ⟨-, -, -, -, -, -, -, hpl, -, -, hptc, -⟩ := hvec
  rw [Spec.P_min_seed] at hpl hptc
  exact ⟨hregLen, Spec.epochToCommittees_ebMax o _ _ ht heb, hpl, hptc, hkeys⟩

end EpochProofs.Etheorem

namespace EpochProofs.Etheorem.Fulu

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs EthCLSpecs.Proofs.Fulu

variable [EthCLSpecs.Fulu.Preset] [EthCLSpecs.Fulu.Config] [HasherTag] [CryptoBackend]

/-- Fulu: the committee step facts at the state that the epoch passes to the committee steps,
from the epoch input, the validator count and the pubkeys. -/
theorem fuluCommitteeStepFacts_of_etheorem [Spec.PresetCfg] [Spec.FuluCfg] [Spec.FuluCfg.Ok]
    (hpa : PresetMatchesEtheorem Spec.P Spec.FC) (o : Spec.Oracle) (ho : OracleAgrees o)
    (e : EtheoremState) (hc : FuluEtheoremBridgeConditions Spec.P o e)
    (heb : Spec.EBOk Spec.P (toSpecState e))
    {t : Spec.BeaconState} (ht : Spec.epochToCommitteesFulu Spec.P Spec.FC o (toSpecState e) = .ok t)
    (hregLen : t.validators.length ≤ 2 ^ 40)
    (hkeys : ∀ v ∈ t.validators, o.bls_KeyValidate v.pubkey = true) : Spec.FuluCommitteeStepFacts o t := by
  obtain ⟨e13, -, rfl⟩ := epochToCommitteesFulu_etheorem hpa o ho e hc ht
  have hvec := fuluVectorLengths_toSpecState hpa e13
  unfold Spec.BeaconState.FuluVectorLengths at hvec
  obtain ⟨-, -, -, -, -, -, -, hpl⟩ := hvec
  rw [Spec.P_min_seed] at hpl
  exact ⟨hregLen, Spec.epochToCommitteesFulu_ebMax o _ _ ht heb, hpl, hkeys⟩

end EpochProofs.Etheorem.Fulu
