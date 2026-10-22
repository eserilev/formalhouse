import EpochProofs.Formalhouse
import EpochProofs.FormalhouseFuluReachable
import EpochProofs.Sanity.Invariants.ForkUpgrade
import EpochProofs.Equiv.SinglePassLoopModel
import EpochProofs.Equiv.DepositWrites
import EpochProofs.Equiv.ListWrites
import EpochProofs.CacheBridge.BuildPath
import EpochProofs.Equiv.ConsolidationTable
import EpochProofs.Equiv.Onboarding
import EpochProofs.Equiv.EpochContexts

/-!
# Formalhouse: the final epoch results

`formalhouse_gloas_epoch_final` and `formalhouse_fulu_epoch_final` are the two final statements,
on mainnet.

- Gloas: on every input of the Gloas `process_epoch` of a run that starts in Fulu from a state
  with the genesis invariants (`FuluStartOk`) and crosses the Gloas fork (`upgrade_to_gloas`),
  Lighthouse's epoch returns `ok` and equals Etheorem's Gloas `processEpoch`. Its cache reads
  and its pubkey cache lookup equal the spec values.
- Fulu: on every input of the Fulu `process_epoch` of a reachable Fulu run, Lighthouse's Fulu
  epoch returns `ok` and equals Etheorem's Fulu `processEpoch`.

Lighthouse's epoch is the model `process_epoch_lh_order` (Fulu: `process_epoch_lh_order_fulu`).
Each step of the model is Lighthouse Rust that Aeneas translates, proved equal to the step:

- the per-validator loop: `single_pass_rows_model`, under `RowsContract`;
- the deposit writes after the loop: `apply_deposit_writes_model`, under `DepositWritesContract`;
- the builder payment writes: `apply_builder_pending_payments_equiv`, under
  `PaymentWritesContract`;
- the PTC window shift: `ptc_window_writes_spec`, under `WindowContract`;
- the effective balance updates after the consolidations: `update_effective_balances_at_spec`,
  under `EffectiveBalanceContract`;
- the pending consolidations on the local table: `process_on_table_spec`, under
  `ConsolidationStateContract` and `BTreeSetIter`;
- the builder onboarding at the Gloas fork: `onboard_spec`, under `OnboardingContract`;
- the other steps: see the step table in README.md.

The contracts (`Trusted/RegistryRows.lean`, `Trusted/EpochTail.lean`,
`Trusted/Consolidations.lean`, `Trusted/Onboarding.lean`) state what the milhouse
implementations of the traits do. They are trusted. Each `?` site of `single_pass.rs` is listed
in the error-site table of README.md with its status.

`formalhouse_gloas_epoch_final` takes the cache build facts at the state that built each cache:
the epoch cache total at a state `b` of the same epoch (`epoch_cache_total_carry`), the pubkey
cache at an earlier state `b'` completed by `update_pubkey_cache` (`pubkey_cache_carry`). The
progressive balances cache stays a fact about the epoch input.
-/

namespace EpochProofs.Formalhouse

open EthCLLib.Spec EthCLLib.Proofs SizzLean.Proofs
open EpochProofs.Etheorem EpochProofs.CacheBridge

section Gloas

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

/-- An input of the Gloas `process_epoch` in a run that starts in Fulu and crosses the Gloas
fork, on mainnet. The run carries its supply bounds: before each Fulu block, before each Gloas
block, and `EpochSupply` at each Gloas epoch input. -/
structure GloasEpochInput (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (u1 : Spec.BeaconState) : Prop where
  run : ∃ (fs t t1 : Spec.FuluState) (s2 g : Spec.BeaconState) (slot : Spec.Slot)
      (max_blobs_per_block : Spec.Epoch → Spec.Uint64) (GLOAS_FORK_EPOCH : Spec.Epoch)
      (s u : Spec.BeaconState) (slotG : Spec.Slot),
    Spec.SupplyBoundFulu o fo c init ∧
    Spec.ReachableFulu o fo c init fs ∧ slot < 2 ^ 64 ∧ Spec.SlotReachFulu o fo fs slot t ∧
    t.state.slot < slot ∧ Spec.process_slot_fulu Spec.Preset.mainnet o fo t = .ok t1 ∧
    (t1.state.slot + 1) % Spec.Preset.mainnet.SLOTS_PER_EPOCH = 0 ∧
    Spec.process_epoch_fulu_m o t1.state = .ok s2 ∧
    Spec.upgrade_to_gloas Spec.Preset.mainnet o uc
      { t1 with state := { s2 with slot := s2.slot + 1 } } = .ok g ∧
    Spec.SupplyBound o max_blobs_per_block GLOAS_FORK_EPOCH g ∧
    Spec.EpochEcon o max_blobs_per_block GLOAS_FORK_EPOCH g Spec.EpochSupply ∧
    Spec.Reachable o max_blobs_per_block GLOAS_FORK_EPOCH g s ∧ slotG < 2 ^ 64 ∧
    Spec.SlotReachG o s slotG u ∧ u.slot < slotG ∧
    Spec.process_slot Spec.Preset.mainnet o u = .ok u1 ∧
    (u1.slot + 1) % Spec.Preset.mainnet.SLOTS_PER_EPOCH = 0

/-- Every assumption of `formalhouse_gloas_epoch_final`, by kind (the cache build facts are
separate arguments of the theorem). -/
structure GloasAssumptions (o : Spec.Oracle) (init : Spec.FuluState) (e : EState) : Prop where
  /-- Start state: the Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- Reachable-state fact kept outside `EpochInputOk''`: no two validators share a pubkey. -/
  pubkeys : Spec.PubkeysUnique (absEState e)
  /-- Reachable-state fact: the SSZ vector fields have their lengths. -/
  vectors : (absEState e).VectorLengths Spec.Preset.mainnet
  /-- Time bounds: the last slot of an epoch, the next slot fits in `u64`, fewer than `2^24`
  historical summaries (`TailPre`), and the slot is `8192` below `2^64`. -/
  boundary : Spec.TailPre (absEState e)
  slot : (absEState e).slot + 8192 < 2 ^ 64
  /-- Supply and time bounds (`RowBounds`, F5). The pyspec raises without them too. -/
  rows : Spec.RowBounds (absEState e)
  /-- True pyspec preconditions and committee state facts: a sync candidate, a proposer
  candidate (F4), at least 32 active validators (F12), each selection ends within `2^64`
  passes (a probability fact), the registry size and window lengths, valid keys. -/
  committees : ∀ s, Spec.CommFrame (absEState e) s → Spec.CommConds o s ∧ Spec.CommPreconds o s
  /-- Probability fact about Etheorem (F3): its selections return all their items. -/
  selections : SelectionsFull e
  /-- Etheorem list limits from alpha.11: registry room for one epoch of deposits (F10) and
  builder pending withdrawals room (F6). beta.4 has no limit on these lists. -/
  etheoremRoom : EpochCondsIn e
  /-- Oracle: the spec Oracle agrees with Etheorem's SHA-256, roots and BLS checks, and SHA-256
  returns 32 bytes. -/
  oracle : OracleAgrees o
  sha : ∀ b : ByteArray, (sha b).size = 32

/-- The conditions of `formalhouse_gloas_epoch`, from the run and the assumptions. -/
theorem gloasEpochConds_of_run (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e) :
    GloasEpochConds o e := by
  obtain ⟨fs, t, t1, s2, g, slot, mbp, gfe, s, u, slotG, hsupply, hr, hslot64, hreach, hlt, ht,
    hz, he, hup, hsupplyG, hecon, hrg, hslotG, hreachG, hltG, hu, hzG⟩ := hin.run
  exact ⟨Spec.fulu_then_gloas_reachable_invariants o fo c uc init ha.start hsupply fs t t1 s2 g
      slot hr hslot64 hreach hlt ht hz he hup mbp gfe hsupplyG Spec.EpochSupply hecon s u
      (absEState e) slotG hrg hslotG hreachG hltG hu hzG,
    ha.pubkeys, ha.vectors, ha.boundary, ha.slot, ha.rows, ha.etheoremRoom, ha.committees,
    ha.selections, ha.oracle, ha.sha⟩

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- The Gloas statement with every cache fact stated at the epoch input. On every Gloas epoch
input of a run that starts in Fulu and crosses the Gloas fork: Lighthouse's epoch returns `ok` and equals Etheorem's `processEpoch`,
its progressive balances, epoch cache and PTC committee reads equal the spec values given the
build fact of each cache, and its pubkey cache lookup equals the spec lookup. -/
theorem formalhouse_gloas_epoch_at_input (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e)
    (cache : LhCache)
    (hcoh : Coherent EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT
      (pbState (absEState e)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH)) cache)
    (total : U64)
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        ((absEState e).validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH))
      ((absEState e).validators.map (·.effective_balance)))
    {M : Type} {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey}
    {view : M → Spec.BLSPubkey → Option Usize} (laws : CacheProofs.IndexMapLaws inst view)
    {m : M} {len : Usize}
    (hpk : CacheProofs.Coherent view m len ((absEState e).validators.map (·.pubkey))) :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      (((∃ e', (EthCLSpecs.Gloas.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ EpochProofs.Etheorem.absEState e' = s') ∧
      let s := EpochProofs.Etheorem.absEState e
      let cur := s.slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH
      (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val cur >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ f : Usize, f.val < 3 → 0 < cur →
        ∃ x : U64, lhPreviousEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val (cur - 1) >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ inc : U64, inc.val = EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT →
        ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
          EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.Preset.mainnet s =
            .ok r.val)) ∧
      (∀ (st : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32),
        Spec.get_seed Spec.Preset.mainnet o st epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed →
        ∀ (shuffling : Slice Usize) (cps spe : Usize),
        CommitteeCacheBuilt CacheProofs.Spec.CommitteeCache.Preset.mainnet o st epoch seed shuffling
          cps →
        spe.val = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        0 < (Spec.get_active_validator_indices st epoch).length →
        (Spec.get_active_validator_indices st epoch).length ≤ 2 ^ 24 →
        (Spec.get_active_validator_indices st epoch).length * (cps.val * spe.val) ≤ Usize.max →
        ∀ (start : Nat), Spec.compute_start_slot_at_epoch Spec.Preset.mainnet epoch = .ok start →
        ∀ (committees : Slice (alloc.vec.Vec Usize)),
        committees.val.length = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        CommitteesFromCache shuffling cps spe epoch start committees →
        ∀ k (hk : k < committees.val.length) l,
          Spec.ptcIndices Spec.Preset.mainnet o st epoch (start + k) = .ok l →
            (committees.val[k]).val.map (·.val) = l)) ∧
    ∀ pk, ∃ r, inst.get_index m pk = ok r ∧
      (r.map (·.val)).bind (fun i => (absEState e).validators[i]?) =
        (absEState e).validators[((absEState e).validators.map (·.pubkey)).idxOf pk]? ∧
      (r.isSome ↔ pk ∈ (absEState e).validators.map (·.pubkey)) ∧
      ∀ i, r.map (·.val) = some i → i = ((absEState e).validators.map (·.pubkey)).idxOf pk :=
  formalhouse_gloas_epoch o e (gloasEpochConds_of_run o fo c uc init e hin ha) cache hcoh total
    htotal laws hpk

end Gloas

section Fulu

attribute [local instance] EthCLSpecs.Fulu.mainnet EthCLSpecs.Fulu.mainnetConfig

variable [HasherTag] [CryptoBackend]

open EpochProofs.Etheorem.Fulu

/-- Every assumption of `formalhouse_fulu_epoch_final`, by kind. -/
structure FuluAssumptions (o : Spec.Oracle) (fo : Spec.FuluOracle) (c : Spec.FuluBlockConfig)
    (init : Spec.FuluState) (e : EState) : Prop where
  /-- Start state: the Fulu start state has the invariants of a genesis state. -/
  start : Spec.FuluStartOk init.state
  /-- Supply bounds of the run: before each Fulu block, and `EpochSupply` at each epoch input. -/
  supply : Spec.SupplyBoundFulu o fo c init
  econ : Spec.EpochEconFulu o fo c init Spec.EpochSupply
  /-- Time bounds: the epoch boundary (`TailPre`) and the slot is `8192` below `2^64`. -/
  boundary : Spec.TailPre (absEState e)
  slot : (absEState e).slot + 8192 < 2 ^ 64
  /-- Reachable-state fact: the Fulu SSZ vector fields have their lengths. -/
  vectors : (absEState e).FuluVectorLengths Spec.Preset.mainnet
  /-- Supply and time bounds (`RowBounds`, F5). -/
  rows : Spec.RowBounds (absEState e)
  /-- True pyspec preconditions and committee state facts: an active validator at the next
  epoch and at `current + 2`, each selection ends within `2^64` passes. Fulu has no F4 and no
  F12. -/
  committees : ∀ s, Spec.CommFrame (absEState e) s →
    Spec.FuluCommConds o s ∧ Spec.FuluCommPreconds o s
  /-- The Etheorem Fulu bridge conditions: Etheorem's list limits from alpha.11 (F10, the
  historical summaries room), its selections return all their items (F3), and the Electra
  proposer loop ends before pass `2^64 - 1` (`ProposerFin`, a probability fact). -/
  etheorem : FuluEpochConds Spec.Preset.mainnet o e
  /-- Oracle: the spec Oracle agrees with Etheorem, and SHA-256 returns 32 bytes. -/
  oracle : OracleAgrees o
  sha : ∀ b : ByteArray, (sha b).size = 32

/-- The final Fulu statement. On every Fulu epoch input of a reachable Fulu run, Lighthouse's
Fulu epoch returns `ok`, and its state equals Etheorem's Fulu `processEpoch`. -/
theorem formalhouse_fulu_epoch_final (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (init : Spec.FuluState) (e : EState)
    (hin : FuluEpochInput o fo c init (absEState e)) (ha : FuluAssumptions o fo c init e) :
    ∃ s', Spec.process_epoch_lh_order_fulu o (absEState e) = .ok s' ∧
      ∃ e', (EthCLSpecs.Fulu.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun)).run (pureState e) =
        .ok ((), pureState e') ∧ absEState e' = s' :=
  formalhouse_fulu_epoch_total_reachable o fo c init ha.start ha.supply ha.econ e hin
    ⟨ha.boundary, ha.etheorem, ha.oracle, ha.sha⟩ ha.slot ha.vectors ha.rows ha.committees

end Fulu

section GloasFinal

attribute [local instance] EthCLSpecs.Gloas.mainnet EthCLSpecs.Gloas.mainnetConfig

variable [HasherTag] [CryptoBackend]

open Aeneas Aeneas.Std Result in
open CacheProofs.PB (LhCache Coherent lhPreviousEpochFlagAttestingBalance
  lhCurrentEpochFlagAttestingBalance) in
/-- The final Gloas statement: `formalhouse_gloas_epoch_at_input` with the epoch cache total
built at a state `b` of the same epoch, and the pubkey cache built at an earlier state `b'` and
completed by `update_pubkey_cache`. -/
theorem formalhouse_gloas_epoch_final (o : Spec.Oracle) (fo : Spec.FuluOracle)
    (c : Spec.FuluBlockConfig) (uc : Spec.UpgradeConfig) (init : Spec.FuluState) (e : EState)
    (hin : GloasEpochInput o fo c uc init (absEState e)) (ha : GloasAssumptions o init e)
    (cache : LhCache)
    (hcoh : Coherent EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT
      (pbState (absEState e)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH)) cache)
    (total : U64) (b : Spec.BeaconState)
    (hagree : Spec.ActiveAgree ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH)
      b (absEState e))
    (htotal : total.val = CacheProofs.EpochCache.activeSum
      (CacheProofs.EpochCache.activeAt
        (b.validators.map ecValidator)
        ((absEState e).slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH))
      (b.validators.map (·.effective_balance)))
    {M : Type} {inst : types.state.pubkey_index.IndexMap M Spec.BLSPubkey}
    {view : M → Spec.BLSPubkey → Option Usize} (laws : CacheProofs.IndexMapLaws inst view)
    (b' : Spec.BeaconState) (hpre : Spec.PkPrefix b' (absEState e))
    {m0 m : M} {len0 len : Usize}
    (hpk0 : CacheProofs.Coherent view m0 len0 (b'.validators.map (·.pubkey)))
    (hupd : CacheProofs.insertAll inst m0 len0
      (((absEState e).validators.map (·.pubkey)).drop len0.val) = ok (some (m, len))) :
    ∃ s', Spec.process_epoch_lh_order o (absEState e) = .ok s' ∧
      (((∃ e', (EthCLSpecs.Gloas.processEpoch
          (StateTransition := EthCLSpecs.Proofs.Gloas.GloasRun)).run (pureState e) =
        .ok ((), pureState e') ∧ EpochProofs.Etheorem.absEState e' = s') ∧
      let s := EpochProofs.Etheorem.absEState e
      let cur := s.slot / EpochProofs.Spec.Preset.mainnet.SLOTS_PER_EPOCH
      (∀ f : Usize, f.val < 3 → ∃ x : U64, lhCurrentEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val cur >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ f : Usize, f.val < 3 → 0 < cur →
        ∃ x : U64, lhPreviousEpochFlagAttestingBalance cache f = ok (.Ok x) ∧
        (EpochProofs.Spec.get_unslashed_participating_indices EpochProofs.Spec.Preset.mainnet s
            f.val (cur - 1) >>=
          EpochProofs.Spec.get_total_balance EpochProofs.Spec.Preset.mainnet s) = .ok x.val) ∧
      (∀ inc : U64, inc.val = EpochProofs.Spec.Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT →
        ∃ r, types.state.total_active_balance.floor_total_active_balance total inc = ok r ∧
          EpochProofs.Spec.get_total_active_balance EpochProofs.Spec.Preset.mainnet s =
            .ok r.val)) ∧
      (∀ (st : Spec.BeaconState) (epoch : Nat) (seed : Spec.Bytes32),
        Spec.get_seed Spec.Preset.mainnet o st epoch Spec.DOMAIN_BEACON_ATTESTER = .ok seed →
        ∀ (shuffling : Slice Usize) (cps spe : Usize),
        CommitteeCacheBuilt CacheProofs.Spec.CommitteeCache.Preset.mainnet o st epoch seed shuffling
          cps →
        spe.val = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        0 < (Spec.get_active_validator_indices st epoch).length →
        (Spec.get_active_validator_indices st epoch).length ≤ 2 ^ 24 →
        (Spec.get_active_validator_indices st epoch).length * (cps.val * spe.val) ≤ Usize.max →
        ∀ (start : Nat), Spec.compute_start_slot_at_epoch Spec.Preset.mainnet epoch = .ok start →
        ∀ (committees : Slice (alloc.vec.Vec Usize)),
        committees.val.length = Spec.Preset.mainnet.SLOTS_PER_EPOCH →
        CommitteesFromCache shuffling cps spe epoch start committees →
        ∀ k (hk : k < committees.val.length) l,
          Spec.ptcIndices Spec.Preset.mainnet o st epoch (start + k) = .ok l →
            (committees.val[k]).val.map (·.val) = l)) ∧
    ∀ pk, ∃ r, inst.get_index m pk = ok r ∧
      (r.map (·.val)).bind (fun i => (absEState e).validators[i]?) =
        (absEState e).validators[((absEState e).validators.map (·.pubkey)).idxOf pk]? ∧
      (r.isSome ↔ pk ∈ (absEState e).validators.map (·.pubkey)) ∧
      ∀ i, r.map (·.val) = some i → i = ((absEState e).validators.map (·.pubkey)).idxOf pk :=
  formalhouse_gloas_epoch_at_input o fo c uc init e hin ha cache hcoh total
    (epoch_cache_total_carry total.val htotal hagree) laws
    (pubkey_cache_carry laws hpre hpk0 hupd)

end GloasFinal

end EpochProofs.Formalhouse
