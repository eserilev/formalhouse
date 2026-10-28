use crate::{
    common::update_progressive_balances_cache::initialize_progressive_balances_cache,
    epoch_cache::{PreEpochCache, initialize_epoch_cache},
    per_block_processing::is_valid_deposit_signature,
    per_epoch_processing::{
        Error, ParticipationEpochSummary, deposit_writes, effective_balance, epoch_committees,
        inactivity_updates, list_writes, pending_consolidations, pending_deposits, registry_rows,
        registry_update, rewards_penalties, single_pass_step, slashings_penalty,
    },
};
use itertools::izip;
use milhouse::{AnyListIter, AnyListIterCow, Cow, List, UpdateMap, Vector};
use safe_arith::{SafeArith, SafeArithIter};
use std::cmp::max;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use swap_or_not_shuffle::Sha256Hash;
use tracing::instrument;
use typenum::Unsigned;
use types::{
    ActivationQueue, BeaconState, BeaconStateError, BuilderPendingPayment,
    BuilderPendingWithdrawal, ChainSpec, CommitteeCache, DepositData, Domain, Epoch, EpochCache,
    EthSpec, ExitCache, ForkName, ParticipationFlags, PendingDeposit, ProgressiveBalancesCache,
    RelativeEpoch, Validator,
    consts::altair::{TIMELY_HEAD_FLAG_INDEX, TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX},
};

pub struct SinglePassConfig {
    pub inactivity_updates: bool,
    pub rewards_and_penalties: bool,
    pub registry_updates: bool,
    pub slashings: bool,
    pub pending_deposits: bool,
    pub pending_consolidations: bool,
    pub effective_balance_updates: bool,
    pub proposer_lookahead: bool,
    pub builder_pending_payments: bool,
    pub ptc_window: bool,
}

impl Default for SinglePassConfig {
    fn default() -> SinglePassConfig {
        Self::enable_all()
    }
}

impl SinglePassConfig {
    pub fn enable_all() -> SinglePassConfig {
        Self {
            inactivity_updates: true,
            rewards_and_penalties: true,
            registry_updates: true,
            slashings: true,
            pending_deposits: true,
            pending_consolidations: true,
            effective_balance_updates: true,
            proposer_lookahead: true,
            builder_pending_payments: true,
            ptc_window: true,
        }
    }

    pub fn disable_all() -> SinglePassConfig {
        SinglePassConfig {
            inactivity_updates: false,
            rewards_and_penalties: false,
            registry_updates: false,
            slashings: false,
            pending_deposits: false,
            pending_consolidations: false,
            effective_balance_updates: false,
            proposer_lookahead: false,
            builder_pending_payments: false,
            ptc_window: false,
        }
    }
}

/// Values from the state that are immutable throughout epoch processing.
struct StateContext {
    current_epoch: Epoch,
    next_epoch: Epoch,
    is_in_inactivity_leak: bool,
    total_active_balance: u64,
    churn_limit: u64,
    fork_name: ForkName,
}

struct RewardsAndPenaltiesContext {
    source_increments: u64,
    target_increments: u64,
    head_increments: u64,
    active_increments: u64,
}

struct SlashingsContext {
    adjusted_total_slashing_balance: u64,
    target_withdrawable_epoch: Epoch,
    penalty_per_effective_balance_increment: u64,
}

struct PendingDepositsContext {
    /// The value to set `next_deposit_index` to *after* processing completes.
    next_deposit_index: usize,
    /// The value to set `deposit_balance_to_consume` to *after* processing completes.
    deposit_balance_to_consume: u64,
    /// Total balance increases for each validator due to pending balance deposits.
    validator_deposits_to_process: HashMap<usize, u64>,
    /// The deposits to append to `pending_deposits` after processing all applicable deposits.
    deposits_to_postpone: Vec<PendingDeposit>,
    /// New validators to be added to the state *after* processing completes.
    new_validator_deposits: Vec<PendingDeposit>,
}

struct EffectiveBalancesContext {
    downward_threshold: u64,
    upward_threshold: u64,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ValidatorInfo {
    pub index: usize,
    pub effective_balance: u64,
    pub base_reward: u64,
    pub is_eligible: bool,
    pub is_slashed: bool,
    pub is_active_current_epoch: bool,
    pub is_active_previous_epoch: bool,
    // Used for determining rewards.
    pub previous_epoch_participation: ParticipationFlags,
    // Used for updating the progressive balances cache for next epoch.
    pub current_epoch_participation: ParticipationFlags,
}

impl ValidatorInfo {
    #[inline]
    pub fn is_unslashed_participating_index(&self, flag_index: usize) -> Result<bool, Error> {
        Ok(self.is_active_previous_epoch
            && !self.is_slashed
            && self
                .previous_epoch_participation
                .has_flag(flag_index)
                .map_err(|_| Error::InvalidFlagIndex(flag_index))?)
    }
}

/// Result of single-pass epoch processing.
pub struct SinglePassEpochResult<E: EthSpec> {
    pub summary: ParticipationEpochSummary<E>,
    /// Committee cache for the lookahead epoch, built during PTC window processing.
    /// Can be installed as the Next committee cache after `advance_caches`.
    pub lookahead_committee_cache: Option<Arc<CommitteeCache>>,
}

#[instrument(skip_all)]
pub fn process_epoch_single_pass<E: EthSpec>(
    state: &mut BeaconState<E>,
    spec: &ChainSpec,
    conf: SinglePassConfig,
) -> Result<SinglePassEpochResult<E>, Error> {
    initialize_epoch_cache(state, spec)?;
    initialize_progressive_balances_cache(state, spec)?;
    state.build_exit_cache(spec)?;
    state.build_committee_cache(RelativeEpoch::Previous, spec)?;
    state.build_committee_cache(RelativeEpoch::Current, spec)?;
    state.update_pubkey_cache()?;

    let previous_epoch = state.previous_epoch();
    let current_epoch = state.current_epoch();
    let next_epoch = state.next_epoch()?;
    let total_active_balance = state.get_total_active_balance()?;
    let churn_limit = state.get_validator_churn_limit(spec)?;
    let activation_churn_limit = state.get_activation_churn_limit(spec)?;
    let finalized_checkpoint = state.finalized_checkpoint();
    let fork_name = state.fork_name_unchecked();

    // The values that are the same for all validators, computed from raw reads.
    let progressive_balances = state.progressive_balances_cache();
    let step_ctxt = single_pass_step::step_context(&single_pass_step::ContextInputs {
        current_epoch: current_epoch.as_u64(),
        finalized_epoch: finalized_checkpoint.epoch.as_u64(),
        genesis_epoch: E::genesis_epoch().as_u64(),
        total_active_balance,
        source_balance: progressive_balances
            .previous_epoch_flag_attesting_balance(TIMELY_SOURCE_FLAG_INDEX)?,
        target_balance: progressive_balances
            .previous_epoch_flag_attesting_balance(TIMELY_TARGET_FLAG_INDEX)?,
        head_balance: progressive_balances
            .previous_epoch_flag_attesting_balance(TIMELY_HEAD_FLAG_INDEX)?,
        sum_slashings: state.get_all_slashings().iter().copied().safe_sum()?,
        min_epochs_to_inactivity_penalty: spec.min_epochs_to_inactivity_penalty,
        inactivity_score_bias: spec.inactivity_score_bias,
        inactivity_score_recovery_rate: spec.inactivity_score_recovery_rate,
        inactivity_penalty_quotient: spec.inactivity_penalty_quotient_for_fork(fork_name),
        proportional_slashing_multiplier: state.get_proportional_slashing_multiplier(spec),
        epochs_per_slashings_vector: E::EpochsPerSlashingsVector::to_u64(),
        effective_balance_increment: spec.effective_balance_increment,
        hysteresis_quotient: spec.hysteresis_quotient,
        hysteresis_downward_multiplier: spec.hysteresis_downward_multiplier,
        hysteresis_upward_multiplier: spec.hysteresis_upward_multiplier,
        inactivity_updates: conf.inactivity_updates,
        rewards_and_penalties: conf.rewards_and_penalties,
        registry_updates: conf.registry_updates,
        slashings: conf.slashings,
        pending_deposits: fork_name.electra_enabled() && conf.pending_deposits,
        effective_balance_updates: conf.effective_balance_updates,
    })?;
    let is_in_inactivity_leak = step_ctxt.is_in_inactivity_leak;

    let state_ctxt = &StateContext {
        current_epoch,
        next_epoch,
        is_in_inactivity_leak,
        total_active_balance,
        churn_limit,
        fork_name,
    };

    // Contexts that require immutable access to `state`.
    let slashings_ctxt = &SlashingsContext::new(&step_ctxt);
    let mut next_epoch_cache = PreEpochCache::new_for_next_epoch(state)?;

    let pending_deposits_ctxt = if fork_name.electra_enabled() && conf.pending_deposits {
        Some(PendingDepositsContext::new(state, spec, &conf)?)
    } else {
        None
    };

    let mut earliest_exit_epoch = state.earliest_exit_epoch().ok();
    let mut exit_balance_to_consume = state.exit_balance_to_consume().ok();
    let validators_in_consolidations = get_validators_in_consolidations(state);

    // Split the state into several disjoint mutable borrows.
    let (
        mut validators,
        mut balances,
        previous_epoch_participation,
        current_epoch_participation,
        mut inactivity_scores,
        progressive_balances,
        exit_cache,
        epoch_cache,
    ) = state.mutable_validator_fields()?;

    let num_validators = validators.len();

    // Take a snapshot of the validators and participation before mutating. This is used for
    // informational purposes (e.g. by the validator monitor).
    let summary = ParticipationEpochSummary::new(
        validators.as_ref().to_owned_list(),
        previous_epoch_participation.to_owned_list(),
        current_epoch_participation.to_owned_list(),
        previous_epoch,
        current_epoch,
    );

    // Compute shared values required for different parts of epoch processing.
    let rewards_ctxt = &RewardsAndPenaltiesContext::new(&step_ctxt);

    let mut activation_queues = if !fork_name.electra_enabled() {
        let activation_queue = epoch_cache
            .activation_queue()?
            .get_validators_eligible_for_activation(
                finalized_checkpoint.epoch,
                activation_churn_limit as usize,
            );
        let next_epoch_activation_queue = ActivationQueue::default();
        Some((activation_queue, next_epoch_activation_queue))
    } else {
        None
    };
    let effective_balances_ctxt = &EffectiveBalancesContext::new(&step_ctxt);

    // After Electra, `single_pass_step` runs the first four steps for each validator.
    let single_pass_step_ctxt = if fork_name.electra_enabled() {
        Some((step_ctxt, registry_constants(fork_name, spec)))
    } else {
        None
    };

    if let Some((step_ctxt, registry_constants)) = &single_pass_step_ctxt {
        let churn = single_pass_step::ExitChurn {
            earliest_exit_epoch: earliest_exit_epoch
                .ok_or(Error::MissingEarliestExitEpoch)?
                .as_u64(),
            exit_balance_to_consume: exit_balance_to_consume
                .ok_or(Error::MissingExitBalanceToConsume)?,
        };
        let previous_epoch_participation = previous_epoch_participation.iter();
        let current_epoch_participation = current_epoch_participation.iter();
        let len = num_validators
            .min(previous_epoch_participation.len())
            .min(current_epoch_participation.len());
        let mut rows = StateRows {
            len,
            validators: validators.iter_cow(),
            balances: balances.iter_cow(),
            inactivity_scores: inactivity_scores.iter_cow(),
            previous_epoch_participation,
            current_epoch_participation,
            epoch_cache,
            exit_cache,
            progressive_balances,
            next_epoch_cache: &mut next_epoch_cache,
            deposits: pending_deposits_ctxt
                .as_ref()
                .map(|ctxt| &ctxt.validator_deposits_to_process),
            validators_in_consolidations: &validators_in_consolidations,
            state_ctxt,
            spec,
            effective_balance_updates: conf.effective_balance_updates,
        };
        let churn =
            registry_rows::single_pass_rows(&mut rows, churn, step_ctxt, registry_constants)?;
        earliest_exit_epoch = Some(Epoch::new(churn.earliest_exit_epoch));
        exit_balance_to_consume = Some(churn.exit_balance_to_consume);
    } else {
        // Iterate over the validators and related fields in one pass.
        let mut validators_iter = validators.iter_cow();
        let mut balances_iter = balances.iter_cow();
        let mut inactivity_scores_iter = inactivity_scores.iter_cow();

        for (index, &previous_epoch_participation, &current_epoch_participation) in izip!(
            0..num_validators,
            previous_epoch_participation.iter(),
            current_epoch_participation.iter(),
        ) {
            let (_, mut validator) = validators_iter
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index))?;
            let (_, mut balance) = balances_iter
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index))?;
            let (_, mut inactivity_score) = inactivity_scores_iter
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index))?;

            let is_active_current_epoch = validator.is_active_at(current_epoch);
            let is_active_previous_epoch = validator.is_active_at(previous_epoch);
            let is_eligible = is_active_previous_epoch
                || (validator.slashed
                    && previous_epoch.safe_add(1)? < validator.withdrawable_epoch);

            let base_reward = if is_eligible {
                epoch_cache.get_base_reward(index)?
            } else {
                0
            };

            let validator_info = &ValidatorInfo {
                index,
                effective_balance: validator.effective_balance,
                base_reward,
                is_eligible,
                is_slashed: validator.slashed,
                is_active_current_epoch,
                is_active_previous_epoch,
                previous_epoch_participation,
                current_epoch_participation,
            };

            if current_epoch != E::genesis_epoch() {
                // `process_inactivity_updates`
                if conf.inactivity_updates {
                    process_single_inactivity_update(
                        &mut inactivity_score,
                        validator_info,
                        state_ctxt,
                        spec,
                    )?;
                }

                // `process_rewards_and_penalties`
                if conf.rewards_and_penalties {
                    process_single_reward_and_penalty(
                        &mut balance,
                        &inactivity_score,
                        validator_info,
                        rewards_ctxt,
                        state_ctxt,
                        spec,
                    )?;
                }
            }

            // `process_registry_updates`
            if conf.registry_updates {
                let (activation_queue, next_epoch_activation_queue) = activation_queues
                    .as_mut()
                    .ok_or(Error::SinglePassMissingActivationQueue)?;
                process_single_registry_update_pre_electra(
                    &mut validator,
                    validator_info,
                    exit_cache,
                    activation_queue,
                    next_epoch_activation_queue,
                    state_ctxt,
                    spec,
                )?;
            }

            // `process_slashings`
            if conf.slashings {
                process_single_slashing(
                    &mut balance,
                    &validator,
                    slashings_ctxt,
                    state_ctxt,
                    spec,
                )?;
            }

            // `process_pending_deposits`
            if let Some(pending_balance_deposits_ctxt) = &pending_deposits_ctxt {
                process_pending_deposits_for_validator(
                    &mut balance,
                    validator_info,
                    pending_balance_deposits_ctxt,
                )?;
            }

            // `process_effective_balance_updates`
            if conf.effective_balance_updates {
                if validators_in_consolidations.contains(&validator_info.index) {
                    process_single_dummy_effective_balance_update(
                        validator_info.index,
                        &validator,
                        &mut next_epoch_cache,
                        state_ctxt,
                    )?;
                } else {
                    process_single_effective_balance_update(
                        validator_info.index,
                        *balance,
                        &mut validator,
                        validator_info.current_epoch_participation,
                        &mut next_epoch_cache,
                        progressive_balances,
                        effective_balances_ctxt,
                        state_ctxt,
                        spec,
                    )?;
                }
            }
        }
    }

    if conf.registry_updates && fork_name.electra_enabled() {
        if let Ok(earliest_exit_epoch_state) = state.earliest_exit_epoch_mut() {
            *earliest_exit_epoch_state =
                earliest_exit_epoch.ok_or(Error::MissingEarliestExitEpoch)?;
        }
        if let Ok(exit_balance_to_consume_state) = state.exit_balance_to_consume_mut() {
            *exit_balance_to_consume_state =
                exit_balance_to_consume.ok_or(Error::MissingExitBalanceToConsume)?;
        }
    }

    // Finish processing pending balance deposits if relevant.
    //
    // This *could* be reordered after `process_pending_consolidations` which pushes only to the end
    // of the `pending_deposits` list. But we may as well preserve the write ordering used
    // by the spec and do this first.
    if let Some(ctxt) = pending_deposits_ctxt {
        let mut deposits = StateDeposits {
            state,
            postponed: ctxt.deposits_to_postpone,
            next_epoch_cache: &mut next_epoch_cache,
            effective_balances_ctxt,
            state_ctxt,
            spec,
        };
        deposit_writes::apply_deposit_writes(
            &mut deposits,
            ctxt.next_deposit_index,
            ctxt.deposit_balance_to_consume,
            &ctxt.new_validator_deposits,
            conf.effective_balance_updates,
        )?;
    }

    // Process consolidations outside the single-pass loop, as they depend on balances for multiple
    // validators and cannot be computed accurately inside the loop.
    if fork_name.electra_enabled() && conf.pending_consolidations {
        process_pending_consolidations(
            state,
            &validators_in_consolidations,
            &mut next_epoch_cache,
            effective_balances_ctxt,
            conf.effective_balance_updates,
            state_ctxt,
            spec,
        )?;
    }

    // Process builder pending payments outside the single-pass loop, as they depend on balances for
    // multiple validators and cannot be computed accurately inside the loop.
    if fork_name.gloas_enabled() && conf.builder_pending_payments {
        process_builder_pending_payments(state, state_ctxt, spec)?;
    }

    // Finally, finish updating effective balance caches. We need this to happen *after* processing
    // of pending consolidations, which recomputes some effective balances.
    if conf.effective_balance_updates {
        let next_epoch_total_active_balance = next_epoch_cache.get_total_active_balance();
        state.set_total_active_balance(next_epoch, next_epoch_total_active_balance, spec);
        let next_epoch_activation_queue =
            activation_queues.map_or_else(ActivationQueue::default, |(_, queue)| queue);
        *state.epoch_cache_mut() =
            next_epoch_cache.into_epoch_cache(next_epoch_activation_queue, spec)?;
    }

    if conf.proposer_lookahead && fork_name.fulu_enabled() {
        process_proposer_lookahead(state, spec)?;
    }

    let lookahead_committee_cache = if conf.ptc_window && fork_name.gloas_enabled() {
        Some(process_ptc_window(state, spec)?)
    } else {
        None
    };

    Ok(SinglePassEpochResult {
        summary,
        lookahead_committee_cache,
    })
}

// TOOO(EIP-7917): use balances cache
pub fn process_proposer_lookahead<E: EthSpec>(
    state: &mut BeaconState<E>,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let lookahead = state.proposer_lookahead()?.clone().to_vec();

    let next_epoch = state
        .current_epoch()
        .safe_add(spec.min_seed_lookahead.as_u64())?
        .safe_add(1)?;

    // Shift out proposers in the first epoch and fill in the last epoch. Post-Gloas, slashed
    // validators are excluded from proposer selection.
    let exclude_slashed = state.fork_name_unchecked().gloas_enabled();
    let indices: Vec<usize> = state
        .validators()
        .iter()
        .enumerate()
        .filter(|(_, validator)| {
            validator.is_active_at(next_epoch) && !(exclude_slashed && validator.slashed)
        })
        .map(|(index, _)| index)
        .collect();
    let mix = *state.get_seed_mix(next_epoch, spec)?;
    let lookahead = epoch_committees::next_proposer_lookahead::<Sha256Hash, _>(
        &*state,
        &lookahead,
        &indices,
        &spec
            .get_domain_constant(Domain::BeaconProposer)
            .to_le_bytes(),
        next_epoch.as_u64(),
        &mix.0,
        next_epoch.start_slot(E::slots_per_epoch()).as_u64(),
        &selection_constants(state, spec),
    )
    .map_err(BeaconStateError::from)?;

    *state.proposer_lookahead_mut()? = Vector::new(lookahead)?;

    Ok(())
}

/// The chain constants of the balance-weighted selection.
pub(crate) fn selection_constants<E: EthSpec>(
    state: &BeaconState<E>,
    spec: &ChainSpec,
) -> epoch_committees::SelectionConstants {
    epoch_committees::SelectionConstants {
        shuffle_round_count: spec.shuffle_round_count,
        max_effective_balance: spec.max_effective_balance_for_fork(state.fork_name_unchecked()),
        slots_per_epoch: E::slots_per_epoch(),
    }
}

/// Process the PTC window, returning the committee cache built for the lookahead epoch.
///
/// The returned cache can be injected into the state's Next committee cache slot after
/// `advance_caches` is called during the epoch transition, avoiding redundant recomputation.
pub fn process_ptc_window<E: EthSpec>(
    state: &mut BeaconState<E>,
    spec: &ChainSpec,
) -> Result<Arc<CommitteeCache>, Error> {
    let slots_per_epoch = E::slots_per_epoch() as usize;

    // Compute PTC for the new lookahead epoch
    let next_epoch = state
        .current_epoch()
        .safe_add(spec.min_seed_lookahead.as_u64())?
        .safe_add(1)?;
    let start_slot = next_epoch.start_slot(E::slots_per_epoch());

    // Build a committee cache for the lookahead epoch (beyond the normal Next bound)
    let committee_cache = state.initialize_committee_cache_for_lookahead(next_epoch, spec)?;

    let mut committees = Vec::with_capacity(slots_per_epoch);
    for i in 0..slots_per_epoch {
        let slot = start_slot.safe_add(i as u64)?;
        let committee_indices: Vec<usize> = committee_cache
            .get_beacon_committees_at_slot(slot)?
            .iter()
            .flat_map(|committee| committee.committee.iter().copied())
            .collect();
        committees.push(committee_indices);
    }
    let mix = *state.get_seed_mix(next_epoch, spec)?;
    let ptcs = epoch_committees::ptc_for_epoch::<Sha256Hash, _>(
        &*state,
        &committees,
        &spec.get_domain_constant(Domain::PTCAttester).to_le_bytes(),
        next_epoch.as_u64(),
        &mix.0,
        start_slot.as_u64(),
        E::ptc_size(),
        &selection_constants(state, spec),
    )
    .map_err(BeaconStateError::from)?;

    // Convert Vector -> List to use tree-efficient pop_front.
    let window = List::from(state.ptc_window()?.clone());
    let mut window = PtcWindowWrites { state, window };
    list_writes::shift_window(&mut window, slots_per_epoch, &ptcs)?;

    Ok(committee_cache)
}

/// Processes the builder pending payments from the previous epoch.
fn process_builder_pending_payments<E: EthSpec>(
    state: &mut BeaconState<E>,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    list_writes::apply_builder_pending_payments(
        &mut StateBuilderPayments { state },
        state_ctxt.total_active_balance,
        E::slots_per_epoch(),
        E::SlotsPerEpoch::to_usize(),
        spec.builder_payment_threshold_numerator,
        spec.builder_payment_threshold_denominator,
    )?;
    Ok(())
}

impl From<list_writes::ListWritesError<Error>> for Error {
    fn from(e: list_writes::ListWritesError<Error>) -> Error {
        match e {
            list_writes::ListWritesError::Arith(e) => e.into(),
            list_writes::ListWritesError::State(e) => e,
        }
    }
}

/// The builder payment lists that `list_writes::apply_builder_pending_payments` writes.
struct StateBuilderPayments<'a, E: EthSpec> {
    state: &'a mut BeaconState<E>,
}

impl<E: EthSpec> list_writes::BuilderPaymentWrites<Error> for StateBuilderPayments<'_, E> {
    fn payments(&self) -> Result<Vec<BuilderPendingPayment>, Error> {
        Ok(self
            .state
            .builder_pending_payments()?
            .iter()
            .cloned()
            .collect())
    }

    fn push_withdrawal(&mut self, withdrawal: BuilderPendingWithdrawal) -> Result<(), Error> {
        self.state
            .builder_pending_withdrawals_mut()?
            .push(withdrawal)?;
        Ok(())
    }

    fn set_payments(&mut self, payments: Vec<BuilderPendingPayment>) -> Result<(), Error> {
        *self.state.builder_pending_payments_mut()? = Vector::new(payments)?;
        Ok(())
    }
}

/// The PTC window that `list_writes::shift_window` shifts, as a list until `commit`.
struct PtcWindowWrites<'a, E: EthSpec> {
    state: &'a mut BeaconState<E>,
    window: List<ssz_types::FixedVector<u64, E::PTCSize>, E::PtcWindowLength>,
}

impl<E: EthSpec> list_writes::WindowWrites<Vec<usize>, Error> for PtcWindowWrites<'_, E> {
    fn pop_front(&mut self, n: usize) -> Result<(), Error> {
        self.window
            .pop_front(n)
            .map_err(|e| Error::BeaconStateError(BeaconStateError::MilhouseError(e)))
    }

    fn push(&mut self, item: &Vec<usize>) -> Result<(), Error> {
        let ptc_u64: Vec<u64> = item.iter().map(|&v| v as u64).collect();
        let entry = ssz_types::FixedVector::new(ptc_u64)
            .map_err(|e| Error::BeaconStateError(BeaconStateError::SszTypesError(e)))?;
        self.window
            .push(entry)
            .map_err(|e| Error::BeaconStateError(BeaconStateError::MilhouseError(e)))
    }

    fn commit(&mut self) -> Result<(), Error> {
        *self.state.ptc_window_mut()? = Vector::try_from(self.window.clone())
            .map_err(|e| Error::BeaconStateError(BeaconStateError::MilhouseError(e)))?;
        Ok(())
    }
}

fn process_single_inactivity_update(
    inactivity_score: &mut Cow<u64>,
    validator_info: &ValidatorInfo,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let new_inactivity_score = inactivity_updates::new_inactivity_score(
        **inactivity_score,
        validator_info.is_eligible,
        validator_info.is_unslashed_participating_index(TIMELY_TARGET_FLAG_INDEX)?,
        state_ctxt.is_in_inactivity_leak,
        spec.inactivity_score_bias,
        spec.inactivity_score_recovery_rate,
    )?;

    // Only mutate when the score changes. It does not change in the common case.
    if new_inactivity_score != **inactivity_score {
        *inactivity_score.make_mut()? = new_inactivity_score;
    }

    Ok(())
}

fn process_single_reward_and_penalty(
    balance: &mut Cow<u64>,
    inactivity_score: &u64,
    validator_info: &ValidatorInfo,
    rewards_ctxt: &RewardsAndPenaltiesContext,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let new_balance = rewards_penalties::new_balance_after_rewards(
        **balance,
        validator_info.is_eligible,
        validator_info.base_reward,
        validator_info.effective_balance,
        *inactivity_score,
        validator_info.is_unslashed_participating_index(TIMELY_SOURCE_FLAG_INDEX)?,
        validator_info.is_unslashed_participating_index(TIMELY_TARGET_FLAG_INDEX)?,
        validator_info.is_unslashed_participating_index(TIMELY_HEAD_FLAG_INDEX)?,
        state_ctxt.is_in_inactivity_leak,
        rewards_ctxt.get_unslashed_participating_increments(TIMELY_SOURCE_FLAG_INDEX)?,
        rewards_ctxt.get_unslashed_participating_increments(TIMELY_TARGET_FLAG_INDEX)?,
        rewards_ctxt.get_unslashed_participating_increments(TIMELY_HEAD_FLAG_INDEX)?,
        rewards_ctxt.active_increments,
        spec.inactivity_score_bias,
        spec.inactivity_penalty_quotient_for_fork(state_ctxt.fork_name),
    )?;
    if new_balance != **balance {
        *balance.make_mut()? = new_balance;
    }
    Ok(())
}

/// Get the weight for a `flag_index` from the constant list of all weights.
impl RewardsAndPenaltiesContext {
    fn new(step_ctxt: &single_pass_step::StepContext) -> Self {
        Self {
            source_increments: step_ctxt.source_increments,
            target_increments: step_ctxt.target_increments,
            head_increments: step_ctxt.head_increments,
            active_increments: step_ctxt.active_increments,
        }
    }

    fn get_unslashed_participating_increments(&self, flag_index: usize) -> Result<u64, Error> {
        match flag_index {
            TIMELY_SOURCE_FLAG_INDEX => Ok(self.source_increments),
            TIMELY_TARGET_FLAG_INDEX => Ok(self.target_increments),
            TIMELY_HEAD_FLAG_INDEX => Ok(self.head_increments),
            _ => Err(Error::InvalidFlagIndex(flag_index)),
        }
    }
}

fn process_single_registry_update_pre_electra(
    validator: &mut Cow<Validator>,
    validator_info: &ValidatorInfo,
    exit_cache: &mut ExitCache,
    activation_queue: &BTreeSet<usize>,
    next_epoch_activation_queue: &mut ActivationQueue,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let current_epoch = state_ctxt.current_epoch;

    if validator.is_eligible_for_activation_queue(spec, state_ctxt.fork_name) {
        validator.make_mut()?.activation_eligibility_epoch = current_epoch.safe_add(1)?;
    }

    if validator.is_active_at(current_epoch) && validator.effective_balance <= spec.ejection_balance
    {
        initiate_validator_exit(validator, exit_cache, state_ctxt, None, None, spec)?;
    }

    if activation_queue.contains(&validator_info.index) {
        validator.make_mut()?.activation_epoch =
            spec.compute_activation_exit_epoch(current_epoch)?;
    }

    // Caching: add to speculative activation queue for next epoch.
    next_epoch_activation_queue.add_if_could_be_eligible_for_activation(
        validator_info.index,
        validator,
        state_ctxt.next_epoch,
        spec,
    );

    Ok(())
}

fn registry_constants(fork_name: ForkName, spec: &ChainSpec) -> registry_update::RegistryConstants {
    let gloas = fork_name.gloas_enabled();
    registry_update::RegistryConstants {
        far_future_epoch: spec.far_future_epoch.as_u64(),
        min_activation_balance: spec.min_activation_balance,
        ejection_balance: spec.ejection_balance,
        max_seed_lookahead: spec.max_seed_lookahead.as_u64(),
        min_validator_withdrawability_delay: spec.min_validator_withdrawability_delay.as_u64(),
        min_per_epoch_churn_limit: spec.min_per_epoch_churn_limit_electra,
        churn_limit_quotient: if gloas {
            spec.churn_limit_quotient_gloas
        } else {
            spec.churn_limit_quotient
        },
        effective_balance_increment: spec.effective_balance_increment,
        exit_churn_cap: if gloas {
            u64::MAX
        } else {
            spec.max_per_epoch_activation_exit_churn_limit
        },
    }
}

/// The constants of the activation churn: `get_activation_churn_limit` after Gloas and
/// `get_activation_exit_churn_limit` before.
fn activation_churn_constants(
    fork_name: ForkName,
    spec: &ChainSpec,
) -> registry_update::RegistryConstants {
    registry_update::RegistryConstants {
        exit_churn_cap: if fork_name.gloas_enabled() {
            spec.max_per_epoch_activation_churn_limit_gloas
        } else {
            spec.max_per_epoch_activation_exit_churn_limit
        },
        ..registry_constants(fork_name, spec)
    }
}

/// Writes back the fields that `single_pass_step` changed. Only changed fields are written, so
/// unchanged tree nodes stay shared.
fn write_back_row(
    old: &single_pass_step::ValidatorRow,
    new: &single_pass_step::ValidatorRow,
    validator: &mut Cow<Validator>,
    balance: &mut Cow<u64>,
    inactivity_score: &mut Cow<u64>,
    exit_cache: &mut ExitCache,
) -> Result<(), Error> {
    if new.inactivity_score != old.inactivity_score {
        *inactivity_score.make_mut()? = new.inactivity_score;
    }
    if new.balance != old.balance {
        *balance.make_mut()? = new.balance;
    }
    if new.activation_eligibility_epoch != old.activation_eligibility_epoch
        || new.activation_epoch != old.activation_epoch
        || new.exit_epoch != old.exit_epoch
        || new.withdrawable_epoch != old.withdrawable_epoch
    {
        let validator = validator.make_mut()?;
        validator.activation_eligibility_epoch = Epoch::new(new.activation_eligibility_epoch);
        validator.activation_epoch = Epoch::new(new.activation_epoch);
        validator.exit_epoch = Epoch::new(new.exit_epoch);
        validator.withdrawable_epoch = Epoch::new(new.withdrawable_epoch);
    }
    if new.effective_balance != old.effective_balance {
        validator.make_mut()?.effective_balance = new.effective_balance;
    }
    if new.exit_epoch != old.exit_epoch {
        exit_cache.record_validator_exit(Epoch::new(new.exit_epoch))?;
    }
    Ok(())
}

/// The validator rows of the state, read and written in index order by
/// `registry_rows::single_pass_rows`.
struct StateRows<'a, 'c, VU, BU, IU, PU>
where
    VU: UpdateMap<Validator>,
    BU: UpdateMap<u64>,
    IU: UpdateMap<u64>,
    PU: UpdateMap<ParticipationFlags>,
{
    len: usize,
    validators: AnyListIterCow<'a, Validator, VU>,
    balances: AnyListIterCow<'a, u64, BU>,
    inactivity_scores: AnyListIterCow<'a, u64, IU>,
    previous_epoch_participation: AnyListIter<'a, ParticipationFlags, PU>,
    current_epoch_participation: AnyListIter<'a, ParticipationFlags, PU>,
    epoch_cache: &'c EpochCache,
    exit_cache: &'c mut ExitCache,
    progressive_balances: &'c mut ProgressiveBalancesCache,
    next_epoch_cache: &'c mut PreEpochCache,
    deposits: Option<&'c HashMap<usize, u64>>,
    validators_in_consolidations: &'c BTreeSet<usize>,
    state_ctxt: &'c StateContext,
    spec: &'c ChainSpec,
    effective_balance_updates: bool,
}

fn rows_error<T, X: Into<Error>>(
    result: Result<T, X>,
) -> Result<T, registry_rows::RowsError<Error>> {
    result.map_err(|e| registry_rows::RowsError::Rows(e.into()))
}

impl From<registry_rows::RowsError<Error>> for Error {
    fn from(e: registry_rows::RowsError<Error>) -> Error {
        match e {
            registry_rows::RowsError::Step(e) => e.into(),
            registry_rows::RowsError::Rows(e) => e,
        }
    }
}

impl From<deposit_writes::DepositWritesError<Error>> for Error {
    fn from(e: deposit_writes::DepositWritesError<Error>) -> Error {
        match e {
            deposit_writes::DepositWritesError::Arith(e) => e.into(),
            deposit_writes::DepositWritesError::State(e) => e,
        }
    }
}

/// The state that `deposit_writes::apply_deposit_writes` writes after the single pass.
struct StateDeposits<'a, E: EthSpec> {
    state: &'a mut BeaconState<E>,
    postponed: Vec<PendingDeposit>,
    next_epoch_cache: &'a mut PreEpochCache,
    effective_balances_ctxt: &'a EffectiveBalancesContext,
    state_ctxt: &'a StateContext,
    spec: &'a ChainSpec,
}

impl<E: EthSpec> deposit_writes::DepositWrites<PendingDeposit, Error> for StateDeposits<'_, E> {
    fn write_queue(
        &mut self,
        next_deposit_index: usize,
        deposit_balance_to_consume: u64,
    ) -> Result<(), Error> {
        let mut new_balance_deposits: Vec<PendingDeposit> = self
            .state
            .pending_deposits()?
            .iter_from(next_deposit_index)?
            .cloned()
            .collect();
        new_balance_deposits.append(&mut self.postponed);
        self.state
            .set_pending_deposits_from_iter(new_balance_deposits)?;
        *self.state.deposit_balance_to_consume_mut()? = deposit_balance_to_consume;
        Ok(())
    }

    fn validator_index(&mut self, deposit: &PendingDeposit) -> Result<Option<usize>, Error> {
        Ok(self.state.get_validator_index(&deposit.pubkey)?)
    }

    fn amount(&self, deposit: &PendingDeposit) -> u64 {
        deposit.amount
    }

    fn balance(&self, index: usize) -> Result<u64, Error> {
        Ok(self.state.get_balance(index)?)
    }

    fn set_balance(&mut self, index: usize, balance: u64) -> Result<(), Error> {
        *self.state.get_balance_mut(index)? = balance;
        Ok(())
    }

    fn is_valid_signature(&self, deposit: &PendingDeposit) -> bool {
        let deposit_data = DepositData {
            pubkey: deposit.pubkey,
            withdrawal_credentials: deposit.withdrawal_credentials,
            amount: deposit.amount,
            signature: deposit.signature.clone(),
        };
        is_valid_deposit_signature(&deposit_data, self.spec).is_ok()
    }

    fn add_validator(&mut self, deposit: &PendingDeposit) -> Result<usize, Error> {
        Ok(self.state.add_validator_to_registry(
            deposit.pubkey,
            deposit.withdrawal_credentials,
            deposit.amount,
            self.spec,
        )?)
    }

    fn update_effective_balance(&mut self, index: usize) -> Result<(), Error> {
        update_effective_balance_at(
            self.state,
            index,
            self.next_epoch_cache,
            self.effective_balances_ctxt,
            self.state_ctxt,
            self.spec,
        )
    }
}

impl<VU, BU, IU, PU> registry_rows::RegistryRows<Error> for StateRows<'_, '_, VU, BU, IU, PU>
where
    VU: UpdateMap<Validator>,
    BU: UpdateMap<u64>,
    IU: UpdateMap<u64>,
    PU: UpdateMap<ParticipationFlags>,
{
    fn row_count(&self) -> usize {
        self.len
    }

    fn apply_step(
        &mut self,
        index: usize,
        churn: single_pass_step::ExitChurn,
        ctx: &single_pass_step::StepContext,
        constants: &registry_update::RegistryConstants,
    ) -> Result<single_pass_step::ExitChurn, registry_rows::RowsError<Error>> {
        let (_, mut validator) = rows_error(
            self.validators
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index)),
        )?;
        let (_, mut balance) = rows_error(
            self.balances
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index)),
        )?;
        let (_, mut inactivity_score) = rows_error(
            self.inactivity_scores
                .next_cow()
                .ok_or(BeaconStateError::UnknownValidator(index)),
        )?;
        let previous_epoch_participation = *rows_error(
            self.previous_epoch_participation
                .next()
                .ok_or(BeaconStateError::UnknownValidator(index)),
        )?;
        let current_epoch_participation = *rows_error(
            self.current_epoch_participation
                .next()
                .ok_or(BeaconStateError::UnknownValidator(index)),
        )?;

        let row = single_pass_step::ValidatorRow {
            balance: *balance,
            inactivity_score: *inactivity_score,
            effective_balance: validator.effective_balance,
            slashed: validator.slashed,
            activation_eligibility_epoch: validator.activation_eligibility_epoch.as_u64(),
            activation_epoch: validator.activation_epoch.as_u64(),
            exit_epoch: validator.exit_epoch.as_u64(),
            withdrawable_epoch: validator.withdrawable_epoch.as_u64(),
            previous_epoch_participation: previous_epoch_participation.into_u8(),
        };
        let is_eligible = single_pass_step::is_eligible(&row, ctx.previous_epoch)
            .map_err(registry_rows::RowsError::Step)?;
        let base_reward = if is_eligible {
            rows_error(self.epoch_cache.get_base_reward(index))?
        } else {
            0
        };
        let in_consolidation = self.validators_in_consolidations.contains(&index);
        let inputs = single_pass_step::RowInputs {
            base_reward,
            deposit: self
                .deposits
                .and_then(|deposits| deposits.get(&index).copied())
                .unwrap_or(0),
            in_consolidation,
            effective_balance_limit: validator
                .get_max_effective_balance(self.spec, self.state_ctxt.fork_name),
        };
        let (new_row, new_churn) =
            single_pass_step::single_pass_step(row, &inputs, churn, ctx, constants)
                .map_err(registry_rows::RowsError::Step)?;
        rows_error(write_back_row(
            &row,
            &new_row,
            &mut validator,
            &mut balance,
            &mut inactivity_score,
            self.exit_cache,
        ))?;

        if self.effective_balance_updates {
            if in_consolidation {
                rows_error(process_single_dummy_effective_balance_update(
                    index,
                    &validator,
                    self.next_epoch_cache,
                    self.state_ctxt,
                ))?;
            } else {
                rows_error(record_effective_balance_update(
                    index,
                    row.effective_balance,
                    &validator,
                    current_epoch_participation,
                    self.next_epoch_cache,
                    self.progressive_balances,
                    self.state_ctxt,
                ))?;
            }
        }
        Ok(new_churn)
    }
}

/// Updates the caches after `single_pass_step` ran the effective balance update of a validator.
fn record_effective_balance_update(
    validator_index: usize,
    old_effective_balance: u64,
    validator: &Validator,
    validator_current_epoch_participation: ParticipationFlags,
    next_epoch_cache: &mut PreEpochCache,
    progressive_balances: &mut ProgressiveBalancesCache,
    state_ctxt: &StateContext,
) -> Result<(), Error> {
    let new_effective_balance = validator.effective_balance;
    if new_effective_balance != old_effective_balance {
        progressive_balances.on_effective_balance_change(
            validator.slashed,
            validator_current_epoch_participation,
            old_effective_balance,
            new_effective_balance,
        )?;
    }
    next_epoch_cache.update_effective_balance(
        validator_index,
        new_effective_balance,
        validator.is_active_at(state_ctxt.next_epoch),
    )?;
    Ok(())
}

fn initiate_validator_exit(
    validator: &mut Cow<Validator>,
    exit_cache: &mut ExitCache,
    state_ctxt: &StateContext,
    earliest_exit_epoch: Option<&mut Epoch>,
    exit_balance_to_consume: Option<&mut u64>,
    spec: &ChainSpec,
) -> Result<(), Error> {
    // Return if the validator already initiated exit
    if validator.exit_epoch != spec.far_future_epoch {
        return Ok(());
    }

    let exit_queue_epoch = if state_ctxt.fork_name.electra_enabled() {
        compute_exit_epoch_and_update_churn(
            validator,
            state_ctxt,
            earliest_exit_epoch.ok_or(Error::MissingEarliestExitEpoch)?,
            exit_balance_to_consume.ok_or(Error::MissingExitBalanceToConsume)?,
            spec,
        )?
    } else {
        // Compute exit queue epoch
        let delayed_epoch = spec.compute_activation_exit_epoch(state_ctxt.current_epoch)?;
        let mut exit_queue_epoch = exit_cache
            .max_epoch()?
            .map_or(delayed_epoch, |epoch| max(epoch, delayed_epoch));
        let exit_queue_churn = exit_cache.get_churn_at(exit_queue_epoch)?;

        if exit_queue_churn >= state_ctxt.churn_limit {
            exit_queue_epoch.safe_add_assign(1)?;
        }
        exit_queue_epoch
    };

    let validator = validator.make_mut()?;
    validator.exit_epoch = exit_queue_epoch;
    validator.withdrawable_epoch =
        exit_queue_epoch.safe_add(spec.min_validator_withdrawability_delay)?;

    exit_cache.record_validator_exit(exit_queue_epoch)?;
    Ok(())
}

fn compute_exit_epoch_and_update_churn(
    validator: &mut Cow<Validator>,
    state_ctxt: &StateContext,
    earliest_exit_epoch_state: &mut Epoch,
    exit_balance_to_consume_state: &mut u64,
    spec: &ChainSpec,
) -> Result<Epoch, Error> {
    let exit_balance = validator.effective_balance;
    let mut earliest_exit_epoch = std::cmp::max(
        *earliest_exit_epoch_state,
        spec.compute_activation_exit_epoch(state_ctxt.current_epoch)?,
    );

    let per_epoch_churn = if state_ctxt.fork_name.gloas_enabled() {
        get_balance_churn_limit(state_ctxt, spec)?
    } else {
        get_activation_exit_churn_limit(state_ctxt, spec)?
    };
    // New epoch for exits
    let mut exit_balance_to_consume = if *earliest_exit_epoch_state < earliest_exit_epoch {
        per_epoch_churn
    } else {
        *exit_balance_to_consume_state
    };

    // Exit doesn't fit in the current earliest epoch
    if exit_balance > exit_balance_to_consume {
        let balance_to_process = exit_balance.safe_sub(exit_balance_to_consume)?;
        let additional_epochs = balance_to_process
            .safe_sub(1)?
            .safe_div(per_epoch_churn)?
            .safe_add(1)?;
        earliest_exit_epoch.safe_add_assign(additional_epochs)?;
        exit_balance_to_consume.safe_add_assign(additional_epochs.safe_mul(per_epoch_churn)?)?;
    }
    // Consume the balance and update state variables
    *exit_balance_to_consume_state = exit_balance_to_consume.safe_sub(exit_balance)?;
    *earliest_exit_epoch_state = earliest_exit_epoch;

    Ok(earliest_exit_epoch)
}

fn get_activation_exit_churn_limit(
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<u64, Error> {
    let max_limit = if state_ctxt.fork_name.gloas_enabled() {
        spec.max_per_epoch_activation_churn_limit_gloas
    } else {
        spec.max_per_epoch_activation_exit_churn_limit
    };
    Ok(std::cmp::min(
        max_limit,
        get_balance_churn_limit(state_ctxt, spec)?,
    ))
}

fn get_balance_churn_limit(state_ctxt: &StateContext, spec: &ChainSpec) -> Result<u64, Error> {
    let total_active_balance = state_ctxt.total_active_balance;
    let quotient = if state_ctxt.fork_name.gloas_enabled() {
        spec.churn_limit_quotient_gloas
    } else {
        spec.churn_limit_quotient
    };
    let churn = std::cmp::max(
        spec.min_per_epoch_churn_limit_electra,
        total_active_balance.safe_div(quotient)?,
    );

    Ok(churn.safe_sub(churn.safe_rem(spec.effective_balance_increment)?)?)
}

impl SlashingsContext {
    fn new(step_ctxt: &single_pass_step::StepContext) -> Self {
        Self {
            adjusted_total_slashing_balance: step_ctxt.adjusted_total_slashing_balance,
            target_withdrawable_epoch: Epoch::new(step_ctxt.target_withdrawable_epoch),
            penalty_per_effective_balance_increment: step_ctxt
                .penalty_per_effective_balance_increment,
        }
    }
}

fn process_single_slashing(
    balance: &mut Cow<u64>,
    validator: &Validator,
    slashings_ctxt: &SlashingsContext,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let new_balance = slashings_penalty::new_balance_after_slashing(
        **balance,
        validator.slashed,
        validator.withdrawable_epoch.as_u64(),
        validator.effective_balance,
        slashings_ctxt.target_withdrawable_epoch.as_u64(),
        slashings_ctxt.adjusted_total_slashing_balance,
        slashings_ctxt.penalty_per_effective_balance_increment,
        state_ctxt.total_active_balance,
        spec.effective_balance_increment,
        state_ctxt.fork_name.electra_enabled(),
    )?;
    if new_balance != **balance {
        *balance.make_mut()? = new_balance;
    }
    Ok(())
}

impl PendingDepositsContext {
    fn new<E: EthSpec>(
        state: &BeaconState<E>,
        spec: &ChainSpec,
        config: &SinglePassConfig,
    ) -> Result<Self, Error> {
        let current_epoch = state.current_epoch();
        let next_epoch = state.next_epoch()?;
        let finalized_slot = state
            .finalized_checkpoint()
            .epoch
            .start_slot(E::slots_per_epoch());
        let fulu_enabled = state.fork_name_unchecked().fulu_enabled();
        let constants = pending_deposits::DepositConstants {
            far_future_epoch: spec.far_future_epoch.as_u64(),
            ejection_balance: spec.ejection_balance,
            max_pending_deposits_per_epoch: E::max_pending_deposits_per_epoch() as u64,
            registry_updates: config.registry_updates,
        };

        // The decisions never look past `max_pending_deposits_per_epoch` deposits.
        let pending_deposits = state.pending_deposits()?;
        let mut views = Vec::new();
        let mut validator_indices = Vec::new();
        for deposit in pending_deposits
            .iter()
            .take(E::max_pending_deposits_per_epoch())
        {
            // Do not process deposit requests if pre-Fulu and the Eth1 bridge deposits are not yet applied.
            // Support for the former Eth1 bridge deposit mechanism was removed in Fulu.
            let eth1_bridge_blocked = !fulu_enabled
                && deposit.slot > spec.genesis_slot
                && state.eth1_deposit_index() < state.deposit_requests_start_index()?;
            let opt_validator_index = state.pubkey_cache().get(&deposit.pubkey);
            let view = if let Some(validator_index) = opt_validator_index {
                let validator = state.get_validator(validator_index)?;
                pending_deposits::DepositView {
                    slot: deposit.slot.as_u64(),
                    amount: deposit.amount,
                    is_known_validator: true,
                    exit_epoch: validator.exit_epoch.as_u64(),
                    withdrawable_epoch: validator.withdrawable_epoch.as_u64(),
                    activation_epoch: validator.activation_epoch.as_u64(),
                    effective_balance: validator.effective_balance,
                    eth1_bridge_blocked,
                }
            } else {
                pending_deposits::DepositView {
                    slot: deposit.slot.as_u64(),
                    amount: deposit.amount,
                    is_known_validator: false,
                    exit_epoch: 0,
                    withdrawable_epoch: 0,
                    activation_epoch: 0,
                    effective_balance: 0,
                    eth1_bridge_blocked,
                }
            };
            views.push(view);
            validator_indices.push(opt_validator_index);
        }

        let outcome = pending_deposits::process_pending_deposits(
            &views,
            finalized_slot.as_u64(),
            current_epoch.as_u64(),
            next_epoch.as_u64(),
            state.deposit_balance_to_consume()?,
            registry_update::exit_churn_limit(
                state.get_total_active_balance()?,
                &activation_churn_constants(state.fork_name_unchecked(), spec),
            )?,
            &constants,
        )?;

        let next_deposit_index = outcome.next_deposit_index as usize;
        let mut validator_deposits_to_process = HashMap::new();
        let mut deposits_to_postpone = vec![];
        let mut new_validator_deposits = vec![];
        for (i, deposit) in pending_deposits.iter().take(next_deposit_index).enumerate() {
            let postpone = outcome
                .postponed
                .get(i)
                .copied()
                .ok_or(Error::PendingDepositsLogicError)?;
            if postpone {
                deposits_to_postpone.push(deposit.clone());
            } else if let Some(Some(validator_index)) = validator_indices.get(i) {
                validator_deposits_to_process
                    .entry(*validator_index)
                    .or_insert(0)
                    .safe_add_assign(deposit.amount)?;
            } else {
                new_validator_deposits.push(deposit.clone());
            }
        }

        Ok(Self {
            next_deposit_index,
            deposit_balance_to_consume: outcome.deposit_balance_to_consume,
            validator_deposits_to_process,
            deposits_to_postpone,
            new_validator_deposits,
        })
    }
}

fn process_pending_deposits_for_validator(
    balance: &mut Cow<u64>,
    validator_info: &ValidatorInfo,
    pending_balance_deposits_ctxt: &PendingDepositsContext,
) -> Result<(), Error> {
    if let Some(deposit_amount) = pending_balance_deposits_ctxt
        .validator_deposits_to_process
        .get(&validator_info.index)
    {
        balance.make_mut()?.safe_add_assign(*deposit_amount)?;
    }
    Ok(())
}

/// Return the set of validators referenced by consolidations, either as source or target.
///
/// This function is blind to whether the consolidations are valid and capable of being processed,
/// it just returns the set of all indices present in consolidations. This is *sufficient* to
/// make consolidations play nicely with effective balance updates. The algorithm used is:
///
/// - In the single pass: apply effective balance updates for all validators *not* referenced by
///   consolidations.
/// - Apply consolidations.
/// - Apply effective balance updates for all validators previously skipped.
///
/// Prior to Electra, the empty set is returned.
fn get_validators_in_consolidations<E: EthSpec>(state: &BeaconState<E>) -> BTreeSet<usize> {
    let mut referenced_validators = BTreeSet::new();

    if let Ok(pending_consolidations) = state.pending_consolidations() {
        for pending_consolidation in pending_consolidations {
            referenced_validators.insert(pending_consolidation.source_index as usize);
            referenced_validators.insert(pending_consolidation.target_index as usize);
        }
    }

    referenced_validators
}

/// We process pending consolidations after all of single-pass epoch processing, and then patch up
/// the effective balances for affected validators.
///
/// This is safe because processing consolidations does not depend on the `effective_balance`.
fn process_pending_consolidations<E: EthSpec>(
    state: &mut BeaconState<E>,
    validators_in_consolidations: &BTreeSet<usize>,
    next_epoch_cache: &mut PreEpochCache,
    effective_balances_ctxt: &EffectiveBalancesContext,
    perform_effective_balance_updates: bool,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    // The moves only touch validators that consolidations reference, so they work on a local
    // table of those validators.
    let local_indices: Vec<usize> = validators_in_consolidations.iter().copied().collect();
    pending_consolidations::process_on_table(&mut StateConsolidations { state }, &local_indices)
        .map_err(|error| match error {
            pending_consolidations::TableError::State(e) => e,
            pending_consolidations::TableError::UnknownValidator(index) => {
                Error::from(BeaconStateError::UnknownValidator(index))
            }
            pending_consolidations::TableError::Overflow => {
                Error::from(safe_arith::ArithError::Overflow)
            }
        })?;

    // the spec tests require we don't perform effective balance updates when testing pending_consolidations
    if !perform_effective_balance_updates {
        return Ok(());
    }

    // Re-process effective balance updates for validators affected by consolidations.
    let indices: Vec<usize> = validators_in_consolidations.iter().copied().collect();
    list_writes::update_effective_balances_at(
        &mut StateEffectiveBalances {
            state,
            next_epoch_cache,
            effective_balances_ctxt,
            state_ctxt,
            spec,
        },
        &indices,
    )?;
    Ok(())
}

/// The state that `pending_consolidations::process_on_table` reads and writes.
struct StateConsolidations<'a, E: EthSpec> {
    state: &'a mut BeaconState<E>,
}

impl<E: EthSpec> pending_consolidations::ConsolidationState<Error> for StateConsolidations<'_, E> {
    fn next_epoch(&self) -> Result<u64, Error> {
        Ok(self.state.next_epoch()?.as_u64())
    }

    fn pending(&self) -> Result<Vec<pending_consolidations::PendingPair>, Error> {
        Ok(self
            .state
            .pending_consolidations()?
            .iter()
            .map(|consolidation| pending_consolidations::PendingPair {
                source: consolidation.source_index,
                target: consolidation.target_index,
            })
            .collect())
    }

    fn local_validator(&self, index: usize) -> pending_consolidations::LocalValidator {
        let validator = self.state.validators().get(index);
        pending_consolidations::LocalValidator {
            exists: validator.is_some(),
            slashed: validator.is_some_and(|validator| validator.slashed),
            withdrawable_epoch: validator
                .map_or(0, |validator| validator.withdrawable_epoch.as_u64()),
            effective_balance: validator.map_or(0, |validator| validator.effective_balance),
        }
    }

    fn balance(&self, index: usize) -> u64 {
        self.state.balances().get(index).copied().unwrap_or(0)
    }

    fn set_balance(&mut self, index: usize, value: u64) {
        if self.state.balances().get(index) != Some(&value)
            && let Ok(balance) = self.state.get_balance_mut(index)
        {
            *balance = value;
        }
    }

    fn pop_pending(&mut self, n: usize) -> Result<(), Error> {
        self.state.pending_consolidations_mut()?.pop_front(n)?;
        Ok(())
    }
}

/// The effective balances that `list_writes::update_effective_balances_at` updates.
struct StateEffectiveBalances<'a, E: EthSpec> {
    state: &'a mut BeaconState<E>,
    next_epoch_cache: &'a mut PreEpochCache,
    effective_balances_ctxt: &'a EffectiveBalancesContext,
    state_ctxt: &'a StateContext,
    spec: &'a ChainSpec,
}

impl<E: EthSpec> list_writes::EffectiveBalanceWrites<Error> for StateEffectiveBalances<'_, E> {
    fn update_effective_balance(&mut self, index: usize) -> Result<(), Error> {
        update_effective_balance_at(
            self.state,
            index,
            self.next_epoch_cache,
            self.effective_balances_ctxt,
            self.state_ctxt,
            self.spec,
        )
    }
}

/// Runs the effective balance update of validator `index` and records it in the caches.
fn update_effective_balance_at<E: EthSpec>(
    state: &mut BeaconState<E>,
    index: usize,
    next_epoch_cache: &mut PreEpochCache,
    effective_balances_ctxt: &EffectiveBalancesContext,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    let (mut validators, balances, _, current_epoch_participation, _, progressive_balances, _, _) =
        state.mutable_validator_fields()?;
    let balance = *balances
        .get(index)
        .ok_or(BeaconStateError::UnknownValidator(index))?;
    let mut validator = validators
        .get_cow(index)
        .ok_or(BeaconStateError::UnknownValidator(index))?;
    let validator_current_epoch_participation = *current_epoch_participation
        .get(index)
        .ok_or(BeaconStateError::UnknownValidator(index))?;
    process_single_effective_balance_update(
        index,
        balance,
        &mut validator,
        validator_current_epoch_participation,
        next_epoch_cache,
        progressive_balances,
        effective_balances_ctxt,
        state_ctxt,
        spec,
    )
}

impl EffectiveBalancesContext {
    fn new(step_ctxt: &single_pass_step::StepContext) -> Self {
        Self {
            downward_threshold: step_ctxt.downward_threshold,
            upward_threshold: step_ctxt.upward_threshold,
        }
    }
}

/// This function is called for validators that do not have their effective balance updated as
/// part of the single-pass loop. For these validators we compute their true effective balance
/// update after processing consolidations. However, to maintain the invariants of the
/// `PreEpochCache` we must register _some_ effective balance for them immediately.
fn process_single_dummy_effective_balance_update(
    validator_index: usize,
    validator: &Cow<Validator>,
    next_epoch_cache: &mut PreEpochCache,
    state_ctxt: &StateContext,
) -> Result<(), Error> {
    // Populate the effective balance cache with the current effective balance. This will be
    // overriden when `process_single_effective_balance_update` is called.
    let is_active_next_epoch = validator.is_active_at(state_ctxt.next_epoch);
    let temporary_effective_balance = validator.effective_balance;
    next_epoch_cache.update_effective_balance(
        validator_index,
        temporary_effective_balance,
        is_active_next_epoch,
    )?;
    Ok(())
}

/// This function abstracts over phase0 and Electra effective balance processing.
#[allow(clippy::too_many_arguments)]
fn process_single_effective_balance_update(
    validator_index: usize,
    balance: u64,
    validator: &mut Cow<Validator>,
    validator_current_epoch_participation: ParticipationFlags,
    next_epoch_cache: &mut PreEpochCache,
    progressive_balances: &mut ProgressiveBalancesCache,
    eb_ctxt: &EffectiveBalancesContext,
    state_ctxt: &StateContext,
    spec: &ChainSpec,
) -> Result<(), Error> {
    // Use the higher effective balance limit if post-Electra and compounding withdrawal credentials
    // are set.
    let effective_balance_limit = validator.get_max_effective_balance(spec, state_ctxt.fork_name);

    let old_effective_balance = validator.effective_balance;
    let new_effective_balance = effective_balance::new_effective_balance(
        balance,
        validator.effective_balance,
        effective_balance_limit,
        eb_ctxt.downward_threshold,
        eb_ctxt.upward_threshold,
        spec.effective_balance_increment,
    )?;

    let is_active_next_epoch = validator.is_active_at(state_ctxt.next_epoch);

    if new_effective_balance != old_effective_balance {
        validator.make_mut()?.effective_balance = new_effective_balance;

        // Update progressive balances cache for the *current* epoch, which will soon become the
        // previous epoch once the epoch transition completes.
        progressive_balances.on_effective_balance_change(
            validator.slashed,
            validator_current_epoch_participation,
            old_effective_balance,
            new_effective_balance,
        )?;
    }

    // Caching: update next epoch effective balances and total active balance.
    next_epoch_cache.update_effective_balance(
        validator_index,
        new_effective_balance,
        is_active_next_epoch,
    )?;

    Ok(())
}
