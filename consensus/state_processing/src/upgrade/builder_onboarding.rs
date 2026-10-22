//! Pure core of `onboard_builders_from_pending_deposits` at the Gloas fork.
//!
//! Aeneas translates this module for the proofs in `../../proofs`. The walk over the pending
//! deposits is generic over `Onboarding`, so Aeneas does not see the state, the pubkey cache,
//! the signature cache or the hash maps. The proofs assume one contract for each trait method.

/// The reads and the lookup tables of the onboarding walk.
pub trait Onboarding<D, B, E> {
    /// Whether the pubkey of `deposit` belongs to a validator. It can update the pubkey cache.
    fn is_validator(&mut self, deposit: &D) -> Result<bool, E>;

    /// Whether `deposit` has builder withdrawal credentials.
    fn is_builder_credential(&self, deposit: &D) -> bool;

    /// Whether the signature of `deposit` is valid.
    fn is_valid_signature(&self, deposit: &D) -> bool;

    /// The builder that `deposit` registers.
    fn new_builder(&self, deposit: &D) -> Result<B, E>;

    /// Adds the amount of `deposit` to the balance of `builder`.
    fn top_up(&self, builder: &mut B, deposit: &D) -> Result<(), E>;

    /// The index of the builder with the pubkey of `deposit`, if one was added.
    fn builder_index(&self, deposit: &D) -> Option<u64>;

    /// Records that the builder with the pubkey of `deposit` has index `index`.
    fn add_builder_index(&mut self, deposit: &D, index: u64);

    /// Whether a kept deposit with the pubkey of `deposit` has a valid signature.
    fn is_pending_validator(&self, deposit: &D) -> bool;

    /// Records that a kept deposit with the pubkey of `deposit` has a valid signature.
    fn add_pending_validator(&mut self, deposit: &D);
}

/// An error of `onboard`.
pub enum OnboardingError<E> {
    /// The state failed to read.
    State(E),
    /// A builder index from the table has no builder.
    UnknownBuilder(u64),
}

/// Walks the pending deposits in order. Returns the deposits that stay in the queue and the
/// builders to add, in order.
pub fn onboard<D: Clone, B, E, S: Onboarding<D, B, E>>(
    state: &mut S,
    deposits: &[D],
) -> Result<(Vec<D>, Vec<B>), OnboardingError<E>> {
    let mut pending: Vec<D> = Vec::new();
    let mut builders: Vec<B> = Vec::new();
    let mut error: Option<OnboardingError<E>> = None;
    let mut i = 0;
    while i < deposits.len() {
        if let Some(deposit) = deposits.get(i) {
            match state.is_validator(deposit) {
                Err(e) => {
                    error = Some(OnboardingError::State(e));
                    break;
                }
                Ok(true) => pending.push(deposit.clone()),
                Ok(false) => match state.builder_index(deposit) {
                    None => {
                        if !state.is_builder_credential(deposit) {
                            pending.push(deposit.clone());
                            if state.is_valid_signature(deposit) {
                                state.add_pending_validator(deposit);
                            }
                        } else if state.is_pending_validator(deposit) {
                            pending.push(deposit.clone());
                        } else if state.is_valid_signature(deposit) {
                            match state.new_builder(deposit) {
                                Err(e) => {
                                    error = Some(OnboardingError::State(e));
                                    break;
                                }
                                Ok(builder) => {
                                    state.add_builder_index(deposit, builders.len() as u64);
                                    builders.push(builder);
                                }
                            }
                        }
                    }
                    Some(index) => match builders.get_mut(index as usize) {
                        None => {
                            error = Some(OnboardingError::UnknownBuilder(index));
                            break;
                        }
                        Some(builder) => {
                            if let Err(e) = state.top_up(builder, deposit) {
                                error = Some(OnboardingError::State(e));
                                break;
                            }
                        }
                    },
                },
            }
        }
        i = i.saturating_add(1);
    }
    match error {
        Some(error) => Err(error),
        None => Ok((pending, builders)),
    }
}
