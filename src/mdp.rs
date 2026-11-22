//! Exact discounted reward maximization on finite Markov decision processes.

mod rational;

pub use rational::Rational;

use std::fmt;

/// An action pays its immediate reward, then samples a successor state.
/// Repeated successor entries contribute their probabilities separately.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Action {
    pub reward: Rational,
    pub transitions: Vec<(usize, Rational)>,
}

/// A proposed stationary deterministic policy and its state values.
/// Use [`Model::verify`] for independently supplied certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub policy: Vec<usize>,
    pub values: Vec<Rational>,
}

/// An immutable process with validated probability rows and discount.
#[derive(Clone, Debug)]
pub struct Model {
    discount: Rational,
    states: Vec<Vec<Action>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidDiscount,
    EmptyModel,
    NoActions {
        state: usize,
    },
    InvalidSuccessor {
        state: usize,
        action: usize,
        successor: usize,
    },
    NegativeProbability {
        state: usize,
        action: usize,
        successor: usize,
    },
    ProbabilitySum {
        state: usize,
        action: usize,
    },
    CertificateSize {
        states: usize,
        policy: usize,
        values: usize,
    },
    InvalidPolicyAction {
        state: usize,
        action: usize,
    },
    PolicyEquality {
        state: usize,
        action: usize,
    },
    BetterAction {
        state: usize,
        action: usize,
    },
    PolicySystemSize,
    PolicySystemAllocation,
    SingularPolicySystem,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InvalidDiscount => write!(f, "discount must be in [0, 1)"),
            Self::EmptyModel => write!(f, "the model needs at least one state"),
            Self::NoActions { state } => write!(f, "state {state} needs at least one action"),
            Self::InvalidSuccessor {
                state,
                action,
                successor,
            } => write!(
                f,
                "state {state}, action {action} refers to absent successor {successor}"
            ),
            Self::NegativeProbability {
                state,
                action,
                successor,
            } => write!(
                f,
                "state {state}, action {action}, successor {successor} has negative probability"
            ),
            Self::ProbabilitySum { state, action } => write!(
                f,
                "state {state}, action {action} probabilities must sum to one"
            ),
            Self::CertificateSize {
                states,
                policy,
                values,
            } => write!(
                f,
                "certificate gives {policy} actions and {values} values for {states} states"
            ),
            Self::InvalidPolicyAction { state, action } => {
                write!(f, "policy selects absent action {action} at state {state}")
            }
            Self::PolicyEquality { state, action } => write!(
                f,
                "value at state {state} differs from selected action {action}"
            ),
            Self::BetterAction { state, action } => write!(
                f,
                "action {action} exceeds the certified value at state {state}"
            ),
            Self::PolicySystemSize => write!(f, "dense policy system size overflows"),
            Self::PolicySystemAllocation => write!(f, "could not reserve the dense policy system"),
            Self::SingularPolicySystem => write!(f, "the policy system is singular"),
        }
    }
}

impl std::error::Error for Error {}

impl Model {
    /// Validate a finite, fully observed discounted process. Rewards are signed.
    pub fn new(discount: Rational, states: Vec<Vec<Action>>) -> Result<Self, Error> {
        let zero = Rational::from(0);
        let one = Rational::from(1);
        if discount < zero || discount >= one {
            return Err(Error::InvalidDiscount);
        }
        if states.is_empty() {
            return Err(Error::EmptyModel);
        }
        for (state, actions) in states.iter().enumerate() {
            if actions.is_empty() {
                return Err(Error::NoActions { state });
            }
            for (action, row) in actions.iter().enumerate() {
                let mut sum = zero.clone();
                for (successor, probability) in &row.transitions {
                    let successor = *successor;
                    if successor >= states.len() {
                        return Err(Error::InvalidSuccessor {
                            state,
                            action,
                            successor,
                        });
                    }
                    if probability < &zero {
                        return Err(Error::NegativeProbability {
                            state,
                            action,
                            successor,
                        });
                    }
                    sum = &sum + probability;
                }
                if sum != one {
                    return Err(Error::ProbabilitySum { state, action });
                }
            }
        }
        Ok(Self { discount, states })
    }

    /// Check a certificate against this model at every state. Equality for
    /// the legal selected action and domination of every other action certify
    /// the **Exact** optimal value vector and the attainment by the policy.
    pub fn verify(&self, certificate: &Certificate) -> Result<(), Error> {
        let states = self.states.len();
        let Certificate { policy, values } = certificate;
        if policy.len() != states || values.len() != states {
            return Err(Error::CertificateSize {
                states,
                policy: policy.len(),
                values: values.len(),
            });
        }
        for (state, actions) in self.states.iter().enumerate() {
            let selected = policy[state];
            let chosen = actions.get(selected).ok_or(Error::InvalidPolicyAction {
                state,
                action: selected,
            })?;
            if self.action_value(chosen, values) != values[state] {
                return Err(Error::PolicyEquality {
                    state,
                    action: selected,
                });
            }
            for (action, row) in actions.iter().enumerate() {
                if action != selected && self.action_value(row, values) > values[state] {
                    return Err(Error::BetterAction { state, action });
                }
            }
        }
        Ok(())
    }

    /// Return an **Exact**, checked policy and all of its values. Strict
    /// improvement preserves the current action on ties. Each distinct policy
    /// is evaluated by dense exact elimination.
    pub fn solve(&self) -> Result<crate::Exact<Certificate>, Error> {
        let mut policy = vec![0; self.states.len()];
        loop {
            let values = self.evaluate_policy(&policy)?;
            let mut improved = false;
            for (state, actions) in self.states.iter().enumerate() {
                let mut best = values[state].clone();
                for (action, row) in actions.iter().enumerate() {
                    let candidate = self.action_value(row, &values);
                    if candidate > best {
                        best = candidate;
                        policy[state] = action;
                        improved = true;
                    }
                }
            }
            if !improved {
                let certificate = Certificate { policy, values };
                self.verify(&certificate)?;
                return Ok(crate::Exact(certificate));
            }
        }
    }

    fn action_value(&self, action: &Action, values: &[Rational]) -> Rational {
        let expected = action
            .transitions
            .iter()
            .fold(Rational::from(0), |sum, (to, probability)| {
                &sum + &(probability * &values[*to])
            });
        &action.reward + &(&self.discount * &expected)
    }

    fn evaluate_policy(&self, policy: &[usize]) -> Result<Vec<Rational>, Error> {
        let n = self.states.len();
        let width = n.checked_add(1).ok_or(Error::PolicySystemSize)?;
        let size = n.checked_mul(width).ok_or(Error::PolicySystemSize)?;
        let mut matrix = Vec::new();
        matrix
            .try_reserve_exact(size)
            .map_err(|_| Error::PolicySystemAllocation)?;
        matrix.resize(size, Rational::from(0));
        for (state, row) in matrix.chunks_exact_mut(width).enumerate() {
            let action = &self.states[state][policy[state]];
            row[state] = Rational::from(1);
            row[n] = action.reward.clone();
            for (to, probability) in &action.transitions {
                row[*to] = &row[*to] - &(&self.discount * probability);
            }
        }

        for column in 0..n {
            let pivot = (column..n)
                .find(|&row| !matrix[row * width + column].is_zero())
                .ok_or(Error::SingularPolicySystem)?;
            for entry in column..width {
                matrix.swap(pivot * width + entry, column * width + entry);
            }
            let (leading, trailing) = matrix.split_at_mut((column + 1) * width);
            let pivot = &leading[column * width..];
            for row in trailing.chunks_exact_mut(width) {
                if row[column].is_zero() {
                    continue;
                }
                let scale = row[column].divide(&pivot[column]);
                for entry in column..width {
                    row[entry] = &row[entry] - &(&scale * &pivot[entry]);
                }
            }
        }

        let mut values = vec![Rational::from(0); n];
        for state in (0..n).rev() {
            let row = &matrix[state * width..][..width];
            let mut residual = row[n].clone();
            for next in state + 1..n {
                residual = &residual - &(&row[next] * &values[next]);
            }
            values[state] = residual.divide(&row[state]);
        }
        Ok(values)
    }
}
