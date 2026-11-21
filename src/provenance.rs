//! Canonical rule-label polynomials for commutative-semiring questions.

use std::collections::BTreeMap;
use std::fmt::Debug;

pub use num_bigint::BigUint;

use crate::{reserve_table, Algebra, Error};

/// A commutative semiring. Implementations must satisfy the additive and
/// multiplicative monoid laws, distributivity and zero annihilation.
/// Fallible implementations give the correspondence on domains where
/// both evaluations succeed. The trait does not test these laws.
pub trait CommutativeSemiring {
    type Value: Clone + Debug + Eq;

    fn zero(&self) -> Self::Value;
    fn one(&self) -> Self::Value;
    fn add(&self, left: &Self::Value, right: &Self::Value) -> Result<Self::Value, Error>;
    fn multiply(&self, left: &Self::Value, right: &Self::Value) -> Result<Self::Value, Error>;
}

/// A direct semiring question with a local weight for each constructor.
pub struct SemiringAlgebra<S, W> {
    semiring: S,
    weight: W,
}

impl<S, W> SemiringAlgebra<S, W> {
    pub fn new(semiring: S, weight: W) -> Self {
        Self { semiring, weight }
    }
}

impl<O, S: CommutativeSemiring, W: Fn(&O) -> S::Value> Algebra<O> for SemiringAlgebra<S, W> {
    type Value = S::Value;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        children
            .iter()
            .try_fold((self.weight)(operator), |value, child| {
                self.semiring.multiply(&value, child)
            })
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        let Some((first, rest)) = candidates.split_first() else {
            return Ok(Vec::new());
        };
        let value = rest
            .iter()
            .try_fold(first.clone(), |value, next| self.semiring.add(&value, next))?;
        Ok(vec![value])
    }
}

/// A polynomial in rule labels with arbitrary-precision natural coefficients.
/// A monomial is a sorted list of labels, including repeated factors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial<K> {
    terms: BTreeMap<Vec<K>, BigUint>,
}

impl<K: Clone + Ord> Polynomial<K> {
    /// The polynomial's nonzero terms in monomial order. The coefficient counts
    /// derivations with that label multiset.
    pub fn terms(&self) -> impl ExactSizeIterator<Item = (&[K], &BigUint)> {
        self.terms
            .iter()
            .map(|(factors, count)| (factors.as_slice(), count))
    }

    fn multiply(&self, other: &Self) -> Result<Self, Error> {
        let mut terms = BTreeMap::<_, BigUint>::new();
        for (left, a) in self.terms() {
            for (right, b) in other.terms() {
                let len = left.len().checked_add(right.len()).ok_or(Error::Overflow)?;
                let mut factors = reserve_table(len)?;
                factors.extend_from_slice(left);
                factors.extend_from_slice(right);
                factors.sort_unstable();
                *terms.entry(factors).or_default() += a * b;
            }
        }
        Ok(Self { terms })
    }

    /// Substitute a weight per label and evaluate this answer in a commutative
    /// semiring. Use the same weight for all occurrences of each label.
    pub fn evaluate<S: CommutativeSemiring>(
        &self,
        semiring: &S,
        weight: impl Fn(&K) -> S::Value,
    ) -> Result<S::Value, Error> {
        let mut sum = semiring.zero();
        for (factors, count) in self.terms() {
            let value = factors.iter().try_fold(semiring.one(), |value, key| {
                semiring.multiply(&value, &weight(key))
            })?;
            // Binary doubling takes a number of additions proportional
            // to the coefficient's bit length.
            let mut term = value.clone();
            for bit in (0..count.bits() - 1).rev() {
                term = semiring.add(&term, &term)?;
                if count.bit(bit) {
                    term = semiring.add(&term, &value)?;
                }
            }
            sum = semiring.add(&sum, &term)?;
        }
        Ok(sum)
    }
}

/// Record the multiset of local labels responsible for each derivation.
///
/// Tabulate once and use [`Polynomial::evaluate`] on any inhabited cell to
/// answer multiple commutative-semiring questions. A rule's weight in a
/// projected question must depend only on its label. To distinguish equal
/// constructors at different sites, include the site in the operator payload
/// and the label. This representation forgets tree shape and child order.
/// Its explicit monomial support can grow with the number of derivations.
pub struct Provenance<F>(F);

impl<F> Provenance<F> {
    pub fn new(label: F) -> Self {
        Self(label)
    }
}

impl<O, K: Clone + Debug + Ord, F: Fn(&O) -> K> Algebra<O> for Provenance<F> {
    type Value = Polynomial<K>;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        let label = (self.0)(operator);
        let value = Polynomial {
            terms: BTreeMap::from([(vec![label], BigUint::from(1u8))]),
        };
        children
            .iter()
            .try_fold(value, |product, child| product.multiply(child))
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        if candidates.is_empty() {
            return Ok(Vec::new());
        }
        let mut terms = BTreeMap::<_, BigUint>::new();
        for candidate in candidates {
            for (factors, count) in candidate.terms() {
                *terms.entry(factors.to_vec()).or_default() += count;
            }
        }
        Ok(vec![Polynomial { terms }])
    }
}
