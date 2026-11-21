use super::{choose, Rational};
use crate::{fast::Fold, Algebra, Error};

/// A signed exact fraction with the same checked magnitude as [`Rational`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SignedRational {
    magnitude: Rational,
    negative: bool,
}

impl SignedRational {
    pub const ZERO: Self = Self::new(Rational::ZERO, false);

    /// Attach a sign to a magnitude. Zero has a unique representation.
    pub const fn new(magnitude: Rational, negative: bool) -> Self {
        Self {
            negative: negative && magnitude.numerator() != 0,
            magnitude,
        }
    }

    pub fn magnitude(self) -> Rational {
        self.magnitude
    }

    pub fn is_negative(self) -> bool {
        self.negative
    }

    pub fn checked_add(self, other: Self) -> Result<Self, Error> {
        if self.negative == other.negative {
            return Ok(Self::new(
                self.magnitude.checked_add(other.magnitude)?,
                self.negative,
            ));
        }
        if self.magnitude == other.magnitude {
            return Ok(Self::ZERO);
        }
        let negative = if self.magnitude > other.magnitude {
            self.negative
        } else {
            other.negative
        };
        Ok(Self::new(
            self.magnitude.checked_abs_diff(other.magnitude)?,
            negative,
        ))
    }

    pub fn checked_scale(self, factor: Rational) -> Result<Self, Error> {
        Ok(Self::new(
            self.magnitude.checked_mul(factor)?,
            self.negative,
        ))
    }

    /// Returns `Ok(None)` for division by zero.
    pub fn checked_div(self, divisor: Rational) -> Result<Option<Self>, Error> {
        Ok(self
            .magnitude
            .checked_div(divisor)?
            .map(|magnitude| Self::new(magnitude, self.negative)))
    }
}

impl From<Rational> for SignedRational {
    fn from(magnitude: Rational) -> Self {
        Self::new(magnitude, false)
    }
}

/// A derivation's mass and one signed first-order component.
///
/// With an additive feature, the component is the unnormalized weighted
/// feature total. With differentiable local weights, it is the derivative
/// of the mass in one chosen direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExpectationValue {
    pub mass: Rational,
    pub moment: SignedRational,
}

impl ExpectationValue {
    /// Lift a local additive feature into the expectation semiring.
    pub fn weighted_feature(mass: Rational, feature: SignedRational) -> Result<Self, Error> {
        Ok(Self {
            mass,
            moment: feature.checked_scale(mass)?,
        })
    }

    /// Divide the first-order component by mass. Zero mass returns `Ok(None)`.
    /// For a feature this is its expectation. For a derivative this is the
    /// directional derivative of the log mass.
    pub fn normalized(self) -> Result<Option<SignedRational>, Error> {
        self.moment.checked_div(self.mass)
    }

    fn sum(self, other: Self) -> Result<Self, Error> {
        Ok(Self {
            mass: self.mass.checked_add(other.mass)?,
            moment: self.moment.checked_add(other.moment)?,
        })
    }

    fn product(self, other: Self) -> Result<Self, Error> {
        Ok(Self {
            mass: self.mass.checked_mul(other.mass)?,
            moment: self
                .moment
                .checked_scale(other.mass)?
                .checked_add(other.moment.checked_scale(self.mass)?)?,
        })
    }
}

/// Supply the mass and first-order component of each constructor occurrence.
pub trait ExpectationOperator {
    fn expectation(&self) -> Result<ExpectationValue, Error>;
}

/// Sum mass and one first-order component over derivation occurrences.
///
/// An inhabited cell with zero mass still carries a summary. In particular
/// a zero local mass may have a nonzero derivative. Intermediate fractions
/// use checked arithmetic, including when values cancel later.
#[derive(Debug, Clone, Copy, Default)]
pub struct Expectation;

impl<O: ExpectationOperator> Algebra<O> for Expectation {
    type Value = ExpectationValue;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        children
            .iter()
            .map(|&&child| child)
            .try_fold(operator.expectation()?, ExpectationValue::product)
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        choose(candidates, ExpectationValue::sum)
    }
}

impl<O: ExpectationOperator> Fold<O> for Expectation {
    type Value = ExpectationValue;

    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a Self::Value> + Clone,
    ) -> Result<Self::Value, Error> {
        children
            .copied()
            .try_fold(operator.expectation()?, ExpectationValue::product)
    }

    fn merge(&self, selected: &mut Option<Self::Value>, next: Self::Value) -> Result<(), Error> {
        *selected = Some(match *selected {
            Some(previous) => previous.sum(next)?,
            None => next,
        });
        Ok(())
    }
}
