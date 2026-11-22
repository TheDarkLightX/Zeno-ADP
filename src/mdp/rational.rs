use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Sub};

use num_bigint::BigInt;
use num_integer::Integer;

/// An exact signed fraction in lowest terms with a positive denominator.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rational {
    numerator: BigInt,
    denominator: BigInt,
}

impl Rational {
    /// Normalize the sign and reduce the fraction. A zero denominator returns `None`.
    pub fn new(numerator: BigInt, denominator: BigInt) -> Option<Self> {
        (denominator != BigInt::ZERO).then(|| Self::reduce(numerator, denominator))
    }

    fn reduce(numerator: BigInt, denominator: BigInt) -> Self {
        let mut divisor = numerator.gcd(&denominator);
        if denominator < BigInt::ZERO {
            divisor = -divisor;
        }
        Self {
            numerator: numerator / &divisor,
            denominator: denominator / divisor,
        }
    }

    pub fn numerator(&self) -> &BigInt {
        &self.numerator
    }

    pub fn denominator(&self) -> &BigInt {
        &self.denominator
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.numerator == BigInt::ZERO
    }

    pub(super) fn divide(&self, divisor: &Self) -> Self {
        Self::reduce(
            &self.numerator * &divisor.denominator,
            &self.denominator * &divisor.numerator,
        )
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self {
            numerator: value.into(),
            denominator: 1.into(),
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add for &Rational {
    type Output = Rational;

    fn add(self, other: Self) -> Rational {
        Rational::reduce(
            &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            &self.denominator * &other.denominator,
        )
    }
}

impl Sub for &Rational {
    type Output = Rational;

    fn sub(self, other: Self) -> Rational {
        Rational::reduce(
            &self.numerator * &other.denominator - &other.numerator * &self.denominator,
            &self.denominator * &other.denominator,
        )
    }
}

impl Mul for &Rational {
    type Output = Rational;

    fn mul(self, other: Self) -> Rational {
        Rational::reduce(
            &self.numerator * &other.numerator,
            &self.denominator * &other.denominator,
        )
    }
}
