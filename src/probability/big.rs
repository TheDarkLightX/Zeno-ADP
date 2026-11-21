use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul};

use num_bigint::BigUint;
use num_integer::Integer;

use crate::provenance::CommutativeSemiring;
use crate::Error;

use super::Rational;

/// A nonnegative fraction in lowest terms with arbitrary-precision integers.
/// Use for exact reference audits whose weights or results exceed `u128`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BigRational {
    numerator: BigUint,
    denominator: BigUint,
}

impl BigRational {
    /// Reduce the fraction. A zero denominator returns `None`.
    pub fn new(numerator: BigUint, denominator: BigUint) -> Option<Self> {
        if denominator == BigUint::ZERO {
            return None;
        }
        let divisor = numerator.gcd(&denominator);
        Some(Self {
            numerator: numerator / &divisor,
            denominator: denominator / divisor,
        })
    }

    pub fn numerator(&self) -> &BigUint {
        &self.numerator
    }

    pub fn denominator(&self) -> &BigUint {
        &self.denominator
    }
}

impl From<Rational> for BigRational {
    fn from(value: Rational) -> Self {
        Self {
            numerator: value.numerator().into(),
            denominator: value.denominator().into(),
        }
    }
}

impl fmt::Display for BigRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl Ord for BigRational {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }
}

impl PartialOrd for BigRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add for &BigRational {
    type Output = BigRational;

    fn add(self, other: Self) -> BigRational {
        let common = self.denominator.gcd(&other.denominator);
        let left = &self.denominator / &common;
        let right = &other.denominator / &common;
        let numerator = &self.numerator * right + &other.numerator * &left;
        // The two reduced inputs leave primes in the shared factor as
        // the only possible common factors of the sum and denominator.
        let cancel = numerator.gcd(&common);
        BigRational {
            numerator: numerator / &cancel,
            denominator: left * (&other.denominator / cancel),
        }
    }
}

impl Mul for &BigRational {
    type Output = BigRational;

    fn mul(self, other: Self) -> BigRational {
        let left = self.numerator.gcd(&other.denominator);
        let right = other.numerator.gcd(&self.denominator);
        BigRational {
            numerator: (&self.numerator / &left) * (&other.numerator / &right),
            denominator: (&self.denominator / right) * (&other.denominator / left),
        }
    }
}

macro_rules! big_semiring {
    ($(#[$doc:meta])* $name:ident, $add:expr) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, Default)]
        pub struct $name;

        impl CommutativeSemiring for $name {
            type Value = BigRational;

            fn zero(&self) -> BigRational {
                Rational::ZERO.into()
            }

            fn one(&self) -> BigRational {
                Rational::ONE.into()
            }

            fn add(&self, left: &BigRational, right: &BigRational) -> Result<BigRational, Error> {
                Ok(($add)(left, right))
            }

            fn multiply(&self, left: &BigRational, right: &BigRational) -> Result<BigRational, Error> {
                Ok(left * right)
            }
        }
    };
}

big_semiring!(
    /// Sum-product on nonnegative big-integer rationals. Pair with
    /// [`crate::provenance::SemiringAlgebra`] for a reference audit.
    BigSumProduct, Add::add
);
big_semiring!(
    /// Max-product on nonnegative big-integer rationals. Pair with
    /// [`crate::provenance::SemiringAlgebra`] for a reference audit.
    BigMaxProduct, |left: &BigRational, right: &BigRational| left.max(right).clone()
);
