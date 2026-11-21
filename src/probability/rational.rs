use std::cmp::Ordering;
use std::num::NonZeroU128;

use crate::Error;

/// A nonnegative, reduced fraction with checked `u128` arithmetic.
///
/// Individual operations may require an intermediate integer wider than
/// `u128`. An unrepresentable intermediate returns [`Error::Overflow`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    numerator: u128,
    denominator: NonZeroU128,
}

impl Rational {
    pub const ZERO: Self = Self {
        numerator: 0,
        denominator: NonZeroU128::MIN,
    };
    pub const ONE: Self = Self {
        numerator: 1,
        denominator: NonZeroU128::MIN,
    };

    /// Reduce a fraction. A zero denominator returns `None`.
    pub fn new(numerator: u128, denominator: u128) -> Option<Self> {
        let denominator = NonZeroU128::new(denominator)?;
        let divisor = gcd(numerator, denominator.get());
        Some(Self::from_reduced(
            numerator / divisor,
            denominator.get() / divisor,
        ))
    }

    fn from_reduced(numerator: u128, denominator: u128) -> Self {
        Self {
            numerator,
            denominator: NonZeroU128::new(denominator).expect("positive denominator"),
        }
    }

    pub fn numerator(self) -> u128 {
        self.numerator
    }

    pub fn denominator(self) -> u128 {
        self.denominator.get()
    }

    pub fn checked_add(self, other: Self) -> Result<Self, Error> {
        let g = gcd(self.denominator(), other.denominator());
        let b = self.denominator() / g;
        let d = other.denominator() / g;
        let numerator = self
            .numerator
            .checked_mul(d)
            .and_then(|left| {
                other
                    .numerator
                    .checked_mul(b)
                    .and_then(|right| left.checked_add(right))
            })
            .ok_or(Error::Overflow)?;
        let cancel = gcd(numerator, g);
        let denominator = b
            .checked_mul(other.denominator() / cancel)
            .ok_or(Error::Overflow)?;
        Ok(Self::from_reduced(numerator / cancel, denominator))
    }

    pub fn checked_mul(self, other: Self) -> Result<Self, Error> {
        self.multiply(other.numerator, other.denominator())
    }

    /// Returns `Ok(None)` for division by zero.
    pub fn checked_div(self, other: Self) -> Result<Option<Self>, Error> {
        if other == Self::ZERO {
            return Ok(None);
        }
        self.multiply(other.denominator(), other.numerator)
            .map(Some)
    }

    fn multiply(self, numerator: u128, denominator: u128) -> Result<Self, Error> {
        let left = gcd(self.numerator, denominator);
        let right = gcd(numerator, self.denominator());
        let numerator = (self.numerator / left)
            .checked_mul(numerator / right)
            .ok_or(Error::Overflow)?;
        let denominator = (self.denominator() / right)
            .checked_mul(denominator / left)
            .ok_or(Error::Overflow)?;
        Ok(Self::from_reduced(numerator, denominator))
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        let (mut a, mut b) = (self.numerator, self.denominator());
        let (mut c, mut d) = (other.numerator, other.denominator());
        let mut reverse = false;
        loop {
            let quotient = (a / b).cmp(&(c / d));
            let (r, s) = (a % b, c % d);
            let order = match (quotient, r == 0, s == 0) {
                (Ordering::Equal, false, false) => {
                    // Invert the two nonzero fractional remainders. This
                    // reverses their order and decreases the denominators.
                    (a, b, c, d) = (b, r, d, s);
                    reverse = !reverse;
                    continue;
                }
                (Ordering::Equal, _, _) => r.cmp(&s),
                (order, _, _) => order,
            };
            return if reverse { order.reverse() } else { order };
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
