//! Weighted derivations, inside–outside tables and exact stochastic sampling.
//!
//! Weights are nonnegative. A derivation weight is the product of its
//! constructor weights. Equal trees produced by different derivations
//! contribute separately. Normalize by the root partition to obtain a
//! distribution when that partition is positive.

mod big;
mod expectation;
pub(crate) mod ranked;
mod rational;
mod sampling;

pub use big::{BigMaxProduct, BigRational, BigSumProduct};
pub use expectation::{Expectation, ExpectationOperator, ExpectationValue, SignedRational};
pub use rational::Rational;
pub use sampling::ExactSampler;

use crate::{tabulate_cells, Algebra, Cell, Chart, Error};

/// Supply a fixed nonnegative weight for each constructor occurrence.
pub trait WeightedOperator {
    fn weight(&self) -> Rational;
}

/// The natural logarithm of a nonnegative weight. Zero maps to negative infinity.
///
/// A single conversion from a positive rational uses an exact integer gap.
/// With round-to-nearest binary64 arithmetic and a one-ulp `ln_1p`, its
/// relative log error is bounded by four binary64 epsilons (unit weights
/// map to zero exactly). Rust gives no portable ulp guarantee for `ln_1p`.
/// The bound concerns the conversion alone. Repeated children, log-space
/// arithmetic and conversion back to a mass can change the error.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LogWeight(f64);

impl Eq for LogWeight {}

impl LogWeight {
    pub fn ln(self) -> f64 {
        self.0
    }

    pub fn mass(self) -> f64 {
        self.0.exp()
    }
}

trait Mass: Copy + Eq + std::fmt::Debug {
    const ZERO: Self;
    const ONE: Self;

    fn from_rational(value: Rational) -> Self;
    fn add(self, other: Self) -> Result<Self, Error>;
    fn mul(self, other: Self) -> Result<Self, Error>;
    fn max(self, other: Self) -> Self;

    fn product(
        weight: Self,
        mut children: impl Iterator<Item = Self> + Clone,
    ) -> Result<Self, Error> {
        if weight == Self::ZERO || children.clone().any(|child| child == Self::ZERO) {
            return Ok(Self::ZERO);
        }
        children.try_fold(weight, Self::mul)
    }
}

impl Mass for Rational {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;

    fn from_rational(value: Rational) -> Self {
        value
    }

    fn add(self, other: Self) -> Result<Self, Error> {
        self.checked_add(other)
    }

    fn mul(self, other: Self) -> Result<Self, Error> {
        self.checked_mul(other)
    }

    fn max(self, other: Self) -> Self {
        Ord::max(self, other)
    }
}

impl Mass for LogWeight {
    const ZERO: Self = Self(f64::NEG_INFINITY);
    const ONE: Self = Self(0.0);

    fn from_rational(value: Rational) -> Self {
        if value == Rational::ZERO {
            return Self::ZERO;
        }
        let (numerator, denominator) = (value.numerator(), value.denominator());
        let gap = numerator.abs_diff(denominator);
        let smaller = numerator.min(denominator);
        // ln(larger/smaller) = ln(1 + gap/smaller). Form the gap before
        // rounding, and keep the argument nonnegative even for tiny weights.
        let magnitude = (gap as f64 / smaller as f64).ln_1p();
        Self(if numerator < denominator {
            -magnitude
        } else {
            magnitude
        })
    }

    fn add(self, other: Self) -> Result<Self, Error> {
        let high = self.0.max(other.0);
        let low = self.0.min(other.0);
        if low == f64::NEG_INFINITY {
            return Ok(Self(high));
        }
        Self::finite(high + (low - high).exp().ln_1p())
    }

    fn mul(self, other: Self) -> Result<Self, Error> {
        if self == Self::ZERO || other == Self::ZERO {
            return Ok(Self::ZERO);
        }
        Self::finite(self.0 + other.0)
    }

    fn max(self, other: Self) -> Self {
        Self(self.0.max(other.0))
    }
}

impl LogWeight {
    fn finite(value: f64) -> Result<Self, Error> {
        value
            .is_finite()
            .then_some(Self(value))
            .ok_or(Error::Overflow)
    }
}

fn choose<M: Copy>(
    candidates: &[M],
    merge: impl Fn(M, M) -> Result<M, Error>,
) -> Result<Vec<M>, Error> {
    let Some((first, rest)) = candidates.split_first() else {
        return Ok(Vec::new());
    };
    Ok(vec![rest.iter().copied().try_fold(*first, merge)?])
}

macro_rules! weighted_algebra {
    ($(#[$doc:meta])* $name:ident, $mass:ty, $merge:expr) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, Default)]
        pub struct $name;

        impl<O: WeightedOperator> Algebra<O> for $name {
            type Value = $mass;

            fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
                <$mass>::product(<$mass>::from_rational(operator.weight()), children.iter().map(|&&value| value))
            }

            fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
                choose(candidates, $merge)
            }
        }
    };
}

weighted_algebra!(/// Sum of derivation weights, with exact rational arithmetic.
    SumProduct, Rational, Mass::add);
weighted_algebra!(/// Maximum derivation weight, with exact rational arithmetic.
    MaxProduct, Rational, |left, right| Ok(Mass::max(left, right)));
weighted_algebra!(/// Sum of derivation weights represented in log space.
    ///
    /// Floating-point regrouping can change the rounded value. Use the
    /// exact algebra for equality-based audits.
    LogSumProduct, LogWeight, Mass::add);
weighted_algebra!(/// Maximum derivation weight represented in log space.
    LogMaxProduct, LogWeight, |left, right| Ok(Mass::max(left, right)));

/// All-cell sum-product observations for a selected root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsideOutside<M> {
    root: Cell,
    inside: Vec<M>,
    outside: Vec<M>,
}

impl<M> InsideOutside<M> {
    pub fn inside(&self) -> &[M] {
        &self.inside
    }

    /// Sum of root context weights for one distinguished occurrence of
    /// each cell. A repeated child contributes once for each position.
    pub fn outside(&self) -> &[M] {
        &self.outside
    }

    pub fn partition(&self) -> &M {
        &self.inside[self.root]
    }
}

/// Sum all root derivation weights, returning zero for an empty root.
pub fn partition<O: WeightedOperator>(chart: &Chart<O>) -> Result<Rational, Error> {
    Ok(crate::tabulate(chart, &SumProduct)?
        .first()
        .copied()
        .unwrap_or(Rational::ZERO))
}

/// Exact inside and outside weights. Every cell has a numeric weight,
/// including zero for absent inside derivations and unreachable contexts.
pub fn inside_outside<O: WeightedOperator>(
    chart: &Chart<O>,
) -> Result<InsideOutside<Rational>, Error> {
    inside_outside_with(chart, &SumProduct)
}

/// Inside and outside weights in log space.
pub fn log_inside_outside<O: WeightedOperator>(
    chart: &Chart<O>,
) -> Result<InsideOutside<LogWeight>, Error> {
    inside_outside_with(chart, &LogSumProduct)
}

fn inside<O, M: Mass>(
    chart: &Chart<O>,
    algebra: &impl Algebra<O, Value = M>,
) -> Result<Vec<M>, Error> {
    Ok(tabulate_cells(chart, algebra)?
        .into_iter()
        .map(|cell| cell.first().copied().unwrap_or(M::ZERO))
        .collect())
}

fn inside_outside_with<O: WeightedOperator, M: Mass>(
    chart: &Chart<O>,
    algebra: &impl Algebra<O, Value = M>,
) -> Result<InsideOutside<M>, Error> {
    let inside = inside(chart, algebra)?;
    let root = chart.root();
    let mut outside = vec![M::ZERO; inside.len()];
    outside[root] = M::ONE;
    let mut suffix = Vec::new();

    for (cell, rules) in chart.cells().iter().enumerate().rev() {
        if outside[cell] == M::ZERO {
            continue;
        }
        for rule in rules {
            add_contexts(
                cell,
                &rule.operator,
                &rule.children,
                &inside,
                &mut outside,
                &mut suffix,
            )?;
        }
    }

    Ok(InsideOutside {
        root,
        inside,
        outside,
    })
}

fn add_contexts<O: WeightedOperator, M: Mass>(
    cell: Cell,
    operator: &O,
    children: &[Cell],
    inside: &[M],
    outside: &mut [M],
    suffix: &mut Vec<M>,
) -> Result<(), Error> {
    let Some((&last, earlier)) = children.split_last() else {
        return Ok(());
    };
    let weight = M::from_rational(operator.weight());
    if weight == M::ZERO {
        return Ok(());
    }
    // Two zero siblings make every position's contribution zero.
    // With one zero, only the hole in that position contributes.
    let mut zero_slots = children
        .iter()
        .enumerate()
        .filter(|&(_, &child)| inside[child] == M::ZERO);
    if let Some((hole, &child)) = zero_slots.next() {
        if zero_slots.next().is_none() {
            let context = outside[cell].mul(weight)?;
            let contribution = M::product(
                context,
                children
                    .iter()
                    .enumerate()
                    .filter(|&(slot, _)| slot != hole)
                    .map(|(_, &sibling)| inside[sibling]),
            )?;
            outside[child] = outside[child].add(contribution)?;
        }
        return Ok(());
    }
    let mut prefix = outside[cell].mul(weight)?;
    suffix.clear();
    suffix
        .try_reserve(earlier.len())
        .map_err(|_| Error::AllocationFailed)?;
    let mut tail = M::ONE;
    for &child in children.iter().skip(1).rev() {
        tail = inside[child].mul(tail)?;
        suffix.push(tail);
    }
    // Suffixes for the earlier positions are in reverse slot order.
    for (&child, &tail) in earlier.iter().zip(suffix.iter().rev()) {
        outside[child] = outside[child].add(prefix.mul(tail)?)?;
        prefix = prefix.mul(inside[child])?;
    }
    outside[last] = outside[last].add(prefix)?;
    Ok(())
}
