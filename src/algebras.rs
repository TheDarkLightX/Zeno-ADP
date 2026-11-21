use crate::{Algebra, Error, Tree};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Cost {
    Finite(i64),
    Infinity,
}

impl Cost {
    pub fn plus(self, other: Self) -> Result<Self, Error> {
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => {
                a.checked_add(b).map(Self::Finite).ok_or(Error::Overflow)
            }
            _ => Ok(Self::Infinity),
        }
    }
}

pub trait ScoredOperator {
    fn cost(&self) -> Cost;
}

/// Additive minimum with attainable infinity. This is equivalent to
/// `Additive::new(CostPolicy::AttainableInfinity)`. If any operand is infinite,
/// the rule yields infinity. Otherwise the ordered partial sums must fit in
/// `i64`. Use [`Additive`] for an explicit policy.
pub struct Minimum;

impl<O: ScoredOperator> Algebra<O> for Minimum {
    type Value = Cost;

    fn apply(&self, operator: &O, children: &[&Cost]) -> Result<Cost, Error> {
        Additive::new(CostPolicy::AttainableInfinity).apply(operator, children)
    }

    fn choose(&self, candidates: &[Cost]) -> Result<Vec<Cost>, Error> {
        <Additive as Algebra<O>>::choose(&Additive::new(CostPolicy::AttainableInfinity), candidates)
    }
}

/// Count derivation occurrences. For distinct terms use [`crate::queries::count`].
pub struct Count;

impl<O> Algebra<O> for Count {
    type Value = u128;

    fn apply(&self, _operator: &O, children: &[&u128]) -> Result<u128, Error> {
        count_product(children.iter().map(|&&n| n))
    }

    fn choose(&self, candidates: &[u128]) -> Result<Vec<u128>, Error> {
        if candidates.is_empty() {
            return Ok(Vec::new());
        }
        let sum = candidates
            .iter()
            .try_fold(0u128, |sum, &n| sum.checked_add(n).ok_or(Error::Overflow))?;
        Ok(vec![sum])
    }
}

pub(crate) fn count_product(mut counts: impl Iterator<Item = u128>) -> Result<u128, Error> {
    counts.try_fold(1u128, |product, n| {
        product.checked_mul(n).ok_or(Error::Overflow)
    })
}

pub struct Enumerate;

impl<O: Clone + std::fmt::Debug + Eq> Algebra<O> for Enumerate {
    type Value = Tree<O>;

    fn apply(&self, operator: &O, children: &[&Tree<O>]) -> Result<Tree<O>, Error> {
        Ok(Tree {
            operator: operator.clone(),
            children: children.iter().map(|&t| t.clone()).collect(),
        })
    }

    fn choose(&self, candidates: &[Tree<O>]) -> Result<Vec<Tree<O>>, Error> {
        Ok(candidates.to_vec())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Optimum {
    pub cost: Cost,
    pub count: u128,
}

/// First select the lowest cost, then count all derivations at that cost.
/// Infinite operators, child costs and candidates return [`Error::InfinityDisabled`]
/// when evaluated. Ordered finite partial sums and tie counts are checked.
/// Use [`MinimumWithMultiplicity`] when a sum can absorb to infinity.
pub struct MinimumCount;

impl<O: ScoredOperator> Algebra<O> for MinimumCount {
    type Value = Optimum;

    fn apply(&self, operator: &O, children: &[&Optimum]) -> Result<Optimum, Error> {
        Ok(Optimum {
            cost: Additive::default()
                .sum(operator.cost(), children.iter().map(|child| child.cost))?,
            count: count_product(children.iter().map(|child| child.count))?,
        })
    }

    fn choose(&self, candidates: &[Optimum]) -> Result<Vec<Optimum>, Error> {
        if candidates
            .iter()
            .any(|candidate| candidate.cost == Cost::Infinity)
        {
            return Err(Error::InfinityDisabled);
        }
        let Some(cost) = candidates.iter().map(|candidate| candidate.cost).min() else {
            return Ok(Vec::new());
        };
        let count = candidates
            .iter()
            .filter(|candidate| candidate.cost == cost)
            .try_fold(0u128, |sum, candidate| {
                sum.checked_add(candidate.count).ok_or(Error::Overflow)
            })?;
        Ok(vec![Optimum { cost, count }])
    }
}

/// Whether a score may be attained at infinity. Empty candidate bags always
/// stay empty in the built-in algebras.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum CostPolicy {
    #[default]
    FiniteOnly,
    AttainableInfinity,
}

/// Additive minimum with checked integer arithmetic. Adding an attainable
/// infinity yields infinity. Otherwise, intermediate sums must fit in `i64`.
#[derive(Debug, Default, Clone, Copy)]
pub struct Additive {
    policy: CostPolicy,
}

impl Additive {
    pub fn new(policy: CostPolicy) -> Self {
        Self { policy }
    }

    pub(crate) fn sum(
        self,
        weight: Cost,
        mut costs: impl Iterator<Item = Cost> + Clone,
    ) -> Result<Cost, Error> {
        if weight == Cost::Infinity || costs.clone().any(|cost| cost == Cost::Infinity) {
            return match self.policy {
                CostPolicy::FiniteOnly => Err(Error::InfinityDisabled),
                CostPolicy::AttainableInfinity => Ok(Cost::Infinity),
            };
        }
        costs.try_fold(weight, Cost::plus)
    }
}

impl<O: ScoredOperator> Algebra<O> for Additive {
    type Value = Cost;

    fn apply(&self, operator: &O, children: &[&Cost]) -> Result<Cost, Error> {
        self.sum(operator.cost(), children.iter().map(|&&cost| cost))
    }

    fn choose(&self, candidates: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(candidates.iter().copied().min().into_iter().collect())
    }
}

/// Additive maximum with finite costs and checked integer arithmetic.
#[derive(Debug, Default, Clone, Copy)]
pub struct Maximum;

impl<O: ScoredOperator> Algebra<O> for Maximum {
    type Value = Cost;

    fn apply(&self, operator: &O, children: &[&Cost]) -> Result<Cost, Error> {
        Additive::default().apply(operator, children)
    }

    fn choose(&self, candidates: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(candidates.iter().copied().max().into_iter().collect())
    }
}

/// Interpret both factors on the same constructor and child tuples. The
/// caller supplies choice on paired answers. Audit the resulting product.
pub struct Product<L, R, C> {
    left: L,
    right: R,
    choose: C,
}

impl<L, R, C> Product<L, R, C> {
    pub fn new(left: L, right: R, choose: C) -> Self {
        Self {
            left,
            right,
            choose,
        }
    }
}

impl<O, L, R, C> Algebra<O> for Product<L, R, C>
where
    L: Algebra<O>,
    R: Algebra<O>,
    C: Fn(&[(L::Value, R::Value)]) -> Result<Vec<(L::Value, R::Value)>, Error>,
{
    type Value = (L::Value, R::Value);

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        let left: Vec<_> = children.iter().map(|pair| &pair.0).collect();
        let right: Vec<_> = children.iter().map(|pair| &pair.1).collect();
        Ok((
            self.left.apply(operator, &left)?,
            self.right.apply(operator, &right)?,
        ))
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        (self.choose)(candidates)
    }
}

/// Choose a single lexicographic minimum. With [`Product`], each constructor
/// must preserve lexicographic order in each paired argument for the usual
/// monotonicity justification. A constructor that merges primary scores can
/// expose a secondary order reversal. Audit the paired algebra on the chart.
pub fn lexicographic_min<L: Clone + Ord, R: Clone + Ord>(
    candidates: &[(L, R)],
) -> Result<Vec<(L, R)>, Error> {
    Ok(candidates.iter().min().cloned().into_iter().collect())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DerivationSummary {
    pub cost: Cost,
    pub optimal_derivations: u128,
    pub total_derivations: u128,
}

/// Additive minimum together with optimal and total derivation counts.
/// If addition absorbs to infinity, every child combination is optimal for
/// that rule. The total counts retain combinations removed by earlier choices.
/// Grammar ambiguity affects both counts.
#[derive(Debug, Default, Clone, Copy)]
pub struct MinimumWithMultiplicity {
    score: Additive,
}

impl MinimumWithMultiplicity {
    pub fn new(policy: CostPolicy) -> Self {
        Self {
            score: Additive::new(policy),
        }
    }

    pub(crate) fn summarize<'a>(
        &self,
        weight: Cost,
        children: impl Iterator<Item = &'a DerivationSummary> + Clone,
    ) -> Result<DerivationSummary, Error> {
        let cost = self
            .score
            .sum(weight, children.clone().map(|child| child.cost))?;
        let mut total_derivations = 1u128;
        let mut optimal_derivations = 1u128;
        for child in children {
            total_derivations = total_derivations
                .checked_mul(child.total_derivations)
                .ok_or(Error::Overflow)?;
            optimal_derivations = optimal_derivations
                .checked_mul(child.optimal_derivations)
                .ok_or(Error::Overflow)?;
        }
        if cost == Cost::Infinity {
            optimal_derivations = total_derivations;
        }
        Ok(DerivationSummary {
            cost,
            optimal_derivations,
            total_derivations,
        })
    }
}

impl<O: ScoredOperator> Algebra<O> for MinimumWithMultiplicity {
    type Value = DerivationSummary;

    fn apply(
        &self,
        operator: &O,
        children: &[&DerivationSummary],
    ) -> Result<DerivationSummary, Error> {
        self.summarize(operator.cost(), children.iter().copied())
    }

    fn choose(&self, candidates: &[DerivationSummary]) -> Result<Vec<DerivationSummary>, Error> {
        let Some(cost) = candidates.iter().map(|candidate| candidate.cost).min() else {
            return Ok(Vec::new());
        };
        let mut total_derivations = 0u128;
        let mut optimal_derivations = 0u128;
        for candidate in candidates {
            total_derivations = total_derivations
                .checked_add(candidate.total_derivations)
                .ok_or(Error::Overflow)?;
            if candidate.cost == cost {
                optimal_derivations = optimal_derivations
                    .checked_add(candidate.optimal_derivations)
                    .ok_or(Error::Overflow)?;
            }
        }
        Ok(vec![DerivationSummary {
            cost,
            optimal_derivations,
            total_derivations,
        }])
    }
}

/// Choose the unique non-dominated pairs in ascending lexicographic order,
/// minimizing both coordinates. Use with [`Product`] when each constructor
/// preserves the non-strict componentwise order in each child. Equality
/// after a constructor is permitted because the result is a set of scores.
pub fn pareto_min<L: Clone + Ord, R: Clone + Ord>(
    candidates: &[(L, R)],
) -> Result<Vec<(L, R)>, Error> {
    let mut sorted: Vec<_> = candidates.iter().collect();
    sorted.sort_unstable();
    let mut front: Vec<(L, R)> = Vec::new();
    for candidate in sorted {
        if front.last().is_none_or(|previous| candidate.1 < previous.1) {
            front.push(candidate.clone());
        }
    }
    Ok(front)
}

/// Return every ordered derivation with finite additive cost at most
/// `delta` above the minimum. A child above its local band can be replaced
/// by a child optimum, lowering the parent by the same difference.
/// Bellman reasoning assumes all intermediate sums fit in `i64`.
#[derive(Debug, Clone, Copy)]
pub struct WithinDelta {
    delta: u64,
}

impl WithinDelta {
    /// The full `u64` range covers every possible difference of two `i64` costs.
    pub fn new(delta: u64) -> Self {
        Self { delta }
    }
}

impl<O: Clone + Eq + std::fmt::Debug + ScoredOperator> Algebra<O> for WithinDelta {
    type Value = crate::queries::RankedTree<O, i64>;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        let cost = Additive::default().sum(
            operator.cost(),
            children.iter().map(|child| Cost::Finite(child.value)),
        )?;
        let Cost::Finite(value) = cost else {
            unreachable!("finite additive policy")
        };
        Ok(crate::queries::RankedTree {
            value,
            tree: Tree {
                operator: operator.clone(),
                children: children.iter().map(|child| child.tree.clone()).collect(),
            },
        })
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        let Some(best) = candidates.iter().map(|candidate| candidate.value).min() else {
            return Ok(Vec::new());
        };
        Ok(candidates
            .iter()
            .filter(|candidate| candidate.value.abs_diff(best) <= self.delta)
            .cloned()
            .collect())
    }
}
