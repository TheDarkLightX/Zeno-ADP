//! Score-window choosers: two questions about natural scores whose exact
//! tabulation keeps a bounded part of each cell's bag.
//!
//! # The grammar and the algebra
//!
//! Candidates are trees over constructors `f` of any arity. Each constructor
//! carries a [`Step`] with a weight `w` and a floor `c`, and the score algebra
//! interprets it as
//!
//! ```text
//! f(x1, ..., xk) = max(c, w + x1 + ... + xk)        (a leaf scores max(c, w))
//! ```
//!
//! over natural numbers. A cell `A -> f(B, C) | g(D) | ...` holds the bag of
//! the scores of all its derivations. A question reads one answer from that
//! bag. A chooser `h` keeps a sub-bag at every cell, and tabulation is exact
//! when `h` satisfies Bellman's laws for every constructor:
//!
//! ```text
//! h([]) = []                      h(h(X)) = h(X)
//! h(X + Y) = h(h(X) + h(Y))       (`+` is bag union: the alternatives of a cell)
//! h(f(X, Y)) = h(f(h(X), Y)) = h(f(X, h(Y)))
//! ```
//!
//! Both choosers here rest on one property of the score algebra: every
//! constructor is monotone in each child and never lowers a child's score.
//!
//! # Evidence
//!
//! The laws are checked by exhaustion over the bag domain of
//! `tests/windows.rs`, and the reference audit runs on its charts. Audit an
//! algebra on your own chart with [`crate::audit_bounded`] before relying on
//! tabulation: the operations that could break the laws are a step that
//! carries a score across the target, and a floor after a near-tie.
//!
//! For `Chart<Stepped>`, the algebras' `tabulate_cells` methods check the
//! largest attainable score of each productive rule in every cell, including
//! cells the root cannot reach. A rule with an empty child has no attainable
//! scores. The generic tabulation entry points require the caller to establish
//! that every literal constructor call fits in `u64` before choice.

use crate::{Algebra, Chart, Error, Operator};

mod lowered;
use lowered::{floor_windowed_two_best, mirror_window};

/// One constructor's action on natural scores: `max(floor, weight + sum of
/// the children)`. A weight alone is `Step::add`; a floor alone is
/// `Step::floor`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Step {
    pub weight: u64,
    pub floor: u64,
}

impl Step {
    /// Add `weight` to the sum of the children.
    pub const fn add(weight: u64) -> Self {
        Self { weight, floor: 0 }
    }

    /// Raise the sum of the children to at least `floor`.
    pub const fn floor(floor: u64) -> Self {
        Self { weight: 0, floor }
    }

    /// Evaluate the step on child scores with checked addition.
    pub fn apply(self, children: impl Iterator<Item = u64>) -> Result<u64, Error> {
        let mut sum = self.weight;
        for child in children {
            sum = sum.checked_add(child).ok_or(Error::Overflow)?;
        }
        Ok(sum.max(self.floor))
    }
}

/// A constructor of the natural-score algebra.
pub trait SteppedOperator {
    /// Return the constructor's fixed weight and floor.
    fn step(&self) -> Step;
}

/// A ready-made constructor: a step and the number of children.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Stepped {
    pub step: Step,
    pub arity: usize,
}

impl Operator for Stepped {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl SteppedOperator for Stepped {
    fn step(&self) -> Step {
        self.step
    }
}

fn apply_step<O: SteppedOperator>(operator: &O, children: &[&u64]) -> Result<u64, Error> {
    operator.step().apply(children.iter().map(|&&score| score))
}

/// The maximum result of a productive rule comes from the tuple of attained
/// child maxima. Nonnegative arithmetic makes every prefix fit if that
/// tuple fits. A rule with an empty child supplies no tuples.
fn check_score_domain(chart: &Chart<Stepped>, max_floor: Option<u64>) -> Result<(), Error> {
    let mut maxima = crate::reserve_table::<Option<u64>>(chart.cells().len())?;
    for rules in chart.cells() {
        let mut maximum = None;
        for rule in rules {
            if rule.children.iter().any(|&child| maxima[child].is_none()) {
                continue;
            }
            let step = rule.operator.step;
            if let Some(max_floor) = max_floor {
                if step.floor > max_floor {
                    return Err(Error::FloorOutsideWindow {
                        floor: step.floor,
                        max_floor,
                    });
                }
            }
            let score =
                step.apply(rule.children.iter().map(|&child| {
                    maxima[child].expect("productive rule has attained child maxima")
                }))?;
            maximum = maximum.max(Some(score));
        }
        maxima.push(maximum);
    }
    Ok(())
}

/// Which derivation score is closest to a target? Ties go to the lower score.
///
/// # Example
///
/// For `A ::= leaf(1) | leaf(4) | leaf(9)` and `B ::= add(2, A)`, the
/// closest score to 3 is 4 in `A` and 3 in `B`. The chooser keeps both
/// 1 and 4 in `A`, because the added weight can make 1 the closer choice.
///
/// ```
/// use zeno_adp::{Chart, Rule};
/// use zeno_adp::windows::{ClosestTo, Step, Stepped};
///
/// let leaves = [1, 4, 9].map(|weight| {
///     Rule::new(Stepped { step: Step::add(weight), arity: 0 }, [])
/// });
/// let shift = Rule::new(Stepped { step: Step::add(2), arity: 1 }, [0]);
/// let chart = Chart::new(vec![leaves.to_vec(), vec![shift]], 1)?;
/// let algebra = ClosestTo::new(3);
/// let cells = algebra.tabulate_cells(&chart)?;
/// assert_eq!(cells[0], [1, 4]);
/// assert_eq!(algebra.closest(&cells[0]), Some(4));
/// assert_eq!(algebra.closest(&cells[1]), Some(3));
/// # Ok::<(), zeno_adp::Error>(())
/// ```
///
/// # The chooser (the mirror window)
///
/// Write `T` for the target. From a cell's bag keep
///
/// ```text
/// every distinct score x <= T, once
/// the least score y > T, once, when no score is <= T,
///                              or when y - T < T - x_max
/// ```
///
/// where `x_max` is the largest kept score at or below `T`. Read the answer
/// with [`ClosestTo::closest`]. A cell stores at most `T + 2` scores.
///
/// # Why choosing early stays exact
///
/// Let `g` be any later constructor seen as a function of one child with the
/// other children fixed. Then `g` is monotone and `g(v) >= v`.
/// - A score above `T` that is not the least one stays above `T` and behind
///   the least one, so it never wins.
/// - Suppose `x <= T < y` and `y - T >= T - x`. If `g(x) >= T`, then
///   `g(y) >= g(x) >= T` and `g(x)` is at least as close. If `g(x) < T`, then
///   `g(x) + g(y) >= x + y >= 2T`, so `T - g(x) <= g(y) - T`. In both cases
///   `g(x)` is at least as close as `g(y)` and no larger, so the tie rule
///   also prefers it. The mirror test only tightens after a step, because
///   the largest image at or below `T` is at least `g(x)`.
/// - Every distinct score at or below `T` can become the answer: adding
///   `T - x` puts `x` exactly on the target. So none of them can be dropped.
///
/// The shift argument describes the exact natural-number model. The checked
/// chart entry point verifies that every attainable score fits in `u64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClosestTo {
    target: u64,
}

impl ClosestTo {
    /// Choose the score closest to this target.
    pub fn new(target: u64) -> Self {
        Self { target }
    }

    /// The target used for choice and readout.
    pub fn target(&self) -> u64 {
        self.target
    }

    /// Validate all attainable scores, then tabulate every cell.
    ///
    /// Use this entry point for a ranked `Stepped` chart whose literal
    /// arithmetic domain has yet to be checked.
    pub fn tabulate_cells(&self, chart: &Chart<Stepped>) -> Result<Vec<Vec<u64>>, Error> {
        check_score_domain(chart, None)?;
        crate::tabulate_cells(chart, self)
    }

    /// The score closest to the target among a stored or literal bag, the
    /// lower one on a tie. An empty bag has no answer.
    pub fn closest(&self, answer: &[u64]) -> Option<u64> {
        answer
            .iter()
            .copied()
            .min_by_key(|&score| (score.abs_diff(self.target), score))
    }
}

impl<O: SteppedOperator> Algebra<O> for ClosestTo {
    type Value = u64;

    fn apply(&self, operator: &O, children: &[&u64]) -> Result<u64, Error> {
        apply_step(operator, children)
    }

    fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
        Ok(mirror_window(self.target, candidates))
    }
}

/// Is the minimum score attained by exactly one derivation, when
/// constructors may raise scores to a floor?
///
/// # Example
///
/// In `A ::= leaf(0) | leaf(2) | leaf(9)` the minimum is unique. In
/// `B ::= floor(2, A)`, the first two derivations both score 2.
///
/// ```
/// use zeno_adp::{Chart, Rule};
/// use zeno_adp::windows::{Step, Stepped, UniqueMinimum};
///
/// let leaves = [0, 2, 9].map(|weight| {
///     Rule::new(Stepped { step: Step::add(weight), arity: 0 }, [])
/// });
/// let release = Rule::new(Stepped { step: Step::floor(2), arity: 1 }, [0]);
/// let chart = Chart::new(vec![leaves.to_vec(), vec![release]], 1)?;
/// let cells = UniqueMinimum::for_chart(&chart).tabulate_cells(&chart)?;
/// assert_eq!(cells[0], [0, 2]);
/// assert_eq!(UniqueMinimum::is_unique(&cells[0]), Some(true));
/// assert_eq!(cells[1], [2, 2]);
/// assert_eq!(UniqueMinimum::is_unique(&cells[1]), Some(false));
/// # Ok::<(), zeno_adp::Error>(())
/// ```
///
/// # The chooser (the floor-windowed two best)
///
/// Write `W` for the largest floor of any constructor. From a cell's bag keep
/// the two smallest occurrences `m <= r`, then drop `r` when
/// `r > max(m, W)`. Read the answer with [`UniqueMinimum::is_unique`]. A cell
/// stores at most two scores.
///
/// # Why choosing early stays exact
///
/// The runner-up matters only while a floor can raise the minimum to meet
/// it. Once `r` is above both `m` and every floor, each later constructor
/// keeps it strictly above the image of `m`: a weight shifts both, a floor
/// leaves `r` unchanged and lifts `m` to at most `max(m, W)`, and a sum with
/// another cell's scores adds at least that cell's minimum to both. An
/// occurrence beyond the two smallest always has two occurrences at or below
/// it after any monotone step.
///
/// The declared maximum is part of the contract. [`Algebra::apply`] refuses a
/// constructor whose floor exceeds it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UniqueMinimum {
    max_floor: u64,
}

impl UniqueMinimum {
    /// Declare the largest floor any constructor may carry.
    pub fn new(max_floor: u64) -> Self {
        Self { max_floor }
    }

    /// Read the largest floor from the chart's rules, including rules with
    /// empty children. A chart with no rules uses zero.
    pub fn for_chart<O: SteppedOperator>(chart: &Chart<O>) -> Self {
        let max_floor = chart
            .cells()
            .iter()
            .flatten()
            .map(|rule| rule.operator.step().floor)
            .max()
            .unwrap_or(0);
        Self { max_floor }
    }

    /// The declared floor ceiling.
    pub fn max_floor(&self) -> u64 {
        self.max_floor
    }

    /// Validate attainable score arithmetic and the floor ceiling, then
    /// tabulate every cell. A floor on a productive rule must fit the ceiling.
    pub fn tabulate_cells(&self, chart: &Chart<Stepped>) -> Result<Vec<Vec<u64>>, Error> {
        check_score_domain(chart, Some(self.max_floor))?;
        crate::tabulate_cells(chart, self)
    }

    /// Whether exactly one occurrence attains the minimum of a stored or
    /// literal bag. An empty bag has no answer.
    pub fn is_unique(answer: &[u64]) -> Option<bool> {
        let least = answer.iter().min()?;
        Some(answer.iter().filter(|&score| score == least).count() == 1)
    }
}

impl<O: SteppedOperator> Algebra<O> for UniqueMinimum {
    type Value = u64;

    fn apply(&self, operator: &O, children: &[&u64]) -> Result<u64, Error> {
        let step = operator.step();
        let floor = step.floor;
        if floor > self.max_floor {
            return Err(Error::FloorOutsideWindow {
                floor,
                max_floor: self.max_floor,
            });
        }
        step.apply(children.iter().map(|&&score| score))
    }

    fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
        Ok(floor_windowed_two_best(self.max_floor, candidates))
    }
}
