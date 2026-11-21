//! Ready-to-use questions over a chart.
use std::collections::BTreeSet;

use crate::algebras::{Additive, Cost, Count, ScoredOperator, WithinDelta};
use crate::{build_trees, enumerate, evaluate_tree, tabulate, Algebra, Chart, Error, Tree};

/// Identity used when returning or counting candidate trees.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum TreeMultiplicity {
    /// Count or return each ordered constructor term once.
    #[default]
    DistinctTrees,
    /// Count or return every derivation, including repeated constructor terms.
    Derivations,
}

/// Return candidate trees in first derivation order. Distinct mode coalesces
/// equal constructor terms at each cell before building parent trees.
pub fn trees<O: Clone + Ord>(chart: &Chart<O>, multiplicity: TreeMultiplicity) -> Vec<Tree<O>> {
    if multiplicity == TreeMultiplicity::Derivations {
        return enumerate(chart);
    }

    let mut cells = Vec::<Vec<Tree<O>>>::with_capacity(chart.cells.len());
    for rules in &chart.cells {
        let mut seen = BTreeSet::new();
        let mut distinct = Vec::new();
        for rule in rules {
            if rule.children.iter().any(|&child| cells[child].is_empty()) {
                continue;
            }
            for tree in build_trees(
                &rule.operator,
                rule.children.iter().map(|&child| &cells[child]),
            ) {
                if seen.insert(tree.clone()) {
                    distinct.push(tree);
                }
            }
        }
        cells.push(distinct);
    }
    std::mem::take(&mut cells[chart.root()])
}

/// Count candidate trees by the chosen identity. The default retains
/// distinct terms in each cell. For the cheaper derivation question see
/// [`derivation_count`].
pub fn count<O: Clone + Ord>(
    chart: &Chart<O>,
    multiplicity: TreeMultiplicity,
) -> Result<u128, Error> {
    match multiplicity {
        TreeMultiplicity::DistinctTrees => Ok(trees(chart, multiplicity).len() as u128),
        TreeMultiplicity::Derivations => derivation_count(chart),
    }
}

/// Count grammar derivations by tabulation. Overflow yields [`Error::Overflow`].
pub fn derivation_count<O>(chart: &Chart<O>) -> Result<u128, Error> {
    Ok(tabulate(chart, &Count)?.first().copied().unwrap_or(0))
}

/// A scored candidate. Equal-score queries preserve input derivation order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RankedTree<O, V> {
    pub value: V,
    pub tree: Tree<O>,
}

fn ranked<O: Clone + Ord, A: Algebra<O>>(
    chart: &Chart<O>,
    scorer: &A,
    multiplicity: TreeMultiplicity,
) -> Result<Vec<RankedTree<O, A::Value>>, Error>
where
    A::Value: Ord,
{
    let mut answers = Vec::new();
    for tree in trees(chart, multiplicity) {
        answers.push(RankedTree {
            value: evaluate_tree(&tree, scorer)?,
            tree,
        });
    }
    answers.sort_by(|a, b| a.value.cmp(&b.value));
    Ok(answers)
}

/// Return every tree at the lowest score under the value's natural order.
/// Ranking uses the scorer's constructor operations and supplies its own
/// ascending choice. Equal scores retain derivation order.
pub fn co_minimal<O: Clone + Ord, A: Algebra<O>>(
    chart: &Chart<O>,
    scorer: &A,
    multiplicity: TreeMultiplicity,
) -> Result<Vec<RankedTree<O, A::Value>>, Error>
where
    A::Value: Ord,
{
    let mut answers = ranked(chart, scorer, multiplicity)?;
    if let Some(best) = answers.first() {
        let ties = answers.partition_point(|answer| answer.value == best.value);
        answers.truncate(ties);
    }
    Ok(answers)
}

/// Return up to `k` lowest-scoring trees, with ties broken by derivation
/// order. Scoring and selection are exhaustive and require no Bellman law.
pub fn k_lowest<O: Clone + Ord, A: Algebra<O>>(
    chart: &Chart<O>,
    scorer: &A,
    k: usize,
    multiplicity: TreeMultiplicity,
) -> Result<Vec<RankedTree<O, A::Value>>, Error>
where
    A::Value: Ord,
{
    if k == 0 {
        return Ok(Vec::new());
    }
    let mut answers = ranked(chart, scorer, multiplicity)?;
    answers.truncate(k);
    Ok(answers)
}

/// Return trees within an inclusive band above the minimum finite additive
/// score, in first derivation order. The threshold applies to every
/// subproblem by the [`WithinDelta`] replacement law.
///
/// For checked arithmetic the equality with exhaustive scoring assumes
/// representable intermediate sums, including sums on discarded derivations.
pub fn within_delta<O: Clone + Ord + std::fmt::Debug + ScoredOperator>(
    chart: &Chart<O>,
    delta: u64,
    multiplicity: TreeMultiplicity,
) -> Result<Vec<RankedTree<O, i64>>, Error> {
    let mut answers = tabulate(chart, &WithinDelta::new(delta))?;
    if multiplicity == TreeMultiplicity::DistinctTrees {
        let mut seen = BTreeSet::new();
        answers.retain(|answer| seen.insert(answer.tree.clone()));
    }
    Ok(answers)
}

/// Backends for the additive minimum-cost question over the same ranked chart.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum MinimumBackend {
    #[default]
    Reference,
    Scalar,
}

/// Return the minimum additive cost. `None` represents absence, and
/// `Some(Cost::Infinity)` is an attained value under the opt-in policy.
/// Bellman reasoning for checked arithmetic requires every relevant finite
/// sum to be representable, including sums eliminated by early choice.
pub fn minimum<O: ScoredOperator>(
    chart: &Chart<O>,
    algebra: &Additive,
    backend: MinimumBackend,
) -> Result<Option<Cost>, Error> {
    match backend {
        MinimumBackend::Reference => Ok(tabulate(chart, algebra)?.first().copied()),
        MinimumBackend::Scalar => Ok(minimum_cells(chart, algebra)?[chart.root()]),
    }
}

/// Run the scalar minimum backend and return the score of every cell.
pub fn minimum_cells<O: ScoredOperator>(
    chart: &Chart<O>,
    algebra: &Additive,
) -> Result<Vec<Option<Cost>>, Error> {
    let mut cells = Vec::<Option<Cost>>::with_capacity(chart.cells.len());
    for rules in &chart.cells {
        let mut result: Option<Cost> = None;
        for rule in rules {
            let children = rule.children.iter().map(|&child| cells[child]);
            if children.clone().any(|cost| cost.is_none()) {
                continue;
            }
            let cost = algebra.sum(rule.operator.cost(), children.flatten())?;
            result = Some(result.map_or(cost, |best| best.min(cost)));
        }
        cells.push(result);
    }
    Ok(cells)
}
