use crate::classification::{Classes, Classification};
use crate::{
    build_trees, evaluate_tree, first_duplicate, rule_values, tabulate_with, Algebra, Cell, Chart,
    Duplicate, Error, Tree,
};

/// Equality of answer bags in the audit. Choice always receives ordered bags.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum AnswerOrder {
    #[default]
    Ordered,
    /// Ignore order and preserve multiplicity. Use only when order is irrelevant
    /// to the observable question and subsequent operations.
    Unordered,
}

/// Bounds the aggregate number of constructor nodes across derivations at all
/// cells. Each occurrence of a shared subtree is charged. The chart and the
/// caller's algebra time, intermediate values and allocations are outside the budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AuditBudget {
    pub max_tree_nodes: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Law {
    EmptyChoice,
    Operation {
        rule: usize,
    },
    Merge,
    MergeAfterChildChoice,
    Tabulation,
    /// Computing a canonical class for the ambiguity check.
    Injectivity,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Counterexample<O, V> {
    pub cell: Cell,
    pub law: Law,
    /// The named constructor for an operation failure, including its payload.
    pub operator: Option<O>,
    pub before: Vec<V>,
    pub after: Vec<V>,
    /// The original terms in the failed production or cell, with multiplicities.
    pub trees: Vec<Tree<O>>,
}

#[derive(Debug)]
pub struct Audit<O, V> {
    pub oracle: Vec<V>,
    pub tabulated: Vec<V>,
    pub cells: usize,
    pub rules: usize,
    pub first_failure: Option<Counterexample<O, V>>,
}

/// Two derivation occurrences with the same identity within a cell.
#[derive(Debug, PartialEq, Eq)]
pub struct Ambiguity<O, K = Tree<O>> {
    pub cell: Cell,
    pub duplicate: Duplicate<K, O>,
}

#[derive(Debug)]
pub struct BoundedAudit<O, V, K = Tree<O>> {
    pub bellman: Audit<O, V>,
    /// The first duplicate by identity key ordering in each ambiguous cell.
    pub ambiguities: Vec<Ambiguity<O, K>>,
    pub tree_nodes: usize,
}

fn same_answers<V: Eq>(before: &[V], after: &[V], order: AnswerOrder) -> bool {
    if before == after {
        return true;
    }
    if order == AnswerOrder::Ordered || before.len() != after.len() {
        return false;
    }
    let mut remaining: Vec<_> = after.iter().collect();
    for value in before {
        let Some(index) = remaining.iter().position(|&item| value == item) else {
            return false;
        };
        remaining.swap_remove(index);
    }
    true
}

fn choice_of_bags<O, A: Algebra<O>>(
    algebra: &A,
    bags: &[Vec<A::Value>],
) -> Result<Vec<A::Value>, Error> {
    let combined: Vec<_> = bags.iter().flatten().cloned().collect();
    algebra.choose(&combined)
}

fn audit_chart<O: Clone, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
    order: AnswerOrder,
    mut inspect_terms: impl FnMut(Cell, &[Tree<O>]) -> Result<(), Error>,
    scoped_errors: bool,
) -> Result<Audit<O, A::Value>, Error> {
    let locate = |cell, law, source| {
        if scoped_errors {
            Error::AuditEvaluation {
                cell,
                law,
                source: Box::new(source),
            }
        } else {
            source
        }
    };
    let mut early = tabulate_with(chart, algebra, locate)?;
    let mut oracle = Vec::with_capacity(chart.cells.len());
    let mut terms = Vec::<Vec<Tree<O>>>::with_capacity(chart.cells.len());
    let mut first_failure = None;
    let mut rules_checked = 0;
    for (cell, rules) in chart.cells.iter().enumerate() {
        let locate = |law, source| locate(cell, law, source);
        let mut compare = |law,
                           operator: Option<&O>,
                           before: &[A::Value],
                           after: &[A::Value],
                           trees: &[Tree<O>]| {
            if first_failure.is_none() && !same_answers(before, after, order) {
                first_failure = Some(Counterexample {
                    cell,
                    law,
                    operator: operator.cloned(),
                    before: before.to_vec(),
                    after: after.to_vec(),
                    trees: trees.to_vec(),
                });
            }
        };
        let mut cell_terms = Vec::new();
        let mut raw_rules = Vec::new();
        let mut reduced_rules = Vec::new();
        let mut raw_choices = Vec::new();
        let mut reduced_choices = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let law = Law::Operation { rule: index };
            let mut trees = if rule.children.iter().any(|&child| terms[child].is_empty()) {
                Vec::new()
            } else {
                build_trees(
                    &rule.operator,
                    rule.children.iter().map(|&child| &terms[child]),
                )
            };
            let raw = trees
                .iter()
                .map(|tree| evaluate_tree(tree, algebra))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|source| locate(law, source))?;
            let reduced =
                rule_values(rule, algebra, &oracle).map_err(|source| locate(law, source))?;
            let raw_choice = algebra.choose(&raw).map_err(|source| locate(law, source))?;
            let reduced_choice = algebra
                .choose(&reduced)
                .map_err(|source| locate(law, source))?;
            compare(
                law,
                Some(&rule.operator),
                &raw_choice,
                &reduced_choice,
                &trees,
            );
            cell_terms.append(&mut trees);
            raw_rules.push(raw);
            reduced_rules.push(reduced);
            raw_choices.push(raw_choice);
            reduced_choices.push(reduced_choice);
            rules_checked += 1;
        }
        let full =
            choice_of_bags(algebra, &raw_rules).map_err(|source| locate(Law::Merge, source))?;
        if cell_terms.is_empty() {
            compare(Law::EmptyChoice, None, &[], &full, &cell_terms);
        }
        compare(
            Law::Merge,
            None,
            &full,
            &choice_of_bags(algebra, &raw_choices).map_err(|source| locate(Law::Merge, source))?,
            &cell_terms,
        );
        let reduced = choice_of_bags(algebra, &reduced_rules)
            .map_err(|source| locate(Law::MergeAfterChildChoice, source))?;
        compare(
            Law::MergeAfterChildChoice,
            None,
            &reduced,
            &choice_of_bags(algebra, &reduced_choices)
                .map_err(|source| locate(Law::MergeAfterChildChoice, source))?,
            &cell_terms,
        );
        compare(Law::Tabulation, None, &full, &early[cell], &cell_terms);
        inspect_terms(cell, &cell_terms).map_err(|source| locate(Law::Injectivity, source))?;
        oracle.push(full);
        terms.push(cell_terms);
    }

    Ok(Audit {
        oracle: std::mem::take(&mut oracle[chart.root]),
        tabulated: std::mem::take(&mut early[chart.root]),
        cells: chart.cells.len(),
        rules: rules_checked,
        first_failure,
    })
}

/// Check a concrete chart with ordered equality, without a work budget.
/// Use [`audit_bounded`] for caller-controlled expansion and ambiguity results.
pub fn audit<O: Clone, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
) -> Result<Audit<O, A::Value>, Error> {
    audit_chart(chart, algebra, AnswerOrder::Ordered, |_, _| Ok(()), false)
}

fn count_tree_nodes<O>(chart: &Chart<O>, budget: AuditBudget) -> Result<usize, Error> {
    let mut totals = Vec::<(usize, usize)>::with_capacity(chart.cells.len());
    let mut aggregate = 0usize;
    for (cell, rules) in chart.cells.iter().enumerate() {
        let exceeded = || Error::AuditBudgetExceeded {
            cell,
            max_tree_nodes: budget.max_tree_nodes,
        };
        let (mut derivations, mut nodes) = (0usize, 0usize);
        for rule in rules {
            if rule.children.iter().any(|&child| totals[child].0 == 0) {
                continue;
            }
            // The empty Cartesian product contributes one constructor node.
            let (mut ways, mut size) = (1usize, 1usize);
            for &child in &rule.children {
                let (child_ways, child_size) = totals[child];
                size = size
                    .checked_mul(child_ways)
                    .and_then(|left| {
                        child_size
                            .checked_mul(ways)
                            .and_then(|right| left.checked_add(right))
                    })
                    .ok_or_else(exceeded)?;
                ways = ways.checked_mul(child_ways).ok_or_else(exceeded)?;
            }
            derivations = derivations.checked_add(ways).ok_or_else(exceeded)?;
            nodes = nodes.checked_add(size).ok_or_else(exceeded)?;
            aggregate = aggregate
                .checked_add(size)
                .filter(|&total| total <= budget.max_tree_nodes)
                .ok_or_else(exceeded)?;
        }
        totals.push((derivations, nodes));
    }
    Ok(aggregate)
}

/// Exhaustively compare production, alternative-merge and table answers on
/// this chart, including cells unreachable from the root. Independently report
/// duplicate constructor terms. A successful report is evidence for this
/// input, algebra and equality only. An error means the audit did not finish.
pub fn audit_bounded<O: Clone + Ord, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
    budget: AuditBudget,
    order: AnswerOrder,
) -> Result<BoundedAudit<O, A::Value>, Error> {
    audit_with_identity(chart, algebra, budget, order, |tree| Ok(tree.clone()))
}

/// Check Bellman's principle for `algebra` and injectivity of the canonical
/// model over raw derivations in every cell. A class with multiple derivations
/// gives two witness trees and its exact occurrence count. This check can
/// expose repeated constructor terms or different terms with the same class.
pub fn audit_bounded_classified<O: Clone, A: Algebra<O>, C: Classification<O>>(
    chart: &Chart<O>,
    algebra: &A,
    classes: &Classes<C>,
    budget: AuditBudget,
    order: AnswerOrder,
) -> Result<BoundedAudit<O, A::Value, C::Class>, Error> {
    audit_with_identity(chart, algebra, budget, order, |tree| {
        evaluate_tree(tree, classes)
    })
}

fn audit_with_identity<O: Clone, A: Algebra<O>, K: Ord>(
    chart: &Chart<O>,
    algebra: &A,
    budget: AuditBudget,
    order: AnswerOrder,
    identity: impl Fn(&Tree<O>) -> Result<K, Error>,
) -> Result<BoundedAudit<O, A::Value, K>, Error> {
    let tree_nodes = count_tree_nodes(chart, budget)?;
    let mut ambiguities = Vec::new();
    let bellman = audit_chart(
        chart,
        algebra,
        order,
        |cell, trees| {
            if let Some(duplicate) = first_duplicate(trees, &identity)? {
                ambiguities.push(Ambiguity { cell, duplicate });
            }
            Ok(())
        },
        true,
    )?;
    Ok(BoundedAudit {
        bellman,
        ambiguities,
        tree_nodes,
    })
}
