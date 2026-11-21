use std::fmt::{self, Debug, Display, Formatter};

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

impl Display for Law {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyChoice => f.write_str("choosing from no candidates"),
            Self::Operation { rule } => write!(f, "choosing children before applying rule {rule}"),
            Self::Merge => f.write_str("choosing within each rule before merging alternatives"),
            Self::MergeAfterChildChoice => {
                f.write_str("choosing within each rule before merging, after child choice")
            }
            Self::Tabulation => f.write_str("comparing exhaustive and tabulated answers"),
            Self::Injectivity => f.write_str("computing answer identity"),
        }
    }
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

fn plural_suffix(count: usize) -> &'static str {
    if count == 1 {
        ""
    } else {
        "s"
    }
}

impl<O: Debug, V: Debug> Display for Counterexample<O, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cell {} differs when {}", self.cell, self.law)?;
        if let Some(operator) = &self.operator {
            write!(f, " ({operator:?})")?;
        }
        write!(
            f,
            ". Expected {:?}, got {:?}. The report retains {} original derivation occurrence{}.",
            self.before,
            self.after,
            self.trees.len(),
            plural_suffix(self.trees.len())
        )
    }
}

impl<O: Debug, V: Debug> Display for Audit<O, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Bellman check across {} cell{} and {} rule{}. ",
            self.cells,
            plural_suffix(self.cells),
            self.rules,
            plural_suffix(self.rules)
        )?;
        match &self.first_failure {
            Some(failure) => Display::fmt(failure, f),
            None => f.write_str("All comparisons agreed on this chart."),
        }
    }
}

impl<O: Debug, K> Display for Ambiguity<O, K> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let d = &self.duplicate;
        write!(
            f,
            "Cell {} has {} derivations with the same answer identity. Witness derivations {} and {} start with {:?} and {:?}.",
            self.cell, d.occurrences, d.indices[0], d.indices[1], d.first.operator, d.second.operator,
        )
    }
}

impl<O: Debug, V: Debug, K> Display for BoundedAudit<O, V, K> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} Examined {} constructor node{}. Repeated answer identities occur in {} cell{}.",
            self.bellman,
            self.tree_nodes,
            plural_suffix(self.tree_nodes),
            self.ambiguities.len(),
            plural_suffix(self.ambiguities.len())
        )?;
        if let Some(first) = self.ambiguities.first() {
            write!(f, " {first}")?;
        }
        Ok(())
    }
}

/// The constructor occurrences needed to enumerate every derivation at
/// every rank, including ranks unreachable from the root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expansion {
    /// Exact total within the caller's structural budget.
    WithinBudget { tree_nodes: usize },
    /// The aggregate first crosses the budget at this rank.
    OverBudget {
        first_cell: Cell,
        max_tree_nodes: usize,
    },
}

/// Concrete grammar size for one bound input and the resulting audit work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GrammarGrowth {
    pub cells: usize,
    pub rules: usize,
    /// Counts repeated child positions separately.
    pub child_slots: usize,
    pub expansion: Expansion,
}

impl Display for GrammarGrowth {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "This chart has {} cell{}, {} rule{} and {} child position{}. ",
            self.cells,
            plural_suffix(self.cells),
            self.rules,
            plural_suffix(self.rules),
            self.child_slots,
            plural_suffix(self.child_slots),
        )?;
        match self.expansion {
            Expansion::WithinBudget { tree_nodes } => {
                write!(
                    f,
                    "Exhaustive expansion accounts for {tree_nodes} constructor node{}.",
                    plural_suffix(tree_nodes)
                )
            }
            Expansion::OverBudget {
                first_cell,
                max_tree_nodes,
            } => {
                write!(f, "Exhaustive expansion crosses the {max_tree_nodes}-node budget at cell {first_cell}.")
            }
        }
    }
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
    let mut totals = crate::reserve_table::<(usize, usize)>(chart.cells.len())?;
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

/// Count ranked rules and child positions and check exhaustive expansion
/// against the budget using the same structural preflight as [`audit_bounded`].
/// This reads the reference chart without constructing any trees or running
/// an algebra. Compare reports over input sizes to measure concrete growth.
pub fn grammar_growth<O>(chart: &Chart<O>, budget: AuditBudget) -> Result<GrammarGrowth, Error> {
    let expansion = match count_tree_nodes(chart, budget) {
        Ok(tree_nodes) => Expansion::WithinBudget { tree_nodes },
        Err(Error::AuditBudgetExceeded {
            cell,
            max_tree_nodes,
        }) => Expansion::OverBudget {
            first_cell: cell,
            max_tree_nodes,
        },
        Err(error) => return Err(error),
    };
    let mut rules = 0_usize;
    let mut child_slots = 0_usize;
    for cell in chart.cells() {
        rules = rules.checked_add(cell.len()).ok_or(Error::Overflow)?;
        for rule in cell {
            child_slots = child_slots
                .checked_add(rule.children.len())
                .ok_or(Error::Overflow)?;
        }
    }
    Ok(GrammarGrowth {
        cells: chart.cells().len(),
        rules,
        child_slots,
        expansion,
    })
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
