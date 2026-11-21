use zeno_adp::algebras::{
    Additive, Cost, CostPolicy, Count, DerivationSummary, MinimumCount, MinimumWithMultiplicity,
    ScoredOperator,
};
use zeno_adp::queries::{
    co_minimal, count, derivation_count, k_lowest, minimum, minimum_cells, MinimumBackend,
    TreeMultiplicity,
};
use zeno_adp::{
    audit_bounded, run, tabulate_cells, Algebra, AnswerOrder, AuditBudget, Chart, Error,
    Evaluation, Law, Operator, Rule,
};

// The controls have at most two nontrivial levels plus their leaf and
// operator grids. Leave room for every exhaustive witness in this file.
const BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 1_000,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Op {
    cost: Cost,
    arity: usize,
}

impl Operator for Op {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        self.cost
    }
}

fn rule(cost: Cost, children: &[usize]) -> Rule<Op> {
    Rule::new(
        Op {
            cost,
            arity: children.len(),
        },
        children,
    )
}

fn leaf(cost: i64) -> Rule<Op> {
    rule(Cost::Finite(cost), &[])
}

#[test]
fn default_count_and_rank_use_distinct_ordered_terms() {
    let grammar =
        |input: &i64| Chart::new(vec![vec![leaf(*input), leaf(*input), leaf(*input + 1)]], 0);
    let chart = grammar(&7).unwrap();
    let score = Additive::default();
    assert_eq!(
        run(&grammar, &7, &score, Evaluation::default()),
        Ok(vec![Cost::Finite(7)])
    );
    assert_eq!(
        run(&grammar, &7, &score, Evaluation::Tabulated),
        Ok(vec![Cost::Finite(7)])
    );
    assert_eq!(count(&chart, Default::default()), Ok(2));
    assert_eq!(count(&chart, TreeMultiplicity::Derivations), Ok(3));
    assert_eq!(derivation_count(&chart), Ok(3));
    assert_eq!(
        co_minimal(&chart, &score, Default::default())
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        co_minimal(&chart, &score, TreeMultiplicity::Derivations)
            .unwrap()
            .len(),
        2
    );
    assert!(k_lowest(&chart, &score, 0, Default::default())
        .unwrap()
        .is_empty());
    let bounded = audit_bounded(&chart, &Count, BUDGET, AnswerOrder::Ordered).unwrap();
    assert!(bounded.bellman.first_failure.is_none());
    assert_eq!(bounded.ambiguities.len(), 1);
    assert_eq!(bounded.ambiguities[0].cell, 0);
    assert_eq!(bounded.ambiguities[0].duplicate.indices, [0, 1]);
    assert_eq!(bounded.tree_nodes, 3);
    assert_eq!(
        audit_bounded(
            &chart,
            &Count,
            AuditBudget {
                max_tree_nodes: bounded.tree_nodes - 1
            },
            AnswerOrder::Ordered
        )
        .unwrap_err(),
        Error::AuditBudgetExceeded {
            cell: 0,
            max_tree_nodes: 2
        }
    );
}

#[test]
fn repeated_equal_rules_coalesce_before_derivations_overflow() {
    let mut cells = vec![vec![leaf(7)]];
    // Two copies of every unary production double the occurrence count
    // at each rank and generate exactly the same term.
    for child in 0..u128::BITS as usize {
        let repeated = rule(Cost::Finite(0), &[child]);
        cells.push(vec![repeated.clone(), repeated]);
    }
    let root = cells.len() - 1;
    let chart = Chart::new(cells, root).unwrap();
    assert_eq!(derivation_count(&chart), Err(Error::Overflow));
    assert_eq!(count(&chart, Default::default()), Ok(1));
    let ranked = k_lowest(&chart, &Additive::default(), 1, Default::default()).unwrap();
    assert_eq!(ranked.len(), 1);
    assert_eq!(ranked[0].value, Cost::Finite(7));
}

#[test]
fn absent_infinite_and_overflow_are_distinct() {
    let chart = Chart::new(
        vec![
            vec![rule(Cost::Infinity, &[])],
            vec![],
            vec![rule(Cost::Infinity, &[1])],
        ],
        2,
    )
    .unwrap();
    let finite = Additive::default();
    let infinite = Additive::new(CostPolicy::AttainableInfinity);
    assert_eq!(minimum_cells(&chart, &finite), Err(Error::InfinityDisabled));
    assert_eq!(
        tabulate_cells(&chart, &finite),
        Err(Error::InfinityDisabled)
    );
    assert_eq!(
        minimum_cells(&chart, &infinite),
        Ok(vec![Some(Cost::Infinity), None, None])
    );
    assert_eq!(
        tabulate_cells(&chart, &infinite),
        Ok(vec![vec![Cost::Infinity], vec![], vec![]])
    );
    assert_eq!(minimum(&chart, &infinite, MinimumBackend::Scalar), Ok(None));
    assert_eq!(derivation_count(&chart), Ok(0));
    assert_eq!(
        audit_bounded(&chart, &finite, BUDGET, AnswerOrder::Ordered).unwrap_err(),
        Error::AuditEvaluation {
            cell: 0,
            law: Law::Operation { rule: 0 },
            source: Box::new(Error::InfinityDisabled)
        }
    );
    assert!(
        audit_bounded(&chart, &infinite, BUDGET, AnswerOrder::Ordered)
            .unwrap()
            .bellman
            .first_failure
            .is_none()
    );

    let big = Chart::new(
        vec![vec![leaf(i64::MAX)], vec![rule(Cost::Finite(1), &[0])]],
        1,
    )
    .unwrap();
    assert_eq!(minimum_cells(&big, &finite), Err(Error::Overflow));
    assert_eq!(tabulate_cells(&big, &finite), Err(Error::Overflow));
    let mut cells = vec![vec![leaf(0), leaf(1)]];
    // With repeated child occurrences the counts square per new rank, so
    // ilog2(u128::BITS) reductions already reach 2^128.
    for child in 0..u128::BITS.ilog2() as usize {
        cells.push(vec![rule(Cost::Finite(0), &[child, child])]);
    }
    let root = cells.len() - 1;
    assert_eq!(
        derivation_count(&Chart::new(cells, root).unwrap()),
        Err(Error::Overflow)
    );
}

#[test]
fn early_minimum_can_hide_overflow_in_a_discarded_candidate() {
    let chart = Chart::new(
        vec![
            vec![leaf(0), leaf(i64::MAX)],
            vec![rule(Cost::Finite(1), &[0])],
        ],
        1,
    )
    .unwrap();
    let finite = Additive::default();
    let reference = minimum(&chart, &finite, MinimumBackend::Reference);
    assert_eq!(reference, Ok(Some(Cost::Finite(1))));
    assert_eq!(minimum(&chart, &finite, MinimumBackend::Scalar), reference);
    assert_eq!(zeno_adp::exhaustive(&chart, &finite), Err(Error::Overflow));
    let identity = TreeMultiplicity::Derivations;
    assert_eq!(co_minimal(&chart, &finite, identity), Err(Error::Overflow));
    assert_eq!(k_lowest(&chart, &finite, 1, identity), Err(Error::Overflow));
    let table = zeno_adp::fast::BestTable::new(&chart).unwrap();
    let expected = [zeno_adp::queries::RankedTree {
        value: Cost::Finite(1),
        tree: zeno_adp::Tree {
            operator: chart.cells()[1][0].operator,
            children: vec![zeno_adp::Tree {
                operator: chart.cells()[0][0].operator,
                children: vec![],
            }],
        },
    }];
    assert_eq!(table.recover().co_minimal(identity).unwrap(), expected);
    assert_eq!(table.recover().k_lowest(1, identity).unwrap(), expected);
    let refusal = audit_bounded(&chart, &finite, BUDGET, Default::default()).unwrap_err();
    assert_eq!(
        refusal,
        Error::AuditEvaluation {
            cell: 1,
            law: Law::Operation { rule: 0 },
            source: Box::new(Error::Overflow),
        }
    );
    println!("discarded arithmetic overflow: {refusal}");
}

struct Reverse;

impl Algebra<Op> for Reverse {
    type Value = Cost;

    fn apply(&self, op: &Op, values: &[&Cost]) -> Result<Cost, Error> {
        Additive::default().apply(op, values)
    }

    fn choose(&self, values: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(values.iter().rev().copied().collect())
    }
}

#[test]
fn unordered_equivalence_is_opt_in_and_keeps_multiplicity() {
    let chart = Chart::new(
        vec![
            vec![leaf(0), leaf(1), leaf(1)],
            vec![rule(Cost::Finite(0), &[0])],
        ],
        1,
    )
    .unwrap();
    let ordered = audit_bounded(&chart, &Reverse, BUDGET, Default::default()).unwrap();
    let witness = ordered.bellman.first_failure.unwrap();
    assert_eq!(witness.cell, chart.root());
    assert_eq!(witness.law, Law::Operation { rule: 0 });
    assert_eq!(
        witness.operator,
        Some(chart.cells()[chart.root()][0].operator)
    );
    assert_eq!(witness.trees.len(), 3);
    let unordered = audit_bounded(&chart, &Reverse, BUDGET, AnswerOrder::Unordered).unwrap();
    assert!(unordered.bellman.first_failure.is_none());
    assert_eq!(unordered.ambiguities.len(), 2);
    let broken =
        audit_bounded(&chart, &BrokenMultiplicity, BUDGET, AnswerOrder::Unordered).unwrap();
    assert!(broken.bellman.first_failure.is_some());
    println!("order control: {witness:?}");
}

struct BrokenMultiplicity;

impl Algebra<Op> for BrokenMultiplicity {
    type Value = Cost;

    fn apply(&self, op: &Op, values: &[&Cost]) -> Result<Cost, Error> {
        Additive::default().apply(op, values)
    }

    fn choose(&self, values: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(if let Some(&first) = values.first() {
            vec![first; values.len() + 1]
        } else {
            Vec::new()
        })
    }
}

fn repair_grid_chart(cost: Cost, args: &[&[Cost]]) -> Chart<Op> {
    let mut cells: Vec<_> = args
        .iter()
        .map(|bag| bag.iter().map(|&cost| rule(cost, &[])).collect())
        .collect();
    let root = cells.len();
    cells.push(vec![rule(cost, &(0..root).collect::<Vec<_>>())]);
    Chart::new(cells, root).unwrap()
}

#[test]
fn repaired_product_agrees_on_round_one_grid_and_nested_absorption() {
    let palette = [Cost::Finite(7), Cost::Finite(31), Cost::Infinity];
    let bags: Vec<Vec<Cost>> = (1..1 << palette.len())
        .map(|mask| {
            palette
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(bit, cost)| (mask & (1 << bit) != 0).then_some(cost))
                .collect()
        })
        .collect();
    let mut args = vec![vec![]];
    for a in &bags {
        args.push(vec![a.as_slice()]);
        for b in &bags {
            args.push(vec![a.as_slice(), b.as_slice()]);
        }
    }
    let product = MinimumWithMultiplicity::new(CostPolicy::AttainableInfinity);
    let mut refused = 0;
    let mut finite_cells = 0;
    for cost in [Cost::Finite(1), Cost::Infinity] {
        for input in &args {
            let chart = repair_grid_chart(cost, input);
            let repaired = audit_bounded(&chart, &product, BUDGET, Default::default()).unwrap();
            assert!(repaired.bellman.first_failure.is_none(), "{repaired:?}");
            let has_infinity =
                cost == Cost::Infinity || input.iter().any(|bag| bag.contains(&Cost::Infinity));
            let finite = zeno_adp::tabulate_cells(&chart, &MinimumCount);
            if has_infinity {
                assert_eq!(finite, Err(Error::InfinityDisabled));
                refused += 1;
            } else {
                let exact = zeno_adp::tabulate_cells(&chart, &product).unwrap();
                let expected: Vec<_> = exact
                    .into_iter()
                    .map(|cell| {
                        cell.into_iter()
                            .map(|summary| zeno_adp::algebras::Optimum {
                                cost: summary.cost,
                                count: summary.optimal_derivations,
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect();
                assert_eq!(finite.unwrap(), expected);
                let audit =
                    audit_bounded(&chart, &MinimumCount, BUDGET, Default::default()).unwrap();
                assert!(audit.bellman.first_failure.is_none(), "{audit:?}");
                finite_cells += expected.len();
            }
        }
    }
    assert_eq!(refused, 101);
    assert_eq!(finite_cells, 34);
    let nested = Chart::new(
        vec![
            vec![leaf(7), leaf(31)],
            vec![rule(Cost::Finite(1), &[0]), rule(Cost::Finite(2), &[0])],
            vec![rule(Cost::Finite(3), &[1, 0])],
            vec![rule(Cost::Infinity, &[2])],
        ],
        3,
    )
    .unwrap();
    let report = audit_bounded(&nested, &product, BUDGET, Default::default()).unwrap();
    let expected = DerivationSummary {
        cost: Cost::Infinity,
        optimal_derivations: 8,
        total_derivations: 8,
    };
    assert!(report.bellman.first_failure.is_none());
    assert_eq!(report.bellman.oracle, [expected]);
    assert_eq!(report.bellman.tabulated, [expected]);
    println!("repair: {} grid charts, {refused} infinity refusals, {finite_cells} finite cells agreed, {expected:?} on nested absorption", 2 * args.len());
}

#[test]
fn attainable_infinity_absorbs_the_whole_rule_in_both_minima() {
    use zeno_adp::algebras::Minimum;
    let chart = Chart::new(
        vec![
            vec![leaf(i64::MAX)],
            vec![rule(Cost::Infinity, &[])],
            vec![rule(Cost::Finite(1), &[0, 1])],
        ],
        2,
    )
    .unwrap();
    let expected = [
        vec![Cost::Finite(i64::MAX)],
        vec![Cost::Infinity],
        vec![Cost::Infinity],
    ];
    let policy = Additive::new(CostPolicy::AttainableInfinity);
    assert_eq!(tabulate_cells(&chart, &Minimum).unwrap(), expected);
    assert_eq!(tabulate_cells(&chart, &policy).unwrap(), expected);
    assert_eq!(
        zeno_adp::exhaustive(&chart, &Minimum).unwrap(),
        expected[chart.root()]
    );
    assert_eq!(
        zeno_adp::exhaustive(&chart, &policy).unwrap(),
        expected[chart.root()]
    );
}

#[test]
fn root_only_exhaustive_count_can_succeed_when_an_unreachable_cell_overflows() {
    let mut cells = vec![vec![leaf(0), leaf(1)]];
    // Starting from two derivations, seven squarings reach 2^128.
    let squarings = u128::BITS.ilog2() as usize;
    for previous in 0..squarings {
        cells.push(vec![rule(Cost::Finite(0), &[previous, previous])]);
    }
    let root = cells.len();
    cells.push(vec![leaf(0)]);
    let chart = Chart::new(cells, root).unwrap();
    assert_eq!(zeno_adp::exhaustive(&chart, &Count).unwrap(), [1]);
    assert_eq!(derivation_count(&chart), Err(Error::Overflow));
}

#[test]
fn tree_ranking_is_ascending_even_for_a_maximum_scorer() {
    use zeno_adp::algebras::Maximum;
    let chart = Chart::new(vec![vec![leaf(2), leaf(7)]], 0).unwrap();
    assert_eq!(
        zeno_adp::exhaustive(&chart, &Maximum).unwrap(),
        [Cost::Finite(7)]
    );
    let minima = co_minimal(&chart, &Maximum, TreeMultiplicity::Derivations).unwrap();
    assert_eq!(
        minima.iter().map(|answer| answer.value).collect::<Vec<_>>(),
        [Cost::Finite(2)]
    );
    let ranked = k_lowest(&chart, &Maximum, 2, TreeMultiplicity::Derivations).unwrap();
    assert_eq!(
        ranked.iter().map(|answer| answer.value).collect::<Vec<_>>(),
        [Cost::Finite(2), Cost::Finite(7)]
    );
}
