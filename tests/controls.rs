use zeno_adp::algebras::{Cost, Count, Minimum, MinimumCount, Optimum, ScoredOperator};
use zeno_adp::classification::{Classes, Classification, Classified};
use zeno_adp::grammars::{nussinov, Fold};
use zeno_adp::{
    audit, audit_bounded, audit_bounded_classified, Algebra, AuditBudget, Chart, Error, Law,
    Operator, Rule, Tree,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Affine {
    Leaf(i64),
    Extend(Cost),
}

impl Operator for Affine {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Extend(_)))
    }
}

impl ScoredOperator for Affine {
    fn cost(&self) -> Cost {
        match *self {
            Self::Leaf(n) => Cost::Finite(n),
            Self::Extend(cost) => cost,
        }
    }
}

fn two_cost_input(input: &[u8], leaves: [i64; 2]) -> Chart<Affine> {
    let first = leaves
        .into_iter()
        .map(|n| Rule::new(Affine::Leaf(n), []))
        .collect();
    let mut cells = vec![first, Vec::new()];
    match input {
        b"+" => cells.push(vec![Rule::new(Affine::Extend(Cost::Finite(1)), [0])]),
        b"!" => cells.push(vec![Rule::new(Affine::Extend(Cost::Infinity), [0])]),
        b"?" => cells.push(vec![Rule::new(Affine::Extend(Cost::Infinity), [1])]),
        _ => panic!("input outside the toy grammar"),
    }
    let root = cells.len() - 1;
    Chart::new(cells, root).unwrap()
}

#[test]
fn finite_tie_count_refuses_infinity_and_repaired_product_keeps_both_ties() {
    let chart = two_cost_input(b"!", [7, 31]);
    let minimum = audit(&chart, &Minimum).unwrap();
    let count = audit(&chart, &Count).unwrap();
    assert!(minimum.first_failure.is_none() && count.first_failure.is_none());
    assert_eq!(minimum.oracle, [Cost::Infinity]);
    assert_eq!(count.oracle, [2]);
    assert_eq!(
        zeno_adp::tabulate(&chart, &MinimumCount),
        Err(Error::InfinityDisabled)
    );
    assert_eq!(
        zeno_adp::exhaustive(&chart, &MinimumCount),
        Err(Error::InfinityDisabled)
    );
    let paired = zeno_adp::algebras::MinimumWithMultiplicity::new(
        zeno_adp::algebras::CostPolicy::AttainableInfinity,
    );
    let report = audit(&chart, &paired).unwrap();
    assert!(report.first_failure.is_none());
    let expected = zeno_adp::algebras::DerivationSummary {
        cost: Cost::Infinity,
        optimal_derivations: 2,
        total_derivations: 2,
    };
    assert_eq!(report.oracle, [expected]);
    assert_eq!(report.tabulated, [expected]);

    let infinite = Optimum {
        cost: Cost::Infinity,
        count: 1,
    };
    let leaf = Affine::Leaf(0);
    assert_eq!(
        MinimumCount.apply(&leaf, &[&infinite]),
        Err(Error::InfinityDisabled)
    );
    assert_eq!(
        <MinimumCount as Algebra<Affine>>::choose(&MinimumCount, &[infinite]),
        Err(Error::InfinityDisabled)
    );
}

struct EvenFirst;

impl Algebra<Affine> for EvenFirst {
    type Value = Cost;

    fn apply(&self, op: &Affine, children: &[&Cost]) -> Result<Cost, Error> {
        Minimum.apply(op, children)
    }

    fn choose(&self, candidates: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(candidates
            .iter()
            .copied()
            .min_by_key(|cost| match cost {
                Cost::Finite(n) => (n % 2 != 0, *cost),
                Cost::Infinity => (true, *cost),
            })
            .into_iter()
            .collect())
    }
}

#[test]
fn parity_preference_is_not_preserved_by_increment() {
    let input = b"+";
    let chart = two_cost_input(input, [0, 1]);
    assert!(audit(&chart, &Minimum).unwrap().first_failure.is_none());
    let observed = audit(&chart, &EvenFirst).unwrap();
    let witness = observed.first_failure.unwrap();
    assert_eq!(witness.cell, chart.root());
    assert_eq!(witness.law, Law::Operation { rule: 0 });
    assert_eq!(observed.oracle, vec![Cost::Finite(2)]);
    assert_eq!(observed.tabulated, vec![Cost::Finite(1)]);
    let lost_tree = Tree {
        operator: Affine::Extend(Cost::Finite(1)),
        children: vec![Tree {
            operator: Affine::Leaf(1),
            children: vec![],
        }],
    };
    assert!(witness.trees.contains(&lost_tree));
    println!("parity-choice: input=+ lost_tree={lost_tree:?} {witness:?}");
}

// The probes use two leaves and one unary production, at most six raw nodes.
const CONTROL_BUDGET: AuditBudget = AuditBudget { max_tree_nodes: 6 };

struct OneClass;

impl<O> Classification<O> for OneClass {
    type Class = ();

    fn classify(&self, _: &O, _: &[&()]) -> Result<(), Error> {
        Ok(())
    }
}

#[test]
fn classified_question_retains_its_bellman_obligation() {
    let chart = two_cost_input(b"+", [0, 1]);
    let question = Classified::new(OneClass, EvenFirst);
    let report = audit_bounded_classified(
        &chart,
        &question,
        question.classes(),
        CONTROL_BUDGET,
        Default::default(),
    )
    .unwrap();
    let witness = report.bellman.first_failure.unwrap();
    assert_eq!(witness.cell, chart.root());
    assert_eq!(witness.law, Law::Operation { rule: 0 });
    assert_eq!(witness.before, [((), Cost::Finite(2))]);
    assert_eq!(witness.after, [((), Cost::Finite(1))]);
    assert_eq!(report.ambiguities.len(), 2);
    assert_ne!(
        report.ambiguities[0].duplicate.first,
        report.ambiguities[0].duplicate.second
    );
    println!("classified parity-choice: input=+ {witness:?}");
}

#[test]
fn ambiguous_grammar_double_counts_even_when_bellman_passes() {
    let input = b"";
    let original = nussinov(input, 0).unwrap();
    let mut cells = original.cells().to_vec();
    cells[original.root()].push(Rule::new(Fold::Empty, []));
    let planted = Chart::new(cells, original.root()).unwrap();

    let exact = audit(&original, &Count).unwrap();
    let duplicate = audit(&planted, &Count).unwrap();
    assert_eq!(exact.oracle, vec![1]);
    assert_eq!(duplicate.oracle, vec![2]);
    assert!(exact.first_failure.is_none() && duplicate.first_failure.is_none());
    let structural = audit_bounded(&original, &Count, CONTROL_BUDGET, Default::default()).unwrap();
    assert!(structural.ambiguities.is_empty());
    let report = audit_bounded(&planted, &Count, CONTROL_BUDGET, Default::default()).unwrap();
    let witness = &report.ambiguities[0].duplicate;
    assert_eq!(witness.occurrences, 2);
    assert_eq!(witness.indices, [0, 1]);
    assert_eq!(witness.first, witness.second);
    assert_eq!(witness.first.operator, Fold::Empty);
    println!("duplicate-fold: input=empty {witness:?}");

    // An answer projection can merge two genuinely different term trees.
    let different = two_cost_input(b"+", [7, 31]);
    let classes = Classes::new(OneClass);
    let report = audit_bounded_classified(
        &different,
        &classes,
        &classes,
        CONTROL_BUDGET,
        Default::default(),
    )
    .unwrap();
    let witness = &report.ambiguities[0].duplicate;
    assert_eq!(witness.occurrences, 2);
    assert_ne!(witness.first, witness.second);
}

#[test]
fn chart_refuses_cycles_or_invalid_constructor_arity() {
    let cycle = Chart::new(
        vec![vec![Rule::new(Affine::Extend(Cost::Finite(1)), [0])]],
        0,
    );
    assert!(matches!(
        cycle,
        Err(Error::NonDescendingChild { cell: 0, child: 0 })
    ));
    let arity = Chart::new(
        vec![vec![Rule::new(Affine::Extend(Cost::Finite(1)), [])]],
        0,
    );
    assert!(matches!(
        arity,
        Err(Error::Arity {
            cell: 0,
            expected: 1,
            actual: 0
        })
    ));
}

#[test]
fn equal_root_answers_can_hide_an_internal_violation() {
    let input = b"+0";
    let bad_child = two_cost_input(&input[..1], [0, 1]);
    let mut cells = bad_child.cells().to_vec();
    let root = cells.len();
    cells.push(vec![
        Rule::new(Affine::Extend(Cost::Finite(0)), [bad_child.root()]),
        Rule::new(Affine::Leaf(0), []),
    ]);
    let chart = Chart::new(cells, root).unwrap();
    let observed = audit(&chart, &EvenFirst).unwrap();
    assert_eq!(observed.oracle, vec![Cost::Finite(0)]);
    assert_eq!(observed.oracle, observed.tabulated);
    let witness = observed.first_failure.unwrap();
    assert_eq!(witness.cell, bad_child.root());
    assert_eq!(witness.law, Law::Operation { rule: 0 });
    println!(
        "root-masks-failure: input=+0 root={:?} {witness:?}",
        observed.oracle
    );
}

#[test]
fn classified_audit_locates_canonical_model_errors() {
    struct Refuse;

    impl Classification<Fold> for Refuse {
        type Class = ();

        fn classify(&self, _: &Fold, _: &[&()]) -> Result<(), Error> {
            Err(Error::Overflow)
        }
    }

    let chart = nussinov(b"", 0).unwrap();
    assert_eq!(
        audit_bounded_classified(
            &chart,
            &Count,
            &Classes::new(Refuse),
            CONTROL_BUDGET,
            Default::default(),
        )
        .unwrap_err(),
        Error::AuditEvaluation {
            cell: chart.root(),
            law: Law::Injectivity,
            source: Box::new(Error::Overflow),
        }
    );
}

struct LeafKey;

impl Classification<Affine> for LeafKey {
    type Class = i64;

    fn classify(&self, op: &Affine, _: &[&i64]) -> Result<i64, Error> {
        Ok(match *op {
            Affine::Leaf(value) => value,
            Affine::Extend(_) => 0,
        })
    }
}

struct TakeFirst;

impl Algebra<Affine> for TakeFirst {
    type Value = Cost;

    fn apply(&self, op: &Affine, children: &[&Cost]) -> Result<Cost, Error> {
        Minimum.apply(op, children)
    }

    fn choose(&self, values: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(values.first().copied().into_iter().collect())
    }
}

#[test]
fn classified_order_can_fail_even_when_both_component_audits_pass() {
    let chart = Chart::new(
        vec![
            vec![
                Rule::new(Affine::Leaf(2), []),
                Rule::new(Affine::Leaf(1), []),
            ],
            vec![Rule::new(Affine::Extend(Cost::Finite(0)), [0])],
        ],
        1,
    )
    .unwrap();
    let paired = Classified::new(LeafKey, TakeFirst);
    assert!(audit(&chart, paired.classes())
        .unwrap()
        .first_failure
        .is_none());
    assert!(audit(&chart, &TakeFirst).unwrap().first_failure.is_none());

    let report = audit_bounded_classified(
        &chart,
        &paired,
        paired.classes(),
        CONTROL_BUDGET,
        Default::default(),
    )
    .unwrap();
    assert_eq!(report.bellman.oracle, [(0, Cost::Finite(2))]);
    assert_eq!(report.bellman.tabulated, [(0, Cost::Finite(1))]);
    let witness = report
        .bellman
        .first_failure
        .expect("paired operation must fail");
    assert_eq!((witness.cell, witness.law), (1, Law::Operation { rule: 0 }));
    assert_eq!(witness.before, report.bellman.oracle);
    assert_eq!(witness.after, report.bellman.tabulated);
    assert_eq!(report.ambiguities[0].duplicate.indices, [0, 1]);
}

struct Coordinate {
    leaf: fn(i64) -> i64,
    parent: fn(i64) -> i64,
}

impl Algebra<Affine> for Coordinate {
    type Value = i64;

    fn apply(&self, op: &Affine, children: &[&i64]) -> Result<i64, Error> {
        Ok(match *op {
            Affine::Leaf(value) => (self.leaf)(value),
            Affine::Extend(_) => (self.parent)(*children[0]),
        })
    }

    fn choose(&self, values: &[i64]) -> Result<Vec<i64>, Error> {
        Ok(values.iter().min().copied().into_iter().collect())
    }
}

#[test]
fn resetting_the_primary_score_can_break_lexicographic_choice() {
    use zeno_adp::algebras::{lexicographic_min, Product};

    let chart = Chart::new(
        vec![
            vec![
                Rule::new(Affine::Leaf(0), []),
                Rule::new(Affine::Leaf(1), []),
            ],
            vec![Rule::new(Affine::Extend(Cost::Finite(0)), [0])],
        ],
        1,
    )
    .unwrap();
    let primary = Coordinate {
        leaf: |value| value,
        parent: |_| 0,
    };
    let secondary = Coordinate {
        leaf: |value| 1 - value,
        parent: |value| value,
    };
    assert!(audit(&chart, &primary).unwrap().first_failure.is_none());
    assert!(audit(&chart, &secondary).unwrap().first_failure.is_none());

    let paired = Product::new(primary, secondary, lexicographic_min);
    let report = audit_bounded(&chart, &paired, CONTROL_BUDGET, Default::default()).unwrap();
    assert_eq!(report.bellman.oracle, [(0, 0)]);
    assert_eq!(report.bellman.tabulated, [(0, 1)]);
    let witness = report
        .bellman
        .first_failure
        .expect("paired operation must fail");
    assert_eq!((witness.cell, witness.law), (1, Law::Operation { rule: 0 }));
    assert_eq!(witness.before, report.bellman.oracle);
    assert_eq!(witness.after, report.bellman.tabulated);
}

struct ChangeOccurrences;

impl Algebra<Affine> for ChangeOccurrences {
    type Value = i64;

    fn apply(&self, op: &Affine, _: &[&i64]) -> Result<i64, Error> {
        match *op {
            Affine::Leaf(value) => Ok(value),
            Affine::Extend(_) => unreachable!("only leaf rules in this fixture"),
        }
    }

    fn choose(&self, values: &[i64]) -> Result<Vec<i64>, Error> {
        Ok(match values {
            [2] => vec![0],
            [3] | [4] => vec![1],
            [2, 3, 4] => vec![0, 0, 1],
            _ => values.to_vec(),
        })
    }
}

#[test]
fn unordered_audit_rejects_equal_length_bags_with_different_counts() {
    let chart = Chart::new(
        vec![(2..=4)
            .map(|value| Rule::new(Affine::Leaf(value), []))
            .collect()],
        0,
    )
    .unwrap();
    let report = audit_bounded(
        &chart,
        &ChangeOccurrences,
        CONTROL_BUDGET,
        zeno_adp::AnswerOrder::Unordered,
    )
    .unwrap();
    let observed = report.bellman.first_failure.as_ref().map(|witness| {
        (
            witness.cell,
            witness.law,
            witness.before.as_slice(),
            witness.after.as_slice(),
        )
    });
    assert_eq!(
        observed,
        Some((0, Law::Merge, &[0, 0, 1][..], &[0, 1, 1][..]))
    );
}
