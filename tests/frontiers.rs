#[path = "support/ranked_fixture.rs"]
mod fixture;

use fixture::{assignments, at, fixture, RANKS};
use std::collections::BTreeSet;
use zeno_adp::algebras::{pareto_min, Cost, Product, ScoredOperator, WithinDelta};
use zeno_adp::queries::{within_delta, RankedTree, TreeMultiplicity};
use zeno_adp::{
    audit, enumerate, exhaustive, tabulate_cells, Algebra, Chart, Error, Operator, Rule, Tree,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Objective {
    arity: usize,
    cost: [i64; 2],
}

impl Operator for Objective {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for Objective {
    fn cost(&self) -> Cost {
        Cost::Finite(self.cost[0])
    }
}

struct Coordinate<const AXIS: usize>;

impl<const AXIS: usize> Algebra<Objective> for Coordinate<AXIS> {
    type Value = i64;

    fn apply(&self, operator: &Objective, children: &[&i64]) -> Result<i64, Error> {
        children
            .iter()
            .try_fold(operator.cost[AXIS], |sum, &&value| {
                sum.checked_add(value).ok_or(Error::Overflow)
            })
    }

    fn choose(&self, candidates: &[i64]) -> Result<Vec<i64>, Error> {
        Ok(candidates.iter().copied().min().into_iter().collect())
    }
}

fn score(tree: &Tree<Objective>) -> (i64, i64) {
    let [left, right] = tree.operator.cost;
    tree.children
        .iter()
        .map(score)
        .fold((left, right), |(a, b), (c, d)| (a + c, b + d))
}

fn pareto_reference(candidates: &[(i64, i64)]) -> Vec<(i64, i64)> {
    candidates
        .iter()
        .copied()
        .filter(|&(a, b)| {
            candidates
                .iter()
                .all(|&(c, d)| (a, b) == (c, d) || c > a || d > b)
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[test]
fn complete_pareto_domain() {
    let pareto = Product::new(Coordinate::<0>, Coordinate::<1>, pareto_min);
    let values = [-1, 0, 1];
    let mut charts = 0;
    let mut inspected = 0;
    let mut retained = 0;
    let mut widest = 0;
    for first in assignments(values) {
        for second in assignments(values) {
            let chart = fixture(RANKS - 1, |_, group, arity| Objective {
                arity,
                cost: [first[group], second[group]],
            });
            let cells = tabulate_cells(&chart, &pareto).unwrap();
            assert!(audit(&chart, &pareto).unwrap().first_failure.is_none());
            for (cell, actual) in cells.iter().enumerate() {
                let chart_at_cell = at(&chart, cell);
                let raw: Vec<_> = enumerate(&chart_at_cell).iter().map(score).collect();
                assert_eq!(*actual, pareto_reference(&raw));
                assert_eq!(*actual, exhaustive(&chart_at_cell, &pareto).unwrap());
                inspected += raw.len();
                retained += actual.len();
                widest = widest.max(actual.len());
            }
            charts += 1;
        }
    }
    println!("{charts} Pareto charts, {} cells, {inspected} exhaustive pairs, {retained} retained pairs, max width {widest}, 0 disagreements", charts * RANKS);
}

#[test]
fn complete_delta_domain() {
    // 0 tests all co-optima; 1–3 span the first three positive
    // integer differences obtainable from the signed coefficients.
    const MAX_DELTA: u64 = 3;
    let mut charts = 0;
    let mut inspected = 0;
    let mut retained = 0;
    for weights in assignments([-1, 0, 1]) {
        let chart = fixture(RANKS - 1, |_, group, arity| Objective {
            arity,
            cost: [weights[group], 0],
        });
        for delta in 0..=MAX_DELTA {
            let question = WithinDelta::new(delta);
            let cells = tabulate_cells(&chart, &question).unwrap();
            assert!(audit(&chart, &question).unwrap().first_failure.is_none());
            for (cell, actual) in cells.iter().enumerate() {
                let chart_at_cell = at(&chart, cell);
                let raw: Vec<_> = enumerate(&chart_at_cell)
                    .into_iter()
                    .map(|tree| RankedTree {
                        value: score(&tree).0,
                        tree,
                    })
                    .collect();
                let best = raw.iter().map(|answer| answer.value).min().unwrap_or(0);
                inspected += raw.len();
                let expected: Vec<_> = raw
                    .into_iter()
                    .filter(|answer| {
                        i128::from(answer.value) <= i128::from(best) + i128::from(delta)
                    })
                    .collect();
                assert_eq!(*actual, expected);
                assert_eq!(*actual, exhaustive(&chart_at_cell, &question).unwrap());
                assert_eq!(
                    within_delta(&chart_at_cell, delta, TreeMultiplicity::Derivations).unwrap(),
                    expected
                );
                let mut distinct = Vec::new();
                for answer in &expected {
                    if !distinct.contains(answer) {
                        distinct.push(answer.clone());
                    }
                }
                assert_eq!(
                    within_delta(&chart_at_cell, delta, TreeMultiplicity::DistinctTrees).unwrap(),
                    distinct
                );
                retained += actual.len();
            }
            charts += 1;
        }
    }
    println!("{charts} chart/Δ cases, {} cells, {inspected} exhaustive derivations, {retained} retained derivations, 0 disagreements", charts * RANKS);
}

#[test]
fn delta_full_width_and_ordered_duplicates() {
    let high = Rule::new(
        Objective {
            arity: 0,
            cost: [i64::MAX, 0],
        },
        [],
    );
    let low = Rule::new(
        Objective {
            arity: 0,
            cost: [i64::MIN, 0],
        },
        [],
    );
    let chart = Chart::new(vec![vec![high.clone(), low, high]], 0).unwrap();
    let all = &tabulate_cells(&chart, &WithinDelta::new(u64::MAX)).unwrap()[0];
    assert_eq!(
        all.iter().map(|answer| answer.value).collect::<Vec<_>>(),
        vec![i64::MAX, i64::MIN, i64::MAX]
    );
    assert_eq!(all[0], all[2]);
    assert_eq!(
        tabulate_cells(&chart, &WithinDelta::new(u64::MAX - 1)).unwrap()[0].len(),
        1
    );
}

struct Contract(WithinDelta);

impl Algebra<Objective> for Contract {
    type Value = RankedTree<Objective, i64>;

    fn apply(&self, operator: &Objective, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        let mut answer = self.0.apply(operator, children)?;
        if operator.arity != 0 {
            answer.value /= 2;
        }
        Ok(answer)
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        self.0.choose(candidates)
    }
}

struct Reverse;

impl Algebra<Objective> for Reverse {
    type Value = i64;

    fn apply(&self, operator: &Objective, children: &[&i64]) -> Result<i64, Error> {
        Ok(children.first().map_or(operator.cost[0], |&&value| -value))
    }

    fn choose(&self, candidates: &[i64]) -> Result<Vec<i64>, Error> {
        Coordinate::<0>.choose(candidates)
    }
}

#[test]
fn nonadditive_and_nonmonotone_controls_are_refuted() {
    let op = |arity, cost| Objective {
        arity,
        cost: [cost, 0],
    };
    let chart = Chart::new(
        vec![
            vec![Rule::new(op(0, 0), []), Rule::new(op(0, 2), [])],
            vec![Rule::new(op(1, 0), [0])],
        ],
        1,
    )
    .unwrap();
    let delta = audit(&chart, &Contract(WithinDelta::new(1))).unwrap();
    assert_eq!(
        delta.oracle.iter().map(|a| a.value).collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(
        delta.tabulated.iter().map(|a| a.value).collect::<Vec<_>>(),
        [0]
    );
    assert_eq!(delta.first_failure.unwrap().cell, 1);

    let pareto = audit(&chart, &Product::new(Reverse, Coordinate::<1>, pareto_min)).unwrap();
    assert_eq!(pareto.oracle, [(-2, 0)]);
    assert_eq!(pareto.tabulated, [(0, 0)]);
    assert_eq!(pareto.first_failure.unwrap().cell, 1);
}

#[test]
fn skyline_comparisons_on_an_antichain() {
    use std::cmp::Ordering;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
    static COMPARISONS: AtomicUsize = AtomicUsize::new(0);
    #[derive(Clone, PartialEq, Eq)]
    struct Counted(usize);
    impl Ord for Counted {
        fn cmp(&self, other: &Self) -> Ordering {
            COMPARISONS.fetch_add(1, AtomicOrdering::Relaxed);
            self.0.cmp(&other.0)
        }
    }
    impl PartialOrd for Counted {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    // Eight bits of indices provide a small but nontrivial complete antichain.
    const WIDTH: usize = u8::MAX as usize + 1;
    let terms: Vec<_> = (0..WIDTH)
        .map(|n| {
            (
                Counted(n.reverse_bits() >> (usize::BITS - u8::BITS)),
                Counted(0),
            )
        })
        .map(|(a, _)| {
            let b = Counted(WIDTH - 1 - a.0);
            (a, b)
        })
        .collect();
    let result = pareto_min(&terms).unwrap();
    let comparisons = COMPARISONS.load(AtomicOrdering::Relaxed);
    assert_eq!(result.len(), WIDTH);
    assert!(comparisons < WIDTH * (WIDTH - 1));
    println!("Pareto antichain width {WIDTH}: {comparisons} skyline scalar comparisons, {} pairwise dominance tests", WIDTH * (WIDTH - 1));
}

#[test]
fn pareto_witnesses_agree_with_ordered_exhaustive_alignment() {
    use zeno_adp::algebras::ParetoWitnesses;
    use zeno_adp::grammars::{alignment, Align};

    const MAX_LENGTH: usize = 3; // Complete small domain with ties and trade-offs.
    let words: Vec<Vec<u8>> = (0..=MAX_LENGTH)
        .flat_map(|n| {
            (0..1_usize << n).map(move |b| (0..n).map(|i| ((b >> i) & 1) as u8).collect())
        })
        .collect();
    let local = |op: &Align| match *op {
        Align::Start => (0, 0),
        Align::Diagonal { left, right } => (i64::from(left != right), 0),
        Align::Left(_) | Align::Right(_) => (1, -1),
    };
    fn score_alignment(tree: &Tree<Align>, local: impl Fn(&Align) -> (i64, i64)) -> (i64, i64) {
        let mut score = (0, 0);
        let mut path = Some(tree);
        while let Some(tree) = path {
            let (a, b) = local(&tree.operator);
            score = (score.0 + a, score.1 + b);
            path = tree.children.first();
        }
        score
    }
    let mut ranks = 0;
    let mut witnesses = 0;
    for left in &words {
        for right in &words {
            let chart = alignment(left, right).unwrap();
            let algebra = ParetoWitnesses::new(local);
            let table = tabulate_cells(&chart, &algebra).unwrap();
            for (cell, actual) in table.iter().enumerate() {
                let chart_at_cell = at(&chart, cell);
                let raw: Vec<_> = enumerate(&chart_at_cell)
                    .into_iter()
                    .map(|tree| RankedTree {
                        value: score_alignment(&tree, local),
                        tree,
                    })
                    .collect();
                let expected: Vec<_> = raw
                    .iter()
                    .filter(|answer| {
                        let (a, b) = answer.value;
                        raw.iter().all(|other| {
                            let (c, d) = other.value;
                            (a, b) == (c, d) || c > a || d > b
                        })
                    })
                    .cloned()
                    .collect();
                assert_eq!(*actual, expected);
                witnesses += actual.len();
                ranks += 1;
            }
        }
    }
    println!("Pareto witness ranks={ranks}, retained={witnesses}, disagreements=0");
    assert_eq!(ranks, 2401);
}

#[test]
fn pareto_witnesses_keep_interleaved_ties_and_refute_weak_collapse() {
    use zeno_adp::algebras::ParetoWitnesses;

    fn objective(arity: usize, a: i64, b: i64) -> Objective {
        Objective {
            arity,
            cost: [a, b],
        }
    }

    fn weight(op: &Objective) -> (i64, i64) {
        (op.cost[0], op.cost[1])
    }

    let a = objective(0, 1, 0);
    let b = objective(0, 0, 1);
    let dominated = objective(0, 1, 1);
    let parent = objective(1, 0, 0);
    let chart = Chart::new(
        vec![
            vec![
                Rule::new(a.clone(), []),
                Rule::new(b, []),
                Rule::new(a, []),
                Rule::new(dominated, []),
            ],
            vec![],
            vec![Rule::new(parent.clone(), [0]), Rule::new(parent, [1])],
        ],
        2,
    )
    .unwrap();
    let ordered = ParetoWitnesses::new(weight);
    let report = audit(&chart, &ordered).unwrap();
    assert!(report.first_failure.is_none());
    assert_eq!(
        report.tabulated.iter().map(|a| a.value).collect::<Vec<_>>(),
        [(1, 0), (0, 1), (1, 0)]
    );
    assert_eq!(report.tabulated[0], report.tabulated[2]);
    assert!(tabulate_cells(&chart, &ordered).unwrap()[1].is_empty());

    struct Collapse;
    impl Algebra<Objective> for Collapse {
        type Value = RankedTree<Objective, (i64, i64)>;
        fn apply(&self, op: &Objective, children: &[&Self::Value]) -> Result<Self::Value, Error> {
            let mut answer = ParetoWitnesses::new(weight).apply(op, children)?;
            if op.arity > 0 {
                answer.value = (0, 0);
            }
            Ok(answer)
        }
        fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
            ParetoWitnesses::new(weight).choose(candidates)
        }
    }
    let report = audit(&chart, &Collapse).unwrap();
    assert_eq!(report.oracle.len(), 4);
    assert_eq!(report.tabulated.len(), 3);
    assert_eq!(report.first_failure.unwrap().cell, 2);
}

#[test]
fn pareto_witnesses_score_both_binary_children_in_order() {
    use zeno_adp::algebras::ParetoWitnesses;

    let rule = |cost, children: &[usize]| {
        Rule::new(
            Objective {
                arity: children.len(),
                cost,
            },
            children,
        )
    };
    let chart = Chart::new(
        vec![
            vec![rule([1, -2], &[])],
            vec![rule([3, -5], &[])],
            vec![rule([0, 0], &[0, 0]), rule([0, 0], &[0, 1])],
        ],
        2,
    )
    .unwrap();
    let question = ParetoWitnesses::new(|op: &Objective| (op.cost[0], op.cost[1]));
    let cells = tabulate_cells(&chart, &question).unwrap();
    assert_eq!(
        cells[2].iter().map(|a| a.value).collect::<Vec<_>>(),
        [(2, -4), (4, -7)]
    );
    for (rank, row) in cells.iter().enumerate() {
        let expected = enumerate(&at(&chart, rank));
        assert!(row
            .iter()
            .map(|answer| (&answer.tree, answer.value))
            .eq(expected.iter().map(|tree| (tree, score(tree)))));
    }
    assert!(audit(&chart, &question).unwrap().first_failure.is_none());
}
