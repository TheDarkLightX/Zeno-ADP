use std::time::Instant;

use num_bigint::BigUint;
use zeno_adp::algebras::{Additive, Cost, ScoredOperator};
use zeno_adp::cyclic::{Certificate, Error, GroundChart, Production, Question, Solution, Witness};
use zeno_adp::{Chart, Operator, Rule};

const CASES: usize = 128;
const MAX_CELLS: usize = 4; // Allows complete enumeration of derivations through n levels.
const MAX_ALTERNATIVES: u32 = 2;
const MAX_ARITY: u32 = 2;
const MAX_WEIGHT: u32 = 3; // Includes zero-cost ties and distinct positive weights.
const STRESS_CELLS: usize = 256; // The registered sparse dependency depth.

struct RawRule {
    weight: u32,
    children: Vec<usize>,
}

fn fixture(case: usize) -> Vec<Vec<RawRule>> {
    let n = case % MAX_CELLS + 1;
    let mut sample = case as u32 + 1;
    let mut next = || {
        // Xorshift32 parameters for a deterministic nonzero state.
        sample ^= sample << 13;
        sample ^= sample >> 17;
        sample ^= sample << 5;
        sample
    };
    (0..n)
        .map(|_| {
            (0..next() % (MAX_ALTERNATIVES + 1))
                .map(|_| RawRule {
                    weight: next() % (MAX_WEIGHT + 1),
                    children: (0..next() % (MAX_ARITY + 1))
                        .map(|_| next() as usize % n)
                        .collect(),
                })
                .collect()
        })
        .collect()
}

fn chart(raw: &[Vec<RawRule>]) -> GroundChart {
    GroundChart::new(
        raw.iter()
            .map(|row| {
                row.iter()
                    .map(|rule| Production::new(BigUint::from(rule.weight), rule.children.clone()))
                    .collect()
            })
            .collect(),
        0,
    )
    .unwrap()
}

// Enumerate the complete tree-cost bag, including ordered child multiplicities.
// A minimal-cost tree can remove any repeated cell along a path at no cost increase.
fn derivations(raw: &[Vec<RawRule>], cell: usize, depth: usize) -> Vec<u32> {
    if depth == 0 {
        return Vec::new();
    }
    raw[cell]
        .iter()
        .flat_map(|rule| {
            let mut constructor = vec![rule.weight];
            for &child in &rule.children {
                let alternatives = derivations(raw, child, depth - 1);
                constructor = constructor
                    .iter()
                    .flat_map(|&prefix| alternatives.iter().map(move |&value| prefix + value))
                    .collect();
            }
            constructor
        })
        .collect()
}

// Synchronous bottom replay with exact arithmetic on this bounded test domain.
fn bottom(raw: &[Vec<RawRule>]) -> (Vec<Option<u32>>, usize, usize) {
    let mut old = vec![None; raw.len()];
    let mut visits = 0;
    for updates in 0..=raw.len() {
        let next: Vec<_> = raw
            .iter()
            .map(|row| {
                row.iter()
                    .filter_map(|rule| {
                        visits += 1;
                        rule.children.iter().try_fold(rule.weight, |sum, &child| {
                            old[child].map(|value| sum + value)
                        })
                    })
                    .min()
            })
            .collect();
        if next == old {
            return (next, updates, visits);
        }
        old = next;
    }
    panic!("bottom replay exceeded the n-round bound");
}

fn check_both(chart: &GroundChart, expected: &[Option<u32>]) {
    let Solution::MinPlus(result) = chart
        .solve(Question::NonnegativeMinPlus)
        .unwrap()
        .into_inner()
    else {
        panic!()
    };
    assert_eq!(
        result.values,
        expected
            .iter()
            .map(|cost| cost.map(BigUint::from))
            .collect::<Vec<_>>()
    );
    let Solution::Boolean(result) = chart.solve(Question::Boolean).unwrap().into_inner() else {
        panic!()
    };
    assert_eq!(
        result.values,
        expected
            .iter()
            .map(|cost| cost.map(|_| ()))
            .collect::<Vec<_>>()
    );
}

#[derive(Clone)]
struct RankedRule {
    weight: u32,
    arity: usize,
}

impl Operator for RankedRule {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for RankedRule {
    fn cost(&self) -> Cost {
        Cost::Finite(self.weight.into())
    }
}

fn ranked_unrolling(raw: &[Vec<RawRule>]) -> Vec<Vec<Cost>> {
    let n = raw.len();
    let mut cells = vec![vec![]; n];
    for level in 0..n {
        for row in raw {
            cells.push(
                row.iter()
                    .map(|rule| {
                        Rule::new(
                            RankedRule {
                                weight: rule.weight,
                                arity: rule.children.len(),
                            },
                            rule.children
                                .iter()
                                .map(|&child| level * n + child)
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect(),
            );
        }
    }
    let chart = Chart::new(cells, n * n).unwrap();
    zeno_adp::tabulate_cells(&chart, &Additive::default()).unwrap()
}

#[test]
fn bounded_height_trees_agree_at_every_cell() {
    let mut cells = 0;
    let mut reference_ranks = 0;
    let mut trees = 0;
    let mut maximum_rounds = 0;
    for case in 0..CASES {
        let raw = fixture(case);
        let ranked = ranked_unrolling(&raw);
        let mut expected = Vec::new();
        for (depth, layer) in ranked.chunks_exact(raw.len()).enumerate() {
            expected.clear();
            for (cell, observed) in layer.iter().enumerate() {
                let bag = derivations(&raw, cell, depth);
                if depth == raw.len() {
                    trees += bag.len();
                }
                let minimum = bag.into_iter().min();
                let reference = minimum.map(|cost| Cost::Finite(cost.into()));
                assert_eq!(
                    observed,
                    reference.as_slice(),
                    "chart {case}, depth {depth}, cell {cell}"
                );
                expected.push(minimum);
            }
        }
        reference_ranks += ranked.len();
        let (replay, rounds, _) = bottom(&raw);
        assert_eq!(replay, expected, "generated chart {case}");
        check_both(&chart(&raw), &expected);
        maximum_rounds = maximum_rounds.max(rounds);
        cells += raw.len();
    }
    println!("cyclic {CASES} charts, {cells} cells, {reference_ranks} ranked reference cells, {trees} bounded trees, {maximum_rounds} maximum changed rounds, 0 disagreements");
}

#[test]
fn sparse_chain_and_cycle_agree_with_whole_chart_replay() {
    for cyclic in [false, true] {
        let mut raw = vec![vec![RawRule {
            weight: 1,
            children: vec![],
        }]];
        raw.extend((1..STRESS_CELLS).map(|cell| {
            vec![RawRule {
                weight: 1,
                children: vec![cell - 1],
            }]
        }));
        if cyclic {
            raw[0].push(RawRule {
                weight: 0,
                children: vec![STRESS_CELLS - 1],
            });
        }
        let start = Instant::now();
        let (expected, rounds, visits) = bottom(&raw);
        let replay_time = start.elapsed();
        assert_eq!(rounds, STRESS_CELLS);
        let chart = chart(&raw);
        let start = Instant::now();
        let Solution::MinPlus(result) = chart
            .solve(Question::NonnegativeMinPlus)
            .unwrap()
            .into_inner()
        else {
            panic!()
        };
        let solve_time = start.elapsed();
        let start = Instant::now();
        chart.verify(&Solution::MinPlus(result.clone())).unwrap();
        let verify_time = start.elapsed();
        assert_eq!(
            result.values,
            expected
                .iter()
                .map(|cost| cost.map(BigUint::from))
                .collect::<Vec<_>>()
        );
        check_both(&chart, &expected);
        let rules: usize = raw.iter().map(Vec::len).sum();
        println!("cyclic stress {cyclic}: {rules} productions, {rounds} changed rounds, {visits} bottom production visits, replay {replay_time:?}, min-plus solve/check {solve_time:?}, separate check {verify_time:?}");
    }
}

#[test]
fn wrong_fixed_points_and_witnesses_are_rejected() {
    let loop_rule = Production::new(BigUint::ZERO, vec![0]);
    let root = GroundChart::new(vec![vec![loop_rule.clone()]], 0).unwrap();
    check_both(&root, &[None]);
    assert_eq!(root.solve(Question::Boolean).unwrap().label(), "Exact");
    assert_eq!(
        root.solve(Question::NonnegativeMinPlus).unwrap().label(),
        "Exact"
    );

    let cyclic = Some(Witness { rule: 0, rank: 0 });
    assert_eq!(
        root.verify(&Solution::Boolean(Certificate {
            values: vec![Some(())],
            witnesses: vec![cyclic]
        })),
        Err(Error::Witness { cell: 0 })
    );
    for cost in [0u32, 1, u32::MAX] {
        assert_eq!(
            root.verify(&Solution::MinPlus(Certificate {
                values: vec![Some(cost.into())],
                witnesses: vec![cyclic]
            })),
            Err(Error::Witness { cell: 0 })
        );
    }
    println!("unseeded self-loop: 4 spurious fixed-point certificates rejected");

    let chart = GroundChart::new(
        vec![
            vec![
                loop_rule,
                Production::new(0u32.into(), vec![1]),
                Production::new(1u32.into(), vec![]),
            ],
            vec![Production::new(0u32.into(), vec![0])],
            vec![Production::new(2u32.into(), vec![1, 1])],
        ],
        2,
    )
    .unwrap();
    check_both(&chart, &[Some(1), Some(1), Some(4)]);
    let Solution::MinPlus(mut good) = chart
        .solve(Question::NonnegativeMinPlus)
        .unwrap()
        .into_inner()
    else {
        panic!()
    };
    assert_eq!(good.witnesses[0].unwrap().rule, 2);
    let mut broken = good.clone();
    broken.values[2] = Some(3u32.into());
    assert_eq!(
        chart.verify(&Solution::MinPlus(broken)),
        Err(Error::Equation { cell: 2 })
    );
    let mut broken = good.clone();
    broken.witnesses[1] = Some(Witness { rule: 0, rank: 0 });
    assert_eq!(
        chart.verify(&Solution::MinPlus(broken)),
        Err(Error::Witness { cell: 1 })
    );
    let mut broken = good.clone();
    broken.witnesses[2] = None;
    assert_eq!(
        chart.verify(&Solution::MinPlus(broken)),
        Err(Error::Witness { cell: 2 })
    );
    good.values.pop();
    assert!(matches!(
        chart.verify(&Solution::MinPlus(good)),
        Err(Error::CertificateSize { .. })
    ));
}

#[test]
fn closed_carriers_child_references_and_wide_weights() {
    assert_eq!("boolean".parse(), Ok(Question::Boolean));
    assert_eq!(
        "nonnegative-min-plus".parse(),
        Ok(Question::NonnegativeMinPlus)
    );
    for name in ["signed-min-plus", "count", "sum-product", "custom"] {
        assert_eq!(
            name.parse::<Question>(),
            Err(Error::UnsupportedCarrier(name.into()))
        );
    }
    assert!(matches!(
        GroundChart::new(vec![], 0),
        Err(Error::MissingRoot(0))
    ));
    assert!(matches!(
        GroundChart::new(vec![vec![Production::new(0u32.into(), vec![1])]], 0),
        Err(Error::InvalidChild {
            cell: 0,
            rule: 0,
            child: 1
        })
    ));

    const WIDE_SHIFT: usize = 160; // Above the 128-bit scalar range.
    let wide = BigUint::from(1u32) << WIDE_SHIFT;
    let chart = GroundChart::new(
        vec![
            vec![Production::new(wide.clone(), vec![])],
            vec![Production::new(wide.clone(), vec![0, 0])],
        ],
        1,
    )
    .unwrap();
    let Solution::MinPlus(solution) = chart
        .solve(Question::NonnegativeMinPlus)
        .unwrap()
        .into_inner()
    else {
        panic!()
    };
    assert_eq!(solution.values, [Some(wide.clone()), Some(&wide * 3u32)]);
}
