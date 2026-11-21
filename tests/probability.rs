#[path = "support/ranked_fixture.rs"]
mod fixture;

use fixture::{assignments, at, fixture, RANKS};
use zeno_adp::probability::{
    inside_outside, log_inside_outside, partition, ExactSampler, LogMaxProduct, LogSumProduct,
    LogWeight, MaxProduct, Rational as Q, SumProduct, WeightedOperator,
};
use zeno_adp::{audit, enumerate, exhaustive, tabulate_cells, Chart, Error, Operator, Rule, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Weighted {
    id: usize,
    arity: usize,
    weight: Q,
}

impl Operator for Weighted {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl WeightedOperator for Weighted {
    fn weight(&self) -> Q {
        self.weight
    }
}

fn mass(tree: &Tree<Weighted>) -> Q {
    tree.children
        .iter()
        .map(mass)
        .fold(tree.operator.weight, mul)
}

fn mul(a: Q, b: Q) -> Q {
    a.checked_mul(b).unwrap()
}

fn sum(weights: impl IntoIterator<Item = Q>) -> Q {
    weights
        .into_iter()
        .fold(Q::ZERO, |a, b| a.checked_add(b).unwrap())
}

/// Enumerate single-hole contexts by unfolding from the root. All
/// off-path siblings range independently over their explicit trees.
fn contexts(
    chart: &Chart<Weighted>,
    tree_masses: &[Vec<Q>],
    parent: usize,
    target: usize,
) -> Vec<Q> {
    if parent == target {
        return vec![Q::ONE];
    }
    let mut result = Vec::new();
    for rule in &chart.cells()[parent] {
        for (hole, &child) in rule.children.iter().enumerate() {
            let mut products = contexts(chart, tree_masses, child, target);
            for (slot, &sibling) in rule.children.iter().enumerate() {
                if slot != hole {
                    products = products
                        .iter()
                        .flat_map(|&p| tree_masses[sibling].iter().map(move |&q| mul(p, q)))
                        .collect();
                }
            }
            result.extend(products.into_iter().map(|p| mul(rule.operator.weight, p)));
        }
    }
    result
}

fn probability(
    chart: &Chart<Weighted>,
    cell: usize,
    tree: &Tree<Weighted>,
    policies: &[Option<Vec<Q>>],
) -> Q {
    let (index, rule) = chart.cells()[cell]
        .iter()
        .enumerate()
        .find(|(_, rule)| rule.operator.id == tree.operator.id)
        .unwrap();
    let Some(weights) = &policies[cell] else {
        return Q::ZERO;
    };
    rule.children
        .iter()
        .zip(&tree.children)
        .map(|(&child, term)| probability(chart, child, term, policies))
        .fold(weights[index], mul)
}

fn check_log(exact: Q, actual: LogWeight, maximum: &mut f64) {
    if exact == Q::ZERO {
        assert_eq!(actual.ln(), f64::NEG_INFINITY);
    } else {
        // Registered slack for the bounded expression depth and libm
        // calls. Zero is checked exactly above.
        const EPSILON_ALLOWANCE: f64 = 64.0;
        let expected = (exact.numerator() as f64 / exact.denominator() as f64).ln();
        let error = (actual.ln() - expected).abs() / (f64::EPSILON * expected.abs().max(1.0));
        assert!(
            error <= EPSILON_ALLOWANCE,
            "{actual:?} versus {exact:?}: {error}"
        );
        *maximum = maximum.max(error);
    }
}

#[test]
fn complete_weighted_domain() {
    let mut charts = 0;
    let mut derivations = 0;
    let mut rule_probabilities = 0;
    let mut context_occurrences = 0;
    let mut zero_partitions = 0;
    let mut maximum_log_error = 0.0f64;
    for weights in assignments([Q::ZERO, Q::new(1, 3).unwrap(), Q::ONE]) {
        for root in 0..RANKS {
            let chart = fixture(root, |id, group, arity| Weighted {
                id,
                arity,
                weight: weights[group],
            });
            let exact = inside_outside(&chart).unwrap();
            let log = log_inside_outside(&chart).unwrap();
            let exact_sum = tabulate_cells(&chart, &SumProduct).unwrap();
            let exact_max = tabulate_cells(&chart, &MaxProduct).unwrap();
            let log_sum = tabulate_cells(&chart, &LogSumProduct).unwrap();
            let log_max = tabulate_cells(&chart, &LogMaxProduct).unwrap();
            let sampler = ExactSampler::new(&chart).unwrap();
            let policies: Vec<_> = (0..RANKS)
                .map(|cell| sampler.rule_probabilities(cell).unwrap())
                .collect();
            let trees: Vec<_> = (0..RANKS)
                .map(|cell| enumerate(&at(&chart, cell)))
                .collect();
            let masses: Vec<_> = trees
                .iter()
                .map(|terms| terms.iter().map(mass).collect::<Vec<_>>())
                .collect();
            assert_eq!(exact.partition(), &partition(&chart).unwrap());
            assert_eq!(exact.partition(), &exact.inside()[root]);
            assert_eq!(log.partition(), &log.inside()[root]);
            zero_partitions += usize::from(*exact.partition() == Q::ZERO);
            assert!(audit(&chart, &SumProduct).unwrap().first_failure.is_none());
            assert!(audit(&chart, &MaxProduct).unwrap().first_failure.is_none());

            for cell in 0..RANKS {
                let on_cell = at(&chart, cell);
                let sum_reference = exhaustive(&on_cell, &SumProduct).unwrap();
                let max_reference = exhaustive(&on_cell, &MaxProduct).unwrap();
                assert_eq!(exact_sum[cell], sum_reference);
                assert_eq!(exact_max[cell], max_reference);
                assert_eq!(
                    exact.inside()[cell],
                    sum_reference.first().copied().unwrap_or(Q::ZERO)
                );
                assert_eq!(exact.inside()[cell], sum(masses[cell].iter().copied()));
                assert_eq!(log_sum[cell].len(), sum_reference.len());
                assert_eq!(log_max[cell].len(), max_reference.len());
                if let Some((&total, &maximum)) = sum_reference.first().zip(max_reference.first()) {
                    check_log(total, log_sum[cell][0], &mut maximum_log_error);
                    check_log(maximum, log_max[cell][0], &mut maximum_log_error);
                }
                let contexts = contexts(&chart, &masses, root, cell);
                context_occurrences += contexts.len();
                assert_eq!(exact.outside()[cell], sum(contexts));
                check_log(
                    exact.inside()[cell],
                    log.inside()[cell],
                    &mut maximum_log_error,
                );
                check_log(
                    exact.outside()[cell],
                    log.outside()[cell],
                    &mut maximum_log_error,
                );

                if let Some(local) = &policies[cell] {
                    assert_eq!(sum(local.iter().copied()), Q::ONE);
                    for (rule, &actual) in chart.cells()[cell].iter().zip(local) {
                        let expected = sum(trees[cell]
                            .iter()
                            .filter(|tree| tree.operator.id == rule.operator.id)
                            .map(mass));
                        assert_eq!(
                            Some(actual),
                            expected.checked_div(exact.inside()[cell]).unwrap()
                        );
                        rule_probabilities += 1;
                    }
                } else {
                    assert_eq!(exact.inside()[cell], Q::ZERO);
                    assert_eq!(
                        sampler.sample_from(cell, || panic!("zero mass reads no words")),
                        None
                    );
                }
                for tree in &trees[cell] {
                    assert_eq!(
                        probability(&chart, cell, tree, &policies),
                        mass(tree)
                            .checked_div(exact.inside()[cell])
                            .unwrap()
                            .unwrap_or(Q::ZERO)
                    );
                    derivations += 1;
                }
            }
            charts += 1;
        }
    }
    println!("{charts} charts, {} cells, {context_occurrences} contexts, {zero_partitions} zero partitions, {rule_probabilities} branch probabilities, {derivations} complete derivation probabilities, 0 disagreements, max scaled log error {maximum_log_error:.3} epsilon", charts * RANKS);
}

#[test]
fn sampled_repeated_positions_use_independent_words() {
    let third = Q::new(1, 3).unwrap();
    let two_thirds = Q::new(2, 3).unwrap();
    let chart = Chart::new(
        vec![
            vec![
                Rule::new(
                    Weighted {
                        id: 0,
                        arity: 0,
                        weight: third,
                    },
                    [],
                ),
                Rule::new(
                    Weighted {
                        id: 1,
                        arity: 0,
                        weight: two_thirds,
                    },
                    [],
                ),
            ],
            vec![Rule::new(
                Weighted {
                    id: 2,
                    arity: 2,
                    weight: Q::ONE,
                },
                [0, 0],
            )],
        ],
        1,
    )
    .unwrap();
    let sampler = ExactSampler::new(&chart).unwrap();
    let mut observed = [[0; 2]; 2];
    // The accepted local tickets are 0, 1 and 2. Enumerate both
    // independent ordered draws, and compare their exact joint law.
    for first in 0..third.denominator() as u64 {
        for second in 0..third.denominator() as u64 {
            let mut words = [first, second].into_iter();
            let sample = sampler.sample(|| words.next().unwrap()).unwrap();
            assert!(words.next().is_none());
            observed[sample.children[0].operator.id][sample.children[1].operator.id] += 1;
        }
    }
    assert_eq!(observed, [[1, 2], [2, 4]]);
}

#[test]
fn rational_limits_and_linear_underflow() {
    let max = u128::MAX;
    assert_eq!(Q::new(1, 0), None);
    assert_eq!(Q::ONE.checked_div(Q::ZERO), Ok(None));
    assert!(Q::new(max - 1, max).unwrap() < Q::new(max, max - 1).unwrap());
    assert!(Q::new(max - 2, max - 1).unwrap() < Q::new(max - 1, max).unwrap());
    assert_eq!(
        Q::new(max, 2).unwrap().checked_mul(Q::new(2, max).unwrap()),
        Ok(Q::ONE)
    );
    assert_eq!(
        Q::new(max, 1).unwrap().checked_add(Q::ONE),
        Err(Error::Overflow)
    );

    // One step past the smallest positive subnormal, rounded to zero.
    const UNDERFLOW_NODES: usize = (-f64::MIN_EXP + f64::MANTISSA_DIGITS as i32 + 1) as usize;
    let half = Q::new(1, 2).unwrap();
    let cells = (0..UNDERFLOW_NODES)
        .map(|id| {
            let children: Vec<_> = id.checked_sub(1).into_iter().collect();
            vec![Rule::new(
                Weighted {
                    id,
                    arity: children.len(),
                    weight: half,
                },
                children,
            )]
        })
        .collect();
    let chart = Chart::new(cells, UNDERFLOW_NODES - 1).unwrap();
    assert_eq!(partition(&chart), Err(Error::Overflow));
    assert_eq!((0..UNDERFLOW_NODES).fold(1.0, |x, _| x * 0.5), 0.0);
    let log = *log_inside_outside(&chart).unwrap().partition();
    assert!(log.ln().is_finite() && log.ln() < f64::MIN_POSITIVE.ln());
    println!(
        "linear underflow at {UNDERFLOW_NODES} factors; log partition {}",
        log.ln()
    );
}

#[test]
fn outside_uses_every_sibling_except_the_distinguished_slot() {
    let one = |id| Weighted {
        id,
        arity: 0,
        weight: Q::ONE,
    };
    let two = Q::new(2, 1).unwrap();
    let three = Q::new(3, 1).unwrap();
    let five = Q::new(5, 1).unwrap();
    let chart = Chart::new(
        vec![
            vec![Rule::new(
                Weighted {
                    weight: two,
                    ..one(0)
                },
                [],
            )],
            vec![Rule::new(
                Weighted {
                    weight: three,
                    ..one(1)
                },
                [],
            )],
            vec![],
            vec![
                Rule::new(
                    Weighted {
                        id: 2,
                        arity: 4,
                        weight: five,
                    },
                    [0, 1, 0, 1],
                ),
                Rule::new(
                    Weighted {
                        id: 3,
                        arity: 3,
                        weight: five,
                    },
                    [0, 2, 1],
                ),
                Rule::new(
                    Weighted {
                        id: 4,
                        arity: 3,
                        weight: five,
                    },
                    [2, 2, 0],
                ),
            ],
        ],
        3,
    )
    .unwrap();
    let exact = inside_outside(&chart).unwrap();
    assert_eq!(
        exact.inside(),
        &[two, three, Q::ZERO, Q::new(180, 1).unwrap()]
    );
    assert_eq!(
        exact.outside(),
        &[
            Q::new(180, 1).unwrap(),
            Q::new(120, 1).unwrap(),
            Q::new(30, 1).unwrap(),
            Q::ONE
        ]
    );
}

#[test]
fn near_unit_logs_preserve_direction_at_every_repeated_child_rank() {
    // Below this exponent, the adjacent floats need not both round to the pivot.
    const FIRST_POWER: u32 = f64::MANTISSA_DIGITS + 1;
    // Ten additional doublings turn a log of about ±1 into about ±1024.
    const EXTRA_DOUBLINGS: u32 = 10;
    const RELATIVE_TOLERANCE: f64 = 8.0 * f64::EPSILON;
    let mut compared = 0;
    let mut max_error = 0.0_f64;
    for power in FIRST_POWER..u128::BITS {
        let unit = 1u128 << power;
        for (numerator, sign) in [(unit - 1, -1.0), (unit + 1, 1.0)] {
            let mut cells = vec![vec![Rule::new(
                Weighted {
                    id: 0,
                    arity: 0,
                    weight: Q::new(numerator, unit).unwrap(),
                },
                [],
            )]];
            for rank in 1..=power as usize + EXTRA_DOUBLINGS as usize {
                cells.push(vec![Rule::new(
                    Weighted {
                        id: 1,
                        arity: 2,
                        weight: Q::ONE,
                    },
                    [rank - 1, rank - 1],
                )]);
            }
            let root = cells.len() - 1;
            let chart = Chart::new(cells, root).unwrap();
            let sums = tabulate_cells(&chart, &LogSumProduct).unwrap();
            let maxima = tabulate_cells(&chart, &LogMaxProduct).unwrap();
            // For |x| <= 2^-54, truncating ln(1+x) after x costs at most
            // |x|/(2*(1-|x|)) relative to x, from integrating t/(1+t).
            // Multiplication by powers of two is exact on this domain.
            let mut expected = sign / unit as f64;
            for (rank, (total, best)) in sums.iter().zip(&maxima).enumerate() {
                for actual in [total[0].ln(), best[0].ln()] {
                    let error = (actual / expected - 1.0).abs();
                    assert!(
                        error <= RELATIVE_TOLERANCE,
                        "{power} {sign} {rank}: {actual}"
                    );
                    max_error = max_error.max(error);
                    compared += 1;
                }
                expected *= 2.0;
            }
        }
    }
    println!("near-unit repeated children: {compared} log results, max error vs linear oracle {} epsilon", max_error / f64::EPSILON);
}

#[test]
fn wide_sampler_keeps_the_two_word_positions_distinct() {
    let one_high_word = 1u128 << u64::BITS;
    let chart = Chart::new(
        vec![vec![
            Rule::new(
                Weighted {
                    id: 0,
                    arity: 0,
                    weight: Q::ONE,
                },
                [],
            ),
            Rule::new(
                Weighted {
                    id: 1,
                    arity: 0,
                    weight: Q::new(one_high_word, 1).unwrap(),
                },
                [],
            ),
        ]],
        0,
    )
    .unwrap();
    let sampler = ExactSampler::new(&chart).unwrap();
    // The first alternative gets ticket zero only. The denominator
    // 2^64 + 1 includes a ticket with a nonzero high word.
    for (pair, selected) in [([0, 0], 0), ([0, 1], 1), ([1, 0], 1)] {
        let mut words = pair.into_iter();
        let tree = sampler.sample(|| words.next().unwrap()).unwrap();
        assert_eq!(tree.operator.id, selected, "words {pair:?}");
        assert_eq!(words.next(), None);
    }
}

#[test]
fn maximum_weight_can_succeed_when_exhaustive_arithmetic_overflows() {
    let leaf = |id, weight| {
        Rule::new(
            Weighted {
                id,
                arity: 0,
                weight,
            },
            [],
        )
    };
    let chart = Chart::new(
        vec![
            vec![leaf(0, Q::ONE), leaf(1, Q::new(1, u128::MAX).unwrap())],
            vec![Rule::new(
                Weighted {
                    id: 2,
                    arity: 2,
                    weight: Q::ONE,
                },
                [0, 0],
            )],
        ],
        1,
    )
    .unwrap();
    assert_eq!(
        tabulate_cells(&chart, &MaxProduct).unwrap(),
        [vec![Q::ONE], vec![Q::ONE]]
    );
    assert_eq!(exhaustive(&chart, &MaxProduct), Err(Error::Overflow));
}
