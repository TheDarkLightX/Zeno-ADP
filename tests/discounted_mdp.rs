use std::time::{Duration, Instant};

use num_bigint::BigInt;
use zeno_adp::mdp::{Action, Certificate, Error, Model, Rational};

const CASES: usize = 128;
const MAX_STATES: usize = 6; // Small enough to enumerate deterministic policies.
const MAX_ACTIONS: usize = 3;
const MAX_TICKETS: i128 = 11; // Covers non-dyadic transition rows.
const DISCOUNTS: [(i128, i128); 4] = [(0, 1), (1, 2), (9, 10), (99, 100)];

fn ratio(top: i128, bottom: i128) -> Rational {
    Rational::new(top.into(), bottom.into()).unwrap()
}

#[derive(Clone)]
struct Row {
    reward: i128,
    tickets: Vec<i128>,
}

fn fixture(case: usize) -> Vec<Vec<Row>> {
    let states = case % MAX_STATES + 1;
    let mut sample = case as u64;
    let mut next = || {
        // Fixed LCG constants from MMIX, high bits for deterministic fixture variation.
        sample = sample
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        i128::from(sample >> 32)
    };
    (0..states)
        .map(|state| {
            let actions = (case / MAX_STATES + state) % MAX_ACTIONS + 1;
            (0..actions)
                .map(|_| {
                    let mut tickets = vec![0; states];
                    for _ in 0..(next() % MAX_TICKETS + 1) {
                        tickets[next() as usize % states] += 1;
                    }
                    Row {
                        reward: next() % 15 - 7,
                        tickets,
                    }
                })
                .collect()
        })
        .collect()
}

fn model(rows: &[Vec<Row>], (g, d): (i128, i128)) -> Model {
    let states = rows
        .iter()
        .map(|actions| {
            actions
                .iter()
                .map(|row| {
                    let total = row.tickets.iter().sum();
                    let transitions = row
                        .tickets
                        .iter()
                        .enumerate()
                        .filter(|(_, t)| **t > 0)
                        .map(|(to, &t)| (to, ratio(t, total)))
                        .collect();
                    Action {
                        reward: ratio(row.reward, 1),
                        transitions,
                    }
                })
                .collect()
        })
        .collect();
    Model::new(ratio(g, d), states).unwrap()
}

// Integer determinant via fraction-free elimination. In this domain each
// entry is bounded by 1100, except one replaced column bounded by 7700.
// The largest product of intermediate minors fits in i128 (Leibniz bound).
fn determinant(mut matrix: Vec<Vec<i128>>) -> i128 {
    let n = matrix.len();
    let mut sign = 1;
    let mut previous = 1;
    for column in 0..n - 1 {
        let Some(pivot) = (column..n).find(|&row| matrix[row][column] != 0) else {
            return 0;
        };
        if pivot != column {
            matrix.swap(pivot, column);
            sign = -sign;
        }
        let pivot = matrix[column][column];
        for row in column + 1..n {
            for entry in column + 1..n {
                let product =
                    pivot * matrix[row][entry] - matrix[row][column] * matrix[column][entry];
                assert_eq!(product % previous, 0);
                matrix[row][entry] = product / previous;
            }
        }
        previous = pivot;
    }
    sign * matrix[n - 1][n - 1]
}

fn enumerate_policies(rows: &[Vec<Row>], (g, d): (i128, i128)) -> (usize, Vec<Rational>) {
    let n = rows.len();
    let count = rows.iter().map(Vec::len).product();
    let mut best: Vec<Option<(BigInt, BigInt)>> = vec![None; n];
    for mut index in 0..count {
        let (matrix, rhs): (Vec<_>, Vec<_>) = rows
            .iter()
            .enumerate()
            .map(|(s, actions)| {
                let row = &actions[index % actions.len()];
                index /= actions.len();
                let total = row.tickets.iter().sum::<i128>() * d;
                let coefficients = row
                    .tickets
                    .iter()
                    .enumerate()
                    .map(|(t, &tickets)| if s == t { total } else { 0 } - g * tickets)
                    .collect::<Vec<_>>();
                (coefficients, total * row.reward)
            })
            .unzip();
        let det = determinant(matrix.clone());
        assert_ne!(det, 0);
        for (state, current) in best.iter_mut().enumerate() {
            let mut replaced = matrix.clone();
            for (row, &value) in replaced.iter_mut().zip(&rhs) {
                row[state] = value;
            }
            let numerator = BigInt::from(determinant(replaced) * det.signum());
            let denominator = BigInt::from(det.abs());
            if current
                .as_ref()
                .is_none_or(|(a, b)| &numerator * b > a * &denominator)
            {
                *current = Some((numerator, denominator));
            }
        }
    }
    (
        count,
        best.into_iter()
            .map(|value| {
                let (a, b) = value.unwrap();
                Rational::new(a, b).unwrap()
            })
            .collect(),
    )
}

#[test]
fn all_state_values_equal_exhaustive_policy_enumeration() {
    let mut state_count = 0;
    let mut policy_count = 0;
    let mut bit_lengths = (0, 0);
    let (mut solver_time, mut checker_time, mut oracle_time) =
        (Duration::ZERO, Duration::ZERO, Duration::ZERO);
    for case in 0..CASES {
        let rows = fixture(case);
        let discount = DISCOUNTS[(case / 3) % DISCOUNTS.len()];
        let model = model(&rows, discount);
        let start = Instant::now();
        let mut answer = model.solve().unwrap().into_inner();
        solver_time += start.elapsed();
        let start = Instant::now();
        model.verify(&answer).unwrap();
        checker_time += start.elapsed();
        let start = Instant::now();
        let (policies, expected) = enumerate_policies(&rows, discount);
        oracle_time += start.elapsed();
        assert_eq!(answer.values, expected, "case {case}");
        for value in &answer.values {
            bit_lengths.0 = bit_lengths.0.max(value.numerator().bits());
            bit_lengths.1 = bit_lengths.1.max(value.denominator().bits());
        }
        policy_count += policies;
        state_count += rows.len();
        let slot = case % rows.len();
        answer.values[slot] = &answer.values[slot] + &ratio(1, 101);
        assert!(matches!(
            model.verify(&answer),
            Err(Error::PolicyEquality { .. })
        ));
    }
    println!("MDP {CASES} models, {state_count} states, {policy_count} policies, {CASES} alterations rejected, 0 disagreements");
    println!("MDP times solve including check {solver_time:?}, check alone {checker_time:?}, oracle {oracle_time:?}, bits {bit_lengths:?}");
}

fn action(reward: i64, target: usize) -> Action {
    Action {
        reward: reward.into(),
        transitions: vec![(target, 1.into())],
    }
}

#[test]
fn certificate_controls() {
    // State 1 is disconnected from state 0. Duplicate optimal actions tie.
    let model = Model::new(
        ratio(1, 2),
        vec![
            vec![action(0, 0), action(1, 0), action(1, 0)],
            vec![action(-1, 1)],
        ],
    )
    .unwrap();
    let best = model.solve().unwrap();
    assert_eq!(best.label(), "Exact");
    let best = best.into_inner();
    assert_eq!(best.policy, [1, 0]);
    assert_eq!(best.values, [2.into(), (-2).into()]);
    let mut other = best.clone();
    other.policy[0] = 2;
    model.verify(&other).unwrap();
    other.policy[0] = 3;
    assert_eq!(
        model.verify(&other),
        Err(Error::InvalidPolicyAction {
            state: 0,
            action: 3
        })
    );
    let mut wrong = best.clone();
    wrong.values[1] = (-1).into();
    assert_eq!(
        model.verify(&wrong),
        Err(Error::PolicyEquality {
            state: 1,
            action: 0
        })
    );
    wrong.policy.pop();
    assert!(matches!(
        model.verify(&wrong),
        Err(Error::CertificateSize { .. })
    ));
    let suboptimal = Certificate {
        policy: vec![0, 0],
        values: vec![0.into(), (-2).into()],
    };
    assert_eq!(
        model.verify(&suboptimal),
        Err(Error::BetterAction {
            state: 0,
            action: 1
        })
    );
}

#[test]
fn exact_model_admission() {
    let model = |discount, transitions| {
        Model::new(
            discount,
            vec![vec![Action {
                reward: 0.into(),
                transitions,
            }]],
        )
    };
    assert!(matches!(
        model(1.into(), vec![(0, 1.into())]),
        Err(Error::InvalidDiscount)
    ));
    assert!(matches!(
        model((-1).into(), vec![(0, 1.into())]),
        Err(Error::InvalidDiscount)
    ));
    assert!(matches!(
        Model::new(0.into(), vec![]),
        Err(Error::EmptyModel)
    ));
    assert!(matches!(
        Model::new(0.into(), vec![vec![]]),
        Err(Error::NoActions { state: 0 })
    ));
    assert!(matches!(
        model(0.into(), vec![(1, 1.into())]),
        Err(Error::InvalidSuccessor { .. })
    ));
    assert!(matches!(
        model(0.into(), vec![(0, ratio(-1, 2)), (0, ratio(3, 2))]),
        Err(Error::NegativeProbability { .. })
    ));
    assert!(matches!(
        model(0.into(), vec![(0, ratio(1, 2))]),
        Err(Error::ProbabilitySum { .. })
    ));
    assert!(matches!(
        model(0.into(), vec![]),
        Err(Error::ProbabilitySum { .. })
    ));
    assert!(model(0.into(), vec![(0, ratio(1, 2)), (0, ratio(1, 2))]).is_ok());
    assert!(Rational::new(1.into(), 0.into()).is_none());
    assert_eq!(ratio(-2, -4), ratio(1, 2));
    assert_eq!(ratio(2, -4), ratio(-1, 2));
}

#[test]
fn wide_signed_solution() {
    const WIDE_SHIFT: usize = 160; // Exceeds the underlying 128-bit scalar range.
    let wide = BigInt::from(1) << WIDE_SHIFT;
    let reward = Rational::new((-1).into(), wide.clone()).unwrap();
    let model = Model::new(
        ratio(1, 3),
        vec![vec![Action {
            reward,
            transitions: vec![(0, ratio(1, 3)), (0, ratio(2, 3))],
        }]],
    )
    .unwrap();
    let result = model.solve().unwrap().into_inner();
    // (-1 / 2^160) / (1 - 1/3) = -3 / (2 * 2^160).
    assert_eq!(
        result.values,
        [Rational::new((-3).into(), 2 * wide).unwrap()]
    );
    assert_eq!(result.values[0].denominator().bits(), WIDE_SHIFT as u64 + 2);
    println!(
        "MDP wide bits ({}, {})",
        result.values[0].numerator().bits(),
        result.values[0].denominator().bits()
    );
}
