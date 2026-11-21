use super::{words, Checks};
use zeno_adp::compiled::{self, Atom, Grammar, Production};
use zeno_adp::probability::{inside_outside, ExactSampler, MaxProduct, Rational, WeightedOperator};
use zeno_adp::{tabulate_cells, Chart, Error, Operator, Rule};

const STATES: usize = 2;
const EMISSIONS: [u128; STATES] = [1, 3]; // Numerators for rolling a over four equiprobable faces.
const FACES: u128 = 4;
const STAY: u128 = 3;

#[derive(Clone, Copy, Debug)]
struct Weighted {
    state: usize,
    weight: Rational,
    arity: usize,
}
impl Operator for Weighted {
    fn arity(&self) -> usize {
        self.arity
    }
}
impl WeightedOperator for Weighted {
    fn weight(&self) -> Rational {
        self.weight
    }
}
fn q(a: u128, b: u128) -> Rational {
    Rational::new(a, b).unwrap()
}
fn weighted<const N: usize>(
    state: usize,
    weight: Rational,
    children: [usize; N],
) -> Rule<Weighted> {
    Rule::new(
        Weighted {
            state,
            weight,
            arity: N,
        },
        children,
    )
}

fn emission(state: usize, observation: u8) -> Rational {
    let a = EMISSIONS[state];
    q(
        match observation {
            b'a' => a,
            b'b' => FACES - a,
            _ => 0,
        },
        FACES,
    )
}
fn transition(from: usize, to: usize) -> Rational {
    q(if from == to { STAY } else { FACES - STAY }, FACES)
}
fn hidden_chart(input: &[u8]) -> Result<Chart<Weighted>, Error> {
    let at = |t, state| t * STATES + state;
    let root = input.len() * STATES;
    let mut cells = vec![Vec::new(); root + 1];
    if input.is_empty() {
        cells[root].push(weighted(0, Rational::ONE, []));
    } else {
        for (t, &obs) in input.iter().enumerate() {
            for state in 0..STATES {
                let e = emission(state, obs);
                if t == 0 {
                    cells[at(t, state)].push(weighted(
                        state,
                        q(1, STATES as u128).checked_mul(e)?,
                        [],
                    ));
                } else {
                    for prev in 0..STATES {
                        cells[at(t, state)].push(weighted(
                            state,
                            transition(prev, state).checked_mul(e)?,
                            [at(t - 1, prev)],
                        ));
                    }
                }
            }
        }
        for state in 0..STATES {
            cells[root].push(weighted(state, Rational::ONE, [at(input.len() - 1, state)]));
        }
    }
    Chart::new(cells, root)
}

pub fn hidden_dice() -> Result<Checks, Error> {
    const MAX_ROLLS: usize = 3; // Includes one interior time with both incoming and outgoing edges.
                                // The direct computation models the four faces of each die and the
                                // four outcomes of the between-roll choice.
    const TRANSITIONS: [[u128; STATES]; STATES] = [[3, 1], [1, 3]];
    let observed = |state: usize, symbol| {
        let faces = [b"abbb", b"aaab"];
        q(
            faces[state].iter().filter(|&&face| face == symbol).count() as u128,
            4,
        )
    };
    let mut checks = Checks::default();
    for input in words(b"ab", MAX_ROLLS).into_iter().chain([b"?".to_vec()]) {
        let chart = hidden_chart(&input)?;
        checks.chart(&chart);
        let weights = inside_outside(&chart)?;
        if input == b"aa" {
            // The four hidden paths give (3 + 3 + 3 + 27) / 128.
            assert_eq!(*weights.partition(), q(9, 32), "likelihood of aa");
        }
        let max = tabulate_cells(&chart, &MaxProduct)?;
        let sampler = ExactSampler::new(&chart)?;
        let mut forward = [q(1, STATES as u128); STATES];
        let mut highest = forward;
        for (t, &obs) in input.iter().enumerate() {
            let prior = forward;
            let prior_max = highest;
            for state in 0..STATES {
                let mut sum = Rational::ZERO;
                let mut best = Rational::ZERO;
                for other in 0..STATES {
                    let factor = if t == 0 {
                        q(u128::from(state == other), 1)
                    } else {
                        q(TRANSITIONS[other][state], FACES)
                    };
                    sum = sum.checked_add(prior[other].checked_mul(factor)?)?;
                    best = best.max(prior_max[other].checked_mul(factor)?);
                }
                forward[state] = sum.checked_mul(observed(state, obs))?;
                highest[state] = best.checked_mul(observed(state, obs))?;
                assert_eq!(weights.inside()[t * STATES + state], forward[state]);
                assert_eq!(max[t * STATES + state], [highest[state]]);
            }
        }
        let partition = forward
            .into_iter()
            .try_fold(Rational::ZERO, Rational::checked_add)?;
        assert_eq!(*weights.partition(), partition);
        assert_eq!(
            max[chart.root()],
            [if input.is_empty() {
                Rational::ONE
            } else {
                *highest.iter().max().unwrap()
            }]
        );
        let mut backward = [Rational::ONE; STATES];
        for (t, &obs) in input.iter().enumerate().rev() {
            assert_eq!(&weights.outside()[t * STATES..(t + 1) * STATES], &backward);
            let next = backward;
            for (state, value) in backward.iter_mut().enumerate() {
                *value = Rational::ZERO;
                for (after, tail) in next.into_iter().enumerate() {
                    *value = value.checked_add(
                        tail.checked_mul(observed(after, obs))?
                            .checked_mul(q(TRANSITIONS[state][after], FACES))?,
                    )?;
                }
            }
        }
        let mut likelihood = Rational::ZERO;
        let mut visits = vec![Rational::ZERO; input.len() * STATES];
        for states in words(&[0, 1], input.len())
            .into_iter()
            .filter(|p| p.len() == input.len())
        {
            let mass = if states.is_empty() {
                Rational::ONE
            } else {
                let mut mass = q(1, STATES as u128);
                for (t, (&state, &obs)) in states.iter().zip(&input).enumerate() {
                    mass = mass.checked_mul(observed(state, obs))?;
                    if t > 0 {
                        mass = mass.checked_mul(q(TRANSITIONS[states[t - 1]][state], FACES))?;
                    }
                }
                mass
            };
            likelihood = likelihood.checked_add(mass)?;
            for (t, &state) in states.iter().enumerate() {
                let cell = t * STATES + state;
                visits[cell] = visits[cell].checked_add(mass)?;
            }
        }
        assert_eq!(likelihood, partition);
        for (cell, mass) in visits.into_iter().enumerate() {
            assert_eq!(
                weights.inside()[cell].checked_mul(weights.outside()[cell])?,
                mass
            );
        }
        if partition == Rational::ZERO {
            assert!(sampler.sample(|| unreachable!()).is_none());
            assert!(sampler.rule_probabilities(chart.root())?.is_none());
        }
        if input == b"a" {
            assert_eq!(
                sampler.rule_probabilities(chart.root())?,
                Some(vec![q(1, FACES), q(3, FACES)])
            );
            let before = sampler.sample(|| 0).unwrap();
            let at = sampler.sample(|| 1).unwrap();
            assert_eq!(
                (
                    before.children[0].operator.state,
                    at.children[0].operator.state
                ),
                (0, 1)
            );
        }
    }
    Ok(checks)
}

const START: usize = 0;
const SPAN: usize = 1;
const LEAF_WEIGHTS: [u128; 2] = [1, 2];
const WEIGHT_UNIT: u128 = 3;

fn parser() -> Result<Grammar<Weighted, 1>, Error> {
    let mut rules = vec![
        Production {
            name: "start".into(),
            parent: START,
            children: vec![SPAN],
            tracks: [vec![Atom::Child(0)]],
            operator: Box::new(|_| Weighted {
                state: START,
                weight: Rational::ONE,
                arity: 1,
            }),
        },
        Production {
            name: "split".into(),
            parent: SPAN,
            children: vec![SPAN, SPAN],
            tracks: [vec![Atom::Child(0), Atom::Child(1)]],
            operator: Box::new(|_| Weighted {
                state: SPAN,
                weight: q(1, WEIGHT_UNIT),
                arity: 2,
            }),
        },
    ];
    for (state, numerator) in LEAF_WEIGHTS.into_iter().enumerate() {
        rules.push(Production {
            name: format!("emission {state}"),
            parent: SPAN,
            children: vec![],
            tracks: [vec![Atom::Byte(b'a')]],
            operator: Box::new(move |_| Weighted {
                state,
                weight: q(numerator, WEIGHT_UNIT),
                arity: 0,
            }),
        });
    }
    Grammar::new(&["start", "span"], START, rules)
}

type MarkedParse = (Rational, Vec<(usize, usize)>);

fn parses(input: &[u8], start: usize) -> Result<Vec<MarkedParse>, Error> {
    let coordinate = (start, start + input.len());
    match input {
        [] | [b'b'] => Ok(Vec::new()),
        [b'a'] => Ok(LEAF_WEIGHTS
            .into_iter()
            .map(|n| (q(n, WEIGHT_UNIT), vec![coordinate]))
            .collect()),
        _ => {
            let mut out = Vec::new();
            for k in 1..input.len() {
                let right = parses(&input[k..], start + k)?;
                for (a, marks) in parses(&input[..k], start)? {
                    for (b, others) in &right {
                        let weight = a.checked_mul(*b)?.checked_mul(q(1, WEIGHT_UNIT))?;
                        out.push((
                            weight,
                            marks
                                .iter()
                                .chain(others)
                                .copied()
                                .chain([coordinate])
                                .collect(),
                        ));
                    }
                }
            }
            Ok(out)
        }
    }
}

pub fn span_parser() -> Result<Checks, Error> {
    const MAX_LEN: usize = 4; // Multiple split trees with an internal marked subspan.
    let grammar = parser()?;
    let mut checks = Checks::default();
    for input in words(b"ab", MAX_LEN) {
        let bound = grammar.bind([&input])?;
        let chart = compiled::reference_chart(&bound)?;
        checks.chart(&chart);
        let max = tabulate_cells(&chart, &MaxProduct)?;
        let reference = inside_outside(&chart)?;
        let compiled = compiled::inside_outside(&bound)?;
        assert_eq!(compiled.weights(), &reference);
        checks.fast_values += 2 * chart.cells().len();
        let root_parses = parses(&input, 0)?;
        for (rank, bag) in max.iter().enumerate() {
            let (symbol, [span]) = bound.cell(rank).unwrap();
            let direct = parses(&input[span.clone()], span.start)?;
            let best = direct.iter().map(|x| x.0).max();
            assert!(bag.iter().copied().eq(best));
            let total = direct
                .iter()
                .map(|x| x.0)
                .try_fold(Rational::ZERO, Rational::checked_add)?;
            assert_eq!(reference.inside()[rank], total);
            let mark = (span.start, span.end);
            let visits = if symbol == START {
                if rank == chart.root() {
                    total
                } else {
                    Rational::ZERO
                }
            } else {
                root_parses
                    .iter()
                    .filter(|(_, marks)| marks.contains(&mark))
                    .map(|x| x.0)
                    .try_fold(Rational::ZERO, Rational::checked_add)?
            };
            assert_eq!(
                reference.inside()[rank].checked_mul(reference.outside()[rank])?,
                visits
            );
        }
    }
    Ok(checks)
}
