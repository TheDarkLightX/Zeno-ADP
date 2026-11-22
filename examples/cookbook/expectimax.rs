use super::{words, Checks};
use num_bigint::BigUint;
use zeno_adp::probability::{BigRational, Rational};
use zeno_adp::{
    audit_bounded, tabulate_cells, Algebra, AnswerOrder, AuditBudget, Chart, Error, Operator, Rule,
};

const STATES: usize = 2;
const ACTIONS: usize = 2;
const TICKETS_PER_ACTION: u128 = 3; // Equiprobable tickets, including asymmetric 1:2 odds.
const MAX_HORIZON: usize = 2; // One chance stage can lead to a further decision.
type Odds = [[u128; ACTIONS]; STATES]; // Tickets leading to state 1.
type Terminals = [u128; STATES]; // Utilities as numerators with a common denominator.
const EXAMPLE_ODDS: Odds = [[1, 0], [0, 2]];
const EXAMPLE_TERMINALS: Terminals = [0, 3];
const UTILITY_NUMERATORS: [u128; 3] = [0, 1, 3]; // Zero, a unit, and a higher utility.

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Terminal(BigRational),
    Action(usize),
    Chance([BigRational; STATES]),
}

impl Operator for Node {
    fn arity(&self) -> usize {
        match self {
            Self::Terminal(_) => 0,
            Self::Action(_) => 1,
            Self::Chance(weights) => weights.len(),
        }
    }
}

struct ExpectedUtility;

impl Algebra<Node> for ExpectedUtility {
    type Value = BigRational;

    fn apply(&self, op: &Node, children: &[&BigRational]) -> Result<BigRational, Error> {
        Ok(match op {
            Node::Terminal(value) => value.clone(),
            Node::Action(_) => children[0].clone(),
            Node::Chance(weights) => {
                let terms = weights.iter().zip(children).map(|(p, &value)| p * value);
                terms.fold(Rational::ZERO.into(), |total, term| &total + &term)
            }
        })
    }

    fn choose(&self, candidates: &[BigRational]) -> Result<Vec<BigRational>, Error> {
        Ok(candidates.iter().max().cloned().into_iter().collect())
    }
}

fn policy_chart(
    terminal: Terminals,
    denominator: &BigUint,
    odds: Odds,
    horizon: usize,
) -> Result<Chart<Node>, Error> {
    let mut rows: Vec<_> = terminal
        .into_iter()
        .map(|value| {
            let utility = BigRational::new(value.into(), denominator.clone()).unwrap();
            vec![Rule::new(Node::Terminal(utility), [])]
        })
        .collect();
    let mut previous = [0, 1];
    for _ in 0..horizon {
        let chance_start = rows.len();
        for &tickets in odds.iter().flatten() {
            let weights = [TICKETS_PER_ACTION - tickets, tickets]
                .map(|count| Rational::new(count, TICKETS_PER_ACTION).unwrap().into());
            rows.push(vec![Rule::new(Node::Chance(weights), previous)]);
        }
        let decision_start = rows.len();
        for state in 0..STATES {
            rows.push(
                (0..ACTIONS)
                    .map(|action| {
                        Rule::new(
                            Node::Action(action),
                            [chance_start + state * ACTIONS + action],
                        )
                    })
                    .collect(),
            );
        }
        previous = std::array::from_fn(|state| decision_start + state);
    }
    Chart::new(rows, previous[1])
}

fn audit_nodes(horizon: usize) -> usize {
    let (mut count, mut size) = (1usize, 1usize); // One terminal tree at each starting rank.
    let mut total = STATES;
    for _ in 0..horizon {
        // All successor states occur in the chance rule, including zero-weight slots.
        let chance_count = count.pow(STATES as u32);
        let chance_size = 1 + STATES * size;
        total += STATES * ACTIONS * chance_count * chance_size;
        count = ACTIONS * chance_count;
        size = 1 + chance_size;
        total += STATES * count * size;
    }
    total
}

fn check_model(
    checks: &mut Checks,
    terminal: Terminals,
    terminal_denominator: &BigUint,
    odds: Odds,
    horizon: usize,
) -> Result<BigRational, Error> {
    let chart = policy_chart(terminal, terminal_denominator, odds, horizon)?;
    checks.chart(&chart);
    let values = tabulate_cells(&chart, &ExpectedUtility)?;
    let budget = audit_nodes(horizon);
    let audit = audit_bounded(
        &chart,
        &ExpectedUtility,
        AuditBudget {
            max_tree_nodes: budget,
        },
        AnswerOrder::Ordered,
    )?;
    assert!(audit.bellman.first_failure.is_none(), "{audit}");
    assert!(audit.ambiguities.is_empty(), "{audit}");
    assert_eq!(audit.tree_nodes, budget);
    checks.audited_nodes += audit.tree_nodes;

    // Count tickets directly from the raw odds. After t decisions, every
    // utility numerator has the same denominator, scaled once per decision.
    let mut cells = values.iter();
    let mut compare = |numerator: u128, denominator: &BigUint| {
        let [answer] = cells.next().unwrap().as_slice() else {
            panic!("every state or action must have exactly one utility");
        };
        assert_eq!(
            answer.numerator() * denominator,
            answer.denominator() * numerator
        );
        checks.oracle_values += 1;
    };
    let mut previous = terminal;
    let mut denominator = terminal_denominator.clone();
    for numerator in terminal {
        compare(numerator, &denominator);
    }
    for _ in 0..horizon {
        denominator *= TICKETS_PER_ACTION;
        let action_values = odds.map(|row| {
            row.map(|tickets| {
                (0..TICKETS_PER_ACTION)
                    .map(|ticket| previous[usize::from(ticket < tickets)])
                    .sum::<u128>()
            })
        });
        for &numerator in action_values.iter().flatten() {
            compare(numerator, &denominator);
        }
        previous = action_values.map(|row| row.into_iter().max().unwrap());
        for numerator in previous {
            compare(numerator, &denominator);
        }
    }
    assert!(cells.next().is_none());
    Ok(values[chart.root()][0].clone())
}

pub fn finite_horizon() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    let tickets: Vec<_> = (0..=TICKETS_PER_ACTION).collect();
    let unit: BigUint = 1u8.into();
    for numerators in words(&tickets, STATES * ACTIONS)
        .into_iter()
        .filter(|row| row.len() == STATES * ACTIONS)
    {
        let odds = std::array::from_fn(|state| {
            std::array::from_fn(|action| numerators[state * ACTIONS + action])
        });
        for a in UTILITY_NUMERATORS {
            for b in UTILITY_NUMERATORS {
                for horizon in 0..=MAX_HORIZON {
                    let terminal = [a, b];
                    let root = check_model(&mut checks, terminal, &unit, odds, horizon)?;
                    if (terminal, odds, horizon) == (EXAMPLE_TERMINALS, EXAMPLE_ODDS, MAX_HORIZON) {
                        assert_eq!(root, Rational::new(5, 3).unwrap().into());
                    }
                }
            }
        }
    }
    // The denominator has one bit beyond the small rational's capacity.
    let wide = unit << u128::BITS;
    let root = check_model(
        &mut checks,
        EXAMPLE_TERMINALS,
        &wide,
        EXAMPLE_ODDS,
        MAX_HORIZON,
    )?;
    assert_eq!(
        root,
        BigRational::new(5u8.into(), wide * TICKETS_PER_ACTION).unwrap()
    );
    Ok(checks)
}
