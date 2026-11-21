#[path = "support/ranked_fixture.rs"]
mod fixture;

use fixture::{assignments, at, fixture, RANKS};
use zeno_adp::probability::{
    Expectation, ExpectationOperator, ExpectationValue, Rational, SignedRational,
};
use zeno_adp::{
    audit, audit_bounded, enumerate, fast, tabulate_cells, AnswerOrder, AuditBudget, Chart, Error,
    Operator, Rule, Tree,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Local {
    id: usize,
    arity: usize,
    scaled: (i128, i128),
}

// The common denominator of the halves and thirds below.
const DENOMINATOR: u128 = 6;

fn signed(n: i128, d: u128) -> SignedRational {
    SignedRational::new(Rational::new(n.unsigned_abs(), d).unwrap(), n.is_negative())
}

impl Operator for Local {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ExpectationOperator for Local {
    fn expectation(&self) -> Result<ExpectationValue, Error> {
        Ok(ExpectationValue {
            mass: Rational::new(self.scaled.0 as u128, DENOMINATOR).unwrap(),
            moment: signed(self.scaled.1, DENOMINATOR),
        })
    }
}

fn factors(tree: &Tree<Local>, terms: &mut Vec<(i128, i128)>) {
    terms.push(tree.operator.scaled);
    for child in &tree.children {
        factors(child, terms);
    }
}

fn oracle(trees: &[Tree<Local>]) -> Option<(i128, i128, u128)> {
    let terms: Vec<_> = trees
        .iter()
        .map(|tree| {
            let mut terms = Vec::new();
            factors(tree, &mut terms);
            terms
        })
        .collect();
    let degree = terms.iter().map(Vec::len).max()? as u32;
    let (mut mass, mut moment) = (0, 0);
    for factors in terms {
        let scale = DENOMINATOR.pow(degree - factors.len() as u32) as i128;
        mass += scale * factors.iter().map(|(w, _)| w).product::<i128>();
        for (index, &(_, slope)) in factors.iter().enumerate() {
            let rest = factors
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != index)
                .map(|(_, (w, _))| w)
                .product::<i128>();
            moment += scale * slope * rest;
        }
    }
    Some((mass, moment, DENOMINATOR.pow(degree)))
}

#[test]
fn expectation_matches_explicit_derivations_at_every_rank() {
    let locals = [(0, 0), (0, 6), (3, -2), (6, 3)];
    let mut charts = 0;
    let mut cells = 0;
    let mut occurrences = 0;
    let mut zero_mass_with_tangent = 0;
    for weights in assignments(locals) {
        let base = fixture(RANKS - 1, |id, group, arity| Local {
            id,
            arity,
            scaled: weights[group],
        });
        let mut rules = base.cells().to_vec();
        let repeated = rules[0][0].clone();
        rules[0].push(repeated);
        let chart = Chart::new(rules, base.root()).unwrap();
        let table = tabulate_cells(&chart, &Expectation).unwrap();
        let fused = fast::tabulate(&chart, &Expectation).unwrap();
        assert!(audit(&chart, &Expectation).unwrap().first_failure.is_none());
        charts += 1;
        for (rank, expected) in table.iter().enumerate() {
            let trees = enumerate(&at(&chart, rank));
            occurrences += trees.len();
            cells += 1;
            let entry = oracle(&trees).map(|(mass, moment, denom)| {
                let wanted = (mass != 0).then(|| signed(moment, mass as u128));
                let summary = ExpectationValue {
                    mass: Rational::new(mass as u128, denom).unwrap(),
                    moment: signed(moment, denom),
                };
                zero_mass_with_tangent += usize::from(mass == 0 && moment != 0);
                assert_eq!(summary.normalized().unwrap(), wanted);
                summary
            });
            assert!(
                entry.iter().eq(expected),
                "weights={weights:?}, rank={rank}"
            );
            assert_eq!(fused.cells()[rank], entry);
        }
    }
    assert!(zero_mass_with_tangent > 0);
    println!(
        "expectation: {charts} charts, {cells} cells, {occurrences} derivation occurrences, \
              {zero_mass_with_tangent} inhabited zero-mass cells with a nonzero tangent"
    );
}

#[test]
fn expectation_checks_signed_arithmetic_and_weighted_features() {
    let half = Rational::new(1, 2).unwrap();
    let feature = ExpectationValue::weighted_feature(half, signed(-3, 2)).unwrap();
    assert_eq!(feature.moment, signed(-3, 4));
    assert_eq!(feature.normalized().unwrap(), Some(signed(-3, 2)));
    assert_eq!(
        SignedRational::new(Rational::ZERO, true),
        SignedRational::ZERO
    );
    let biggest = Rational::new(u128::MAX, 1).unwrap();
    let big = SignedRational::from(biggest);
    assert_eq!(big.checked_add(signed(1, 1)), Err(Error::Overflow));
    assert_eq!(
        big.checked_add(SignedRational::new(biggest, true)),
        Ok(SignedRational::ZERO)
    );

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Leaf;
    impl Operator for Leaf {
        fn arity(&self) -> usize {
            0
        }
    }
    impl ExpectationOperator for Leaf {
        fn expectation(&self) -> Result<ExpectationValue, Error> {
            Ok(ExpectationValue {
                mass: Rational::ZERO,
                moment: Rational::new(u128::MAX, 1).unwrap().into(),
            })
        }
    }
    let chart = Chart::new(vec![vec![Rule::new(Leaf, []), Rule::new(Leaf, [])]], 0).unwrap();
    assert_eq!(tabulate_cells(&chart, &Expectation), Err(Error::Overflow));
    assert_eq!(fast::tabulate(&chart, &Expectation), Err(Error::Overflow));
    assert!(matches!(
        audit_bounded(
            &chart,
            &Expectation,
            AuditBudget {
                max_tree_nodes: chart.cells()[0].len()
            },
            AnswerOrder::Ordered,
        ),
        Err(Error::AuditEvaluation { .. })
    ));
}
