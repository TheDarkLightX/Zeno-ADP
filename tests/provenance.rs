use std::collections::BTreeMap;

use zeno_adp::algebras::{Enumerate, ScoredOperator};
use zeno_adp::grammars::{alignment, Align};
use zeno_adp::provenance::{BigUint, CommutativeSemiring, Provenance, SemiringAlgebra};
use zeno_adp::{audit, tabulate_cells, Chart, Error, Operator, Rule, Tree};

struct Count;

impl CommutativeSemiring for Count {
    type Value = BigUint;
    fn zero(&self) -> BigUint {
        0u8.into()
    }
    fn one(&self) -> BigUint {
        1u8.into()
    }
    fn add(&self, a: &BigUint, b: &BigUint) -> Result<BigUint, Error> {
        Ok(a + b)
    }
    fn multiply(&self, a: &BigUint, b: &BigUint) -> Result<BigUint, Error> {
        Ok(a * b)
    }
}

struct Exists;

impl CommutativeSemiring for Exists {
    type Value = bool;
    fn zero(&self) -> bool {
        false
    }
    fn one(&self) -> bool {
        true
    }
    fn add(&self, a: &bool, b: &bool) -> Result<bool, Error> {
        Ok(*a || *b)
    }
    fn multiply(&self, a: &bool, b: &bool) -> Result<bool, Error> {
        Ok(*a && *b)
    }
}

struct Min;

impl CommutativeSemiring for Min {
    type Value = Option<i64>;
    fn zero(&self) -> Self::Value {
        None
    }
    fn one(&self) -> Self::Value {
        Some(0)
    }
    fn add(&self, a: &Self::Value, b: &Self::Value) -> Result<Self::Value, Error> {
        Ok(match (*a, *b) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        })
    }
    fn multiply(&self, a: &Self::Value, b: &Self::Value) -> Result<Self::Value, Error> {
        a.zip(*b)
            .map(|(a, b)| a.checked_add(b).ok_or(Error::Overflow))
            .transpose()
    }
}

fn factors<T: Copy>(tree: &Tree<T>, labels: &mut Vec<T>) {
    labels.push(tree.operator);
    for child in &tree.children {
        factors(child, labels);
    }
}

#[test]
fn one_polynomial_answers_three_questions_on_every_rank() {
    // Two symbols through length two expose collisions of commuted labels.
    let words = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 0],
        vec![0, 1],
        vec![1, 0],
        vec![1, 1],
    ];
    let mut ranks = 0;
    let mut terms = 0;
    let mut max_bits = 0;
    let cost = |op: &Align| match op.cost() {
        zeno_adp::algebras::Cost::Finite(cost) => Some(cost),
        _ => unreachable!(),
    };
    for left in &words {
        for right in &words {
            let chart = alignment(left, right).unwrap();
            let polynomials = tabulate_cells(&chart, &Provenance::new(|op: &Align| *op)).unwrap();
            let counts = tabulate_cells(
                &chart,
                &SemiringAlgebra::new(Count, |_: &Align| Count.one()),
            )
            .unwrap();
            let exists =
                tabulate_cells(&chart, &SemiringAlgebra::new(Exists, |_: &Align| true)).unwrap();
            let minima = tabulate_cells(&chart, &SemiringAlgebra::new(Min, cost)).unwrap();
            let trees = tabulate_cells(&chart, &Enumerate).unwrap();
            for (rank, bag) in polynomials.iter().enumerate() {
                let polynomial = &bag[0];
                let mut expected = BTreeMap::<_, BigUint>::new();
                for tree in &trees[rank] {
                    let mut labels = Vec::new();
                    factors(tree, &mut labels);
                    labels.sort_unstable();
                    *expected.entry(labels).or_default() += 1u8;
                }
                terms += polynomial.terms().len();
                max_bits = max_bits.max(
                    polynomial
                        .terms()
                        .map(|(_, count)| count.bits())
                        .max()
                        .unwrap(),
                );
                assert!(polynomial.terms().eq(expected
                    .iter()
                    .map(|(labels, count)| (labels.as_slice(), count))));
                assert_eq!(
                    polynomial.evaluate(&Count, |_| Count.one()).unwrap(),
                    counts[rank][0]
                );
                assert_eq!(
                    polynomial.evaluate(&Exists, |_| true).unwrap(),
                    exists[rank][0]
                );
                assert_eq!(polynomial.evaluate(&Min, cost).unwrap(), minima[rank][0]);
                ranks += 1;
            }
        }
    }
    println!(
        "provenance ranks={ranks}, terms={terms}, max coefficient bits={max_bits}, disagreements=0"
    );
    assert_eq!(ranks, 289);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Label(usize);

impl Operator for Label {
    fn arity(&self) -> usize {
        self.0
    }
}

#[test]
fn repeated_children_and_zero_weights_keep_inhabitation() {
    let chart = Chart::new(
        vec![
            vec![Rule::new(Label(0), []), Rule::new(Label(0), [])],
            vec![],
            vec![Rule::new(Label(2), [0, 0]), Rule::new(Label(2), [0, 1])],
        ],
        2,
    )
    .unwrap();
    let algebra = Provenance::new(|op: &Label| *op);
    let values = tabulate_cells(&chart, &algebra).unwrap();
    assert!(values[1].is_empty());
    let polynomial = &values[2][0];
    assert!(polynomial
        .terms()
        .eq([(&[Label(0), Label(0), Label(2)][..], &4u8.into())]));
    assert!(!polynomial.evaluate(&Exists, |label| label.0 == 0).unwrap());
    assert!(audit(&chart, &algebra).unwrap().first_failure.is_none());
}

#[test]
fn coefficients_are_exact_past_u128() {
    // Two indistinguishable extensions per layer, just past bounded capacity.
    let layers = u128::BITS as usize;
    let chart = Chart::new(
        std::iter::once(vec![Rule::new(Label(0), [])])
            .chain((0..layers).map(|child| vec![Rule::new(Label(1), [child]); 2]))
            .collect(),
        layers,
    )
    .unwrap();
    let answer = zeno_adp::tabulate(&chart, &Provenance::new(|op: &Label| *op)).unwrap();
    let expected = BigUint::from(1u8) << layers;
    assert_eq!(answer[0].terms().next().unwrap().1, &expected);
    assert_eq!(
        answer[0].evaluate(&Count, |_| Count.one()).unwrap(),
        expected
    );
    println!("wide provenance case: {} coefficient bits", expected.bits());
}
