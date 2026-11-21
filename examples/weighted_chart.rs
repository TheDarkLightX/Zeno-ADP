use zeno_adp::probability::{inside_outside, ExactSampler, Rational, WeightedOperator};
use zeno_adp::{Chart, Operator, Rule};

#[derive(Clone)]
enum Weighted {
    Leaf(Rational),
    Pair,
}

impl Operator for Weighted {
    fn arity(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Pair => 2,
        }
    }
}

impl WeightedOperator for Weighted {
    fn weight(&self) -> Rational {
        match self {
            Self::Leaf(weight) => *weight,
            Self::Pair => Rational::ONE,
        }
    }
}

fn main() -> Result<(), zeno_adp::Error> {
    let third = Rational::new(1, 3).unwrap();
    let two_thirds = Rational::new(2, 3).unwrap();
    let chart = Chart::new(
        vec![
            vec![
                Rule::new(Weighted::Leaf(third), []),
                Rule::new(Weighted::Leaf(two_thirds), []),
            ],
            vec![Rule::new(Weighted::Pair, [0, 0])],
        ],
        1,
    )?;

    let masses = inside_outside(&chart)?;
    assert_eq!(*masses.partition(), Rational::ONE);
    assert_eq!(masses.outside()[0], Rational::new(2, 1).unwrap());

    let sampler = ExactSampler::new(&chart)?;
    assert_eq!(
        sampler.rule_probabilities(0)?,
        Some(vec![third, two_thirds])
    );
    Ok(())
}
