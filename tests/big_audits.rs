#[path = "support/ranked_fixture.rs"]
mod fixture;

use fixture::{assignments, at, fixture, RANKS};
use zeno_adp::probability::{
    BigMaxProduct, BigRational, BigSumProduct, MaxProduct, Rational, SumProduct, WeightedOperator,
};
use zeno_adp::provenance::{BigUint, SemiringAlgebra};
use zeno_adp::{audit_bounded, tabulate_cells, AnswerOrder, AuditBudget, Error, Operator};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Weight {
    id: usize,
    arity: usize,
    weight: Rational,
}

impl Operator for Weight {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl WeightedOperator for Weight {
    fn weight(&self) -> Rational {
        self.weight
    }
}

fn lift(op: &Weight) -> BigRational {
    op.weight().into()
}

// The fixture has 2, 0, 17 and 86 tree nodes in its four exhaustive bags.
const BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 105,
};

#[test]
fn big_and_bounded_arithmetic_equal_on_every_rank() {
    let weights = [
        Rational::ZERO,
        Rational::new(1, 3).unwrap(),
        Rational::new(2, 5).unwrap(),
        Rational::ONE,
    ];
    let sum = SemiringAlgebra::new(BigSumProduct, lift);
    let max = SemiringAlgebra::new(BigMaxProduct, lift);
    let mut ranks = 0;
    for (case, args) in assignments(weights).enumerate() {
        let chart = fixture(RANKS - 1, |id, group, arity| Weight {
            id,
            arity,
            weight: args[group],
        });
        let sums = tabulate_cells(&chart, &sum).unwrap();
        let maxima = tabulate_cells(&chart, &max).unwrap();
        for (wide, bounded) in [
            (&sums, tabulate_cells(&chart, &SumProduct).unwrap()),
            (&maxima, tabulate_cells(&chart, &MaxProduct).unwrap()),
        ] {
            assert_eq!(
                *wide,
                bounded
                    .into_iter()
                    .map(|bag| bag.into_iter().map(BigRational::from).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            );
        }
        for report in [
            audit_bounded(&chart, &sum, BUDGET, AnswerOrder::Ordered).unwrap(),
            audit_bounded(&chart, &max, BUDGET, AnswerOrder::Ordered).unwrap(),
        ] {
            assert!(report.bellman.first_failure.is_none());
            assert_eq!(report.tree_nodes, BUDGET.max_tree_nodes);
        }
        for (rank, (sum_bag, max_bag)) in sums.iter().zip(maxima.iter()).enumerate() {
            assert_eq!(
                *sum_bag,
                zeno_adp::exhaustive(&at(&chart, rank), &sum).unwrap()
            );
            let encode =
                |bag: &[BigRational]| bag.first().map_or_else(|| "-".into(), ToString::to_string);
            println!(
                "fraction {case} {rank} {} {}",
                encode(sum_bag),
                encode(max_bag)
            );
            ranks += 1;
        }
    }
    println!("exact big-rational ranks={ranks}, disagreements=0");
    assert_eq!(ranks, 1024);
}

#[test]
fn widened_weights_and_results_pass_reference_audits() {
    // One step past the smallest binary64 subnormal's power of two.
    const TINY_POWER: usize = 1075;
    const MAX_BOUNDED_SHIFT: usize = u128::BITS as usize - 1;
    let chart = zeno_adp::Chart::new(
        vec![
            vec![zeno_adp::Rule::new(
                Weight {
                    id: 0,
                    arity: 0,
                    weight: Rational::new(1, 1u128 << MAX_BOUNDED_SHIFT).unwrap(),
                },
                [],
            )],
            vec![zeno_adp::Rule::new(
                Weight {
                    id: 1,
                    arity: 2,
                    weight: Rational::ONE,
                },
                [0, 0],
            )],
        ],
        1,
    )
    .unwrap();
    let wide = |op: &Weight| {
        if op.id == 1 {
            BigRational::new(1u8.into(), BigUint::from(1u8) << TINY_POWER).unwrap()
        } else {
            lift(op)
        }
    };
    let expected = BigRational::new(
        1u8.into(),
        BigUint::from(1u8) << (TINY_POWER + 2 * MAX_BOUNDED_SHIFT),
    )
    .unwrap();
    let bounded = audit_bounded(&chart, &SumProduct, BUDGET, AnswerOrder::Ordered).unwrap_err();
    assert!(
        matches!(bounded, Error::AuditEvaluation { cell: 1, source, .. } if *source == Error::Overflow)
    );
    let sums = SemiringAlgebra::new(BigSumProduct, wide);
    let max = SemiringAlgebra::new(BigMaxProduct, wide);
    for report in [
        audit_bounded(&chart, &sums, BUDGET, AnswerOrder::Ordered).unwrap(),
        audit_bounded(&chart, &max, BUDGET, AnswerOrder::Ordered).unwrap(),
    ] {
        assert!(report.bellman.first_failure.is_none());
        assert_eq!(
            report.bellman.tabulated.as_slice(),
            std::slice::from_ref(&expected)
        );
    }
    assert!(BigRational::new(1u8.into(), BigUint::ZERO).is_none());
    assert_eq!(
        BigRational::new(BigUint::ZERO, expected.denominator().clone()),
        Some(Rational::ZERO.into())
    );
    println!(
        "bounded audit overflow at rank 1; big denominator bits={}",
        expected.denominator().bits()
    );
}
