//! Find the derivations that are optimal under several cost models at once.
//!
//! Three matrix-multiplication orders are scored by time, memory and energy.
//! Each pair of models shares an optimum. The common set for all three is empty.
//!
//! Run with `cargo run --offline --locked --example common_optimum`.

use num_bigint::BigUint;
use zeno_adp::assurance::Label;
use zeno_adp::common_optimum::{common, Costed, Error, ModelSet};
use zeno_adp::Chart;

fn main() -> Result<(), Error> {
    // One cell with three alternatives, costed in (time, memory, energy).
    let chart = Chart::new(
        vec![vec![
            Costed::rule([0, 0, 1], []),
            Costed::rule([0, 1, 0], []),
            Costed::rule([1, 0, 0], []),
        ]],
        0,
    )
    .expect("valid chart");
    for pair in [[0, 1], [0, 2], [1, 2]] {
        let answer = common(&chart, 3, &ModelSet::new(pair, 3)?)?;
        assert_eq!(answer.as_ref().count(), &BigUint::from(1u32));
    }
    let all = common(&chart, 3, &ModelSet::all(3)?)?;
    assert_eq!(all.label(), "Exact");
    assert!(!all.as_ref().exists());

    // A two-level chart: count the common optima and list them by rank.
    let chart = Chart::new(
        vec![
            vec![
                Costed::rule([1, 2], []),
                Costed::rule([1, 2], []),
                Costed::rule([2, 5], []),
            ],
            vec![Costed::rule([3, 0], [0, 0]), Costed::rule([4, 4], [0])],
        ],
        1,
    )
    .expect("valid chart");
    let both = common(&chart, 2, &ModelSet::all(2)?)?.into_inner();
    both.verify(&chart, 2)?;
    // Each child slot has two equal-cost derivations, so four trees share the optimum.
    assert_eq!(both.count(), &BigUint::from(4u32));
    let mut rank = BigUint::ZERO;
    while let Some(witness) = both.witness(&chart, &rank)? {
        both.verify_witness(&chart, &witness)?;
        println!(
            "rank {rank}: {:?} costs {:?}",
            witness.preorder, witness.costs
        );
        rank += 1u32;
    }
    println!("{} common optima, label {}", both.count(), Label::Exact);
    Ok(())
}
