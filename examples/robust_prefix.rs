//! Commit to the most useful first steps of a plan before learning which world holds.
//!
//! A query plan is costed in three worlds. A special route is best in each world
//! alone, so no whole plan is optimal everywhere, yet scanning and pushing the
//! predicate down keep an optimal finish in every world. A budget of regret per
//! world lets the plan commit further.
//!
//! Run with `cargo run --offline --locked --example robust_prefix`.

use num_bigint::BigUint;
use zeno_adp::robust_prefix::{regret, state_bound, within_budget, zero_regret, Error, Step};
use zeno_adp::Chart;

fn main() -> Result<(), Error> {
    let z = [0, 0, 0];
    let chart = Chart::new(
        vec![
            // 0: choose a join: hash left, hash right or broadcast.
            vec![
                Step::finish([0, 0, 2], 2),
                Step::finish([2, 0, 0], 2),
                Step::finish([0, 2, 0], 2),
            ],
            // 1: push the predicate down.
            vec![Step::to(z, 2, 0)],
            // 2: a special route per world, or scan.
            vec![
                Step::finish([0, 8, 8], 1),
                Step::finish([8, 0, 8], 1),
                Step::finish([8, 8, 0], 1),
                Step::to(z, 3, 1),
            ],
        ],
        2,
    )
    .expect("valid chart");
    let answer = zero_regret(&chart, 3)?;
    assert_eq!(answer.label(), "Exact");
    let answer = answer.into_inner();
    assert_eq!(answer.prefix, vec![(2, 3), (1, 0)]);
    assert_eq!(answer.best_credit(2), 5);
    assert!(!answer.common_plan_exists());
    for (world, plan) in answer.completions.iter().enumerate() {
        println!("world {world}: {plan:?}");
    }

    // With a regret budget of 2 in every world, the join can be committed too.
    let budget = vec![BigUint::from(2u32); 3];
    // Use the theoretical bound for live states in each pass.
    let limit = usize::try_from(state_bound(&chart, &budget)).expect("small chart");
    let within = within_budget(&chart, 3, &budget, limit)?.into_inner();
    assert_eq!(within.best, 7);
    println!(
        "budget 2: {:?}, regret {:?}",
        within.prefix,
        regret(&chart, 3, &within.prefix)?
    );
    Ok(())
}
