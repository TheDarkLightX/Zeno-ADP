mod support;

use zeno_adp::grammars::{knapsack, Item};
use zeno_adp::Error;

fn main() -> Result<(), Error> {
    let chart = knapsack(
        &[
            Item {
                weight: 2,
                value: 3,
            },
            Item {
                weight: 1,
                value: 2,
            },
            Item {
                weight: 2,
                value: 3,
            },
        ],
        3,
    )?;
    support::run("0/1 knapsack, capacity 3", &chart, support::DEMO_BUDGET)
}
