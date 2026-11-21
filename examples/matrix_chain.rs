mod support;

use zeno_adp::grammars::matrix_chain;
use zeno_adp::Error;

fn main() -> Result<(), Error> {
    let chart = matrix_chain(&[10, 30, 5, 60])?;
    support::run(
        "Matrix chain, dimensions 10,30,5,60",
        &chart,
        support::DEMO_BUDGET,
    )
}
