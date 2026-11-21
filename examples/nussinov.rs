mod support;

use zeno_adp::grammars::nussinov;
use zeno_adp::Error;

fn main() -> Result<(), Error> {
    let chart = nussinov(b"AUAU", 0)?;
    support::run(
        "Nussinov, AUAU, zero minimum loop",
        &chart,
        support::DEMO_BUDGET,
    )
}
