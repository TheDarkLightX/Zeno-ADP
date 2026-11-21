mod support;

use zeno_adp::grammars::alignment;
use zeno_adp::Error;

fn main() -> Result<(), Error> {
    let chart = alignment(b"AC", b"AG")?;
    support::run(
        "Global alignment, AC against AG",
        &chart,
        support::DEMO_BUDGET,
    )
}
