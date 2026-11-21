#[path = "support/local_classes.rs"]
mod local_classes;
mod support;

use local_classes::Columns;
use zeno_adp::algebras::{Additive, Cost};
use zeno_adp::classification::Classified;
use zeno_adp::grammars::local_alignment;
use zeno_adp::queries::co_minimal;
use zeno_adp::{audit_bounded_classified, exhaustive, Error};

fn main() -> Result<(), Error> {
    let chart = local_alignment(b"AA", b"A")?;
    support::run(
        "Local alignment, AA against A",
        &chart,
        support::DEMO_BUDGET,
    )?;
    let score = Additive::default();
    let positioned = co_minimal(&chart, &score, Default::default())?;
    assert_eq!(positioned.len(), 2);
    assert_eq!(positioned[0].value, Cost::Finite(-2));

    let product = Classified::new(Columns, score);
    let report = audit_bounded_classified(
        &chart,
        &product,
        product.classes(),
        support::DEMO_BUDGET,
        Default::default(),
    )?;
    let exact = exhaustive(&chart, &product)?;
    assert_eq!(report.bellman.tabulated, exact);
    assert!(report.bellman.first_failure.is_none());
    let optimal: Vec<_> = exact
        .iter()
        .filter(|(_, cost)| *cost == positioned[0].value)
        .collect();
    assert_eq!(optimal.len(), 1);
    println!(
        "{} positional optima, {} coordinate-free optimal class: {optimal:?}",
        positioned.len(),
        optimal.len()
    );
    Ok(())
}
