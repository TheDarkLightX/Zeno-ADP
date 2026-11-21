use std::fmt::Debug;

use zeno_adp::algebras::{Additive, MinimumWithMultiplicity, ScoredOperator};
use zeno_adp::queries::{co_minimal, count, derivation_count, k_lowest, minimum, MinimumBackend};
use zeno_adp::{audit_bounded, AuditBudget, Chart, Error};

// Headroom for every small worked example. The report prints actual use.
pub const DEMO_BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 10_000,
};

pub fn run<O: Clone + Debug + Ord + ScoredOperator>(
    name: &str,
    chart: &Chart<O>,
    budget: AuditBudget,
) -> Result<(), Error> {
    let score = Additive::default();
    let product = MinimumWithMultiplicity::default();
    let report = audit_bounded(chart, &product, budget, Default::default())?;
    if let Some(failure) = report.bellman.first_failure {
        panic!("Bellman counterexample: {failure:?}");
    }
    let best = minimum(chart, &score, MinimumBackend::Reference)?;
    let ties = co_minimal(chart, &score, Default::default())?;
    // Show two ranked candidates so one can see the treatment of ties.
    let top = k_lowest(chart, &score, 2, Default::default())?;
    println!("{name}: minimum {best:?}");
    println!(
        "distinct trees {}, derivations {}",
        count(chart, Default::default())?,
        derivation_count(chart)?
    );
    println!("{} co-optimal trees, first two ranked: {top:?}", ties.len());
    println!("Product: {:?}", report.bellman.tabulated);
    println!(
        "Finite audit: {} cells, {} rules, {} tree nodes, {} ambiguous cells",
        report.bellman.cells,
        report.bellman.rules,
        report.tree_nodes,
        report.ambiguities.len()
    );
    Ok(())
}
