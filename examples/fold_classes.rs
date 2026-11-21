#[path = "support/fold_classes.rs"]
mod fold_classes;

use fold_classes::{chart, DotBracket};
use zeno_adp::algebras::Count;
use zeno_adp::classification::Classified;
use zeno_adp::{audit_bounded_classified, exhaustive, AuditBudget, Error};

// Four bases keep exhaustive expansion small even with redundant splits.
const BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 1_000,
};

fn main() -> Result<(), Error> {
    for (name, split) in [("leftmost-base", false), ("with redundant splits", true)] {
        let chart = chart(b"AUAU", 0, split)?;
        let counts = Classified::new(DotBracket, Count);
        let report = audit_bounded_classified(
            &chart,
            &counts,
            counts.classes(),
            BUDGET,
            Default::default(),
        )?;
        let expected = exhaustive(&chart, &counts)?;
        assert_eq!(report.bellman.tabulated, expected);
        assert!(report.bellman.first_failure.is_none());
        assert_eq!(expected.len(), 7);
        println!(
            "{name}: {} dot-bracket classes, {} ambiguous cells",
            expected.len(),
            report.ambiguities.len()
        );
        for (fold, derivations) in expected {
            println!("  {fold}  {derivations} derivation(s)");
        }
    }
    Ok(())
}
