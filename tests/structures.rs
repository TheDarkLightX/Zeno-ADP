use zeno_adp::algebras::Enumerate;
use zeno_adp::{
    audit_bounded, tabulate_cells, Algebra, AnswerOrder, AuditBudget, Chart, Operator, Tree,
};

#[path = "structures/forests.rs"]
mod forests;
#[path = "structures/mcfg.rs"]
mod mcfg;
#[path = "structures/sets.rs"]
mod sets;

fn audit_example<O, A>(chart: &Chart<O>, algebra: &A) -> usize
where
    O: Operator + Ord + std::fmt::Debug,
    A: Algebra<O>,
{
    fn size<O>(tree: &Tree<O>) -> usize {
        1 + tree.children.iter().map(size).sum::<usize>()
    }

    let budget = tabulate_cells(chart, &Enumerate)
        .unwrap()
        .iter()
        .flatten()
        .map(size)
        .sum();
    let audit = audit_bounded(
        chart,
        algebra,
        AuditBudget {
            max_tree_nodes: budget,
        },
        AnswerOrder::Ordered,
    )
    .unwrap();
    assert!(audit.bellman.first_failure.is_none());
    assert!(audit.ambiguities.is_empty());
    assert_eq!(audit.tree_nodes, budget);
    budget
}
