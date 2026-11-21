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

fn check_generated<O: zeno_adp::Operator + Eq + std::fmt::Debug, A>(
    grammar: &impl zeno_adp::compiled::Program<Op = O>,
    reference: &zeno_adp::Chart<O>,
    algebra: &A,
    site_for: impl Fn(usize, usize, &O) -> &'static str,
) -> zeno_adp::fast::Table<<A as zeno_adp::fast::Fold<O>>::Value>
where
    A: zeno_adp::fast::Fold<O>
        + zeno_adp::Algebra<O, Value = <A as zeno_adp::fast::Fold<O>>::Value>,
    <A as zeno_adp::fast::Fold<O>>::Value: Eq + std::fmt::Debug,
{
    let mut emitted = 0;
    zeno_adp::compiled::replay(grammar, |rank, ordinal, site, operator, children| {
        let expected = &reference.cells()[rank][ordinal];
        assert_eq!(operator, expected.operator);
        assert_eq!(children, expected.children);
        assert_eq!(site, site_for(rank, ordinal, &expected.operator));
        emitted += 1;
        Ok(())
    })
    .unwrap();
    assert_eq!(
        emitted,
        reference.cells().iter().map(Vec::len).sum::<usize>()
    );
    let expected = zeno_adp::tabulate_cells(reference, algebra).unwrap();
    let actual = zeno_adp::compiled::tabulate(grammar, algebra).unwrap();
    assert_eq!(actual.root(), reference.root());
    assert!(actual
        .cells()
        .iter()
        .zip(&expected)
        .all(|(one, bag)| one.iter().eq(bag)));
    assert_eq!(actual.cells().len(), expected.len());
    actual
}
