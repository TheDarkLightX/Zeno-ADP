mod stream;

use std::fmt::Debug;

use zeno_adp::algebras::{
    lexicographic_min, Additive, Cost, Count, DerivationSummary, Enumerate,
    MinimumWithMultiplicity, Product, ScoredOperator,
};
use zeno_adp::classification::{Classification, Classified};
use zeno_adp::compiled::Program;
use zeno_adp::fast::MinimumTable;
use zeno_adp::queries::{
    co_minimal, count, derivation_count, k_lowest, minimum, minimum_cells, MinimumBackend,
};
use zeno_adp::{
    audit_bounded, audit_bounded_classified, exhaustive, tabulate, tabulate_cells, AuditBudget,
    Chart, Error, Operator, Tree,
};

// The domains have at most 321 global paths, and local paths on these smaller
// grids remain well below this aggregate node budget. It catches scope growth.
pub const TEST_BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 100_000,
};
// Exercises truncation and a cutoff within an equal-score group.
const K: usize = 3;

pub fn words<T: Copy>(alphabet: [T; 2], max: usize) -> Vec<Vec<T>> {
    let mut all = vec![Vec::new()];
    for len in 1..=max {
        for mask in 0..1 << len {
            all.push((0..len).map(|i| alphabet[(mask >> i) & 1]).collect());
        }
    }
    all
}

fn keep_pairs<O: Clone>(candidates: &[(Tree<O>, Cost)]) -> Result<Vec<(Tree<O>, Cost)>, Error> {
    Ok(candidates.to_vec())
}

struct Nodes;

impl<O> zeno_adp::Algebra<O> for Nodes {
    type Value = usize;

    fn apply(&self, _: &O, children: &[&usize]) -> Result<usize, Error> {
        Ok(1 + children.iter().map(|&&child| child).sum::<usize>())
    }

    fn choose(&self, candidates: &[usize]) -> Result<Vec<usize>, Error> {
        Ok(candidates.iter().copied().min().into_iter().collect())
    }
}

fn node_count<O>(tree: &Tree<O>) -> usize {
    1 + tree.children.iter().map(node_count).sum::<usize>()
}

pub fn public_questions<O: Operator + Debug + Ord + ScoredOperator>(
    chart: &Chart<O>,
    source: &impl Program<Op = O>,
    fused: MinimumTable,
    expected_min: i64,
    expected_count: usize,
) -> (usize, usize, usize, usize) {
    let additive = Additive::default();
    let recovered = stream::fast_questions(source, chart);
    assert_eq!(stream::compiled_questions(source, chart), recovered);
    let oracle = exhaustive(chart, &Product::new(Enumerate, additive, keep_pairs::<O>)).unwrap();
    assert_eq!(oracle.len(), expected_count);
    assert_eq!(
        oracle.iter().map(|pair| pair.1).min(),
        Some(Cost::Finite(expected_min))
    );
    assert_eq!(count(chart, Default::default()), Ok(expected_count as u128));
    assert_eq!(derivation_count(chart), Ok(expected_count as u128));

    let trees = oracle.iter().map(|pair| pair.0.clone()).collect::<Vec<_>>();
    let ordered = audit_bounded(chart, &Enumerate, TEST_BUDGET, Default::default()).unwrap();
    assert_eq!(ordered.bellman.oracle, trees);
    assert_eq!(ordered.bellman.tabulated, trees);
    assert!(ordered.bellman.first_failure.is_none(), "{ordered:?}");
    assert!(ordered.ambiguities.is_empty(), "{ordered:?}");

    let mut sorted: Vec<_> = oracle.iter().collect();
    sorted.sort_by_key(|pair| pair.1);
    let best = Cost::Finite(expected_min);
    let optimal: Vec<_> = oracle.iter().filter(|pair| pair.1 == best).collect();
    let ties = co_minimal(chart, &additive, Default::default()).unwrap();
    assert!(ties
        .iter()
        .map(|entry| (&entry.tree, entry.value))
        .eq(optimal.iter().map(|pair| (&pair.0, pair.1))));
    let ranked = k_lowest(chart, &additive, K, Default::default()).unwrap();
    assert!(ranked
        .iter()
        .map(|entry| (&entry.tree, entry.value))
        .eq(sorted.iter().take(K).map(|pair| (&pair.0, pair.1))));

    let expected = DerivationSummary {
        cost: best,
        optimal_derivations: optimal.len() as u128,
        total_derivations: expected_count as u128,
    };
    let summary = audit_bounded(
        chart,
        &MinimumWithMultiplicity::default(),
        TEST_BUDGET,
        Default::default(),
    )
    .unwrap();
    assert!(summary.bellman.first_failure.is_none(), "{summary:?}");
    assert_eq!(summary.bellman.oracle, [expected]);
    assert_eq!(summary.bellman.tabulated, [expected]);

    let product = Product::new(additive, Nodes, lexicographic_min);
    let smallest_optimum = optimal
        .iter()
        .map(|pair| node_count(&pair.0))
        .min()
        .unwrap();
    let product = audit_bounded(chart, &product, TEST_BUDGET, Default::default()).unwrap();
    assert!(product.bellman.first_failure.is_none(), "{product:?}");
    assert_eq!(product.bellman.oracle, [(best, smallest_optimum)]);
    assert_eq!(product.bellman.tabulated, [(best, smallest_optimum)]);

    let score_audit = audit_bounded(chart, &additive, TEST_BUDGET, Default::default()).unwrap();
    assert!(
        score_audit.bellman.first_failure.is_none(),
        "{score_audit:?}"
    );
    let scalar = minimum_cells(chart, &additive).unwrap();
    let reference = tabulate_cells(chart, &additive).unwrap();
    assert_eq!(fused.root(), chart.root());
    assert!(reference.iter().map(|bag| bag.first().copied()).eq(scalar));
    assert!(reference
        .iter()
        .map(|bag| bag.first().copied())
        .eq(fused.cells().iter().map(|value| value.map(Cost::Finite))));
    assert_eq!(fused.minimum(), Some(expected_min));
    assert_eq!(
        minimum(chart, &additive, MinimumBackend::Scalar),
        Ok(Some(best))
    );
    (
        ordered.bellman.cells,
        ordered.bellman.rules,
        ordered.tree_nodes,
        recovered,
    )
}

/// Compare the classified question with both root enumeration and the
/// cell-local audit. Cross-check ambiguity witnesses with pretty × count.
pub fn classified_questions<O: Clone + Debug + ScoredOperator, C: Classification<O> + Copy>(
    chart: &Chart<O>,
    classifier: C,
    expected_minima: &[(C::Class, Cost)],
) -> (usize, Vec<(C::Class, u128)>) {
    let minimum = Classified::new(classifier, Additive::default());
    let report = audit_bounded_classified(
        chart,
        &minimum,
        minimum.classes(),
        TEST_BUDGET,
        Default::default(),
    )
    .unwrap();
    assert!(report.bellman.first_failure.is_none(), "{report:?}");
    assert_eq!(report.bellman.oracle, expected_minima);
    assert_eq!(report.bellman.tabulated, expected_minima);
    assert_eq!(exhaustive(chart, &minimum).unwrap(), expected_minima);
    let keys: Vec<_> = expected_minima.iter().map(|(key, _)| key.clone()).collect();
    assert_eq!(tabulate(chart, minimum.classes()).unwrap(), keys);
    assert_eq!(exhaustive(chart, minimum.classes()).unwrap(), keys);

    let count = Classified::new(classifier, Count);
    let mut sizes = tabulate_cells(chart, &count).unwrap();
    assert!(sizes
        .iter()
        .enumerate()
        .filter_map(|(cell, groups)| {
            groups
                .iter()
                .find(|(_, count)| *count > 1)
                .map(|(key, count)| (cell, key, *count))
        })
        .eq(report.ambiguities.iter().map(|witness| (
            witness.cell,
            &witness.duplicate.answer,
            witness.duplicate.occurrences as u128,
        ))));
    let root = std::mem::take(&mut sizes[chart.root()]);
    assert_eq!(root, exhaustive(chart, &count).unwrap());
    (report.ambiguities.len(), root)
}
