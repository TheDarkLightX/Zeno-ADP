use std::fmt::Debug;

use zeno_adp::algebras::{
    Additive, Cost, Count, Enumerate, Maximum, MinimumWithMultiplicity, Product, ScoredOperator,
};
use zeno_adp::fast::{self, BestTable, Fold, RuleSource, ScoreTrees};
use zeno_adp::queries::{k_lowest, TreeMultiplicity};
use zeno_adp::{compiled, tabulate_cells, Chart, Error, Operator, Tree};

// Includes empty results, single-best, ties, and cutoffs.
const RANKS: [usize; 4] = [0, 1, 2, 5];

fn select_ties<O: Clone>(bag: &[(Cost, Tree<O>)]) -> Result<Vec<(Cost, Tree<O>)>, Error> {
    let best = bag.iter().map(|(score, _)| score).min();
    Ok(bag
        .iter()
        .filter(|(score, _)| Some(score) == best)
        .cloned()
        .collect())
}

#[allow(dead_code)] // The standalone compiler tests also include this module.
pub fn fast_questions<O: Operator + Debug + Ord + ScoredOperator>(
    source: &impl RuleSource<Op = O>,
    chart: &Chart<O>,
) -> usize {
    let score = Additive::default();
    let best = BestTable::new(source).unwrap();
    let count = fast::tabulate(source, &Count).unwrap();
    let product = MinimumWithMultiplicity::default();
    let multiplicity = fast::tabulate(source, &product).unwrap();
    let eager = fast::tabulate(source, &ScoreTrees).unwrap();
    compare(
        best.scores(),
        tabulate_cells(chart, &score).unwrap(),
        chart.root(),
    );
    compare(&count, tabulate_cells(chart, &Count).unwrap(), chart.root());
    compare(
        &multiplicity,
        tabulate_cells(chart, &product).unwrap(),
        chart.root(),
    );
    check_trees(chart, &best, &eager)
}

fn compare<V: Debug + Eq>(fast: &fast::Table<V>, reference: Vec<Vec<V>>, root: usize) {
    assert_eq!(fast.root(), root);
    assert_eq!(fast.cells().len(), reference.len());
    for (cell, (actual, expected)) in fast.cells().iter().zip(reference).enumerate() {
        assert_eq!(actual.as_slice(), expected, "cell {cell}");
    }
}

#[allow(dead_code)] // The standalone streaming tests also include this module.
pub fn compiled_questions<O: Operator + Debug + Ord + ScoredOperator>(
    source: &impl compiled::Program<Op = O>,
    chart: &Chart<O>,
) -> usize {
    let mut counts = vec![0; chart.cells().len()];
    compiled::replay(source, |cell, ordinal, site, operator, children| {
        assert!(!site.is_empty());
        assert_eq!(ordinal, counts[cell]);
        let rule = &chart.cells()[cell][ordinal];
        assert_eq!(operator, rule.operator, "{cell}/{ordinal}/{site}");
        assert_eq!(children, rule.children, "{cell}/{ordinal}/{site}");
        counts[cell] += 1;
        Ok(())
    })
    .unwrap();
    assert!(counts.into_iter().eq(chart.cells().iter().map(Vec::len)));
    compare_compiled_tables(source, chart)
}

#[allow(dead_code)]
pub fn compare_compiled_tables<O: Operator + Debug + Ord + ScoredOperator>(
    source: &impl compiled::Program<Op = O>,
    chart: &Chart<O>,
) -> usize {
    let score = Additive::default();
    let product = MinimumWithMultiplicity::default();
    let best = compiled::best(source).unwrap();
    let eager = compiled::tabulate(source, &ScoreTrees).unwrap();
    check_compiled_question(source, chart, &score, best.scores());
    check_compiled_question(
        source,
        chart,
        &Maximum,
        &compiled::tabulate(source, &Maximum).unwrap(),
    );
    check_compiled_question(
        source,
        chart,
        &Count,
        &compiled::tabulate(source, &Count).unwrap(),
    );
    check_compiled_question(
        source,
        chart,
        &product,
        &compiled::tabulate(source, &product).unwrap(),
    );
    let reference = tabulate_cells(chart, &Product::new(score, Enumerate, select_ties)).unwrap();
    check_live(source, &ScoreTrees, &reference, |actual, expected| {
        let paired = actual
            .iter()
            .flat_map(|answer| answer.trees.iter().map(move |tree| (answer.cost, tree)));
        assert!(paired.eq(expected.iter().map(|(score, tree)| (*score, tree))));
    });
    check_trees(chart, &best, &eager)
}

fn check_compiled_question<O, V>(
    source: &impl compiled::Program<Op = O>,
    chart: &Chart<O>,
    algebra: &(impl Fold<O, Value = V> + zeno_adp::Algebra<O, Value = V>),
    table: &fast::Table<V>,
) where
    V: Debug + Eq + Clone,
{
    let reference = tabulate_cells(chart, algebra).unwrap();
    check_live(source, algebra, &reference, |actual, expected| {
        assert!(expected.len() <= 1);
        assert_eq!(actual, expected.first());
    });
    compare(table, reference, chart.root());
}

fn check_live<O, A: Fold<O>, R>(
    source: &impl compiled::Program<Op = O>,
    algebra: &A,
    reference: &[Vec<R>],
    compare_answer: impl Fn(Option<&A::Value>, &[R]),
) {
    let mut next = 0;
    let root = compiled::tabulate_root(source, algebra, |rank, actual| {
        assert_eq!(rank, next);
        compare_answer(actual, &reference[rank]);
        next += 1;
    })
    .unwrap();
    assert_eq!(next, reference.len());
    compare_answer(root.as_ref(), &reference[source.root()]);
}

fn check_trees<O: Operator + Debug + Ord + ScoredOperator>(
    chart: &Chart<O>,
    best: &BestTable<'_, impl RuleSource<Op = O>>,
    eager: &fast::Table<fast::OptimalTrees<O>>,
) -> usize {
    let score = Additive::default();
    let reference_eager =
        tabulate_cells(chart, &Product::new(score, Enumerate, select_ties)).unwrap();
    assert_eq!(eager.root(), chart.root());
    assert_eq!(eager.cells().len(), chart.cells().len());
    let mut checked_trees = 0;
    for (cell, expected) in reference_eager.iter().enumerate() {
        let paired = eager.cells()[cell]
            .iter()
            .flat_map(|answer| answer.trees.iter().map(move |tree| (answer.cost, tree)));
        assert!(
            paired.eq(expected.iter().map(|(score, tree)| (*score, tree))),
            "cell {cell}"
        );
        let subchart = Chart::new(chart.cells()[..=cell].to_vec(), cell).unwrap();
        let recover = best.recover_at(cell).unwrap();
        for identity in [
            TreeMultiplicity::DistinctTrees,
            TreeMultiplicity::Derivations,
        ] {
            let ranked = k_lowest(&subchart, &score, usize::MAX, identity).unwrap();
            let ties: Vec<_> = ranked
                .iter()
                .take_while(|answer| answer.value == ranked[0].value)
                .cloned()
                .collect();
            assert_eq!(
                recover.first_minimum_tree().unwrap().as_ref(),
                ranked.first(),
                "cell {cell}"
            );
            checked_trees += usize::from(!ranked.is_empty());
            assert_eq!(recover.co_minimal(identity).unwrap(), ties, "cell {cell}");
            checked_trees += ties.len();
            for k in RANKS {
                let expected = &ranked[..k.min(ranked.len())];
                assert_eq!(
                    recover.k_lowest(k, identity).unwrap(),
                    expected,
                    "cell {cell}, k={k}"
                );
                checked_trees += expected.len();
            }
            if identity == TreeMultiplicity::Derivations {
                match &eager.cells()[cell] {
                    Some(answer) => {
                        assert!(ties.iter().all(|entry| entry.value == answer.cost));
                        assert!(answer.trees.iter().eq(ties.iter().map(|entry| &entry.tree)));
                        checked_trees += answer.trees.len();
                    }
                    None => assert!(ties.is_empty()),
                }
            }
        }
    }
    checked_trees
}
