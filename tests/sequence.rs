#[path = "../examples/support/fold_classes.rs"]
mod fold_classes;
mod support;

use std::collections::BTreeSet;
use std::fmt::Debug;
use support::{classified_questions, public_questions, words};
use zeno_adp::algebras::{Cost, Count, Enumerate, Minimum, MinimumCount, Optimum, ScoredOperator};
use zeno_adp::grammars::{alignment, alignment_source, nussinov, nussinov_source, Align, Fold};
use zeno_adp::{audit, enumerate, exhaustive, Algebra, Chart, Operator, Tree};

// Motzkin(6) bounds fold enumeration by 51; Delannoy(4,4) bounds paths by 321.
const FOLD_LENGTH: usize = 6;
const ALIGN_LENGTH: usize = 4;
const NO_LOOP_RESTRICTION: usize = 0;

#[derive(Default, Debug)]
struct Totals {
    cells: usize,
    rules: usize,
    trees: usize,
    largest: usize,
    returned_tree_comparisons: usize,
}

impl Totals {
    fn measure(&mut self, chart: &Chart<impl Operator>, trees: usize, recovered: usize) {
        self.cells += chart.cells().len();
        self.rules += chart.cells().iter().map(Vec::len).sum::<usize>();
        self.trees += trees;
        self.largest = self.largest.max(trees);
        self.returned_tree_comparisons += recovered;
    }
}

fn checked<O: Clone + Debug, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
    expected: &[A::Value],
    input: &impl Debug,
) {
    let observed = audit(chart, algebra).unwrap();
    assert!(observed.first_failure.is_none(), "{input:?} {observed:?}");
    assert_eq!(observed.oracle, expected, "{input:?}");
    assert_eq!(observed.tabulated, expected, "{input:?}");
}

fn all_questions<O: Operator + Debug + Eq + ScoredOperator>(
    chart: &Chart<O>,
    trees: &[Tree<O>],
    scores: impl Iterator<Item = i64>,
    input: &impl Debug,
) -> (i64, u128) {
    let all_scores: Vec<_> = scores.collect();
    let best = *all_scores.iter().min().unwrap();
    let count = trees.len() as u128;
    let ties = all_scores.iter().filter(|&&cost| cost == best).count() as u128;
    let cost = Cost::Finite(best);

    checked(chart, &Minimum, &[cost], input);
    checked(chart, &Count, &[count], input);
    checked(chart, &Enumerate, trees, input);
    checked(
        chart,
        &MinimumCount,
        &[Optimum { cost, count: ties }],
        input,
    );
    assert_eq!(exhaustive(chart, &Enumerate).unwrap(), trees);

    (best, count)
}

// Scalar hyperedge experiment. The numeric identities and additions are safe
// over the test domains' score and derivation bounds.
fn scalar_semirings<O: Operator + ScoredOperator>(chart: &Chart<O>) -> (i64, u128) {
    let mut table = Vec::<(i64, u128)>::new();
    for rules in chart.cells() {
        let mut minimum = i64::MAX;
        let mut count = 0;
        for rule in rules {
            let Cost::Finite(weight) = rule.operator.cost() else {
                unreachable!()
            };
            let (cost, ways) = rule
                .children
                .iter()
                .fold((weight, 1), |(cost, ways), &child| {
                    (cost + table[child].0, ways * table[child].1)
                });
            minimum = minimum.min(cost);
            count += ways;
        }
        table.push((minimum, count));
    }
    table[chart.root()]
}

// A separately expressed, implicit chart with no rule data or witness identities.
fn embedded_alignment(a: &[u8], b: &[u8]) -> (i64, u128) {
    let mut table = vec![vec![(0, 1); b.len() + 1]; a.len() + 1];
    for (i, row) in table.iter_mut().enumerate() {
        row[0].0 = i as i64;
    }
    for (j, entry) in table[0].iter_mut().enumerate() {
        entry.0 = j as i64;
    }
    for (i, left) in a.iter().enumerate() {
        for (j, right) in b.iter().enumerate() {
            let (diagonal, d) = table[i][j];
            let (up, u) = table[i][j + 1];
            let (across, c) = table[i + 1][j];
            let score = (diagonal + i64::from(left != right))
                .min(up + 1)
                .min(across + 1);
            table[i + 1][j + 1] = (score, d + u + c);
        }
    }
    table[a.len()][b.len()]
}

type Pairs = Vec<(usize, usize)>;

// Independent fold oracle: filter subsets of all compatible pairs for shared
// endpoints and crossing pairs. It has no interval recurrence.
fn matching_subsets(word: &[u8]) -> BTreeSet<Pairs> {
    let mut compatible = Vec::new();
    for (i, left) in word.iter().enumerate() {
        for (j, right) in word.iter().enumerate().skip(i + 1) {
            if left != right {
                compatible.push((i, j));
            }
        }
    }
    (0..1 << compatible.len())
        .filter_map(|mask| {
            let pairs: Pairs = compatible
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(bit, pair)| (mask & (1 << bit) != 0).then_some(pair))
                .collect();
            let valid = pairs.iter().enumerate().all(|(p, &(i, j))| {
                pairs[p + 1..].iter().all(|&(k, l)| {
                    i != k && i != l && j != k && j != l && !(i < k && k < j && j < l)
                })
            });
            valid.then_some(pairs)
        })
        .collect()
}

fn folding_yield(tree: &Tree<Fold>, n: usize) -> Pairs {
    fn visit(tree: &Tree<Fold>, positions: &mut Vec<usize>, pairs: &mut Pairs) {
        match tree.operator {
            Fold::Empty => {}
            Fold::Unpaired { at } => positions.push(at),
            Fold::Pair { left, right } => {
                positions.extend([left, right]);
                pairs.push((left, right));
            }
        }
        for child in &tree.children {
            visit(child, positions, pairs);
        }
    }
    let mut positions = Vec::new();
    let mut pairs = Vec::new();
    visit(tree, &mut positions, &mut pairs);
    positions.sort_unstable();
    assert!(positions.into_iter().eq(0..n), "{tree:?}");
    pairs.sort_unstable();
    pairs
}

#[test]
fn nussinov_exhaustive() {
    let domain = words(*b"AU", FOLD_LENGTH);
    let mut totals = Totals::default();
    for input in &domain {
        let chart = nussinov(input, NO_LOOP_RESTRICTION).unwrap();
        let trees = enumerate(&chart);
        let expected = matching_subsets(input);
        let observed: BTreeSet<_> = trees
            .iter()
            .map(|t| folding_yield(t, input.len()))
            .collect();
        assert_eq!(observed, expected, "{input:?}");
        assert_eq!(observed.len(), trees.len(), "{input:?}");
        let summary = all_questions(
            &chart,
            &trees,
            expected.iter().map(|pairs| -(pairs.len() as i64)),
            input,
        );
        assert_eq!(scalar_semirings(&chart), summary, "{input:?}");
        let (_, _, _, recovered) = public_questions(
            &chart,
            &nussinov_source(input, NO_LOOP_RESTRICTION).unwrap(),
            zeno_adp::fast::nussinov(input, NO_LOOP_RESTRICTION).unwrap(),
            summary.0,
            trees.len(),
        );
        totals.measure(&chart, trees.len(), recovered);
    }
    assert_eq!(totals.largest, 30);
    println!("fold: {} inputs; {totals:?}; four audits each, scalar comparison and independent matching yields", domain.len());
}

type Column = (Option<u8>, Option<u8>);

fn paths(left: &[u8], right: &[u8], prefix: &mut Vec<Column>, out: &mut BTreeSet<Vec<Column>>) {
    match (left.split_first(), right.split_first()) {
        (None, None) => {
            assert!(out.insert(prefix.clone()));
        }
        (Some((&a, next_left)), Some((&b, next_right))) => {
            prefix.push((Some(a), Some(b)));
            paths(next_left, next_right, prefix, out);
            prefix.pop();
        }
        _ => {}
    }
    if let Some((&a, rest)) = left.split_first() {
        prefix.push((Some(a), None));
        paths(rest, right, prefix, out);
        prefix.pop();
    }
    if let Some((&b, rest)) = right.split_first() {
        prefix.push((None, Some(b)));
        paths(left, rest, prefix, out);
        prefix.pop();
    }
}

fn columns(tree: &Tree<Align>) -> Vec<Column> {
    let column = match tree.operator {
        Align::Start => return Vec::new(),
        Align::Diagonal { left, right } => (Some(left), Some(right)),
        Align::Left(left) => (Some(left), None),
        Align::Right(right) => (None, Some(right)),
    };
    let mut result = columns(&tree.children[0]);
    result.push(column);
    result
}

#[test]
fn alignment_exhaustive() {
    let domain = words(*b"AC", ALIGN_LENGTH);
    let mut totals = Totals::default();
    for left in &domain {
        for right in &domain {
            let chart = alignment(left, right).unwrap();
            let trees = enumerate(&chart);
            let mut expected = BTreeSet::new();
            paths(left, right, &mut Vec::new(), &mut expected);
            let observed: BTreeSet<_> = trees.iter().map(columns).collect();
            assert_eq!(observed, expected, "{left:?} {right:?}");
            assert_eq!(observed.len(), trees.len(), "{left:?} {right:?}");
            let scores = expected
                .iter()
                .map(|path| path.iter().filter(|(a, b)| a != b).count() as i64);
            let summary = all_questions(&chart, &trees, scores, &(left, right));
            assert_eq!(scalar_semirings(&chart), summary, "{left:?} {right:?}");
            assert_eq!(
                embedded_alignment(left, right),
                summary,
                "{left:?} {right:?}"
            );
            let (_, _, _, recovered) = public_questions(
                &chart,
                &alignment_source(left, right).unwrap(),
                zeno_adp::fast::alignment(left, right).unwrap(),
                summary.0,
                trees.len(),
            );
            totals.measure(&chart, trees.len(), recovered);
        }
    }
    assert_eq!(totals.largest, 321);
    println!("alignment: {} ordered input pairs; {totals:?}; four audits each, scalar and embedded comparisons and independent column paths", domain.len().pow(2));
}

#[test]
fn classified_folds_agree_on_the_complete_short_domain() {
    use fold_classes::{chart, DotBracket};
    use zeno_adp::algebras::Additive;
    use zeno_adp::queries::minimum_cells;
    use zeno_adp::tabulate_cells;

    let domain = words(*b"AU", FOLD_LENGTH);
    let mut totals = [(0, 0, 0); 2];
    for input in &domain {
        let mut expected: Vec<_> = matching_subsets(input)
            .into_iter()
            .map(|pairs| {
                let score = Cost::Finite(-(pairs.len() as i64));
                let mut model = vec![b'.'; input.len()];
                for (left, right) in pairs {
                    model[left] = b'(';
                    model[right] = b')';
                }
                (String::from_utf8(model).unwrap(), score)
            })
            .collect();
        expected.sort_unstable();
        for (split, (cells, ambiguities, classes)) in [false, true].into_iter().zip(&mut totals) {
            let chart = chart(input, NO_LOOP_RESTRICTION, split).unwrap();
            let (ambiguous, root) = classified_questions(&chart, DotBracket, &expected);
            let additive = Additive::default();
            let scalar = minimum_cells(&chart, &additive).unwrap();
            let reference = tabulate_cells(&chart, &additive).unwrap();
            assert!(reference.iter().map(|bag| bag.first().copied()).eq(scalar));
            assert_eq!(ambiguous > 0, split && input.len() >= 2);
            assert_eq!(
                root.iter().any(|(_, multiplicity)| *multiplicity > 1),
                split && input.len() >= 2
            );
            *cells += chart.cells().len();
            *ambiguities += ambiguous;
            *classes += root.len();
        }
    }
    println!(
        "classified folds: {} inputs per grammar, (cells, ambiguous cells, root classes) {totals:?}",
        domain.len()
    );
}

#[test]
fn rolling_alignment_agrees_at_each_rank_and_root() {
    let domain = words(*b"AC", ALIGN_LENGTH);
    let mut checked_cells = 0;
    for left in &domain {
        for right in &domain {
            let chart = alignment(left, right).unwrap();
            let reference = zeno_adp::tabulate_cells(&chart, &Minimum).unwrap();
            let mut next = 0;
            let root = zeno_adp::compiled::alignment_rolling(left, right, |rank, score| {
                assert_eq!(rank, next, "{left:?} {right:?}");
                assert_eq!(
                    reference[rank],
                    [Cost::Finite(score)],
                    "{left:?} {right:?} rank {rank}"
                );
                next += 1;
            })
            .unwrap();
            assert_eq!(next, reference.len());
            assert_eq!(
                reference[chart.root()],
                [Cost::Finite(root)],
                "{left:?} {right:?} root"
            );
            checked_cells += next;
        }
    }
    assert_eq!(checked_cells, 16_641);
    println!(
        "rolling alignment: {} roots and {checked_cells} ranked observations",
        domain.len().pow(2)
    );
}
