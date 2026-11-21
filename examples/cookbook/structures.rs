use super::{words, Checks};
use std::collections::{BTreeMap, BTreeSet};
use zeno_adp::algebras::{Additive, Cost, Count, Maximum, Minimum, ScoredOperator};
use zeno_adp::classification::{Classification, Classified};
use zeno_adp::grammars::{self, Fold};
use zeno_adp::probability::{Rational, SumProduct, WeightedOperator};
use zeno_adp::{
    audit_bounded_classified, enumerate, tabulate_cells, AuditBudget, Chart, Error, Operator, Rule,
    Tree,
};

#[path = "../support/fold_classes.rs"]
#[allow(dead_code)]
mod fold_classes;
use fold_classes::Folding;

const MAX_LEN: usize = 5; // Nonempty interior and trailing intervals around pairs.
const LAST_LOOP_MIN: usize = 2; // Test adjacent pairs and two stricter loop lengths.
type Pair = (usize, usize);

fn raw_pairs(sequence: &[u8], loop_min: usize) -> BTreeSet<Vec<Pair>> {
    let allowed: Vec<_> = (0..sequence.len())
        .flat_map(|left| {
            (left + 1..sequence.len())
                .filter(move |&right| right - left > loop_min && sequence[left] != sequence[right])
                .map(move |right| (left, right))
        })
        .collect();
    let mut folds = BTreeSet::new();
    for mask in 0..1 << allowed.len() {
        let pairs: Vec<_> = allowed
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(i, p)| (mask & (1 << i) != 0).then_some(p))
            .collect();
        let valid = pairs.iter().enumerate().all(|(i, &(a, b))| {
            pairs[i + 1..]
                .iter()
                .all(|&(c, d)| a != c && a != d && b != c && b != d && !(a < c && c < b && b < d))
        });
        if valid {
            folds.insert(pairs);
        }
    }
    folds
}

fn raw_best(sequence: &[u8], loop_min: usize) -> Vec<Vec<i64>> {
    let n = sequence.len();
    let mut best = vec![vec![0; n + 1]; n + 1];
    for right in 1..=n {
        for left in (0..right).rev() {
            let mut score = best[left][right - 1];
            for partner in left..right - 1 {
                if right - 1 - partner > loop_min && sequence[partner] != sequence[right - 1] {
                    score = score.min(best[left][partner] + best[partner + 1][right - 1] - 1);
                }
            }
            best[left][right] = score;
        }
    }
    best
}

fn read_fold(tree: &Tree<Fold>, pairs: &mut Vec<Pair>) {
    if let Fold::Pair { left, right } = tree.operator {
        pairs.push((left, right));
    }
    for child in &tree.children {
        read_fold(child, pairs);
    }
}

pub fn nussinov() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for sequence in words(b"AU", MAX_LEN) {
        for loop_min in 0..=LAST_LOOP_MIN {
            let chart = grammars::nussinov(&sequence, loop_min)?;
            let source = grammars::nussinov_source(&sequence, loop_min)?;
            checks.chart(&chart);
            checks.compiled(&source, &chart, &Additive::default())?;
            let minimum = tabulate_cells(&chart, &Minimum)?;
            let counts = tabulate_cells(&chart, &Count)?;
            let fast = zeno_adp::fast::nussinov(&sequence, loop_min)?;
            let finite: Vec<_> = minimum
                .iter()
                .map(|v| match v.as_slice() {
                    [Cost::Finite(n)] => vec![*n],
                    _ => unreachable!(),
                })
                .collect();
            checks.equal_values(fast.cells(), &finite);
            let best = raw_best(&sequence, loop_min);
            assert_eq!(counts[0], [1]);
            assert_eq!(finite[0], [0]);
            let mut rank = 1;
            for len in 1..=sequence.len() {
                for start in 0..=sequence.len() - len {
                    let end = start + len;
                    assert_eq!(finite[rank], [best[start][end]]);
                    assert_eq!(
                        counts[rank],
                        [raw_pairs(&sequence[start..end], loop_min).len() as u128]
                    );
                    rank += 1;
                }
            }
            let direct = raw_pairs(&sequence, loop_min);
            let mut found = BTreeSet::new();
            for tree in enumerate(&chart) {
                let mut pairs = Vec::new();
                read_fold(&tree, &mut pairs);
                pairs.sort_unstable();
                assert!(found.insert(pairs));
            }
            assert_eq!(found, direct);
            // Three outputs cover the boundary between tied and lower-ranked folds.
            const FIRST_FOLDS: usize = 3;
            let mut scores: Vec<_> = direct
                .iter()
                .map(|pairs| Cost::Finite(-(pairs.len() as i64)))
                .collect();
            scores.sort_unstable();
            let ranked = zeno_adp::queries::k_lowest(
                &chart,
                &Minimum,
                FIRST_FOLDS,
                zeno_adp::queries::TreeMultiplicity::DistinctTrees,
            )?;
            assert!(ranked
                .iter()
                .map(|answer| answer.value)
                .eq(scores.into_iter().take(FIRST_FOLDS)));
        }
    }
    Ok(checks)
}

const PAIR_WEIGHT: u128 = 2; // One toy relative weight per chosen pair.

impl WeightedOperator for Folding {
    fn weight(&self) -> Rational {
        match self {
            Self::Base(Fold::Pair { .. }) => Rational::new(PAIR_WEIGHT, 1).unwrap(),
            _ => Rational::ONE,
        }
    }
}

#[derive(Clone, Copy)]
struct Shape;

impl Classification<Folding> for Shape {
    type Class = String;
    fn classify(&self, op: &Folding, parts: &[&String]) -> Result<String, Error> {
        Ok(match op {
            Folding::Base(Fold::Empty) => String::new(),
            Folding::Base(Fold::Unpaired { .. }) => parts[0].clone(),
            Folding::Base(Fold::Pair { .. }) => format!("({}){}", parts[0], parts[1]),
            Folding::Split => format!("{}{}", parts[0], parts[1]),
        })
    }
}

fn raw_shapes(sequence: &[u8], loop_min: usize) -> BTreeMap<String, (i64, u128, Rational)> {
    let mut counts = BTreeMap::new();
    for pairs in raw_pairs(sequence, loop_min) {
        let mut brackets = vec!['.'; sequence.len()];
        for &(i, j) in &pairs {
            brackets[i] = '(';
            brackets[j] = ')';
        }
        let key: String = brackets.into_iter().filter(|&c| c != '.').collect();
        let row = counts.entry(key).or_insert((0_i64, 0_u128, Rational::ZERO));
        row.0 = row.0.min(-(pairs.len() as i64));
        row.1 += 1;
        row.2 = row
            .2
            .checked_add(Rational::new(PAIR_WEIGHT.pow(pairs.len() as u32), 1).unwrap())
            .unwrap();
    }
    counts
}

pub fn shapes() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for sequence in words(b"AU", MAX_LEN) {
        for loop_min in 0..=LAST_LOOP_MIN {
            let chart = fold_classes::chart(&sequence, loop_min, false)?;
            checks.chart(&chart);
            let min = tabulate_cells(&chart, &Classified::new(Shape, Minimum))?;
            let count = tabulate_cells(&chart, &Classified::new(Shape, Count))?;
            let mass = tabulate_cells(&chart, &Classified::new(Shape, SumProduct))?;
            let spans = std::iter::once(0..0).chain(
                (1..=sequence.len())
                    .flat_map(|len| (0..=sequence.len() - len).map(move |a| a..a + len)),
            );
            for (rank, span) in spans.enumerate() {
                let expected = raw_shapes(&sequence[span], loop_min);
                assert!(min[rank]
                    .iter()
                    .map(|(key, v)| (key, *v))
                    .eq(expected.iter().map(|(k, v)| (k, Cost::Finite(v.0)))));
                assert!(count[rank]
                    .iter()
                    .map(|(key, v)| (key, *v))
                    .eq(expected.iter().map(|(k, v)| (k, v.1))));
                assert!(mass[rank]
                    .iter()
                    .map(|(key, v)| (key, *v))
                    .eq(expected.iter().map(|(k, v)| (k, v.2))));
            }
        }
    }
    let ambiguous = fold_classes::chart(b"AU", 0, true)?;
    checks.chart(&ambiguous);
    let question = Classified::new(Shape, Count);
    // One empty node, two 2-node unary trees, then the 3-, 3- and
    // 5-node full-span derivations.
    const TWO_BASE_BUDGET: AuditBudget = AuditBudget { max_tree_nodes: 16 };
    let report = audit_bounded_classified(
        &ambiguous,
        &question,
        question.classes(),
        TWO_BASE_BUDGET,
        Default::default(),
    )?;
    assert!(report.bellman.first_failure.is_none());
    assert_eq!(report.ambiguities.last().unwrap().duplicate.answer, "");
    assert_eq!(
        report.bellman.tabulated,
        [("".to_string(), 2), ("()".to_string(), 1)]
    );
    Ok(checks)
}

#[derive(Clone, Copy)]
enum Crossing {
    Pair { endpoints: Pair, matched: u8 },
    Cross,
}

impl Operator for Crossing {
    fn arity(&self) -> usize {
        match self {
            Self::Pair { .. } => 0,
            Self::Cross => 2,
        }
    }
}

impl ScoredOperator for Crossing {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Pair { matched, .. } => 1 + i64::from(matched == b'b'),
            Self::Cross => 0,
        })
    }
}

pub fn single_crossing() -> Result<Checks, Error> {
    const MAX_CROSSING_LEN: usize = 5; // Four endpoints, with room for one unused token.
    let mut checks = Checks::default();
    for word in words(b"ab", MAX_CROSSING_LEN) {
        let n = word.len();
        let root = n * n;
        let cell = |a, b| a * n + b;
        let mut rows = vec![Vec::new(); root + 1];
        for a in 0..n {
            for b in a + 1..n {
                if word[a] == word[b] {
                    rows[cell(a, b)].push(Rule::new(
                        Crossing::Pair {
                            endpoints: (a, b),
                            matched: word[a],
                        },
                        [],
                    ));
                }
                for c in a + 1..b {
                    for d in b + 1..n {
                        rows[root].push(Rule::new(Crossing::Cross, [cell(a, b), cell(c, d)]));
                    }
                }
            }
        }
        let chart = Chart::new(rows, root)?;
        checks.chart(&chart);
        let scores = tabulate_cells(&chart, &Maximum)?;
        let counts = tabulate_cells(&chart, &Count)?;
        for a in 0..n {
            for b in 0..n {
                let legal = a < b && word[a] == word[b];
                assert!(scores[cell(a, b)]
                    .iter()
                    .copied()
                    .eq(legal.then_some(Cost::Finite(1 + i64::from(word[a] == b'b')))));
                assert!(counts[cell(a, b)].iter().copied().eq(legal.then_some(1)));
            }
        }
        let mut options = BTreeMap::new();
        for mask in 0..1_usize << n {
            let ends: Vec<_> = (0..n).filter(|&i| mask & (1 << i) != 0).collect();
            if let [a, b, c, d] = ends.as_slice() {
                if word[*a] == word[*c] && word[*b] == word[*d] {
                    options.insert(
                        [(*a, *c), (*b, *d)],
                        Cost::Finite(2 + i64::from(word[*a] == b'b') + i64::from(word[*b] == b'b')),
                    );
                }
            }
        }
        assert!(scores[root]
            .iter()
            .copied()
            .eq(options.values().copied().max()));
        assert!(counts[root]
            .iter()
            .copied()
            .eq((!options.is_empty()).then_some(options.len() as u128)));
        let mut found = BTreeSet::new();
        for tree in enumerate(&chart) {
            let [first, second] = tree.children.as_slice() else {
                unreachable!()
            };
            let pair = |node: &Tree<Crossing>| match node.operator {
                Crossing::Pair { endpoints, .. } => endpoints,
                Crossing::Cross => unreachable!(),
            };
            assert!(found.insert([pair(first), pair(second)]));
        }
        assert!(found.into_iter().eq(options.into_keys()));
    }
    Ok(checks)
}
