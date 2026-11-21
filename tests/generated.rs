#[path = "../examples/support/optimal_bst.rs"]
mod optimal_bst;
#[path = "../examples/support/segmentation.rs"]
mod segmentation;

use std::fmt::Debug;
use zeno_adp::algebras::{Additive, Cost, Count, Enumerate, ScoredOperator};
use zeno_adp::compiled::{self, Program};
use zeno_adp::fast::{self, Fold, Table};
use zeno_adp::probability::{
    Expectation, ExpectationOperator, ExpectationValue, Rational, SignedRational,
};
use zeno_adp::{
    audit_bounded, compiled_grammar, tabulate_cells, Algebra, AnswerOrder, AuditBudget, Chart,
    Error, Operator, Rule,
};

use optimal_bst::SearchTree;
use segmentation::Segment;

impl ExpectationOperator for Segment {
    fn expectation(&self) -> Result<ExpectationValue, Error> {
        local_expectation(self)
    }
}

impl ExpectationOperator for SearchTree {
    fn expectation(&self) -> Result<ExpectationValue, Error> {
        local_expectation(self)
    }
}

fn local_expectation(op: &(impl Operator + ScoredOperator)) -> Result<ExpectationValue, Error> {
    let Cost::Finite(score) = op.cost() else {
        unreachable!()
    };
    let denominator = if op.arity() == 0 { 1 } else { 2 };
    let feature = Rational::new(score.unsigned_abs().into(), 1).unwrap();
    ExpectationValue::weighted_feature(
        Rational::new(1, denominator).unwrap(),
        SignedRational::new(feature, score < 0),
    )
}

// Five keys have Catalan(5) = 42 trees. The audit at all ranks is bounded
// by 21 spans × 42 occurrences × 11 nodes (5 keys and 6 empty children).
const DOMAIN_LENGTH: usize = 5;
const AUDIT_NODES: usize = 21 * 42 * 11;

type NamedRule<O> = (&'static str, Rule<O>);

// The objective charges two per segment, plus mismatches to the better of
// the two constant fitted levels. Count mismatches from raw observations.
fn segment_score(segment: &[bool]) -> i64 {
    const NEW_LEVEL_COST: i64 = 2;
    let mismatches = |level| segment.iter().filter(|&&bit| bit != level).count() as i64;
    NEW_LEVEL_COST + mismatches(false).min(mismatches(true))
}

fn exhaustive_segment_score(prefix: &[bool]) -> i64 {
    if prefix.is_empty() {
        return 0;
    }
    (0..1 << (prefix.len() - 1))
        .map(|cuts| {
            let mut start = 0;
            let mut score = 0;
            for end in 1..prefix.len() {
                if cuts & (1 << (end - 1)) != 0 {
                    score += segment_score(&prefix[start..end]);
                    start = end;
                }
            }
            score + segment_score(&prefix[start..])
        })
        .min()
        .unwrap()
}

fn segment_rules(input: &[bool]) -> Vec<Vec<NamedRule<Segment>>> {
    let mut cells = vec![vec![("Empty", Rule::new(Segment::Empty, []))]];
    for end in 1..=input.len() {
        cells.push(
            (0..end)
                .map(|start| {
                    (
                        "Append",
                        Rule::new(
                            Segment::Append {
                                start,
                                end,
                                cost: segment_score(&input[start..end]),
                            },
                            [start],
                        ),
                    )
                })
                .collect(),
        );
    }
    cells
}

fn search_tree_rules(input: &[u32]) -> Vec<Vec<NamedRule<SearchTree>>> {
    let mut spans: Vec<_> = (0..=input.len())
        .flat_map(|i| (i..=input.len()).map(move |j| (i, j)))
        .collect();
    spans.sort_unstable_by_key(|&(i, j)| (j, std::cmp::Reverse(i)));
    let rank = |i, j| spans.iter().position(|span| *span == (i, j)).unwrap();
    spans
        .iter()
        .map(|&(start, end)| {
            if start == end {
                vec![("Empty", Rule::new(SearchTree::Empty, []))]
            } else {
                let cost = input[start..end].iter().copied().map(i64::from).sum();
                (start..end)
                    .map(|index| {
                        (
                            "Key",
                            Rule::new(
                                SearchTree::Key { index, cost },
                                [rank(start, index), rank(index + 1, end)],
                            ),
                        )
                    })
                    .collect()
            }
        })
        .collect()
}

// Enumerate the costs of every tree by charging each key at its depth.
// This oracle takes raw weights and uses neither prefix sums nor interval ranks.
fn search_tree_costs(frequencies: &[u32], depth: i64) -> Vec<i64> {
    if frequencies.is_empty() {
        return vec![0];
    }
    let mut costs = Vec::new();
    for (root, &frequency) in frequencies.iter().enumerate() {
        let left = search_tree_costs(&frequencies[..root], depth + 1);
        let right = search_tree_costs(&frequencies[root + 1..], depth + 1);
        for left_cost in left {
            costs.extend(
                right
                    .iter()
                    .map(|right_cost| i64::from(frequency) * depth + left_cost + right_cost),
            );
        }
    }
    costs
}

#[test]
fn generated_search_tree_charges_the_single_key_frequency() {
    let input = optimal_bst::prepare(&[7]).unwrap();
    let table = optimal_bst::minimum(&input).unwrap();
    assert_eq!(table.answer(), Some(&Cost::Finite(7)));
    let program = optimal_bst::grammar(&input).unwrap();
    let chart = compiled::reference_chart(&program).unwrap();
    assert_eq!(
        tabulate_cells(&chart, &Additive::default()).unwrap(),
        [
            vec![Cost::Finite(0)],
            vec![Cost::Finite(0)],
            vec![Cost::Finite(7)]
        ],
    );
    assert_eq!(
        table,
        compiled::tabulate(&program, &Additive::default()).unwrap()
    );
}

#[test]
fn search_tree_scores_equal_exhaustive_depth_costs() {
    // These weights give zero-cost ties, uniform costs and unequal costs.
    const FREQUENCIES: [u32; 3] = [0, 1, 2];
    let mut charts = 0;
    let mut ranks = 0;
    for len in 0..=DOMAIN_LENGTH {
        for mut word in 0..FREQUENCIES.len().pow(len as u32) {
            let frequencies: Vec<_> = (0..len)
                .map(|_| {
                    let value = FREQUENCIES[word % FREQUENCIES.len()];
                    word /= FREQUENCIES.len();
                    value
                })
                .collect();
            let input = optimal_bst::prepare(&frequencies).unwrap();
            let bound = optimal_bst::grammar(&input).unwrap();
            let chart = compiled::reference_chart(&bound).unwrap();
            let reference = tabulate_cells(&chart, &Additive::default()).unwrap();
            let generated = optimal_bst::minimum(&input).unwrap();
            let direct = optimal_bst::direct(&input).unwrap();
            let mut rank = 0;
            for end in 0..=len {
                for start in (0..=end).rev() {
                    let raw = &frequencies[start..end];
                    let expected = search_tree_costs(raw, 1).into_iter().min().unwrap();
                    assert_eq!(direct[rank], expected, "{frequencies:?} at {start}..{end}");
                    assert_eq!(generated.cells()[rank], Some(Cost::Finite(expected)));
                    assert_eq!(reference[rank], [Cost::Finite(expected)]);
                    rank += 1;
                }
            }
            assert_eq!(rank, generated.cells().len());
            assert_eq!(rank, reference.len());
            assert_eq!(rank, direct.len());
            assert_eq!(generated.root(), chart.root());
            charts += 1;
            ranks += rank;
        }
    }
    println!("BST exhaustive depth costs: {charts} charts, {ranks} spans");
}

fn check_question<G, A, V>(source: &G, chart: &Chart<G::Op>, algebra: &A) -> Vec<Vec<V>>
where
    G: Program,
    A: Algebra<G::Op, Value = V> + Fold<G::Op, Value = V>,
    V: Debug + Clone + Eq,
{
    let expected = tabulate_cells(chart, algebra).unwrap();
    let generated = compiled::tabulate(source, algebra).unwrap();
    assert_eq!(generated.root(), chart.root());
    assert_eq!(generated, fast::tabulate(source, algebra).unwrap());
    for (actual, wanted) in generated.cells().iter().zip(&expected) {
        assert!(actual.iter().eq(wanted));
    }
    let mut observed = 0;
    let root = compiled::tabulate_root(source, algebra, |rank, actual| {
        assert_eq!(rank, observed);
        observed += 1;
        assert!(actual.into_iter().eq(&expected[rank]));
    })
    .unwrap();
    assert_eq!(observed, expected.len());
    assert_eq!(root.as_ref(), generated.answer());
    expected
}

fn check<O>(
    source: &impl Program<Op = O>,
    cells: Vec<Vec<NamedRule<O>>>,
    direct: Vec<i64>,
    paired: Table<Cost>,
) -> (usize, usize)
where
    O: Operator + Ord + Debug + ScoredOperator + ExpectationOperator,
{
    let root = cells.len() - 1;
    let mut observed = 0;
    compiled::replay(source, |rank, ordinal, site, op, children| {
        let (wanted_site, rule) = &cells[rank][ordinal];
        assert_eq!(
            (site, &op, children),
            (*wanted_site, &rule.operator, &rule.children[..])
        );
        observed += 1;
        Ok(())
    })
    .unwrap();
    assert_eq!(source.cell_count(), cells.len());
    assert_eq!(observed, cells.iter().map(Vec::len).sum::<usize>());
    let reference = Chart::new(
        cells
            .into_iter()
            .map(|row| row.into_iter().map(|(_, rule)| rule).collect())
            .collect(),
        root,
    )
    .unwrap();
    let chart = compiled::reference_chart(source).unwrap();
    assert_eq!(chart.root(), root);
    for (rank, row) in reference.cells().iter().enumerate() {
        let mut at = 0;
        source
            .rules_at(rank, |op, child| {
                assert_eq!((&op, child), (&row[at].operator, &row[at].children[..]));
                at += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(at, row.len());
    }
    assert_eq!(
        source.rules_at(reference.cells().len(), |_, _| unreachable!()),
        Err(Error::CellOutOfRange(reference.cells().len()))
    );
    assert_eq!(
        tabulate_cells(&chart, &Enumerate),
        tabulate_cells(&reference, &Enumerate)
    );
    let min = check_question(source, &reference, &Additive::default());
    assert_eq!(direct.len(), min.len());
    for (rank, score) in direct.into_iter().enumerate() {
        assert_eq!(min[rank], [Cost::Finite(score)]);
        assert_eq!(paired.cells()[rank], Some(Cost::Finite(score)));
    }
    check_question(source, &reference, &Count);
    check_question(source, &reference, &Expectation);
    let audit = audit_bounded(
        &chart,
        &Expectation,
        AuditBudget {
            max_tree_nodes: AUDIT_NODES,
        },
        AnswerOrder::Ordered,
    )
    .unwrap();
    assert!(audit.bellman.first_failure.is_none());
    assert!(audit.ambiguities.is_empty());
    (reference.cells().len(), observed)
}

#[test]
fn generated_routes_agree_on_complete_binary_domains() {
    let mut charts = 0;
    let mut prefix = (0, 0);
    let mut interval = (0, 0);
    for len in 0..=DOMAIN_LENGTH {
        for word in 0..1 << len {
            let bits: Vec<_> = (0..len).map(|index| word & (1 << index) != 0).collect();
            let input = segmentation::prepare(&bits);
            let bound = segmentation::grammar(&input).unwrap();
            let direct = segmentation::direct(&input).unwrap();
            for (end, &actual) in direct.iter().enumerate() {
                assert_eq!(
                    actual,
                    exhaustive_segment_score(&bits[..end]),
                    "prefix {:?}",
                    &bits[..end]
                );
            }
            let (cells, rules) = check(
                &bound,
                segment_rules(&bits),
                direct,
                segmentation::minimum(&input).unwrap(),
            );
            prefix.0 += cells;
            prefix.1 += rules;
            let frequencies: Vec<_> = bits.into_iter().map(|bit| 1 + u32::from(bit)).collect();
            let input = optimal_bst::prepare(&frequencies).unwrap();
            let bound = optimal_bst::grammar(&input).unwrap();
            let (cells, rules) = check(
                &bound,
                search_tree_rules(&frequencies),
                optimal_bst::direct(&input).unwrap(),
                optimal_bst::minimum(&input).unwrap(),
            );
            interval.0 += cells;
            interval.1 += rules;
            charts += 1;
        }
    }
    println!(
        "generated prefix: {charts} charts, {} cells, {} productions",
        prefix.0, prefix.1
    );
    println!(
        "generated interval: {charts} charts, {} cells, {} productions",
        interval.0, interval.1
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Toy(usize);
impl Operator for Toy {
    fn arity(&self) -> usize {
        self.0
    }
}

compiled_grammar! {
    fn sparse(input: char) -> Toy {
        prefix |input, start, end|;
        empty Base => Ok(Some(Toy(0)));
        empty Repeated => Ok(Some(Toy(0)));
        extend Allowed(split) => Ok((input[split] == 'a' && input[end - 1] == 'a').then_some(Toy(1)));
    }
    with fn sparse_count: Count = Count;
}

compiled_grammar! {
    fn invalid(input: char) -> Toy {
        interval |input, start, end|;
        pivot WrongArity(_k) => Ok(Some(Toy(1)));
    }
}

#[test]
fn generated_guards_repetitions_and_error_precedence() {
    let input = ['a', 'b', 'a'];
    let program = sparse(&input).unwrap();
    let reference = Chart::new(
        vec![
            vec![Rule::new(Toy(0), []), Rule::new(Toy(0), [])],
            vec![Rule::new(Toy(1), [0])],
            vec![],
            vec![Rule::new(Toy(1), [0]), Rule::new(Toy(1), [2])],
        ],
        input.len(),
    )
    .unwrap();
    let counts = check_question(&program, &reference, &Count);
    assert_eq!(counts, [vec![2], vec![2], vec![], vec![2]]);
    let reconstruct = compiled::reference_chart(&program).unwrap();
    assert_eq!(
        tabulate_cells(&reconstruct, &Enumerate),
        tabulate_cells(&reference, &Enumerate)
    );
    assert_eq!(
        sparse_count(&input).unwrap().cells(),
        [Some(2), Some(2), None, Some(2)]
    );

    let invalid = invalid(&input).unwrap();
    let bad = Error::Arity {
        cell: 2,
        expected: 1,
        actual: 2,
    };
    assert_eq!(compiled::reference_chart(&invalid).unwrap_err(), bad);
    assert_eq!(compiled::tabulate(&invalid, &Count), Err(bad));
}

#[allow(non_snake_case, non_upper_case_globals)]
mod caller_names {
    use super::*;

    const PREFIX: bool = false;
    type AtCell = Toy;
    type Rules = u8;
    type Generated = Count;
    type ClauseNames = Toy;

    fn GrammarRules(arity: usize) -> Toy {
        Toy(arity)
    }
    fn cell(token: u8) -> bool {
        token == 1
    }
    fn payload(arity: usize) -> Toy {
        Toy(arity)
    }
    fn operator(arity: usize) -> Toy {
        Toy(arity)
    }
    const algebra: Count = Count;

    compiled_grammar! {
        fn prefix_names(input: Rules) -> AtCell {
            prefix |input, start, end|;
            empty Caller => Ok(PREFIX.then_some(GrammarRules(0)));
            empty Base => {
                let value: ClauseNames = Toy(0);
                let _: Generated = algebra;
                Ok(Some(value))
            };
            extend Step(split) => Ok(cell(input[split]).then_some(payload(1)));
        }
        with fn prefix_count: Generated = algebra;
    }

    compiled_grammar! {
        fn interval_names(input: Rules) -> AtCell {
            interval |input, start, end|;
            empty Base => Ok(Some(operator(0)));
            empty Repeat => Ok((!PREFIX).then_some(operator(0)));
            pivot Pivot(cell) => Ok((input[cell] == 1 && start <= cell).then_some(payload(2)));
        }
        with fn interval_count: Generated = algebra;
    }

    #[test]
    fn generated_names_preserve_caller_scope() {
        // All words through the first length with more than one split per cell.
        const MAX_LENGTH: usize = 2;
        for length in 0..=MAX_LENGTH {
            for bits in 0..1 << length {
                let input: Vec<_> = (0..length).map(|i| (bits >> i) & 1).collect();
                let prefix = (0..=length)
                    .map(|end| {
                        if end == 0 {
                            vec![("Base", Rule::new(Toy(0), []))]
                        } else {
                            (0..end)
                                .filter(|&i| input[i] == 1)
                                .map(|i| ("Step", Rule::new(Toy(1), [i])))
                                .collect()
                        }
                    })
                    .collect();
                check_names(
                    &prefix_names(&input).unwrap(),
                    prefix,
                    prefix_count(&input).unwrap(),
                );

                let spans: Vec<_> = (0..=length)
                    .flat_map(|stop| (0..=stop).rev().map(move |start| (start, stop)))
                    .collect();
                let rank = |s, e| spans.iter().position(|&span| span == (s, e)).unwrap();
                let interval = spans
                    .iter()
                    .map(|&(s, e)| {
                        if s == e {
                            vec![
                                ("Base", Rule::new(Toy(0), [])),
                                ("Repeat", Rule::new(Toy(0), [])),
                            ]
                        } else {
                            (s..e)
                                .filter(|&i| input[i] == 1)
                                .map(|i| ("Pivot", Rule::new(Toy(2), [rank(s, i), rank(i + 1, e)])))
                                .collect()
                        }
                    })
                    .collect();
                check_names(
                    &interval_names(&input).unwrap(),
                    interval,
                    interval_count(&input).unwrap(),
                );
            }
        }
        println!("caller names: 14 charts, 48 ranks, 0 disagreements");
    }

    fn check_names(
        source: &impl Program<Op = Toy>,
        named: Vec<Vec<NamedRule<Toy>>>,
        paired: Table<u128>,
    ) {
        let mut seen = 0;
        compiled::replay(source, |rank, ordinal, label, op, children| {
            let (wanted, rule) = &named[rank][ordinal];
            assert_eq!(
                (label, op, children),
                (*wanted, rule.operator, &rule.children[..])
            );
            seen += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(seen, named.iter().map(Vec::len).sum::<usize>());
        let root = named.len() - 1;
        let chart = Chart::new(
            named
                .into_iter()
                .map(|row| row.into_iter().map(|(_, rule)| rule).collect())
                .collect(),
            root,
        )
        .unwrap();
        let expected = check_question(source, &chart, &Count);
        assert_eq!(paired.cells().len(), expected.len());
        for (actual, wanted) in paired.cells().iter().zip(&expected) {
            assert!(actual.iter().eq(wanted));
        }
    }
}
