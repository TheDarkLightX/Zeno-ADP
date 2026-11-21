#[path = "support/stream.rs"]
mod stream;

use std::fmt::Debug;
use zeno_adp::algebras::{
    Additive, Cost, Count, MinimumCount, MinimumWithMultiplicity, ScoredOperator,
};
use zeno_adp::compiled::{self, Atom::*, Grammar, Production};
use zeno_adp::fast::RuleSource;
use zeno_adp::{audit, tabulate_cells, Chart, Error, Operator, Rule};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Op(&'static str, Cost, usize);

impl Operator for Op {
    fn arity(&self) -> usize {
        self.2
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        self.1
    }
}

fn finite(label: &'static str, weight: i64, arity: usize) -> Op {
    Op(label, Cost::Finite(weight), arity)
}

fn words(max: usize) -> Vec<Vec<u8>> {
    (0..=max)
        .flat_map(|n| (0..1 << n).map(move |m| (0..n).map(|i| b"ab"[(m >> i) & 1]).collect()))
        .collect()
}

fn check<const N: usize>(
    source: &compiled::Sequence<'_, Op, N>,
    rules: Vec<Vec<Rule<Op>>>,
) -> (usize, usize, usize) {
    let rules_count = rules.iter().map(Vec::len).sum();
    let chart = Chart::new(rules, source.root()).unwrap();
    let cells = chart.cells().len();
    let trees = stream::compiled_questions(source, &chart);
    (cells, rules_count, trees)
}

/// Positional intervals ranked by their length, then start.
fn spans(n: usize) -> Vec<std::ops::Range<usize>> {
    (0..=n)
        .flat_map(|len| (0..=n - len).map(move |start| start..start + len))
        .collect()
}

#[test]
fn single_track_recursive_grammar_and_named_sites() {
    let grammar = Grammar::new(
        &["Run"],
        0,
        vec![
            Production {
                name: "empty".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| finite("empty", 1, 0)),
            },
            Production {
                name: "literal".into(),
                parent: 0,
                children: vec![0],
                tracks: [vec![Byte(b'a'), Child(0)]],
                operator: Box::new(|_| finite("a", -1, 1)),
            },
            Production {
                name: "copy".into(),
                parent: 0,
                children: vec![0],
                tracks: [vec![Any, Child(0)]],
                operator: Box::new(|m| {
                    finite("copy", i64::from(m.inputs[0][m.parent[0].start]), 1)
                }),
            },
        ],
    )
    .unwrap();
    assert_eq!(grammar.minimum_yields(0), Some([Some(0)]));
    // Includes a triple recursive step and all mixtures of the two terminals.
    const LENGTH: usize = 3;
    let (mut cells, mut rules, mut trees) = (0, 0, 0);
    for word in words(LENGTH) {
        let source = grammar.bind([&word]).unwrap();
        let intervals = spans(word.len());
        let reference = intervals
            .iter()
            .map(|span| {
                if span.is_empty() {
                    return vec![Rule::new(finite("empty", 1, 0), [])];
                }
                let suffix = (span.start + 1)..span.end;
                let child = intervals.iter().position(|span| *span == suffix).unwrap();
                let mut rules = Vec::new();
                if word[span.start] == b'a' {
                    rules.push(Rule::new(finite("a", -1, 1), [child]));
                }
                rules.push(Rule::new(
                    finite("copy", i64::from(word[span.start]), 1),
                    [child],
                ));
                rules
            })
            .collect();
        let (c, r, t) = check(&source, reference);
        cells += c;
        rules += r;
        trees += t;
        compiled::replay(&source, |_, _, name, op, _| {
            assert_eq!(
                name,
                match op.0 {
                    "a" => "literal",
                    other => other,
                }
            );
            Ok(())
        })
        .unwrap();
    }
    println!("One track: {} charts, {cells} cells, {rules} productions, {trees} returned tree comparisons", words(LENGTH).len());
}

#[test]
fn two_tracks_independent_spans_and_reordered_children() {
    let grammar = Grammar::new(
        &["Pair", "Atom", "Epsilon"],
        0,
        vec![
            Production {
                name: "reversed".into(),
                parent: 0,
                children: vec![1, 2],
                tracks: [vec![Child(0), Child(1)], vec![Child(1), Child(0)]],
                operator: Box::new(|m| {
                    assert_eq!(m.children.len(), 2);
                    let left_start = m.children[0][0].start as i64;
                    let right_start = m.children[1][1].start as i64;
                    finite("pair", left_start - right_start, 2)
                }),
            },
            Production {
                name: "left".into(),
                parent: 1,
                children: vec![],
                tracks: [vec![Byte(b'a')], vec![]],
                operator: Box::new(|_| finite("left", 0, 0)),
            },
            Production {
                name: "right".into(),
                parent: 1,
                children: vec![],
                tracks: [vec![], vec![Byte(b'b')]],
                operator: Box::new(|_| finite("right", 1, 0)),
            },
            Production {
                name: "eps".into(),
                parent: 2,
                children: vec![],
                tracks: [vec![], vec![]],
                operator: Box::new(|m| {
                    assert!(m.children.is_empty());
                    finite("eps", 0, 0)
                }),
            },
        ],
    )
    .unwrap();
    assert_eq!(grammar.minimum_yields(1), Some([Some(0), Some(0)]));
    // Exercises empty, one-boundary and interior-boundary splits on both sides.
    const LENGTH: usize = 2;
    const ORDER: [usize; 3] = [1, 0, 2];
    let (mut cells, mut rules, mut trees) = (0, 0, 0);
    for a in words(LENGTH) {
        for b in words(LENGTH) {
            let source = grammar.bind([&a, &b]).unwrap();
            let (left, right) = (spans(a.len()), spans(b.len()));
            let rank = |l, r, nt| {
                let x = left.iter().position(|s| *s == l).unwrap();
                let y = right.iter().position(|s| *s == r).unwrap();
                (x * right.len() + y) * ORDER.len() + ORDER.iter().position(|&id| id == nt).unwrap()
            };
            let mut reference = Vec::new();
            for l in &left {
                for r in &right {
                    for nt in ORDER {
                        assert_eq!(
                            source.cell(reference.len()),
                            Some((nt, [l.clone(), r.clone()]))
                        );
                        let mut out = Vec::new();
                        match nt {
                            0 if !l.is_empty() || !r.is_empty() => {
                                out.push(Rule::new(
                                    finite("pair", l.start as i64 - r.start as i64, 2),
                                    [
                                        rank(l.clone(), r.clone(), 1),
                                        rank(l.end..l.end, r.start..r.start, 2),
                                    ],
                                ));
                            }
                            1 if a[l.clone()] == *b"a" && r.is_empty() => {
                                out.push(Rule::new(finite("left", 0, 0), []))
                            }
                            1 if l.is_empty() && b[r.clone()] == *b"b" => {
                                out.push(Rule::new(finite("right", 1, 0), []))
                            }
                            2 if l.is_empty() && r.is_empty() => {
                                out.push(Rule::new(finite("eps", 0, 0), []))
                            }
                            _ => {}
                        }
                        reference.push(out);
                    }
                }
            }
            assert_eq!(source.root(), rank(0..a.len(), 0..b.len(), 0));
            let (c, r, t) = check(&source, reference);
            cells += c;
            rules += r;
            trees += t;
        }
    }
    println!("Two tracks: {} charts, {cells} cells, {rules} productions, {trees} returned tree comparisons", words(LENGTH).len().pow(2));
}

#[test]
fn named_refusals_and_mapped_absorption() {
    let recursive = || Production {
        name: "recursive".into(),
        parent: 0,
        children: vec![0],
        tracks: [vec![Child(0)]],
        operator: Box::new(|_| finite("self", 0, 1)),
    };
    let Err(Error::UnsupportedGrammar { name, .. }) = Grammar::new(&["Loop"], 0, vec![recursive()])
    else {
        panic!("expected a named cyclic grammar refusal");
    };
    assert_eq!(name, "Loop");
    let Err(Error::UnsupportedGrammar { name, .. }) = Grammar::new(
        &["Loop"],
        0,
        vec![Production {
            tracks: [vec![Child(0), Child(0)]],
            ..recursive()
        }],
    ) else {
        panic!("expected a named repeated-track-child refusal");
    };
    assert_eq!(name, "recursive");

    let grammar = Grammar::new(
        &["Leaf", "Goal"],
        1,
        vec![
            Production {
                name: "low".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| finite("leaf", 7, 0)),
            },
            Production {
                name: "high".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| finite("leaf", 31, 0)),
            },
            Production {
                name: "absorption".into(),
                parent: 1,
                children: vec![0],
                tracks: [vec![Child(0)]],
                operator: Box::new(|_| Op("absorb", Cost::Infinity, 1)),
            },
        ],
    )
    .unwrap();
    let source = grammar.bind([b""]).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    assert_eq!(
        audit(&chart, &MinimumCount).unwrap_err(),
        Error::InfinityDisabled
    );
    let repaired = MinimumWithMultiplicity::new(zeno_adp::algebras::CostPolicy::AttainableInfinity);
    assert!(audit(&chart, &repaired).unwrap().first_failure.is_none());
    let result = compiled::tabulate(&source, &repaired).unwrap();
    assert_eq!(result.answer().unwrap().optimal_derivations, 2);
    let reference = tabulate_cells(&chart, &repaired).unwrap();
    let mut observed = 0;
    let live = compiled::tabulate_root(&source, &repaired, |rank, answer| {
        assert_eq!(rank, observed);
        assert_eq!(answer, reference[rank].first());
        observed += 1;
    })
    .unwrap();
    assert_eq!(observed, reference.len());
    assert_eq!(live.as_ref(), reference[chart.root()].first());
    assert_eq!(
        compiled::tabulate(&source, &Additive::default()),
        Err(Error::InfinityDisabled)
    );
    assert_eq!(
        compiled::tabulate(&source, &Count).unwrap().answer(),
        Some(&2)
    );

    let malformed = Grammar::new(
        &["Mismatch"],
        0,
        vec![Production {
            name: "wrong-arity".into(),
            parent: 0,
            children: vec![],
            tracks: [vec![]],
            operator: Box::new(|_| finite("wrong", 0, 1)),
        }],
    )
    .unwrap();
    assert_eq!(
        compiled::tabulate(&malformed.bind([b""]).unwrap(), &Count),
        Err(Error::Arity {
            cell: 0,
            expected: 1,
            actual: 0
        })
    );
}

#[test]
fn a_malformed_later_cell_takes_precedence_over_an_earlier_algebra_error() {
    let grammar = Grammar::new(
        &["Start"],
        0,
        vec![
            Production {
                name: "infinite-empty".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| Op("infinite", Cost::Infinity, 0)),
            },
            Production {
                name: "bad-token".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![Any]],
                operator: Box::new(|_| finite("wrong", 0, 1)),
            },
        ],
    )
    .unwrap();
    let source = grammar.bind([b"a"]).unwrap();
    let reference = compiled::reference_chart(&source).unwrap_err();
    assert!(matches!(
        reference,
        Error::Arity {
            expected: 1,
            actual: 0,
            ..
        }
    ));
    assert_eq!(
        compiled::tabulate(&source, &Additive::default()),
        Err(reference.clone())
    );
    assert_eq!(
        compiled::tabulate_root(&source, &Additive::default(), |_, _| {
            panic!("the complete schedule must validate before observation");
        }),
        Err(reference)
    );
}

#[test]
fn root_selection_preserves_an_unreachable_cells_arithmetic_error() {
    let grammar = Grammar::new(
        &["Root", "Later"],
        0,
        vec![
            Production {
                name: "root".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| finite("root", 0, 0)),
            },
            Production {
                name: "unreachable-infinity".into(),
                parent: 1,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| Op("unreachable", Cost::Infinity, 0)),
            },
        ],
    )
    .unwrap();
    let source = grammar.bind([b""]).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    let score = Additive::default();
    assert_eq!(source.root(), 0);
    let expected = tabulate_cells(&chart, &score).unwrap_err();
    let mut observed = Vec::new();
    assert_eq!(
        compiled::tabulate_root(&source, &score, |cell, answer| {
            observed.push((cell, answer.copied()));
        }),
        Err(expected)
    );
    assert_eq!(observed, vec![(0, Some(Cost::Finite(0)))]);

    let score = Additive::new(zeno_adp::algebras::CostPolicy::AttainableInfinity);
    assert_eq!(
        compiled::tabulate_root(&source, &score, |_, _| {}).unwrap(),
        Some(Cost::Finite(0))
    );
}

#[test]
fn impossible_dense_table_layouts_return_allocation_errors() {
    use zeno_adp::distinct::{BinaryTreeGrammar, Production::Leaf};
    use zeno_adp::{fast, grammars};

    // A logical length can fit in usize while the table's layout cannot.
    let binary = BinaryTreeGrammar::new(vec![vec![Leaf(b'a')]]).unwrap();
    let huge = usize::MAX / 2;
    assert_eq!(binary.chart(huge, 0).unwrap_err(), Error::AllocationFailed);
    assert_eq!(
        binary.distinct_counts(huge).unwrap_err(),
        Error::AllocationFailed
    );

    let capacity = usize::MAX - 1; // The width is capacity plus one.
    let source = grammars::knapsack_source(&[], capacity).unwrap();
    assert_eq!(
        compiled::reference_chart(&source).unwrap_err(),
        Error::AllocationFailed
    );
    assert_eq!(
        compiled::tabulate(&source, &Count),
        Err(Error::AllocationFailed)
    );
    assert_eq!(
        compiled::tabulate_root(&source, &Count, |_, _| panic!("no table reserved")),
        Err(Error::AllocationFailed)
    );
    assert_eq!(
        fast::reference_chart(&source).unwrap_err(),
        Error::AllocationFailed
    );
    assert_eq!(
        fast::tabulate(&source, &Count),
        Err(Error::AllocationFailed)
    );
    assert_eq!(fast::knapsack(&[], capacity), Err(Error::AllocationFailed));
    assert_eq!(
        grammars::knapsack(&[], capacity).unwrap_err(),
        Error::AllocationFailed
    );
}

#[test]
fn public_rule_sources_reject_invalid_ranks_before_emission() {
    use zeno_adp::grammars;

    fn check(source: &impl RuleSource) {
        for rank in [source.cell_count(), usize::MAX] {
            let mut visits = 0;
            let result = source.rules_at(rank, |_, _| {
                visits += 1;
                Ok(())
            });
            assert_eq!((result, visits), (Err(Error::CellOutOfRange(rank)), 0));
        }
    }

    check(&grammars::nussinov_source(b"A", 0).unwrap());
    check(&grammars::alignment_source(b"A", b"C").unwrap());
    check(&grammars::local_alignment_source(b"A", b"C").unwrap());
    check(&grammars::matrix_chain_source(&[2, 3, 4]).unwrap());
    check(&grammars::knapsack_source(&[], 0).unwrap());
    check(&grammars::nussinov(b"A", 0).unwrap());
    let grammar = Grammar::new(
        &["Atom"],
        0,
        vec![Production {
            name: "byte".into(),
            parent: 0,
            children: vec![],
            tracks: [vec![Any]],
            operator: Box::new(|_| finite("leaf", 0, 0)),
        }],
    )
    .unwrap();
    check(&grammar.bind([b"A"]).unwrap());
}

#[test]
fn an_unrepresentable_yield_bound_refuses_the_whole_declaration() {
    // Start also accepts a single byte. The other production generates twice
    // the preceding yield at each level, ending at 2^usize::BITS.
    let last = usize::BITS as usize;
    let names: Vec<_> = (0..=last).map(|i| format!("N{i}")).collect();
    let names: Vec<_> = names.iter().map(String::as_str).collect();
    let leaf = |parent| Production {
        name: format!("leaf{parent}"),
        parent,
        children: vec![],
        tracks: [vec![Any]],
        operator: Box::new(|_| finite("leaf", 0, 0)),
    };
    let mut rules: Vec<Production<_, 1>> = vec![leaf(0)];
    for parent in 1..=last {
        rules.push(Production {
            name: format!("double{parent}"),
            parent,
            children: vec![parent - 1, parent - 1],
            tracks: [vec![Child(0), Child(1)]],
            operator: Box::new(|_| finite("double", 0, 2)),
        });
    }
    rules.push(leaf(last));
    assert!(matches!(
        Grammar::new(&names, last, rules),
        Err(Error::Overflow)
    ));
}

fn check_yield_interleavings<const TRACKS: usize>(inputs: &[[&[u8]; TRACKS]]) -> (usize, usize) {
    // Doubling from one byte to this level gives the largest power of two
    // that fits. Two occurrences in the root then exceed usize provisionally.
    let tail = usize::BITS as usize - 1;
    let root = tail + 1;
    let absent = root + 1;
    let names: Vec<_> = (0..=absent).map(|i| format!("N{i}")).collect();
    let names: Vec<_> = names.iter().map(String::as_str).collect();
    let leaf = |parent, label: &'static str| Production {
        name: label.into(),
        parent,
        children: vec![],
        tracks: std::array::from_fn(|_| vec![Byte(b'a')]),
        operator: Box::new(move |_| finite(label, 1, 0)),
    };

    let mut charts = 0;
    let mut cells = 0;
    for dead in [false, true] {
        for delayed in [false, true] {
            let mut rules = vec![leaf(0, "base")];
            for parent in 1..=tail {
                rules.push(Production {
                    name: format!("double{parent}"),
                    parent,
                    children: vec![parent - 1, parent - 1],
                    tracks: std::array::from_fn(|_| vec![Child(0), Child(1)]),
                    operator: Box::new(|_| finite("double", 0, 2)),
                });
            }
            if !delayed {
                rules.push(leaf(tail, "short"));
            }
            rules.extend([leaf(root, "first"), leaf(root, "second")]);
            let mut children = vec![tail, tail];
            if dead {
                children.push(absent);
            }
            let arity = children.len();
            rules.push(Production {
                name: "join".into(),
                parent: root,
                children,
                tracks: std::array::from_fn(|_| (0..arity).map(Child).collect()),
                operator: Box::new(move |_| finite("join", 0, arity)),
            });
            if delayed {
                rules.push(leaf(tail, "short"));
            }

            let grammar = Grammar::new(&names, root, rules).unwrap();
            assert_eq!(grammar.minimum_yields(absent), Some([None; TRACKS]));
            for nonterminal in 0..absent {
                let expected = if nonterminal >= tail {
                    1
                } else {
                    1 << nonterminal
                };
                assert_eq!(
                    grammar.minimum_yields(nonterminal),
                    Some([Some(expected); TRACKS])
                );
            }

            for &input in inputs {
                let source = grammar.bind(input).unwrap();
                let intervals = input.map(|word| spans(word.len()));
                let rank_of = |nonterminal, regions: [std::ops::Range<usize>; TRACKS]| {
                    let mut rank = 0;
                    for (track, region) in regions.iter().enumerate() {
                        let axis = &intervals[track];
                        rank = rank * axis.len() + axis.iter().position(|s| s == region).unwrap();
                    }
                    rank * names.len() + nonterminal
                };
                let expected_root = rank_of(root, input.map(|word| 0..word.len()));
                assert_eq!(source.root(), expected_root);
                let mut expected_cells = Vec::new();
                for rank in 0..source.cell_count() {
                    let (nonterminal, regions) = source.cell(rank).unwrap();
                    assert_eq!(rank_of(nonterminal, regions.clone()), rank);
                    let mut row = Vec::new();
                    if regions
                        .iter()
                        .enumerate()
                        .all(|(track, span)| input[track][span.clone()] == *b"a")
                    {
                        let labels: &[&str] = match nonterminal {
                            0 => &["base"],
                            n if n == tail => &["short"],
                            n if n == root => &["first", "second"],
                            _ => &[],
                        };
                        row.extend(
                            labels
                                .iter()
                                .map(|label| Rule::new(finite(label, 1, 0), [])),
                        );
                    }
                    // The two unit spans are legal splits even when a
                    // child's own terminal rule fails to match its byte.
                    if regions.iter().all(|span| span.len() == 2) {
                        let branch = match nonterminal {
                            1 => Some(("double", 0)),
                            n if n == root && !dead => Some(("join", tail)),
                            _ => None,
                        };
                        if let Some((label, child)) = branch {
                            let left = regions.each_ref().map(|span| span.start..span.start + 1);
                            let right = regions.each_ref().map(|span| span.start + 1..span.end);
                            row.push(Rule::new(
                                finite(label, 0, 2),
                                [rank_of(child, left), rank_of(child, right)],
                            ));
                        }
                    }
                    expected_cells.push(row);
                }

                let expected = Chart::new(expected_cells, expected_root).unwrap();
                let emitted = compiled::reference_chart(&source).unwrap();
                assert_eq!(emitted.cells().len(), expected.cells().len());
                for (actual, reference) in emitted.cells().iter().zip(expected.cells()) {
                    assert_eq!(actual.len(), reference.len());
                    for (actual, reference) in actual.iter().zip(reference) {
                        assert_eq!(actual.operator, reference.operator);
                        assert_eq!(actual.children, reference.children);
                    }
                }
                for (actual, reference) in compiled::tabulate(&source, &Count)
                    .unwrap()
                    .cells()
                    .iter()
                    .zip(tabulate_cells(&expected, &Count).unwrap())
                {
                    assert_eq!(actual.as_ref(), reference.first());
                }
                let enumeration = zeno_adp::algebras::Enumerate;
                assert_eq!(
                    tabulate_cells(&emitted, &enumeration).unwrap(),
                    tabulate_cells(&expected, &enumeration).unwrap()
                );
                let minimum = Additive::default();
                let expected_scores = tabulate_cells(&expected, &minimum).unwrap();
                let mut visited = 0;
                let actual_root = compiled::tabulate_root(&source, &minimum, |rank, answer| {
                    assert_eq!(rank, visited);
                    assert_eq!(answer, expected_scores[rank].first());
                    visited += 1;
                })
                .unwrap();
                assert_eq!(actual_root.as_ref(), expected_scores[expected_root].first());
                assert_eq!(visited, expected.cells().len());
                charts += 1;
                cells += visited;
            }
        }
    }
    (charts, cells)
}

#[test]
fn interleaving_unrelated_clauses_preserves_acceptance_and_ranked_answers() {
    // Include the empty input, the short yield and the live root join.
    const LENGTH: usize = 2;
    let words = words(LENGTH);
    let single: Vec<_> = words.iter().map(|word| [word.as_slice()]).collect();
    let double: Vec<_> = words
        .iter()
        .flat_map(|left| {
            words
                .iter()
                .map(move |right| [left.as_slice(), right.as_slice()])
        })
        .collect();
    let (single_charts, single_cells) = check_yield_interleavings(&single);
    let (double_charts, double_cells) = check_yield_interleavings(&double);
    println!("Yield interleavings: {single_charts} one-track charts, {single_cells} cells; {double_charts} two-track charts, {double_cells} cells; 0 differences");
}
