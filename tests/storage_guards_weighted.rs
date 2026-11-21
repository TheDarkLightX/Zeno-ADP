use zeno_adp::algebras::{Additive, Cost, Count, ScoredOperator};
use zeno_adp::compiled::{
    self, generated::tracks, Atom, Grammar, Production, ProductionSink, Program,
};
use zeno_adp::fast::RuleSource;
use zeno_adp::probability::{self, Rational, SumProduct, WeightedOperator};
use zeno_adp::{compiled_grammar, tabulate_cells, Cell, Chart, Error, Operator, Rule};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Op(u8, usize, Rational);

impl Operator for Op {
    fn arity(&self) -> usize {
        self.1
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        Cost::Finite(i64::from(self.0))
    }
}

impl WeightedOperator for Op {
    fn weight(&self) -> Rational {
        self.2
    }
}

fn op(tag: u8, arity: usize) -> Op {
    Op(tag, arity, Rational::ONE)
}

macro_rules! edit {
    ($name:ident, $band:expr) => {
        compiled_grammar! {
            fn $name(input: u8) -> Op {
                prefix_tracks 2 |tracks, ends|;
                empty Start => Ok(Some(op(0, 0)));
                step Left [true, false] =>
                    Ok((ends[0].abs_diff(ends[1]) <= $band).then(|| op(1, 1)));
                step Right [false, true] =>
                    Ok((ends[0].abs_diff(ends[1]) <= $band).then(|| op(1, 1)));
                step Diagonal [true, true] =>
                    Ok((ends[0].abs_diff(ends[1]) <= $band)
                        .then(|| op(u8::from(tracks[0][ends[0] - 1] != tracks[1][ends[1] - 1]), 1)));
            }
        }
    };
}

const NARROW_BAND: usize = 2; // Admit an offset of two while leaving holes in large grids.
edit!(diagonal, 0);
edit!(single_offset, 1);
edit!(narrow_edit, NARROW_BAND);
edit!(full_edit, usize::MAX);

fn words(max: usize) -> Vec<Vec<u8>> {
    (0..=max)
        .flat_map(|len| {
            (0..1usize << len)
                .map(move |bits| (0..len).map(|at| ((bits >> at) & 1) as u8).collect())
        })
        .collect()
}

#[test]
fn packed_edit_matches_every_chart_cell() {
    fn compare(grammar: &impl Program<Op = Op>) -> usize {
        let chart = compiled::reference_chart(grammar).unwrap();
        let counts = tabulate_cells(&chart, &Count).unwrap();
        let costs = tabulate_cells(&chart, &Additive::default()).unwrap();
        let packed_count = compiled::tabulate_compact(grammar, &Count).unwrap();
        let packed_cost = compiled::tabulate_compact(grammar, &Additive::default()).unwrap();
        let budget = |dense: usize, value: usize| {
            (counts.len() * dense).min(
                packed_count.stored_cells() * value
                    + packed_count.run_count() * std::mem::size_of::<[usize; 2]>(),
            )
        };
        let budgeted_count = compiled::tabulate_with_budget(
            grammar,
            &Count,
            budget(
                std::mem::size_of::<Option<u128>>(),
                std::mem::size_of::<u128>(),
            ),
        )
        .unwrap();
        let budgeted_cost = compiled::tabulate_with_budget(
            grammar,
            &Additive::default(),
            budget(
                std::mem::size_of::<Option<Cost>>(),
                std::mem::size_of::<Cost>(),
            ),
        )
        .unwrap();
        for (rank, (count, cost)) in counts.iter().zip(&costs).enumerate() {
            assert_eq!(packed_count.get(rank), count.first());
            assert_eq!(packed_cost.get(rank), cost.first());
            assert_eq!(budgeted_count.get(rank), count.first());
            assert_eq!(budgeted_cost.get(rank), cost.first());
        }
        assert_eq!(packed_count.cell_count(), counts.len());
        assert_eq!(packed_count.root(), chart.root());
        assert_eq!(packed_count.answer(), counts[chart.root()].first());
        assert_eq!(packed_count.get(usize::MAX), None);
        assert_eq!(
            packed_count.stored_cells(),
            counts.iter().filter(|values| !values.is_empty()).count()
        );
        assert_eq!(
            packed_count.run_count(),
            counts
                .iter()
                .enumerate()
                .filter(|&(i, values)| !values.is_empty() && (i == 0 || counts[i - 1].is_empty()))
                .count()
        );
        counts.len()
    }

    const MAX_WORD: usize = 3; // Include a root outside even the two-offset band.
    let mut cells = 0;
    for left in &words(MAX_WORD) {
        for right in &words(MAX_WORD) {
            let input = [left.as_slice(), right.as_slice()];
            cells += compare(&diagonal(input).unwrap());
            cells += compare(&single_offset(input).unwrap());
            cells += compare(&narrow_edit(input).unwrap());
            cells += compare(&full_edit(input).unwrap());
        }
    }
    println!(
        "packed charts=900 logical_cells={cells} comparisons_per_entry_point={}",
        2 * cells
    );
}

const WORD: usize = 0;
const SENTENCE: usize = 1;
const MAX_CAP: usize = 3; // Covers empty, singleton and multi-token restrictions.

fn atom_weight(token: u8, unit: bool) -> Rational {
    if unit {
        Rational::ONE
    } else {
        Rational::new(u128::from(token), 2).unwrap()
    }
}

fn parser(cap: usize, unit: bool) -> Grammar<Op, 1> {
    use Atom::{Any, Byte, Child};
    let make = |name: &str, parent, children: Vec<usize>, atoms, tag| {
        let arity = children.len();
        Production {
            name: name.into(),
            parent,
            tracks: [atoms],
            operator: Box::new(move |_| op(tag, arity)),
            children,
        }
    };
    let mut atom = make("atom", WORD, vec![], vec![Any], 0);
    atom.operator = Box::new(move |m| Op(0, 0, atom_weight(m.inputs[0][m.parent[0].start], unit)));
    let mut productions = vec![
        atom,
        make("grow", WORD, vec![WORD], vec![Child(0), Any], 1),
        make("single", SENTENCE, vec![WORD], vec![Child(0)], 2),
        make(
            "split",
            SENTENCE,
            vec![WORD, SENTENCE],
            vec![Child(0), Child(1)],
            3,
        ),
        make("empty", SENTENCE, vec![], vec![Byte(2)], 4),
    ];
    if !unit {
        productions.insert(
            4,
            make(
                "again",
                SENTENCE,
                vec![WORD, SENTENCE],
                vec![Child(0), Child(1)],
                3,
            ),
        );
    }
    Grammar::new(&["word", "sentence"], SENTENCE, productions)
        .unwrap()
        .with_span_limits(WORD, [Some(cap)])
        .unwrap()
        .with_split_guard(move |split| {
            if (split.rule == "split" || split.rule == "again") && split.child == 0 {
                // The permitted first word is longer when its first token is one.
                let maximum = 1 + usize::from(split.inputs[0][split.start]) * cap;
                Some(split.start..=split.start + maximum)
            } else {
                Some(0..=usize::MAX)
            }
        })
}

fn raw_rows(
    input: &[u8],
    cap: usize,
    coordinates: &[(usize, std::ops::Range<usize>)],
) -> Vec<Vec<Rule<Op>>> {
    let rank = |nt, start, end| {
        coordinates
            .iter()
            .position(|(kind, span)| (*kind, span.start, span.end) == (nt, start, end))
            .unwrap()
    };
    coordinates
        .iter()
        .map(|(nt, span)| {
            let (start, end) = (span.start, span.end);
            let len = span.len();
            if *nt == WORD {
                return match len {
                    0 => vec![],
                    len if len > cap => vec![],
                    1 => vec![Rule::new(Op(0, 0, atom_weight(input[start], false)), [])],
                    _ => vec![Rule::new(op(1, 1), [rank(WORD, start, end - 1)])],
                };
            }
            let mut row = vec![];
            if (1..=cap).contains(&len) {
                row.push(Rule::new(op(2, 1), [rank(WORD, start, end)]));
            }
            for _ in ["split", "again"] {
                for middle in start + 1..end {
                    let first_len = middle - start;
                    if first_len <= cap && (input[start] == 1 || first_len == 1) {
                        row.push(Rule::new(
                            op(3, 2),
                            [rank(WORD, start, middle), rank(SENTENCE, middle, end)],
                        ));
                    }
                }
            }
            if len == 1 && input[start] == 2 {
                row.push(Rule::new(op(4, 0), []));
            }
            row
        })
        .collect()
}

// Enumerate complete weighted root derivations with their occurrence bags.
// Equal operator payloads and repeated child ranks keep separate visits.
type Derivation = (Rational, Vec<(Cell, usize)>);

fn derive(chart: &Chart<Op>, cell: Cell) -> Vec<Derivation> {
    let mut result = Vec::new();
    for (ordinal, rule) in chart.cells()[cell].iter().enumerate() {
        let mut combinations = vec![(rule.operator.weight(), vec![(cell, ordinal)])];
        for &child in &rule.children {
            let choices = derive(chart, child);
            combinations = combinations
                .iter()
                .flat_map(|(weight, visits)| {
                    choices.iter().map(move |(other, tail)| {
                        (
                            weight.checked_mul(*other).unwrap(),
                            visits.iter().chain(tail).copied().collect(),
                        )
                    })
                })
                .collect();
        }
        result.extend(combinations);
    }
    result
}

fn compare_outside(
    grammar: &impl Program<Op = Op>,
    chart: &Chart<Op>,
    optimized: &compiled::CompiledInsideOutside<'_, impl Program<Op = Op>, Rational>,
) -> usize {
    assert_eq!(
        optimized.weights(),
        &probability::inside_outside(chart).unwrap()
    );
    let log = compiled::log_inside_outside(grammar).unwrap();
    let reference_log = probability::log_inside_outside(chart).unwrap();
    for (actual, expected) in log
        .weights()
        .inside()
        .iter()
        .chain(log.weights().outside())
        .zip(reference_log.inside().iter().chain(reference_log.outside()))
    {
        assert_eq!(actual.ln().to_bits(), expected.ln().to_bits());
    }
    let mut totals: Vec<Vec<_>> = chart
        .cells()
        .iter()
        .map(|row| vec![Rational::ZERO; row.len()])
        .collect();
    let mut partition = Rational::ZERO;
    for (mass, visits) in derive(chart, chart.root()) {
        partition = partition.checked_add(mass).unwrap();
        for (rank, ordinal) in visits {
            totals[rank][ordinal] = totals[rank][ordinal].checked_add(mass).unwrap();
        }
    }
    assert_eq!(*optimized.weights().partition(), partition);
    let mut events = Rational::ZERO;
    let mut occurrences = 0;
    for (rank, row) in totals.iter().enumerate() {
        for (ordinal, &expected) in row.iter().enumerate() {
            assert_eq!(optimized.rule_mass(rank, ordinal).unwrap(), Some(expected));
            if chart.cells()[rank][ordinal].operator.0 == 3 {
                events = events.checked_add(expected).unwrap();
            }
            occurrences += 1;
        }
        assert_eq!(optimized.rule_mass(rank, row.len()).unwrap(), None);
    }
    let matches = |_: Cell, _: usize, _: &str, operator: &Op, _: &[Cell]| operator.0 == 3;
    assert_eq!(optimized.event_mass(matches).unwrap(), events);
    assert_eq!(
        optimized.expected_visits(matches).unwrap(),
        events.checked_div(partition).unwrap()
    );
    assert_eq!(
        optimized.rule_mass(chart.cells().len(), 0),
        Err(Error::CellOutOfRange(chart.cells().len()))
    );
    occurrences
}

#[test]
fn bounded_weighted_spans_match_raw_rows_and_weighted_derivations() {
    const MAX_WORD: usize = 5; // Small enough for full derivation expansion with duplicate splits.
    let mut cells = 0;
    let mut rules = 0;
    for cap in 0..=MAX_CAP {
        let declaration = parser(cap, false);
        for input in words(MAX_WORD) {
            let grammar = declaration.bind([&input]).unwrap();
            let slow = compiled::reference_chart(&grammar).unwrap();
            let ranks: Vec<_> = (0..grammar.cell_count())
                .map(|cell| {
                    let (nt, [span]) = grammar.cell(cell).unwrap();
                    (nt, span)
                })
                .collect();
            let raw = raw_rows(&input, cap, &ranks);
            for (post_filtered, oracle) in slow.cells().iter().zip(&raw) {
                assert!(post_filtered
                    .iter()
                    .map(|rule| (rule.operator, &rule.children))
                    .eq(oracle.iter().map(|rule| (rule.operator, &rule.children))));
            }
            let mut seen = vec![0; ranks.len()];
            compiled::replay(&grammar, |cell, ordinal, site, operator, children| {
                assert_eq!(ordinal, seen[cell]);
                assert!(
                    ordinal < raw[cell].len(),
                    "unexpected production {ordinal} at rank {cell}"
                );
                assert_eq!(
                    (operator, children),
                    (
                        raw[cell][ordinal].operator,
                        raw[cell][ordinal].children.as_slice()
                    )
                );
                if operator.0 == 3 {
                    assert!(matches!(site, "split" | "again"));
                }
                seen[cell] += 1;
                Ok(())
            })
            .unwrap();
            assert_eq!(seen, raw.iter().map(Vec::len).collect::<Vec<_>>());
            let count = compiled::tabulate(&grammar, &Count).unwrap();
            let expected = tabulate_cells(&slow, &Count).unwrap();
            let exact = compiled::inside_outside(&grammar).unwrap();
            let products = tabulate_cells(&slow, &SumProduct).unwrap();
            for (rank, (bag, mass)) in expected.iter().zip(&products).enumerate() {
                assert_eq!(count.cells()[rank].as_ref(), bag.first());
                assert_eq!(
                    exact.weights().inside()[rank],
                    mass.first().copied().unwrap_or(Rational::ZERO)
                );
            }
            rules += compare_outside(&grammar, &slow, &exact);
            let named = exact
                .event_mass(|_, _, site, _, _| site == "again")
                .unwrap();
            let both = exact
                .event_mass(|_, _, site, _, _| matches!(site, "split" | "again"))
                .unwrap();
            assert_eq!(named.checked_add(named).unwrap(), both);
            cells += ranks.len();
        }
    }
    println!("spans charts=252 cells={cells} rule_occurrences={rules}");
}

struct Repeated;

impl tracks::TrackRules<(), Op, 1> for Repeated {
    fn prepare(&mut self, _: &[usize; 1], _: &[usize; 1]) -> Result<(), Error> {
        Ok(())
    }

    fn emit(
        &self,
        _: [&[()]; 1],
        cell: Cell,
        _: [usize; 1],
        sink: &mut impl ProductionSink<Op>,
    ) -> Result<(), Error> {
        if cell == 0 {
            sink.rule("leaf", op(3, 0), [])?;
        } else {
            sink.rule("fork", op(4, 2), [0, 0])?;
            sink.rule("zero", Op(4, 0, Rational::ZERO), [])?;
        }
        Ok(())
    }
}

#[test]
fn repeated_occurrences_are_expected_visits() {
    let source = tracks::bind("repeated", [&[()][..]], Repeated).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    let query = compiled::inside_outside(&source).unwrap();
    assert_eq!(compare_outside(&source, &chart, &query), 3);
    assert_eq!(query.rule_mass(0, 0).unwrap(), Rational::new(2, 1));
    assert_eq!(query.rule_mass(1, 1).unwrap(), Some(Rational::ZERO));
    assert_eq!(
        query
            .expected_visits(|_, _, name, _, _| name == "leaf")
            .unwrap(),
        Rational::new(2, 1)
    );
}

#[test]
fn multi_track_guard_preserves_declared_child_order_and_empty_spans() {
    use Atom::{Any, Child};
    let rule = |name: &str, parent, tracks, children: Vec<usize>| {
        let arity = children.len();
        Production {
            name: name.into(),
            parent,
            children,
            tracks,
            operator: Box::new(move |_| op(0, arity)),
        }
    };
    type Guard = fn(compiled::SplitContext<'_, 2, u8>) -> Option<std::ops::RangeInclusive<usize>>;
    let build = |guard: Guard| {
        Grammar::new(
            &["left", "right", "join"],
            2,
            vec![
                rule("left", 0, [vec![Any], vec![]], vec![]),
                rule("right", 1, [vec![], vec![Any]], vec![]),
                rule(
                    "join",
                    2,
                    [vec![Child(0), Child(1)], vec![Child(1), Child(0)]],
                    vec![0, 1],
                ),
            ],
        )
        .unwrap()
        .with_span_limits(0, [Some(usize::MAX), Some(0)])
        .unwrap()
        .with_span_limits(1, [Some(0), Some(1)])
        .unwrap()
        .with_split_guard(guard)
    };
    let normal = build(|m: compiled::SplitContext<'_, 2, u8>| {
        let extent = if m.track == m.child { 1 } else { 0 };
        let end = m.start + extent;
        Some(end..=end)
    });
    let empty = build(|_| Some(std::ops::RangeInclusive::new(usize::MAX, 0)));
    let rejected = build(|_| None);
    let exhausted = build(|m| {
        let end = m.start + usize::from(m.track == m.child);
        let mut inclusive = end..=end;
        inclusive.next().unwrap();
        Some(inclusive)
    });
    for declaration in [&normal, &empty, &rejected, &exhausted] {
        let source = declaration.bind([&[0], &[1]]).unwrap();
        let chart = compiled::reference_chart(&source).unwrap();
        let count = compiled::tabulate(&source, &Count).unwrap();
        let actual = tabulate_cells(&chart, &Count).unwrap();
        for (rank, expected) in actual.iter().enumerate() {
            assert_eq!(count.cells()[rank].as_ref(), expected.first());
        }
        if std::ptr::eq(declaration, &normal) {
            let row = &chart.cells()[chart.root()];
            assert_eq!(row.len(), 1);
            assert_eq!(source.cell(row[0].children[0]), Some((0, [0..1, 1..1])));
            assert_eq!(source.cell(row[0].children[1]), Some((1, [1..1, 0..1])));
        } else {
            assert!(chart.cells()[chart.root()].is_empty());
        }
    }
}

#[test]
fn outside_keeps_nonfinal_roots_and_reports_checked_overflow() {
    let input = [0];
    let declaration = Grammar::new(
        &["root", "later"],
        0,
        vec![
            Production {
                name: "zero".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![Atom::Any]],
                operator: Box::new(|_| Op(3, 0, Rational::ZERO)),
            },
            Production {
                name: "one".into(),
                parent: 1,
                children: vec![],
                tracks: [vec![Atom::Any]],
                operator: Box::new(|_| op(3, 0)),
            },
        ],
    )
    .unwrap();
    let source = declaration.bind([&input]).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    let query = compiled::inside_outside(&source).unwrap();
    assert!(chart.root() + 1 < chart.cells().len());
    assert_eq!(compare_outside(&source, &chart, &query), 2);
    assert_eq!(query.weights().outside()[chart.root() + 1], Rational::ZERO);
    assert_eq!(query.expected_visits(|_, _, _, _, _| true).unwrap(), None);

    compiled_grammar! {
        fn overflow(data: u8) -> Op {
            prefix |tokens, start, end|;
            empty Leaf => Ok(Some(Op(0, 0, Rational::new(u128::MAX, 1).unwrap())));
            extend Twice(split) => Ok(Some(Op(0, 1, Rational::new(2, 1).unwrap())));
        }
    }
    let overflow = overflow(&input).unwrap();
    let chart = compiled::reference_chart(&overflow).unwrap();
    assert_eq!(
        probability::inside_outside(&chart).err(),
        Some(Error::Overflow)
    );
    assert_eq!(
        compiled::inside_outside(&overflow).err(),
        Some(Error::Overflow)
    );

    compiled_grammar! {
        fn zero_inside(data: u8) -> Op {
            prefix |tokens, start, end|;
            empty Leaf => Ok(Some(Op(0, 0, Rational::ZERO)));
            extend Heavy(split) => Ok(Some(Op(
                0, 1, Rational::new(if end == 1 { u128::MAX } else { 2 }, 1).unwrap()
            )));
        }
    }
    let source = zero_inside(&[0, 0]).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    assert_eq!(probability::partition(&chart).unwrap(), Rational::ZERO);
    assert_eq!(
        probability::inside_outside(&chart).err(),
        Some(Error::Overflow)
    );
    assert_eq!(
        compiled::inside_outside(&source).err(),
        Some(Error::Overflow)
    );
}

const FLANK: usize = 0;
const CORE: usize = 1;
const INFIX: usize = 2;

fn exact_infix(query: &[u8]) -> Grammar<Op, 1> {
    use Atom::{Any, Byte, Child};
    let rule = |name: &str, parent, children: Vec<usize>, track| {
        let arity = children.len();
        Production {
            name: name.into(),
            parent,
            children,
            tracks: [track],
            operator: Box::new(move |_| op(0, arity)),
        }
    };
    let width = query.len();
    let declaration = Grammar::new(
        &["flank", "core", "infix"],
        INFIX,
        vec![
            rule("empty_flank", FLANK, vec![], vec![]),
            rule("extend_flank", FLANK, vec![FLANK], vec![Child(0), Any]),
            rule(
                "core",
                CORE,
                vec![],
                query.iter().copied().map(Byte).collect(),
            ),
            rule(
                "infix",
                INFIX,
                vec![FLANK, CORE, FLANK],
                vec![Child(0), Child(1), Child(2)],
            ),
        ],
    )
    .unwrap()
    .with_span_limits(CORE, [Some(width)])
    .unwrap();
    let query = query.to_vec();
    declaration.with_split_guard(move |m| {
        if m.rule == "infix" && m.child == 1 {
            let end = m.start.checked_add(width)?;
            (m.inputs[0].get(m.start..end)? == query).then_some(end..=end)
        } else {
            Some(0..=usize::MAX)
        }
    })
}

#[test]
fn guarded_infix_matches_direct_substring_counts() {
    const TARGET_MAX: usize = 5; // Includes overlapping matches with an interior flank.
    const QUERY_MAX: usize = 2; // Include both singleton queries and pairs with unequal tokens.
    let mut cells = 0;
    for query in words(QUERY_MAX)
        .into_iter()
        .filter(|query| !query.is_empty())
    {
        let declaration = exact_infix(&query);
        for input in words(TARGET_MAX) {
            let source = declaration.bind([&input]).unwrap();
            let chart = compiled::reference_chart(&source).unwrap();
            let reference = tabulate_cells(&chart, &Count).unwrap();
            let dense = compiled::tabulate(&source, &Count).unwrap();
            let packed = compiled::tabulate_compact(&source, &Count).unwrap();
            for (rank, expected) in reference.iter().enumerate() {
                let (nt, [span]) = source.cell(rank).unwrap();
                let tokens = &input[span];
                let count = match nt {
                    FLANK => 1,
                    CORE => usize::from(tokens == query),
                    INFIX => tokens
                        .windows(query.len())
                        .filter(|&window| window == query)
                        .count(),
                    _ => unreachable!(),
                } as u128;
                assert_eq!(expected.first().copied(), (count != 0).then_some(count));
                assert_eq!(dense.cells()[rank].as_ref(), expected.first());
                assert_eq!(packed.get(rank), expected.first());
            }
            cells += reference.len();
        }
    }
    println!(
        "infix charts=378 logical_cells={cells} comparisons={}",
        2 * cells
    );
}

#[test]
fn split_end_unions_match_ordered_raw_membership() {
    use compiled::SplitEnds;

    const INPUT: &[u8] = b"aa";
    const ENDPOINTS: usize = INPUT.len() + 2; // Includes the first end beyond the input.
    let ranges: Vec<_> = (0..ENDPOINTS)
        .flat_map(|lo| (0..ENDPOINTS).map(move |hi| lo..=hi))
        .collect();
    let pairs = ranges
        .iter()
        .flat_map(|a| ranges.iter().map(|b| vec![a.clone(), b.clone()]));
    let disjoint = vec![0..=0, 2..=2];
    let last = usize::MAX;
    let cases = std::iter::once(vec![])
        .chain(ranges.iter().cloned().map(|range| vec![range]))
        .chain(pairs)
        .chain([
            vec![2..=3, 0..=0, 1..=2],
            vec![last..=last, last - 1..=last],
        ])
        .chain([disjoint.clone()]);
    let mut charts = 0;
    let mut ranks = 0;
    let mut rules = 0;
    for raw in cases {
        let union = SplitEnds::new(raw.clone());
        assert!(union.ranges().iter().all(|range| !range.is_empty()));
        assert!(union
            .ranges()
            .windows(2)
            .all(|pair| { pair[0].end().saturating_add(1) < *pair[1].start() }));
        if raw.first().is_some_and(|range| *range.start() == last) {
            assert_eq!(union.ranges(), [last - 1..=last]);
        }
        let grammar = nullable_join(move |context| {
            if context.rule == "join" && context.child == 0 {
                union.clone()
            } else {
                SplitEnds::from(0..=usize::MAX)
            }
        });
        let source = grammar.bind([INPUT]).unwrap();
        let reference = compiled::reference_chart(&source).unwrap();
        let coordinates: Vec<_> = (0..source.cell_count())
            .map(|rank| source.cell(rank).unwrap())
            .collect();
        let mut replayed = vec![vec![]; coordinates.len()];
        compiled::replay(&source, |rank, ordinal, _, operator, children| {
            assert_eq!(ordinal, replayed[rank].len());
            replayed[rank].push(Rule::new(operator, children));
            Ok(())
        })
        .unwrap();
        let rank_at = |start, end| {
            coordinates
                .iter()
                .position(|(nt, [span])| *nt == 0 && *span == (start..end))
                .unwrap()
        };
        let counts = compiled::tabulate(&source, &Count).unwrap();
        let expected = tabulate_cells(&reference, &Count).unwrap();
        for (rank, (nt, [span])) in coordinates.iter().enumerate() {
            let oracle: Vec<_> = if *nt == 0 {
                vec![Rule::new(
                    op(0, usize::from(!span.is_empty())),
                    (!span.is_empty())
                        .then(|| rank_at(span.start, span.end - 1))
                        .into_iter()
                        .collect::<Vec<_>>(),
                )]
            } else {
                (span.start..=span.end)
                    .filter(|end| raw.iter().any(|range| range.contains(end)))
                    .map(|end| {
                        Rule::new(
                            Op(3, 2, Rational::new(2, 1).unwrap()),
                            [rank_at(span.start, end), rank_at(end, span.end)],
                        )
                    })
                    .collect()
            };
            let view = |rule: &Rule<Op>| (rule.operator, rule.children.clone());
            assert!(replayed[rank].iter().map(view).eq(oracle.iter().map(view)));
            assert!(reference.cells()[rank]
                .iter()
                .map(view)
                .eq(oracle.iter().map(view)));
            assert_eq!(counts.cells()[rank].as_ref(), expected[rank].first());
        }
        let compiled = compiled::inside_outside(&source).unwrap();
        let exact = probability::inside_outside(&reference).unwrap();
        assert_eq!(compiled.weights(), &exact);
        if raw == disjoint {
            assert_eq!(counts.answer(), Some(&2));
            assert_eq!(*exact.partition(), Rational::new(4, 1).unwrap());
        }
        charts += 1;
        ranks += coordinates.len();
        rules += reference.cells().iter().map(Vec::len).sum::<usize>();
    }
    println!(
        "unions charts={charts} ranks={ranks} rules={rules} value_comparisons={}",
        ranks * 3
    );
}

fn nullable_join(
    guard: impl Fn(compiled::SplitContext<'_, 1, u8>) -> compiled::SplitEnds + 'static,
) -> Grammar<Op, 1> {
    let word = |name: &str, children: Vec<usize>, track| {
        let arity = children.len();
        Production {
            name: name.into(),
            parent: 0,
            children,
            tracks: [track],
            operator: Box::new(move |_| op(0, arity)),
        }
    };
    Grammar::new(
        &["word", "join"],
        1,
        vec![
            word("empty", vec![], vec![]),
            word("extend", vec![0], vec![Atom::Child(0), Atom::Byte(b'a')]),
            Production {
                name: "join".into(),
                parent: 1,
                children: vec![0, 0],
                tracks: [vec![Atom::Child(0), Atom::Child(1)]],
                operator: Box::new(|_| Op(3, 2, Rational::new(2, 1).unwrap())),
            },
        ],
    )
    .unwrap()
    .with_split_ends(guard)
}
