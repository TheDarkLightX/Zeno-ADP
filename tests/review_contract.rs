use std::num::NonZeroUsize;

use zeno_adp::algebras::Count;
use zeno_adp::compiled::generated::tracks::{bind, TrackRules};
use zeno_adp::compiled::{self, ProductionSink, Program};
use zeno_adp::fast::{self, Fold, RuleSource};
use zeno_adp::{compiled_grammar, tabulate_cells, Algebra, Cell, Chart, Error, Operator, Rule};

#[derive(Clone, Copy)]
struct Op {
    tag: u64,
    arity: usize,
}

impl Op {
    fn new(tag: u64, arity: usize) -> Self {
        Self { tag, arity }
    }
}

impl Operator for Op {
    fn arity(&self) -> usize {
        self.arity
    }
}

fn digest(left: u64, right: u64) -> u64 {
    left.rotate_left(9).wrapping_mul(31).wrapping_add(right)
}

struct ObserveChildren;

// Keep the signature used by 0.3 implementations.
impl Fold<Op> for ObserveChildren {
    type Value = u64;

    fn apply<'a>(
        &self,
        op: &'a Op,
        mut children: impl Iterator<Item = &'a u64> + Clone,
    ) -> Result<u64, Error> {
        let (initial, upper) = children.size_hint();
        assert_eq!((initial, upper), (op.arity, Some(op.arity)));
        let mut skipped = children.clone();
        assert_eq!(skipped.nth(initial), None);
        assert_eq!(skipped.size_hint(), (0, Some(0)));
        let mut value = digest(op.tag, initial as u64);
        for remaining in (0..initial).rev() {
            let child = *children.next().expect("enabled child");
            assert_eq!(children.size_hint(), (remaining, Some(remaining)));
            assert_eq!(children.clone().count(), remaining);
            value = digest(value, child);
        }
        assert_eq!(children.next(), None);
        Ok(value)
    }

    fn merge(&self, chosen: &mut Option<u64>, next: u64) -> Result<(), Error> {
        *chosen = Some(digest(chosen.unwrap_or(0), next));
        Ok(())
    }
}

impl Algebra<Op> for ObserveChildren {
    type Value = u64;

    fn apply(&self, op: &Op, children: &[&u64]) -> Result<u64, Error> {
        Ok(children
            .iter()
            .fold(digest(op.tag, children.len() as u64), |value, &&child| {
                digest(value, child)
            }))
    }

    fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
        Ok((!candidates.is_empty())
            .then(|| candidates.iter().copied().fold(0, digest))
            .into_iter()
            .collect())
    }
}

compiled_grammar! {
    fn prefix(data: u8) -> Op {
        prefix |word, start, end|;
        empty Leaf => Ok(Some(Op::new(1, 0)));
        extend First(split) => Ok((word[split] == 1).then(|| Op::new(split as u64, 1)));
        extend Again(split) => Ok((word[split] == 1).then(|| Op::new(split as u64, 1)));
    }
    with fn prefix_fold: ObserveChildren = ObserveChildren;
}

compiled_grammar! {
    fn intervals(data: u8) -> Op {
        interval |word, start, end|;
        empty Leaf => Ok(Some(Op::new(start as u64, 0)));
        pivot Fork(p) => Ok((word[p] == 1).then(|| Op::new(p as u64, 2)));
    }
    with fn interval_fold: ObserveChildren = ObserveChildren;
}

compiled_grammar! {
    fn tracks(data: u8) -> Op {
        prefix_tracks 4 |word, end|;
        empty Leaf => Ok(Some(Op::new(1, 0)));
        step First[true, false, false, false] => Ok((word[0][end[0] - 1] == 1).then(|| Op::new((end[0] - 1) as u64, 1)));
        step Again[true, false, false, false] => Ok((word[0][end[0] - 1] == 1).then(|| Op::new((end[0] - 1) as u64, 1)));
    }
    with fn track_fold: ObserveChildren = ObserveChildren;
}

fn prefix_chart(word: &[u8], adjacent_only: bool) -> Chart<Op> {
    let mut rows = vec![vec![Rule::new(Op::new(1, 0), [])]];
    for end in 1..=word.len() {
        let first = if adjacent_only { end - 1 } else { 0 };
        let alternatives: Vec<_> = (first..end)
            .filter(|&child| word[child] == 1)
            .map(|child| Rule::new(Op::new(child as u64, 1), [child]))
            .collect();
        rows.push(alternatives.iter().chain(&alternatives).cloned().collect());
    }
    Chart::new(rows, word.len()).unwrap()
}

fn interval_chart(word: &[u8]) -> Chart<Op> {
    let spans: Vec<_> = (0..=word.len())
        .flat_map(|end| (0..=end).rev().map(move |start| (start, end)))
        .collect();
    let rank = |span| spans.iter().position(|&other| other == span).unwrap();
    let rows = spans
        .iter()
        .map(|&(start, end)| {
            if start == end {
                return vec![Rule::new(Op::new(start as u64, 0), [])];
            }
            (start..end)
                .filter(|&pivot| word[pivot] == 1)
                .map(|pivot| {
                    Rule::new(
                        Op::new(pivot as u64, 2),
                        [rank((start, pivot)), rank((pivot + 1, end))],
                    )
                })
                .collect()
        })
        .collect();
    Chart::new(rows, rank((0, word.len()))).unwrap()
}

const WORKERS: [usize; 4] = [1, 2, 4, 8]; // Serial and all three lead worker counts.

fn check_modes(
    program: &(impl Program<Op = Op> + Sync),
    chart: &Chart<Op>,
    paired: Option<fast::Table<u64>>,
) -> usize {
    let reference: Vec<_> = tabulate_cells(chart, &ObserveChildren)
        .unwrap()
        .into_iter()
        .map(|bag| bag.first().copied())
        .collect();
    let ranks: Vec<_> = (0..reference.len()).collect();
    let check_table = |table: fast::Table<u64>| {
        assert_eq!(table.root(), chart.root());
        assert_eq!(table.cells(), reference);
    };
    if let Some(table) = paired {
        check_table(table);
    }
    check_table(fast::tabulate(program, &ObserveChildren).unwrap());
    check_table(compiled::tabulate(program, &ObserveChildren).unwrap());
    let packed = compiled::tabulate_compact(program, &ObserveChildren).unwrap();
    assert_eq!(packed.root(), chart.root());
    for (rank, expected) in reference.iter().enumerate() {
        assert_eq!(packed.get(rank), expected.as_ref());
    }
    for workers in WORKERS {
        check_table(
            compiled::tabulate_parallel(
                program,
                &ObserveChildren,
                NonZeroUsize::new(workers).unwrap(),
            )
            .unwrap(),
        );
    }

    let mut observed = Vec::new();
    let root = compiled::tabulate_root(program, &ObserveChildren, |rank, value| {
        observed.push((rank, value.copied()));
    })
    .unwrap();
    assert!(observed
        .into_iter()
        .eq(reference.iter().copied().enumerate()));
    assert_eq!(root, reference[chart.root()]);

    let mut observed = Vec::new();
    let selected = compiled::tabulate_selected(program, &ObserveChildren, &ranks, |rank, value| {
        observed.push((rank, value.copied()));
    })
    .unwrap();
    assert!(observed
        .into_iter()
        .eq(reference.iter().copied().enumerate()));
    assert!(selected
        .answers
        .into_iter()
        .eq(reference.iter().copied().enumerate()));

    let mut seen = 0;
    let joint = compiled::tabulate_joint(
        program,
        (&ObserveChildren, &ranks),
        (&ObserveChildren, &ranks),
        |rank, left, right| {
            assert_eq!(rank, seen);
            assert_eq!(
                (left.copied(), right.copied()),
                (reference[rank], reference[rank])
            );
            seen += 1;
        },
    )
    .unwrap();
    assert_eq!(seen, reference.len());
    for side in [joint.left, joint.right] {
        assert!(side
            .answers
            .into_iter()
            .eq(reference.iter().copied().enumerate()));
    }
    reference.len()
}

#[test]
fn all_evaluators_expose_the_exact_ordered_child_sequence() {
    // Includes repeated alternatives, disabled children and a fork with
    // distinct child values in both positions.
    const LENGTH: usize = 3;
    let mut cells = [0; 3];
    for len in 0..=LENGTH {
        for bits in 0..1 << len {
            let word: Vec<_> = (0..len).map(|i| ((bits >> i) & 1) as u8).collect();
            cells[0] += check_modes(
                &prefix(&word).unwrap(),
                &prefix_chart(&word, false),
                Some(prefix_fold(&word).unwrap()),
            );
            cells[1] += check_modes(
                &intervals(&word).unwrap(),
                &interval_chart(&word),
                Some(interval_fold(&word).unwrap()),
            );
            let input = [word.as_slice(), &[], &[], &[]];
            cells[2] += check_modes(
                &tracks(input).unwrap(),
                &prefix_chart(&word, true),
                Some(track_fold(input).unwrap()),
            );
        }
    }
    assert_eq!(cells, [49, 111, 49]);
}

#[derive(Clone, Copy)]
enum Row {
    Fixed,
    Slice,
    BadArity,
    BadRank,
    EarlyFinish,
    IgnoredArity,
}

impl TrackRules<u8, Op, 1> for Row {
    fn prepare(&mut self, _: &[usize; 1], _: &[usize; 1]) -> Result<(), Error> {
        Ok(())
    }

    fn emit(
        &self,
        _: [&[u8]; 1],
        cell: Cell,
        _: [usize; 1],
        sink: &mut impl ProductionSink<Op>,
    ) -> Result<(), Error> {
        match self {
            Row::Fixed => {
                sink.rule("leaf", Op::new(cell as u64, 0), [])?;
                if cell != 0 {
                    sink.rule("unary", Op::new(0, 1), [0])?;
                    sink.rule("binary", Op::new(0, 2), [0, 0])?;
                    sink.rule("ternary", Op::new(0, 3), [0, 0, 0])?;
                    sink.rule("quaternary", Op::new(0, 4), [0, 0, 0, 0])?;
                }
                Ok(())
            }
            Row::Slice => {
                // Match the fixed arities while forcing the borrowed-slice entry.
                let children = [0; 4];
                let limit = if cell == 0 { 0 } else { children.len() };
                for arity in 0..=limit {
                    let tag = if arity == 0 { cell as u64 } else { 0 };
                    sink.rule_slice("row", Op::new(tag, arity), &children[..arity])?;
                }
                Ok(())
            }
            Row::BadArity => sink.rule("bad", Op::new(0, 1), []),
            Row::BadRank => sink.rule_slice("bad", Op::new(0, 1), &[cell]),
            Row::EarlyFinish => sink.finish_cell(),
            Row::IgnoredArity => {
                let _ = sink.rule("bad", Op::new(0, 1), []);
                let _ = sink.rule("valid after bad", Op::new(0, 0), []);
                Ok(())
            }
        }
    }
}

#[test]
fn fixed_and_slice_emissions_agree_at_arities_zero_through_four() {
    let chart = Chart::new(
        vec![
            vec![Rule::new(Op::new(0, 0), [])],
            std::iter::once(Rule::new(Op::new(1, 0), []))
                .chain((1..=4).map(|arity| Rule::new(Op::new(0, arity), vec![0; arity])))
                .collect(),
        ],
        1,
    )
    .unwrap();
    for row in [Row::Fixed, Row::Slice] {
        assert_eq!(
            check_modes(&bind("shape", [&[1]], row).unwrap(), &chart, None),
            2
        );
    }
}

#[test]
fn malformed_external_rows_are_rejected_at_the_emission_boundary() {
    const NAME: &str = "external rows";
    let arity_error = Error::Arity {
        cell: 0,
        expected: 1,
        actual: 0,
    };
    for (row, expected) in [
        (Row::BadArity, arity_error.clone()),
        (
            Row::BadRank,
            Error::NonDescendingChild { cell: 0, child: 0 },
        ),
        (
            Row::EarlyFinish,
            Error::UnsupportedGrammar {
                name: NAME.to_owned(),
                reason: "a track emitter cannot finish a cell",
            },
        ),
        (Row::IgnoredArity, arity_error),
    ] {
        let source = bind(NAME, [&[]], row).unwrap();
        let rejected = |error| assert_eq!(error, Some(expected.clone()));
        rejected(compiled::tabulate(&source, &Count).err());
        rejected(compiled::tabulate_compact(&source, &Count).err());
        rejected(source.rules_at(0, |_, _| Ok(())).err());
        rejected(compiled::replay(&source, |_, _, _, _, _| Ok(())).err());
        rejected(compiled::reference_chart(&source).err());
        rejected(fast::reference_chart(&source).err());
        rejected(fast::tabulate(&source, &Count).err());
        rejected(compiled::tabulate_root(&source, &Count, |_, _| {}).err());
        rejected(compiled::tabulate_selected(&source, &Count, &[0], |_, _| {}).err());
        rejected(
            compiled::tabulate_joint(&source, (&Count, &[0]), (&Count, &[0]), |_, _, _| {}).err(),
        );
        for workers in [1, 2] {
            rejected(
                compiled::tabulate_parallel(&source, &Count, NonZeroUsize::new(workers).unwrap())
                    .err(),
            );
        }
    }
}

compiled_grammar! {
    fn mixed(data: u8) -> Op {
        interval |word, start, end|;
        empty Leaf => Ok(Some(Op::new((end == word.len()) as u64, 0)));
        pivot Pair(p) => {
            if word[p] == 8 {
                return Err(Error::InvalidSymbol(word[p]));
            }
            Ok(Some(Op::new(0, 2)))
        };
    }
}

struct Unwind;

impl Fold<Op> for Unwind {
    type Value = u64;

    fn apply<'a>(
        &self,
        op: &'a Op,
        _: impl Iterator<Item = &'a u64> + Clone,
    ) -> Result<u64, Error> {
        if op.arity == 2 {
            return Err(Error::InvalidDimensions);
        }
        if op.tag == 1 {
            std::panic::panic_any("empty interval at end 2");
        }
        Ok(0)
    }

    fn merge(&self, chosen: &mut Option<u64>, next: u64) -> Result<(), Error> {
        *chosen = Some(next);
        Ok(())
    }
}

#[test]
fn analytic_waves_can_unwind_before_a_lower_rank_returns_an_error() {
    let one = NonZeroUsize::new(1).unwrap();
    let two = NonZeroUsize::new(2).unwrap();
    for (token, error) in [(8, Error::InvalidSymbol(8)), (7, Error::InvalidDimensions)] {
        let input = [token; 2];
        let source = mixed(&input).unwrap();
        assert_eq!(
            compiled::tabulate_parallel(&source, &Unwind, one),
            Err(error)
        );
        let unwound =
            std::panic::catch_unwind(|| compiled::tabulate_parallel(&source, &Unwind, two))
                .expect_err("empty intervals are evaluated before nonempty intervals");
        assert_eq!(
            unwound.downcast_ref::<&str>(),
            Some(&"empty interval at end 2")
        );
    }
    let bad_source = mixed(&[8, 8]).unwrap();
    for workers in [one, two] {
        assert_eq!(
            compiled::tabulate_parallel(&bad_source, &Count, workers),
            Err(Error::InvalidSymbol(8))
        );
    }
}
