use std::num::NonZeroUsize;

use zeno_adp::algebras::{Additive, Cost, Count};
use zeno_adp::compiled;
use zeno_adp::fast::Fold;
use zeno_adp::grammars::{self, Align};
use zeno_adp::{compiled_grammar, tabulate_cells, Algebra, Error, Operator};

// Include the serial path, a non-power-of-two partition and all timing counts.
const WORKER_COUNTS: [usize; 5] = [1, 2, 3, 4, 8];

#[derive(Clone, Copy)]
struct Op(u8, usize);

impl Operator for Op {
    fn arity(&self) -> usize {
        self.1
    }
}

compiled_grammar! {
    fn intervals(input: u8) -> Op {
        interval |tokens, start, end|;
        empty Base => Ok(Some(Op(0, 0)));
        empty Second => Ok(Some(Op(1, 0)));
        pivot Join(pivot) => Ok((tokens[pivot] == 1).then_some(Op(2, 2)));
    }
}

fn workers(count: usize) -> NonZeroUsize {
    NonZeroUsize::new(count).unwrap()
}

fn compare<G, A>(source: &G, chart: &zeno_adp::Chart<G::Op>, algebra: &A) -> usize
where
    G: compiled::Program + Sync,
    A: Algebra<G::Op> + Fold<G::Op, Value = <A as Algebra<G::Op>>::Value> + Sync,
    <A as Algebra<G::Op>>::Value: PartialEq + std::fmt::Debug + Send + Sync,
{
    compare_projected(source, chart, algebra, Clone::clone)
}

fn compare_projected<G, A>(
    source: &G,
    chart: &zeno_adp::Chart<G::Op>,
    algebra: &A,
    project: impl Fn(&<A as Fold<G::Op>>::Value) -> <A as Algebra<G::Op>>::Value,
) -> usize
where
    G: compiled::Program + Sync,
    A: Algebra<G::Op> + Fold<G::Op> + Sync,
    <A as Fold<G::Op>>::Value: Send + Sync,
{
    let expected = tabulate_cells(chart, algebra).unwrap();
    for count in WORKER_COUNTS {
        let actual = compiled::tabulate_parallel(source, algebra, workers(count)).unwrap();
        assert_eq!(actual.root(), chart.root());
        assert_eq!(actual.cells().len(), expected.len());
        for (rank, (actual, expected)) in actual.cells().iter().zip(&expected).enumerate() {
            assert_eq!(
                actual.as_ref().map(&project).as_slice(),
                expected.as_slice(),
                "worker count {count}, rank {rank}"
            );
        }
    }
    expected.len() * WORKER_COUNTS.len()
}

#[test]
fn alignment_and_interval_waves_match_reference_cells() {
    // Three tokens cover absent intervals, multiple split positions and
    // independent cells from distinct intervals in the same wave.
    const MAX_INPUT: usize = 3;
    let words: Vec<Vec<_>> = (0..=MAX_INPUT)
        .flat_map(|width| {
            (0..1 << width)
                .map(move |bits| (0..width).map(|axis| ((bits >> axis) & 1) as u8).collect())
        })
        .collect();
    let mut interval_cells = 0;
    let mut alignment_cells = 0;
    for word in &words {
        let intervals = intervals(word).unwrap();
        let chart = compiled::reference_chart(&intervals).unwrap();
        interval_cells += compare(&intervals, &chart, &Count);
        interval_cells += compare(&intervals, &chart, &First);
        for other in &words {
            let chart = grammars::alignment(word, other).unwrap();
            let alignment = grammars::alignment_source(word, other).unwrap();
            alignment_cells += compare(&alignment, &chart, &Additive::default());
        }
    }
    println!("small waves: {interval_cells} interval and {alignment_cells} alignment comparisons");
}

#[test]
fn nussinov_length_waves_match_reference_cells() {
    // Four bases cover the first legal pair at loop size one and the
    // first simultaneous pair and unpaired alternatives at several spans.
    const MAX_INPUT: u32 = 4;
    const MIN_LOOPS: [usize; 4] = [0, 1, 3, usize::MAX];
    let alphabet = b"ACGU";
    let mut comparisons = 0;
    for len in 0..=MAX_INPUT {
        for digits in 0..alphabet.len().pow(len) {
            let word: Vec<_> = (0..len)
                .map(|pos| alphabet[(digits / alphabet.len().pow(pos)) % alphabet.len()])
                .collect();
            for min_loop in MIN_LOOPS {
                let source = grammars::nussinov_source(&word, min_loop).unwrap();
                let chart = grammars::nussinov(&word, min_loop).unwrap();
                comparisons += compare(&source, &chart, &Additive::default());
                comparisons += compare(&source, &chart, &Count);
            }
        }
    }
    println!("Nussinov: {comparisons} comparisons");
}

#[test]
fn alignment_tiles_match_reference_cells() {
    // Empty tracks, exact tile edges, remainders and a wave with three tiles.
    const PREFIX_DIMS: [usize; 5] = [1, 31, 32, 33, 65];
    let mut comparisons = 0;
    for height in PREFIX_DIMS {
        for width in PREFIX_DIMS {
            let left = sequence(height - 1, 1);
            let right = sequence(width - 1, 2);
            let source = grammars::alignment_source(&left, &right).unwrap();
            let chart = grammars::alignment(&left, &right).unwrap();
            comparisons += compare(&source, &chart, &Additive::default());
            comparisons += compare_projected(&source, &chart, &FirstColumn, |trace| trace.0);
        }
    }
    println!("tiles: {comparisons} comparisons");
}

fn sequence(n: usize, mut state: u64) -> Vec<u8> {
    // LCG constants of the fixed timing fixture.
    const MULTIPLIER: u64 = 6_364_136_223_846_793_005;
    const INCREMENT: u64 = 1_442_695_040_888_963_407;
    (0..n)
        .map(|_| {
            state = state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT);
            b"ACGU"[(state >> (u64::BITS - 2)) as usize]
        })
        .collect()
}

#[derive(Debug, PartialEq)]
struct Trace(u64);

struct FirstColumn;

impl FirstColumn {
    fn extend(operator: &Align, previous: u64) -> u64 {
        let column = match operator {
            Align::Start => 0,
            Align::Diagonal { left, right } => u64::from(*left) << 8 | u64::from(*right),
            Align::Left(token) => u64::from(*token) << 16,
            Align::Right(token) => u64::from(*token) << 24,
        };
        previous.rotate_left(5) ^ column
    }
}

impl Algebra<Align> for FirstColumn {
    type Value = u64;
    fn apply(&self, operator: &Align, children: &[&u64]) -> Result<u64, Error> {
        Ok(Self::extend(
            operator,
            children.first().map_or(0, |&&trace| trace),
        ))
    }
    fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
        Ok(candidates.first().copied().into_iter().collect())
    }
}

impl Fold<Align> for FirstColumn {
    type Value = Trace;
    fn apply<'a>(
        &self,
        operator: &'a Align,
        mut children: impl Iterator<Item = &'a Trace> + Clone,
    ) -> Result<Trace, Error> {
        Ok(Trace(Self::extend(
            operator,
            children.next().map_or(0, |trace| trace.0),
        )))
    }
    fn merge(&self, chosen: &mut Option<Trace>, next: Trace) -> Result<(), Error> {
        chosen.get_or_insert(next);
        Ok(())
    }
}

struct First;

impl Algebra<Op> for First {
    type Value = u8;
    fn apply(&self, operator: &Op, _: &[&u8]) -> Result<u8, Error> {
        Ok(operator.0)
    }
    fn choose(&self, candidates: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(candidates.first().copied().into_iter().collect())
    }
}

impl Fold<Op> for First {
    type Value = u8;
    fn apply<'a>(
        &self,
        operator: &'a Op,
        _: impl Iterator<Item = &'a u8> + Clone,
    ) -> Result<u8, Error> {
        Ok(operator.0)
    }
    fn merge(&self, chosen: &mut Option<u8>, next: u8) -> Result<(), Error> {
        chosen.get_or_insert(next);
        Ok(())
    }
}

compiled_grammar! {
    fn failures(input: u8) -> Op {
        prefix |tokens, start, end|;
        empty Base => Ok(Some(Op(0, 0)));
        extend Rule(prior) => {
            let token = tokens[end - 1];
            if token == u8::MAX {
                return Err(Error::InvalidSymbol(token));
            }
            let child = if token == 4 { 0 } else { end - 1 };
            Ok((child == prior).then_some(Op(token, 1)))
        };
    }
}

struct Failing;
impl Fold<Op> for Failing {
    type Value = Cost;
    fn apply<'a>(
        &self,
        operator: &'a Op,
        _: impl Iterator<Item = &'a Cost> + Clone,
    ) -> Result<Cost, Error> {
        match operator.0 {
            2 => Err(Error::InvalidDimensions),
            4 => Err(Error::Overflow),
            _ => Ok(Cost::Finite(0)),
        }
    }
    fn merge(&self, selected: &mut Option<Cost>, next: Cost) -> Result<(), Error> {
        *selected = Some(next);
        Ok(())
    }
}

#[test]
fn waves_preserve_rank_order_error_and_source_priority() {
    // Rank 4 fails in wave 1, while rank 2 fails in wave 2. A malformed
    // source at rank 5 must be reported before either algebra failure.
    for (input, error) in [
        (&[1, 2, 3, 4][..], Error::InvalidDimensions),
        (&[1, 2, 3, 4, u8::MAX][..], Error::InvalidSymbol(u8::MAX)),
    ] {
        let source = failures(input).unwrap();
        assert_eq!(compiled::tabulate(&source, &Failing), Err(error.clone()));
        for count in WORKER_COUNTS {
            assert_eq!(
                compiled::tabulate_parallel(&source, &Failing, workers(count)),
                Err(error.clone())
            );
        }
    }
}

#[test]
fn sparse_prefix_replay_waves_match_reference_cells() {
    // Three tokens cover independent skips at ranks 1..=3 and skip-to-chain joins.
    const MAX_INPUT: usize = 3;
    let mut comparisons = 0;
    for length in 0..=MAX_INPUT {
        for bits in 0..1 << length {
            let input: Vec<_> = (0..length)
                .map(|position| if bits & (1 << position) == 0 { 1 } else { 4 })
                .collect();
            let source = failures(&input).unwrap();
            let chart = compiled::reference_chart(&source).unwrap();
            comparisons += compare(&source, &chart, &Count);
            comparisons += compare(&source, &chart, &First);
        }
    }
    println!("replay: {comparisons} comparisons");
}

compiled_grammar! {
    fn interval_errors(input: u8) -> Op {
        interval |tokens, start, end|;
        empty Base => {
            if start == 2 && tokens[1] == u8::MAX {
                Err(Error::InvalidSymbol(u8::MAX))
            } else {
                Ok(Some(Op(0, 0)))
            }
        };
        empty Merge => Ok(Some(Op(1, 0)));
        empty Apply => Ok(Some(Op(2, 0)));
        pivot Guard(pivot) => {
            if tokens[pivot] == u8::MAX {
                Err(Error::InvalidSymbol(0))
            } else {
                Ok(None)
            }
        };
    }
}

struct FailingMerge;

impl Fold<Op> for FailingMerge {
    type Value = Cost;
    fn apply<'a>(
        &self,
        operator: &'a Op,
        children: impl Iterator<Item = &'a Cost> + Clone,
    ) -> Result<Cost, Error> {
        Failing.apply(operator, children)
    }
    fn merge(&self, chosen: &mut Option<Cost>, next: Cost) -> Result<(), Error> {
        if chosen.replace(next).is_some() {
            Err(Error::InfinityDisabled)
        } else {
            Ok(())
        }
    }
}

#[test]
fn analytic_interval_errors_preserve_source_and_apply_priority() {
    let source = interval_errors(&[0, 0]).unwrap();
    let malformed = interval_errors(&[u8::MAX, u8::MAX]).unwrap();
    // The empty span at end 2 fails earlier in length order. The
    // shorter end's pivot error comes first in original rank order.
    assert!(matches!(
        compiled::reference_chart(&malformed),
        Err(Error::InvalidSymbol(0))
    ));
    for count in WORKER_COUNTS {
        assert_eq!(
            compiled::tabulate_parallel(&source, &FailingMerge, workers(count)),
            Err(Error::InvalidDimensions)
        );
        assert_eq!(
            compiled::tabulate_parallel(&malformed, &FailingMerge, workers(count)),
            Err(Error::InvalidSymbol(0))
        );
    }
}

struct FailingAlignment;

impl Fold<Align> for FailingAlignment {
    type Value = Cost;
    fn apply<'a>(
        &self,
        operator: &'a Align,
        _: impl Iterator<Item = &'a Cost> + Clone,
    ) -> Result<Cost, Error> {
        match operator {
            Align::Diagonal {
                left: b'X',
                right: b'Z',
            } => Err(Error::InvalidDimensions),
            Align::Diagonal {
                left: b'Y',
                right: b'W',
            } => Err(Error::Overflow),
            _ => Ok(Cost::Finite(0)),
        }
    }
    fn merge(&self, chosen: &mut Option<Cost>, next: Cost) -> Result<(), Error> {
        *chosen = Some(next);
        Ok(())
    }
}

#[test]
fn alignment_reports_a_lower_rank_from_a_later_tile_wave() {
    // The Y/W failure is at (33, 1) in wave 1. The X/Z failure is at
    // (1, 64) in wave 2, despite having a smaller original rank.
    const LENGTH: usize = 64;
    let mut left = [b'A'; LENGTH];
    let mut right = [b'B'; LENGTH];
    left[0] = b'X';
    left[32] = b'Y';
    right[0] = b'W';
    right[LENGTH - 1] = b'Z';
    let source = grammars::alignment_source(&left, &right).unwrap();
    for count in WORKER_COUNTS {
        assert_eq!(
            compiled::tabulate_parallel(&source, &FailingAlignment, workers(count)),
            Err(Error::InvalidDimensions)
        );
    }
}

struct PanicOnWorker(std::thread::ThreadId);

impl Fold<Op> for PanicOnWorker {
    type Value = u8;
    fn apply<'a>(
        &self,
        operator: &'a Op,
        _: impl Iterator<Item = &'a u8> + Clone,
    ) -> Result<u8, Error> {
        if std::thread::current().id() != self.0 {
            std::panic::panic_any("fold panic on worker");
        }
        Ok(operator.0)
    }
    fn merge(&self, chosen: &mut Option<u8>, next: u8) -> Result<(), Error> {
        *chosen = Some(next);
        Ok(())
    }
}

#[test]
fn a_worker_panic_unwinds_the_team_with_its_payload() {
    let source = intervals(&[1, 1]).unwrap();
    let fold = PanicOnWorker(std::thread::current().id());
    let panic =
        std::panic::catch_unwind(|| compiled::tabulate_parallel(&source, &fold, workers(2)))
            .expect_err("the length-zero wave dispatches to a worker");
    assert_eq!(panic.downcast_ref::<&str>(), Some(&"fold panic on worker"));
    compare(
        &source,
        &compiled::reference_chart(&source).unwrap(),
        &Count,
    );
}
