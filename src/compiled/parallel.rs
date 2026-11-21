use std::num::NonZeroUsize;
use std::ops::Range;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{mpsc, RwLock};

use crate::fast::{fold_rule, Fold, Table};
use crate::{reserve_table, Cell, Error};

use super::{replay, sealed::Sealed, tabulate, Program};

// A 32-square tile holds 16 KiB at 16 bytes per summary, leaving room
// in a 32 KiB L1 data cache for ranks and boundary reads.
const ALIGNMENT_TILE_EDGE: usize = 32;

// With one task there is no independent work for a second worker.
const MIN_PARALLEL_TASKS: usize = 2;

/// Geometry supplied only by the crate's sealed programs.
pub enum Layout<'a> {
    Replay,
    PrefixGrid { height: usize, width: usize },
    IntervalLengths(&'a [Cell]),
    GeneratedIntervals(&'a [Cell]),
}

/// Experimental parallel filling. Dependencies and answers are indexed
/// by the program's original ranks. Each cell visits alternatives in
/// source order.
///
/// Constructors and the [`Fold`] must be deterministic and independent of
/// schedule and thread identity. With storage available and callbacks that
/// return normally, source errors take precedence, then the earliest
/// failing evaluation rank, with application before merge in the same cell.
/// A callback that panics can unwind the call before that ordering applies.
/// Multi-worker schedules can visit a later rank first. An unwind from a
/// worker resumes with its original payload when the caller receives it.
/// Closed-form schedules replay source rows on a returned error.
///
/// Bound programs from [`super::TokenGrammar`] and [`crate::mcfg::Grammar`]
/// hold boxed callbacks that can capture non-`Sync` state. Evaluate those
/// programs with [`super::tabulate`]. This includes the MCFG macro form.
pub fn tabulate_parallel<G, A>(
    grammar: &G,
    algebra: &A,
    workers: NonZeroUsize,
) -> Result<Table<A::Value>, Error>
where
    G: Program + Sync,
    A: Fold<G::Op> + Sync,
    A::Value: Send + Sync,
{
    if workers.get() == 1 {
        return tabulate(grammar, algebra);
    }

    let size = grammar.cell_count();
    let mut cells = reserve_table(size)?;
    cells.resize_with(size, || None);
    let requested = workers.get();
    let result = match Sealed::parallel_layout(grammar) {
        Layout::Replay => {
            let waves = wavefronts(grammar)?;
            let widest = waves.iter().map(Vec::len).max().unwrap_or(0);
            return fill_waves(
                grammar,
                algebra,
                cells,
                waves.iter().map(|wave| Wave::Ranks(wave)),
                requested.min(widest),
            );
        }
        Layout::PrefixGrid { height, width } => {
            let grid = Grid { height, width };
            let rows = height.div_ceil(ALIGNMENT_TILE_EDGE);
            let columns = width.div_ceil(ALIGNMENT_TILE_EDGE);
            let waves = (0..rows + (columns - 1)).map(|diagonal| {
                let first_row = diagonal.saturating_sub(columns - 1);
                let last_row = diagonal.min(rows - 1);
                Wave::Tiles {
                    grid,
                    diagonal,
                    first_row,
                    count: last_row - first_row + 1,
                }
            });
            fill_waves(
                grammar,
                algebra,
                cells,
                waves,
                requested.min(rows).min(columns),
            )
        }
        Layout::IntervalLengths(offsets) => {
            // All empty spans share rank zero. Each nonempty length is contiguous.
            let waves = std::iter::once(Wave::Contiguous { start: 0, count: 1 }).chain(
                offsets
                    .iter()
                    .enumerate()
                    .map(|(index, &start)| Wave::Contiguous {
                        start,
                        count: offsets.len() - index,
                    }),
            );
            fill_waves(
                grammar,
                algebra,
                cells,
                waves,
                requested.min(offsets.len().max(1)),
            )
        }
        Layout::GeneratedIntervals(offsets) => {
            // End-major ranks. A fixed length is one rank from each eligible end.
            let waves = (0..offsets.len()).map(|length| Wave::GeneratedIntervals {
                ends: &offsets[length..],
                length,
            });
            fill_waves(grammar, algebra, cells, waves, requested.min(offsets.len()))
        }
    };
    if result.is_err() {
        // Analytic waves may meet source errors in a different order. Rank-order
        // replay gives source errors precedence over any evaluation error.
        replay(grammar, |_, _, _, _, _| Ok(()))?;
    }
    result
}

#[derive(Clone, Copy)]
enum Wave<'a> {
    Ranks(&'a [Cell]),
    Contiguous {
        start: Cell,
        count: usize,
    },
    GeneratedIntervals {
        ends: &'a [Cell],
        length: usize,
    },
    Tiles {
        grid: Grid,
        diagonal: usize,
        first_row: usize,
        count: usize,
    },
}

impl Wave<'_> {
    fn len(self) -> usize {
        match self {
            Self::Ranks(ranks) => ranks.len(),
            Self::Contiguous { count, .. } | Self::Tiles { count, .. } => count,
            Self::GeneratedIntervals { ends, .. } => ends.len(),
        }
    }

    fn task(self, index: usize) -> Task {
        match self {
            Self::Ranks(ranks) => Task::Cell(ranks[index]),
            Self::Contiguous { start, .. } => Task::Cell(start + index),
            Self::GeneratedIntervals { ends, length } => Task::Cell(ends[index] + length),
            Self::Tiles {
                grid,
                diagonal,
                first_row,
                ..
            } => {
                let row = first_row + index;
                Task::Tile(grid.tile(row, diagonal - row))
            }
        }
    }
}

enum Task {
    Cell(Cell),
    Tile(Tile),
}

#[derive(Clone, Copy)]
struct Grid {
    height: usize,
    width: usize,
}

impl Grid {
    fn tile(self, row: usize, column: usize) -> Tile {
        let row = row * ALIGNMENT_TILE_EDGE;
        let column = column * ALIGNMENT_TILE_EDGE;
        Tile {
            rows: row..row.saturating_add(ALIGNMENT_TILE_EDGE).min(self.height),
            columns: column..column.saturating_add(ALIGNMENT_TILE_EDGE).min(self.width),
            stride: self.width,
        }
    }
}

struct Tile {
    rows: Range<usize>,
    columns: Range<usize>,
    stride: usize,
}

impl Tile {
    fn offset(&self, rank: Cell) -> Option<usize> {
        let row = rank / self.stride;
        let column = rank % self.stride;
        (self.rows.contains(&row) && self.columns.contains(&column))
            .then(|| (row - self.rows.start) * self.columns.len() + (column - self.columns.start))
    }
}

struct Work<'a, V> {
    wave: Wave<'a>,
    tasks: Range<usize>,
    before: Cell,
    answers: Vec<(Cell, Option<V>)>,
}

type BatchResult<V> = Result<(Vec<(Cell, Option<V>)>, Option<(Cell, Error)>), Error>;

fn fill_waves<'a, G, A>(
    grammar: &G,
    algebra: &A,
    cells: Vec<Option<A::Value>>,
    waves: impl Iterator<Item = Wave<'a>>,
    team_size: usize,
) -> Result<Table<A::Value>, Error>
where
    G: Program + Sync,
    A: Fold<G::Op> + Sync,
    A::Value: Send + Sync,
{
    let cells = RwLock::new(cells);
    let earliest = std::thread::scope(|scope| {
        // A worker reads a wave's completed predecessors under one read lock.
        // The caller publishes results only after every chunk has replied.
        let evaluate = |work| evaluate_chunk(grammar, algebra, &cells.read().unwrap(), work);
        let mut workers = Vec::new();
        for _ in 1..team_size {
            let (send, receive) = mpsc::channel();
            let (reply, results) = mpsc::channel();
            let started = std::thread::Builder::new().spawn_scoped(scope, move || {
                for work in receive {
                    let result = catch_unwind(AssertUnwindSafe(|| evaluate(work)));
                    let panicked = result.is_err();
                    if reply.send(result).is_err() || panicked {
                        break;
                    }
                }
            });
            if started.is_err() {
                break;
            }
            workers.push((send, results, Vec::new()));
        }

        let mut earliest = None;
        let mut local_answers = Vec::new();
        for wave in waves {
            let before = earliest
                .as_ref()
                .map_or(grammar.cell_count(), |&(rank, _)| rank);
            let chunk = if wave.len() < MIN_PARALLEL_TASKS {
                wave.len()
            } else {
                wave.len().div_ceil(workers.len() + 1)
            };
            let mut ranges = (0..wave.len())
                .step_by(chunk)
                .map(|start| start..start.saturating_add(chunk).min(wave.len()));
            let work = |tasks, answers| Work {
                wave,
                tasks,
                before,
                answers,
            };
            let local = work(ranges.next().expect("a wave is nonempty"), local_answers);
            let mut dispatched = 0;
            for (tasks, (send, _, answers)) in ranges.zip(&mut workers) {
                send.send(work(tasks, std::mem::take(answers)))
                    .unwrap_or_else(|_| unreachable!("scoped worker stopped before a reply"));
                dispatched += 1;
            }

            let (mut answers, mut error) = evaluate(local)?;
            for (_, receive, buffer) in workers.iter_mut().take(dispatched) {
                let result = receive.recv().expect("scoped worker must reply");
                let (completed, failure) = result.unwrap_or_else(|panic| resume_unwind(panic))?;
                *buffer = completed;
                if let Some(failure) = failure {
                    if error.as_ref().is_none_or(|&(rank, _)| failure.0 < rank) {
                        error = Some(failure);
                    }
                }
            }
            let mut cells = cells.write().unwrap();
            let remote = workers
                .iter_mut()
                .take(dispatched)
                .map(|(_, _, buffer)| buffer);
            for batch in std::iter::once(&mut answers).chain(remote) {
                for (rank, answer) in batch.drain(..) {
                    cells[rank] = answer;
                }
            }
            local_answers = answers;
            if error.is_some() {
                earliest = error;
            }
        }
        Ok::<_, Error>(earliest)
    })?;
    if let Some((_, error)) = earliest {
        return Err(error);
    }
    Ok(Table::new(cells.into_inner().unwrap(), grammar.root()))
}

fn evaluate_chunk<G, A>(
    grammar: &G,
    algebra: &A,
    cells: &[Option<A::Value>],
    Work {
        wave,
        tasks,
        before,
        mut answers,
    }: Work<'_, A::Value>,
) -> BatchResult<A::Value>
where
    G: Program,
    A: Fold<G::Op>,
{
    answers
        .try_reserve(tasks.len())
        .map_err(|_| Error::AllocationFailed)?;
    // Tasks within a chunk visit increasing original ranks. Alignment tiles
    // on one diagonal occupy disjoint, increasing bands of rows.
    for task in tasks {
        match wave.task(task) {
            Task::Cell(rank) => {
                if rank >= before {
                    break;
                }
                match evaluate_rank(grammar, algebra, rank, |child| cells[child].as_ref()) {
                    Ok(answer) => answers.push((rank, answer)),
                    Err(error) => return Ok((answers, Some((rank, error)))),
                }
            }
            Task::Tile(tile) => {
                answers
                    .try_reserve(tile.rows.len() * tile.columns.len())
                    .map_err(|_| Error::AllocationFailed)?;
                let base = answers.len();
                for row in tile.rows.clone() {
                    for column in tile.columns.clone() {
                        let rank = row * tile.stride + column;
                        if rank >= before {
                            return Ok((answers, None));
                        }
                        let lookup = |child| match tile.offset(child) {
                            Some(offset) => answers[base + offset].1.as_ref(),
                            None => cells[child].as_ref(),
                        };
                        match evaluate_rank(grammar, algebra, rank, lookup) {
                            Ok(answer) => answers.push((rank, answer)),
                            Err(error) => return Ok((answers, Some((rank, error)))),
                        }
                    }
                }
            }
        }
    }
    Ok((answers, None))
}

#[inline]
fn evaluate_rank<'a, G, A>(
    grammar: &G,
    algebra: &A,
    rank: Cell,
    lookup: impl Fn(Cell) -> Option<&'a A::Value> + Clone,
) -> Result<Option<A::Value>, Error>
where
    G: Program,
    A: Fold<G::Op>,
    A::Value: 'a,
{
    let mut chosen = Ok(None);
    grammar.rules_at(rank, |operator, children| {
        fold_rule(
            algebra,
            &mut chosen,
            &operator,
            children.iter().map(|&child| lookup(child)),
        )
    })?;
    chosen
}

fn wavefronts<G: Program>(grammar: &G) -> Result<Vec<Vec<Cell>>, Error> {
    let n = grammar.cell_count();
    let mut levels = reserve_table(n)?;
    levels.resize(n, 0);
    replay(grammar, |cell, _, _, _, children| {
        for &child in children {
            levels[cell] = levels[cell].max(levels[child] + 1);
        }
        Ok(())
    })?;
    let mut waves = Vec::<Vec<Cell>>::new();
    for (rank, level) in levels.into_iter().enumerate() {
        if waves.len() <= level {
            waves
                .try_reserve(level + 1 - waves.len())
                .map_err(|_| Error::AllocationFailed)?;
            waves.resize_with(level + 1, Vec::new);
        }
        waves[level]
            .try_reserve(1)
            .map_err(|_| Error::AllocationFailed)?;
        waves[level].push(rank);
    }
    Ok(waves)
}
