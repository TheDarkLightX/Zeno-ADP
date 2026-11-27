//! Exact minimum-cost interval covers, counting distinct tied row selections.
//!
//! Each row has its own identity (its index), even if another row has an
//! identical footprint and price. A zero-price redundant row may therefore
//! contribute an additional optimum. This is not a count of cover paths.
//! The default and range solvers use O((points + rows) log(points + 2)) arithmetic
//! operations and O(points + rows) entries, excluding the bit cost of counts.

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigUint;

use crate::{reserve_table, tabulate, Algebra, Chart, Error, Operator, Rule};

/// A nonempty half-open interval of points with a nonnegative price.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub start: usize,
    pub end: usize,
    pub cost: u64,
}

/// Restriction on one row. An empty pin slice means all rows are unrestricted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pin {
    Either,
    Include,
    Exclude,
}

/// Optimum cost and exact number of attaining sets. `None` denotes infeasible.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Optimum {
    pub cost: u128,
    pub count: BigUint,
}

#[derive(Debug, PartialEq, Eq)]
pub enum CoverError {
    InvalidSparseLimit {
        limit: usize,
    },
    PinCount {
        expected: usize,
        actual: usize,
    },
    InvalidInterval {
        row: usize,
        start: usize,
        end: usize,
        points: usize,
    },
    Engine(Error),
}

impl From<Error> for CoverError {
    fn from(error: Error) -> Self {
        Self::Engine(error)
    }
}

impl fmt::Display for CoverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSparseLimit { limit } => {
                write!(f, "sparse limit must be positive, got {limit}")
            }
            Self::PinCount { expected, actual } => {
                write!(
                    f,
                    "expected {expected} pins or an empty slice, got {actual}"
                )
            }
            Self::InvalidInterval {
                row,
                start,
                end,
                points,
            } => {
                write!(
                    f,
                    "row {row}: invalid interval [{start}, {end}) for {points} points"
                )
            }
            Self::Engine(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for CoverError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Engine(error) => Some(error),
            _ => None,
        }
    }
}

type Score = Option<Optimum>;

impl Optimum {
    fn seed() -> Self {
        Self {
            cost: 0,
            count: BigUint::from(1_u8),
        }
    }

    fn pay(&mut self, cost: u64) -> Result<(), Error> {
        self.cost = self.cost.checked_add(cost.into()).ok_or(Error::Overflow)?;
        Ok(())
    }
}

fn merge(out: &mut Score, x: &Optimum) {
    match out.as_mut() {
        None => *out = Some(x.clone()),
        Some(y) => match x.cost.cmp(&y.cost) {
            Ordering::Less => *y = x.clone(),
            Ordering::Equal => y.count += &x.count,
            Ordering::Greater => {}
        },
    }
}

fn union(a: &Score, b: &Score) -> Score {
    match (a, b) {
        (Some(x), Some(y)) if x.cost == y.cost => Some(Optimum {
            cost: x.cost,
            count: &x.count + &y.count,
        }),
        (Some(x), Some(y)) if x.cost <= y.cost => Some(x.clone()),
        (_, Some(y)) => Some(y.clone()),
        (Some(x), None) => Some(x.clone()),
        (None, None) => None,
    }
}

#[derive(Debug, Clone, Copy, Default)]
enum Pending {
    #[default]
    Identity,
    Clear,
    Shift(usize),
}

#[derive(Default)]
struct Node {
    answer: Score,
    lazy: Pending,
}

struct Tree {
    cells: Vec<Node>,
    leaves: usize,
}

impl Tree {
    fn new(width: usize) -> Result<Self, Error> {
        let leaves = width.checked_next_power_of_two().ok_or(Error::Overflow)?;
        let length = leaves.checked_mul(2).ok_or(Error::Overflow)?;
        let mut cells = reserve_table(length)?;
        cells.resize_with(length, Node::default);
        Ok(Self { cells, leaves })
    }

    fn apply(&mut self, i: usize, action: Pending) -> Result<(), Error> {
        let node = &mut self.cells[i];
        let Some(x) = node.answer.as_mut() else {
            // This range is already empty, including under any pending clear.
            return Ok(());
        };
        match action {
            Pending::Identity => {}
            Pending::Clear => {
                node.answer = None;
                node.lazy = Pending::Clear;
            }
            Pending::Shift(s) => {
                x.count <<= s;
                if i < self.leaves {
                    node.lazy = match node.lazy {
                        Pending::Shift(old) => {
                            Pending::Shift(old.checked_add(s).ok_or(Error::Overflow)?)
                        }
                        _ => Pending::Shift(s),
                    };
                }
            }
        }
        Ok(())
    }

    fn push(&mut self, i: usize) -> Result<(), Error> {
        let action = std::mem::take(&mut self.cells[i].lazy);
        self.apply(i * 2, action)?;
        self.apply(i * 2 + 1, action)
    }

    fn pull(&mut self, i: usize) {
        self.cells[i].answer = union(&self.cells[i * 2].answer, &self.cells[i * 2 + 1].answer);
    }

    fn insert(
        &mut self,
        i: usize,
        l: usize,
        r: usize,
        idx: usize,
        x: Optimum,
    ) -> Result<(), Error> {
        if r - l == 1 {
            merge(&mut self.cells[i].answer, &x);
            self.cells[i].lazy = Pending::Identity;
            return Ok(());
        }
        self.push(i)?;
        let mid = l + (r - l) / 2;
        if idx < mid {
            self.insert(i * 2, l, mid, idx, x)?;
        } else {
            self.insert(i * 2 + 1, mid, r, idx, x)?;
        }
        self.pull(i);
        Ok(())
    }

    fn prefix(&mut self, i: usize, l: usize, r: usize, end: usize) -> Result<Score, Error> {
        if end <= l || self.cells[i].answer.is_none() {
            Ok(None)
        } else if r <= end {
            Ok(self.cells[i].answer.clone())
        } else {
            self.push(i)?;
            let mid = l + (r - l) / 2;
            let a = self.prefix(i * 2, l, mid, end)?;
            let b = self.prefix(i * 2 + 1, mid, r, end)?;
            Ok(union(&a, &b))
        }
    }

    fn update(
        &mut self,
        i: usize,
        l: usize,
        r: usize,
        range: (usize, usize),
        action: Pending,
    ) -> Result<(), Error> {
        if range.1 <= l || r <= range.0 || self.cells[i].answer.is_none() {
            return Ok(());
        }
        if range.0 <= l && r <= range.1 {
            return self.apply(i, action);
        }
        self.push(i)?;
        let mid = l + (r - l) / 2;
        self.update(i * 2, l, mid, range, action)?;
        self.update(i * 2 + 1, mid, r, range, action)?;
        self.pull(i);
        Ok(())
    }
}

struct Menu {
    events: Vec<Vec<(Interval, Pin)>>,
    width: usize,
    rows: usize,
}

fn menu(points: usize, rows: &[Interval], pins: &[Pin]) -> Result<Menu, CoverError> {
    if !pins.is_empty() && pins.len() != rows.len() {
        return Err(CoverError::PinCount {
            expected: rows.len(),
            actual: pins.len(),
        });
    }
    let width = points.checked_add(1).ok_or(Error::Overflow)?;
    for (i, &row) in rows.iter().enumerate() {
        if row.start >= row.end || row.end > points {
            return Err(CoverError::InvalidInterval {
                row: i,
                start: row.start,
                end: row.end,
                points,
            });
        }
    }
    let mut events = reserve_table(points)?;
    events.resize_with(points, Vec::new);
    let mut n = 0;
    for (i, &row) in rows.iter().enumerate() {
        let pin = pins.get(i).copied().unwrap_or(Pin::Either);
        if pin != Pin::Exclude {
            events[row.start].push((row, pin));
            n += 1;
        }
    }
    Ok(Menu {
        events,
        width,
        rows: n,
    })
}

// Sparse rows scan or shift up to one frontier. The tree touches O(height)
// nodes for each prefix, update and insertion. Calibrate their relative cost
// using the peak live edges / tree height where forced-mode times cross.
// On 2026-11-27, Ryzen Threadripper 1950X, CPU 22, Rust 1.97.1:
// taskset -c 22 cargo run --release --offline --locked --example interval_cover_cross_bench -- --grid
// Log interpolation between adjacent mixed sizes gave 31.0, 44.0 and 42.6
// edges/level for 1, 3 and 6 rows/point. Round the median to 43.
// Narrow independent menus peaked at two live edges at every size.
fn default_sparse_limit(points: usize) -> usize {
    let height = (usize::BITS - points.leading_zeros()) as usize; // ceil(log2(points + 1))
    43 * height.max(1)
}

enum Sweep {
    Sparse(Vec<(usize, Optimum)>),
    Range(Tree),
}

impl Sweep {
    fn range(width: usize, states: Vec<(usize, Optimum)>) -> Result<Self, Error> {
        let mut t = Tree::new(width)?;
        for (edge, v) in states {
            t.insert(1, 0, t.leaves, edge, v)?;
        }
        Ok(Self::Range(t))
    }

    fn take_row(
        &mut self,
        width: usize,
        sparse_limit: usize,
        row: Interval,
        pin: Pin,
    ) -> Result<(), Error> {
        // Required-row prices are accounted for once in the caller's fixed cost.
        let end = row.end;
        let required = pin == Pin::Include;
        let mut prior = None;
        match self {
            Self::Sparse(active) => {
                let split = active.partition_point(|(edge, _)| *edge < end);
                for (_, score) in &active[..split] {
                    merge(&mut prior, score);
                }
                let mut insert_at = split;
                if required {
                    active.drain(..split);
                    insert_at = 0;
                } else if row.cost == 0 {
                    for (_, score) in &mut active[split..] {
                        score.count <<= 1usize;
                    }
                }
                if let Some(mut score) = prior {
                    if !required {
                        score.pay(row.cost)?;
                    }
                    if let Some((_, prev)) =
                        active.get_mut(insert_at).filter(|(edge, _)| *edge == end)
                    {
                        match score.cost.cmp(&prev.cost) {
                            Ordering::Less => *prev = score,
                            Ordering::Equal => prev.count += score.count,
                            Ordering::Greater => {}
                        }
                    } else {
                        active.insert(insert_at, (end, score));
                    }
                }
                if active.len() > sparse_limit {
                    *self = Self::range(width, std::mem::take(active))?;
                }
            }
            Self::Range(tree) => {
                let leaves = tree.leaves;
                let prior = tree.prefix(1, 0, leaves, end)?;
                if required {
                    tree.update(1, 0, leaves, (0, end), Pending::Clear)?;
                } else if row.cost == 0 {
                    tree.update(1, 0, leaves, (end, leaves), Pending::Shift(1))?;
                }
                if let Some(mut score) = prior {
                    if !required {
                        score.pay(row.cost)?;
                    }
                    tree.insert(1, 0, leaves, end, score)?;
                }
            }
        }
        Ok(())
    }

    fn retire(&mut self, point: usize) -> Result<(), Error> {
        match self {
            Self::Sparse(active) => {
                if active.first().is_some_and(|(edge, _)| *edge == point) {
                    active.remove(0);
                }
            }
            Self::Range(tree) => tree.update(1, 0, tree.leaves, (0, point + 1), Pending::Clear)?,
        }
        Ok(())
    }

    fn answer(self, points: usize) -> Score {
        match self {
            Self::Sparse(mut states) => states
                .pop()
                .filter(|(edge, _)| *edge == points)
                .map(|(_, score)| score),
            Self::Range(mut tree) => tree.cells[1].answer.take(),
        }
    }
}

fn run(
    points: usize,
    rows: &[Interval],
    pins: &[Pin],
    sparse_limit: usize,
) -> Result<Score, CoverError> {
    let menu = menu(points, rows, pins)?;
    let initial = vec![(0, Optimum::seed())];
    let mut sweep = if sparse_limit == 0 {
        Sweep::range(menu.width, initial)?
    } else {
        Sweep::Sparse(initial)
    };
    let mut fixed_cost = 0_u128;
    for (point, events) in menu.events.into_iter().enumerate() {
        for (row, pin) in events {
            if pin == Pin::Include {
                fixed_cost = fixed_cost
                    .checked_add(row.cost.into())
                    .ok_or(Error::Overflow)?;
            }
            sweep.take_row(menu.width, sparse_limit, row, pin)?;
        }
        sweep.retire(point)?;
    }
    let mut answer = sweep.answer(points);
    if let Some(x) = answer.as_mut() {
        x.cost = x.cost.checked_add(fixed_cost).ok_or(Error::Overflow)?;
    }
    Ok(answer)
}

/// Return minimum cost and the number of distinct attaining subsets.
/// Begin with sparse states and promote once the frontier widens.
/// For zero points the empty menu has one optimum at cost zero.
pub fn solve(points: usize, rows: &[Interval], pins: &[Pin]) -> Result<Score, CoverError> {
    run(points, rows, pins, default_sparse_limit(points))
}

/// Start sparse and promote after a row leaves more than `limit` live boundaries.
/// A limit of zero is invalid. Use [`solve_range`] to start in range mode,
/// or `usize::MAX` to keep all reachable boundaries sparse.
pub fn solve_with_sparse_limit(
    points: usize,
    rows: &[Interval],
    pins: &[Pin],
    limit: usize,
) -> Result<Score, CoverError> {
    if limit == 0 {
        return Err(CoverError::InvalidSparseLimit { limit });
    }
    run(points, rows, pins, limit)
}

/// Range-table implementation, for comparison or for callers that know
/// the frontier will be wide early.
pub fn solve_range(points: usize, rows: &[Interval], pins: &[Pin]) -> Result<Score, CoverError> {
    run(points, rows, pins, 0)
}

#[derive(Clone, Copy)]
enum Branch {
    Seed,
    Move(u64),
}

impl Operator for Branch {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Move(_)))
    }
}

struct MinCount;

impl Algebra<Branch> for MinCount {
    type Value = Optimum;

    fn apply(&self, op: &Branch, children: &[&Optimum]) -> Result<Optimum, Error> {
        match op {
            Branch::Seed => Ok(Optimum::seed()),
            Branch::Move(cost) => {
                let mut x = children[0].clone();
                x.pay(*cost)?;
                Ok(x)
            }
        }
    }

    fn choose(&self, candidates: &[Optimum]) -> Result<Vec<Optimum>, Error> {
        let mut chosen = None;
        for x in candidates {
            merge(&mut chosen, x);
        }
        Ok(chosen.into_iter().collect())
    }
}

struct Reference {
    chart: Chart<Branch>,
}

fn reference(points: usize, rows: &[Interval], pins: &[Pin]) -> Result<Reference, CoverError> {
    let menu = menu(points, rows, pins)?;
    let stages = menu.width.checked_add(menu.rows).ok_or(Error::Overflow)?;
    let mut cells = reserve_table(menu.width.checked_mul(stages).ok_or(Error::Overflow)?)?;
    cells.resize_with(menu.width, Vec::new);
    cells[0].push(Rule::new(Branch::Seed, vec![]));
    let mut base = 0;
    for (point, events) in menu.events.into_iter().enumerate() {
        for (row, pin) in events {
            let next = cells.len();
            cells.resize_with(next + menu.width, Vec::new);
            for q in 0..menu.width {
                if pin == Pin::Either {
                    cells[next + q].push(Rule::new(Branch::Move(0), vec![base + q]));
                }
                cells[next + q.max(row.end)]
                    .push(Rule::new(Branch::Move(row.cost), vec![base + q]));
            }
            base = next;
        }
        let next = cells.len();
        cells.resize_with(next + menu.width, Vec::new);
        for q in point + 1..menu.width {
            cells[next + q].push(Rule::new(Branch::Move(0), vec![base + q]));
        }
        base = next;
    }
    Ok(Reference {
        chart: Chart::new(cells, base + points)?,
    })
}

/// Explicit reference chart, provided for auditing small cases. This method
/// materializes O((points + 1)(points + rows + 1)) cells.
pub fn solve_chart(points: usize, rows: &[Interval], pins: &[Pin]) -> Result<Score, CoverError> {
    let chart = reference(points, rows, pins)?;
    Ok(tabulate(&chart.chart, &MinCount)?.pop())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn automatic_limit_spans_the_measured_crossover() {
        // The 1,024-point mixed menu peaks at 258 edges and favours sparse
        // at each measured density. Range wins at 1,026 edges / 4,096 points.
        assert!(default_sparse_limit(1024) >= 258);
        assert!(default_sparse_limit(4096) < 1026);
        assert!(default_sparse_limit(0) > 0);
        assert!(default_sparse_limit(usize::MAX) > default_sparse_limit(4096));
    }
}
