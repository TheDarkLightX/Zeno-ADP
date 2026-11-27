//! Report cost/count under individual pins and publish only optimum-unanimous rows.
//! This is a separate opt-in query; keeping the tape uses more memory than counting.
use super::interval_cover::{CoverError, Interval, Optimum, Pin};
use num_bigint::BigUint;

type Score = Option<Optimum>;
type Id = usize;
const EMPTY: Id = 0;
const ONE: Id = 1;

fn add(a: &Score, b: &Score) -> Score {
    use std::cmp::Ordering::*;
    match (a, b) {
        (None, _) => b.clone(),
        (_, None) => a.clone(),
        (Some(a), Some(b)) => match a.cost.cmp(&b.cost) {
            Less => Some(a.clone()),
            Greater => Some(b.clone()),
            Equal => Some(Optimum {
                cost: a.cost,
                count: &a.count + &b.count,
            }),
        },
    }
}

fn accumulate(sum: &mut Score, term: Score) {
    if let Some(value) = term {
        match sum {
            Some(best) if best.cost < value.cost => {}
            Some(best) if best.cost == value.cost => best.count += value.count,
            _ => *sum = Some(value),
        }
    }
}

fn mul(a: &Score, b: &Score) -> Score {
    let (a, b) = (a.as_ref()?, b.as_ref()?);
    Some(Optimum {
        // Every term charges each row at most once; on Rust's supported
        // pointer widths the sum of a slice of u64 prices fits in u128.
        cost: a.cost + b.cost,
        count: &a.count * &b.count,
    })
}

#[derive(Clone, Copy)]
enum Gate {
    Leaf,
    Add(Id, Id),
    Mul(Id, Id),
}

struct Tape {
    values: Vec<Score>,
    gates: Vec<Gate>,
}
impl Tape {
    fn new() -> Self {
        Self {
            values: vec![
                None,
                Some(Optimum {
                    cost: 0,
                    count: BigUint::from(1u8),
                }),
            ],
            gates: vec![Gate::Leaf, Gate::Leaf],
        }
    }
    fn node(&mut self, gate: Gate, value: Score) -> Id {
        let id = self.gates.len();
        self.gates.push(gate);
        self.values.push(value);
        id
    }
    fn tag(&mut self, w: u64) -> Id {
        self.node(
            Gate::Leaf,
            Some(Optimum {
                cost: u128::from(w),
                count: BigUint::from(1u8),
            }),
        )
    }
    fn either(&mut self, a: Id, b: Id) -> Id {
        if a == EMPTY {
            b
        } else if b == EMPTY {
            a
        } else {
            self.node(Gate::Add(a, b), add(&self.values[a], &self.values[b]))
        }
    }
    fn both(&mut self, a: Id, b: Id) -> Id {
        if a == EMPTY || b == EMPTY {
            EMPTY
        } else if a == ONE {
            b
        } else if b == ONE {
            a
        } else {
            self.node(Gate::Mul(a, b), mul(&self.values[a], &self.values[b]))
        }
    }
    fn outside(&self, root: Id) -> Vec<Score> {
        let mut d = vec![None; self.gates.len()];
        if root == EMPTY {
            return d;
        }
        d[root] = self.values[ONE].clone();
        for i in (2..=root).rev() {
            // Only leaf contexts are returned to the caller. Once an internal
            // gate is visited, move its contribution to its operands.
            if matches!(self.gates[i], Gate::Leaf) || d[i].is_none() {
                continue;
            }
            let context = d[i].take();
            match self.gates[i] {
                Gate::Leaf => unreachable!(),
                Gate::Add(a, b) => {
                    accumulate(&mut d[a], context.clone());
                    accumulate(&mut d[b], context);
                }
                Gate::Mul(a, b) => {
                    accumulate(&mut d[a], mul(&context, &self.values[b]));
                    accumulate(&mut d[b], mul(&context, &self.values[a]));
                }
            }
        }
        d
    }
}

#[derive(Clone, Copy)]
struct Range {
    start: usize,
    end: usize,
}
impl Range {
    fn split(self) -> (Self, Self) {
        let m = self.start + (self.end - self.start) / 2;
        (
            Self {
                start: self.start,
                end: m,
            },
            Self {
                start: m,
                end: self.end,
            },
        )
    }
}

#[derive(Clone, Copy)]
struct RowGates {
    end: usize,
    skip: Id,
    take: Id,
    stay: Id,
}

struct Chart {
    a: Vec<Id>,
    lazy: Vec<Id>,
    tape: Tape,
}
impl Chart {
    fn apply(&mut self, k: usize, g: Id) {
        if self.a[k] != EMPTY {
            self.a[k] = self.tape.both(self.a[k], g);
            if k < self.a.len() / 2 {
                self.lazy[k] = self.tape.both(self.lazy[k], g);
            }
        }
    }
    fn push(&mut self, k: usize) {
        let g = self.lazy[k];
        if g != ONE {
            self.apply(2 * k, g);
            self.apply(2 * k + 1, g);
            self.lazy[k] = ONE;
        }
    }
    fn pull(&mut self, k: usize) {
        self.a[k] = self.tape.either(self.a[2 * k], self.a[2 * k + 1]);
    }
    // Follow the path to the row end once. Whole siblings to its left
    // contribute their *old* states to the take branch, then keep only skips.
    // Siblings to its right keep their edge under either permitted choice.
    fn row(&mut self, k: usize, r: Range, row: RowGates, mut prior: Id) {
        if r.end - r.start == 1 {
            let advance = self.tape.both(prior, row.take);
            let stay = self.tape.both(self.a[k], row.stay);
            self.a[k] = self.tape.either(stay, advance);
            return;
        }
        self.push(k);
        let (left, right) = r.split();
        if row.end < left.end {
            self.apply(2 * k + 1, row.stay);
            self.row(2 * k, left, row, prior);
        } else {
            prior = self.tape.either(prior, self.a[2 * k]);
            self.apply(2 * k, row.skip);
            self.row(2 * k + 1, right, row, prior);
        }
        self.pull(k);
    }
    fn set(&mut self, k: usize, r: Range, i: usize, v: Id) {
        if r.end - r.start == 1 {
            self.a[k] = v;
            self.lazy[k] = ONE;
            return;
        }
        self.push(k);
        let (l, r) = r.split();
        if i < l.end {
            self.set(2 * k, l, i, v);
        } else {
            self.set(2 * k + 1, r, i, v);
        }
        self.pull(k);
    }
}

/// No row decision is published unless every globally optimal cover agrees.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Agreement {
    Included,
    Excluded,
    Varies,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RowDecision {
    pub exclude: Option<Optimum>,
    pub include: Option<Optimum>,
    pub agreement: Agreement,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Choice {
    pub optimum: Optimum,
    pub rows: Vec<RowDecision>,
}

impl Choice {
    /// Safe publication projection. Rows whose selections differ are omitted.
    pub fn unanimous_rows(&self) -> impl Iterator<Item = (usize, bool)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .filter_map(|(i, row)| match row.agreement {
                Agreement::Included => Some((i, true)),
                Agreement::Excluded => Some((i, false)),
                Agreement::Varies => None,
            })
    }
}

/// Analyze each single include/exclude constraint under the current pins.
/// `Ok(None)` means no cover, not a unanimous answer by vacuous truth.
/// Complexity: O((points + rows) log(points + 1)) arithmetic operations and
/// tape entries. Integer bit costs and memory are additional.
pub fn analyze(
    points: usize,
    rows: &[Interval],
    pins: &[Pin],
) -> Result<Option<Choice>, CoverError> {
    if !pins.is_empty() && pins.len() != rows.len() {
        return Err(CoverError::PinCount {
            expected: rows.len(),
            actual: pins.len(),
        });
    }
    for (row, &Interval { start, end, .. }) in rows.iter().enumerate() {
        if start >= end || end > points {
            return Err(CoverError::InvalidInterval {
                row,
                start,
                end,
                points,
            });
        }
    }
    let width = points
        .checked_add(1)
        .and_then(usize::checked_next_power_of_two)
        .ok_or(crate::Error::Overflow)?;
    let len = width.checked_mul(2).ok_or(crate::Error::Overflow)?;
    let mut events = crate::reserve_table(points)?;
    events.resize_with(points, Vec::new);
    let mut a = crate::reserve_table(len)?;
    let mut lazy = crate::reserve_table(len)?;
    a.resize(len, EMPTY);
    lazy.resize(len, ONE);
    let mut chart = Chart {
        a,
        lazy,
        tape: Tape::new(),
    };
    let whole = Range {
        start: 0,
        end: width,
    };
    chart.set(1, whole, 0, ONE);
    let mut labels = crate::reserve_table(rows.len())?;
    for (i, &Interval { start, end, cost }) in rows.iter().enumerate() {
        let pin = pins.get(i).copied().unwrap_or(Pin::Either);
        let skip = if pin == Pin::Include {
            EMPTY
        } else {
            chart.tape.tag(0)
        };
        let take = if pin == Pin::Exclude {
            EMPTY
        } else {
            chart.tape.tag(cost)
        };
        labels.push((skip, take));
        events[start].push((end, skip, take));
    }
    for (i, group) in events.into_iter().enumerate() {
        for (end, skip, take) in group {
            let stay = chart.tape.either(skip, take);
            chart.row(
                1,
                whole,
                RowGates {
                    end,
                    skip,
                    take,
                    stay,
                },
                EMPTY,
            );
        }
        chart.set(1, whole, i, EMPTY);
    }
    let root = chart.a[1];
    let Some(optimum) = chart.tape.values[root].clone() else {
        return Ok(None);
    };
    let outside = chart.tape.outside(root);
    let mut out = crate::reserve_table(rows.len())?;
    for (skip, take) in labels {
        let exclude = mul(&outside[skip], &chart.tape.values[skip]);
        let include = mul(&outside[take], &chart.tape.values[take]);
        let agreement = if exclude.as_ref() == Some(&optimum) {
            Agreement::Excluded
        } else if include.as_ref() == Some(&optimum) {
            Agreement::Included
        } else {
            Agreement::Varies
        };
        out.push(RowDecision {
            exclude,
            include,
            agreement,
        });
    }
    Ok(Some(Choice { optimum, rows: out }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fast::interval_cover::{solve, solve_chart};
    #[test]
    fn outside_counts_each_operand_of_a_shared_gate() {
        let mut tape = Tape::new();
        let leaf = tape.tag(3);
        let sum = tape.either(leaf, leaf);
        let root = tape.both(sum, sum);
        let outside = tape.outside(root);
        assert_eq!(
            outside[leaf],
            Some(Optimum {
                cost: 3,
                count: 8u8.into()
            })
        );
    }
    #[test]
    fn no_tie_break_publication_or_numeric_pruning() {
        let rows = [
            Interval {
                start: 0,
                end: 1,
                cost: 1,
            },
            Interval {
                start: 0,
                end: 1,
                cost: 1,
            },
            Interval {
                start: 0,
                end: 1,
                cost: 5,
            },
        ];
        let out = analyze(1, &rows, &[]).unwrap().unwrap();
        assert_eq!(out.optimum.count, BigUint::from(2u8));
        assert_eq!(
            out.rows.iter().map(|r| r.agreement).collect::<Vec<_>>(),
            [Agreement::Varies, Agreement::Varies, Agreement::Excluded]
        );
        assert_eq!(out.unanimous_rows().collect::<Vec<_>>(), [(2, false)]);
        assert_eq!(out.rows[2].include.as_ref().unwrap().cost, 5);
        assert!(analyze(2, &rows, &[]).unwrap().is_none());
        assert_eq!(
            analyze(0, &[], &[]).unwrap().unwrap().optimum.count,
            BigUint::from(1u8)
        );
    }
    #[test]
    fn reversible_slices_match_chart_with_independent_pins() {
        let mut rng = 0x5cd93b71abb0u64;
        let mut rand = |k| {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            ((rng >> 32) as usize) % k
        };
        for _ in 0..350 {
            let n = 1 + rand(6);
            let rows: Vec<_> = (0..rand(10))
                .map(|_| {
                    let start = rand(n);
                    Interval {
                        start,
                        end: start + 1 + rand(n - start),
                        cost: rand(5) as u64,
                    }
                })
                .collect();
            let mut pins = vec![Pin::Either; rows.len()];
            if !pins.is_empty() && rand(2) == 0 {
                pins[rand(rows.len())] = if rand(2) == 0 {
                    Pin::Exclude
                } else {
                    Pin::Include
                };
            }
            let actual = analyze(n, &rows, &pins).unwrap();
            assert_eq!(
                actual.as_ref().map(|r| r.optimum.clone()),
                solve(n, &rows, &pins).unwrap()
            );
            if let Some(actual) = actual {
                for (i, row) in actual.rows.iter().enumerate() {
                    for (q, a) in [(Pin::Include, &row.include), (Pin::Exclude, &row.exclude)] {
                        if pins[i] != Pin::Either && pins[i] != q {
                            assert!(a.is_none());
                            continue;
                        }
                        let mut intervention = pins.clone();
                        intervention[i] = q;
                        assert_eq!(*a, solve_chart(n, &rows, &intervention).unwrap());
                    }
                }
            }
        }
    }
}
