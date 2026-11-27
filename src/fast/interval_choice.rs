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
            if d[i].is_none() {
                continue;
            }
            match self.gates[i] {
                Gate::Leaf => {}
                Gate::Add(a, b) => {
                    d[a] = add(&d[a], &d[i]);
                    d[b] = add(&d[b], &d[i]);
                }
                Gate::Mul(a, b) => {
                    d[a] = add(&d[a], &mul(&d[i], &self.values[b]));
                    d[b] = add(&d[b], &mul(&d[i], &self.values[a]));
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

struct Chart {
    a: Vec<Id>,
    lazy: Vec<Id>,
    tape: Tape,
}
impl Chart {
    fn apply(&mut self, k: usize, g: Id) {
        if self.a[k] != EMPTY {
            self.a[k] = self.tape.both(self.a[k], g);
            self.lazy[k] = self.tape.both(self.lazy[k], g);
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
    fn scale(&mut self, k: usize, r: Range, s: Range, g: Id) {
        if self.a[k] == EMPTY || r.end <= s.start || s.end <= r.start {
            return;
        }
        if s.start <= r.start && r.end <= s.end {
            self.apply(k, g);
            return;
        }
        self.push(k);
        let (l, r) = r.split();
        self.scale(2 * k, l, s, g);
        self.scale(2 * k + 1, r, s, g);
        self.pull(k);
    }
    fn prefix(&mut self, k: usize, r: Range, end: usize) -> Id {
        if end <= r.start || self.a[k] == EMPTY {
            return EMPTY;
        }
        if r.end <= end {
            return self.a[k];
        }
        self.push(k);
        let (l, r) = r.split();
        let a = self.prefix(2 * k, l, end);
        let b = self.prefix(2 * k + 1, r, end);
        self.tape.either(a, b)
    }
    fn point(&mut self, k: usize, r: Range, i: usize, v: Id, combine: bool) {
        if r.end - r.start == 1 {
            self.a[k] = if combine {
                self.tape.either(self.a[k], v)
            } else {
                v
            };
            self.lazy[k] = ONE;
            return;
        }
        self.push(k);
        let (l, r) = r.split();
        if i < l.end {
            self.point(2 * k, l, i, v, combine);
        } else {
            self.point(2 * k + 1, r, i, v, combine);
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
    chart.point(1, whole, 0, ONE, false);
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
            let a = chart.prefix(1, whole, end);
            let advance = chart.tape.both(a, take);
            chart.scale(1, whole, Range { start: 0, end }, skip);
            let stay = chart.tape.either(skip, take);
            chart.scale(
                1,
                whole,
                Range {
                    start: end,
                    end: width,
                },
                stay,
            );
            chart.point(1, whole, end, advance, true);
        }
        chart.point(1, whole, i, EMPTY, false);
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
