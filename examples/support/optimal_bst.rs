//! Optimal binary search tree for successful lookups with known frequencies.

use zeno_adp::algebras::{Additive, Cost, ScoredOperator};
use zeno_adp::{compiled_grammar, Error, Operator};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SearchTree {
    Empty,
    Key { index: usize, cost: i64 },
}

impl Operator for SearchTree {
    fn arity(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Key { .. } => 2,
        }
    }
}

impl ScoredOperator for SearchTree {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Empty => 0,
            Self::Key { cost, .. } => cost,
        })
    }
}

/// Cumulative lookup frequencies before and after a key in sorted order.
#[derive(Clone, Copy)]
pub struct Frequency {
    before: i64,
    after: i64,
}

pub fn prepare(frequencies: &[u32]) -> Result<Vec<Frequency>, Error> {
    let mut total = 0_i64;
    frequencies
        .iter()
        .map(|&frequency| {
            let before = total;
            total = total
                .checked_add(i64::from(frequency))
                .ok_or(Error::Overflow)?;
            Ok(Frequency {
                before,
                after: total,
            })
        })
        .collect()
}

pub fn interval_mass(input: &[Frequency], start: usize, end: usize) -> i64 {
    input[end - 1].after - input[start].before
}

compiled_grammar! {
    pub fn grammar(input: Frequency) -> SearchTree {
        interval |input, start, end|;
        empty Empty => Ok(Some(SearchTree::Empty));
        pivot Key(root) => Ok(Some(SearchTree::Key {
            index: root, cost: interval_mass(input, start, end),
        }));
    }
    with pub fn minimum: Additive = Additive::default();
}

pub fn direct(input: &[Frequency]) -> Result<Vec<i64>, Error> {
    // Each row is one right endpoint, with the empty interval first.
    let mut offsets = Vec::with_capacity(input.len() + 1);
    let mut count = 0_usize;
    for end in 0..=input.len() {
        offsets.push(count);
        count = count.checked_add(end + 1).ok_or(Error::Overflow)?;
    }
    let mut scores = Vec::with_capacity(count);
    for end in 0..=input.len() {
        scores.push(0_i64);
        for start in (0..end).rev() {
            let cost = interval_mass(input, start, end);
            let mut best = i64::MAX;
            for root in start..end {
                let left = scores[offsets[root] + (root - start)];
                let right = scores[offsets[end] + (end - root - 1)];
                let candidate = cost
                    .checked_add(left)
                    .and_then(|x| x.checked_add(right))
                    .ok_or(Error::Overflow)?;
                best = best.min(candidate);
            }
            scores.push(best);
        }
    }
    Ok(scores)
}
