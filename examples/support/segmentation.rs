//! Change-point detection for binary observations, with an exact mismatch cost.

use zeno_adp::algebras::{Additive, Cost, ScoredOperator};
use zeno_adp::{compiled_grammar, Error, Operator};

/// Each fitted segment pays for a new level as well as its mismatches.
const SEGMENT_PENALTY: i64 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Segment {
    Empty,
    Append { start: usize, end: usize, cost: i64 },
}

impl Operator for Segment {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Append { .. }))
    }
}

impl ScoredOperator for Segment {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Empty => 0,
            Self::Append { cost, .. } => cost,
        })
    }
}

/// Cumulative number of ones before and after each observation.
#[derive(Clone, Copy)]
pub struct Observation {
    before: i64,
    after: i64,
}

pub fn prepare(bits: &[bool]) -> Vec<Observation> {
    let mut ones = 0;
    bits.iter()
        .map(|&bit| {
            let before = ones;
            ones += i64::from(bit);
            Observation {
                before,
                after: ones,
            }
        })
        .collect()
}

pub fn segment_cost(input: &[Observation], start: usize, end: usize) -> Result<i64, Error> {
    let ones = input[end - 1].after - input[start].before;
    let width = i64::try_from(end - start).map_err(|_| Error::Overflow)?;
    // Fit the majority level on this segment.
    SEGMENT_PENALTY
        .checked_add(ones.min(width - ones))
        .ok_or(Error::Overflow)
}

compiled_grammar! {
    pub fn grammar(input: Observation) -> Segment {
        prefix |input, start, end|;
        empty Empty => Ok(Some(Segment::Empty));
        extend Append(split) => Ok(Some(Segment::Append {
            start: split, end, cost: segment_cost(input, split, end)?,
        }));
    }
    with pub fn minimum: Additive = Additive::default();
}

pub fn direct(input: &[Observation]) -> Result<Vec<i64>, Error> {
    let mut scores = Vec::with_capacity(input.len() + 1);
    scores.push(0_i64);
    for end in 1..=input.len() {
        let mut best = i64::MAX;
        for (split, &past) in scores.iter().enumerate() {
            let cost = segment_cost(input, split, end)?;
            best = best.min(cost.checked_add(past).ok_or(Error::Overflow)?);
        }
        scores.push(best);
    }
    Ok(scores)
}
