//! Ranked grammars over subsets of a finite indexed carrier.

use crate::{Chart, Error, Operator, Rule};

/// A partition is a chain of disjoint blocks in order of least member.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PartitionOp {
    Empty,
    Block(usize),
}

impl Operator for PartitionOp {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Block(_)))
    }
}

/// Construct the set partition grammar on element indices zero through
/// the carrier size minus one. A cell's rank is its subset's bit mask.
/// The root is the full carrier. The predicate sees nonempty blocks once
/// each, in increasing mask order. An empty carrier has one partition.
///
/// Storage grows exponentially. The carrier size must allow its power set
/// length to be represented as a machine word and as a chart allocation.
pub fn partitions(
    elements: u32,
    allowed_block: impl Fn(usize) -> bool,
) -> Result<Chart<PartitionOp>, Error> {
    let size = 1usize.checked_shl(elements).ok_or(Error::Overflow)?;
    let mut cells = Vec::new();
    cells.try_reserve_exact(size).map_err(|_| Error::Overflow)?;
    let mut allowed = Vec::new();
    allowed
        .try_reserve_exact(size)
        .map_err(|_| Error::Overflow)?;
    allowed.push(false);
    allowed.extend((1..size).map(allowed_block));

    cells.push(vec![Rule::new(PartitionOp::Empty, [])]);
    for set in 1..size {
        let anchor = 1usize << set.trailing_zeros();
        let optional = set ^ anchor;
        let mut tail = optional;
        let mut rules = Vec::new();
        loop {
            let block = anchor | tail;
            if allowed[block] {
                rules.push(Rule::new(PartitionOp::Block(block), [set ^ block]));
            }
            if tail == 0 {
                break;
            }
            tail = (tail - 1) & optional;
        }
        cells.push(rules);
    }
    Chart::new(cells, size - 1)
}

/// Bind the set partition schedule without retaining any productions.
/// The predicate is evaluated once per nonempty mask, in increasing order.
pub fn partition_source(
    elements: u32,
    allowed_block: impl Fn(usize) -> bool,
) -> Result<impl crate::compiled::Program<Op = PartitionOp>, Error> {
    let size = 1usize.checked_shl(elements).ok_or(Error::Overflow)?;
    let mut allowed = crate::reserve_table(size)?;
    allowed.push(false);
    allowed.extend((1..size).map(allowed_block));
    Ok(crate::compiled::generated::Ranked(Partitions(allowed)))
}

struct Partitions(Vec<bool>);

impl crate::compiled::generated::Layout for Partitions {
    type Op = PartitionOp;

    fn cell_count(&self) -> usize {
        self.0.len()
    }

    fn root(&self) -> crate::Cell {
        self.0.len() - 1
    }

    #[inline]
    fn emit(
        &self,
        set: crate::Cell,
        sink: &mut impl crate::compiled::ProductionSink<PartitionOp>,
    ) -> Result<(), Error> {
        if set == 0 {
            return sink.rule("Empty", PartitionOp::Empty, []);
        }
        let anchor = set & set.wrapping_neg();
        let optional = set ^ anchor;
        let mut tail = optional;
        loop {
            let block = anchor | tail;
            if self.0[block] {
                sink.rule("Block", PartitionOp::Block(block), [optional ^ tail])?;
            }
            if tail == 0 {
                return Ok(());
            }
            tail = (tail - 1) & optional;
        }
    }
}
