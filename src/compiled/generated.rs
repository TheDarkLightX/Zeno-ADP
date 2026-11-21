//! Implementation of the generated single-track grammar schedules.

use std::marker::PhantomData;

use crate::fast::{Fold, RuleSource, Table};
use crate::{reserve_table, validate_arity, Cell, Error, Operator};

use super::{sealed, ProductionSink, Program};

/// Evaluate a paired algebra after constructing it in the caller's scope.
pub fn tabulate<G: Program, A: Fold<G::Op>>(
    algebra: A,
    grammar: Result<G, Error>,
) -> Result<Table<A::Value>, Error> {
    super::tabulate(&grammar?, &algebra)
}

/// Implementation hook for [`crate::compiled_grammar!`].
pub trait Rules<T, O, const PREFIX: bool> {
    fn emit(
        &self,
        input: &[T],
        cell: &mut AtCell<'_, O, impl ProductionSink<O>, PREFIX>,
    ) -> Result<(), Error>;
}

impl<T, O, const PREFIX: bool, Head, Tail> Rules<T, O, PREFIX> for (Head, Tail)
where
    Head: Rules<T, O, PREFIX>,
    Tail: Rules<T, O, PREFIX>,
{
    #[inline]
    fn emit(
        &self,
        input: &[T],
        cell: &mut AtCell<'_, O, impl ProductionSink<O>, PREFIX>,
    ) -> Result<(), Error> {
        self.0.emit(input, cell)?;
        self.1.emit(input, cell)
    }
}

pub struct Empty<F>(pub &'static str, pub F);
pub struct Extend<F>(pub &'static str, pub F);
pub struct Pivot<F>(pub &'static str, pub F);

impl<T, O, F, const PREFIX: bool> Rules<T, O, PREFIX> for Empty<F>
where
    O: Operator,
    F: Fn(&[T], usize, usize) -> Result<Option<O>, Error>,
{
    #[inline]
    fn emit(
        &self,
        input: &[T],
        cell: &mut AtCell<'_, O, impl ProductionSink<O>, PREFIX>,
    ) -> Result<(), Error> {
        if cell.start == cell.end {
            if let Some(operator) = (self.1)(input, cell.start, cell.end)? {
                cell.rule(self.0, operator, [])?;
            }
        }
        Ok(())
    }
}

impl<T, O, F> Rules<T, O, true> for Extend<F>
where
    O: Operator,
    F: Fn(&[T], usize, usize, usize) -> Result<Option<O>, Error>,
{
    #[inline]
    fn emit(
        &self,
        input: &[T],
        cell: &mut AtCell<'_, O, impl ProductionSink<O>, true>,
    ) -> Result<(), Error> {
        for split in 0..cell.end {
            if let Some(operator) = (self.1)(input, cell.start, cell.end, split)? {
                cell.rule(self.0, operator, [split])?;
            }
        }
        Ok(())
    }
}

impl<T, O, F> Rules<T, O, false> for Pivot<F>
where
    O: Operator,
    F: Fn(&[T], usize, usize, usize) -> Result<Option<O>, Error>,
{
    #[inline]
    fn emit(
        &self,
        input: &[T],
        cell: &mut AtCell<'_, O, impl ProductionSink<O>, false>,
    ) -> Result<(), Error> {
        // The left row advances with the pivot. The first right child
        // precedes the parent by one rank and the remaining children
        // advance toward the beginning of that same row.
        let offsets = &cell.offsets[cell.start..cell.end];
        let mut right = cell.rank;
        for (index, &row) in offsets.iter().enumerate() {
            right -= 1;
            if let Some(operator) = (self.1)(input, cell.start, cell.end, cell.start + index)? {
                cell.rule(self.0, operator, [row + index, right])?;
            }
        }
        Ok(())
    }
}

/// A bound, statically generated grammar.
pub struct Generated<'a, T, O, R, const PREFIX: bool> {
    input: &'a [T],
    offsets: Vec<usize>,
    count: usize,
    rules: R,
    operator: PhantomData<fn() -> O>,
}

impl<'a, T, O, R, const PREFIX: bool> Generated<'a, T, O, R, PREFIX> {
    pub fn bind(input: &'a [T], rules: R) -> Result<Self, Error> {
        let boundaries = input.len().checked_add(1).ok_or(Error::Overflow)?;
        let (offsets, count) = if PREFIX {
            (Vec::new(), boundaries)
        } else {
            let size = (boundaries as u128) * (boundaries as u128 + 1) / 2;
            let count = usize::try_from(size).map_err(|_| Error::Overflow)?;
            let mut offsets = reserve_table(boundaries)?;
            let mut next = 0;
            for end in 0..boundaries {
                offsets.push(next);
                next += end + 1;
            }
            (offsets, count)
        };
        Ok(Self {
            input,
            offsets,
            count,
            rules,
            operator: PhantomData,
        })
    }
}

impl<T, O: Operator, R: Rules<T, O, PREFIX>, const PREFIX: bool> Generated<'_, T, O, R, PREFIX> {
    #[inline]
    fn emit(
        &self,
        rank: Cell,
        start: usize,
        end: usize,
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error> {
        self.rules.emit(
            self.input,
            &mut AtCell {
                rank,
                start,
                end,
                offsets: &self.offsets,
                sink,
                operator: PhantomData,
            },
        )
    }
}

impl<T, O: Operator, R: Rules<T, O, PREFIX>, const PREFIX: bool> RuleSource
    for Generated<'_, T, O, R, PREFIX>
{
    type Op = O;

    fn cell_count(&self) -> usize {
        self.count
    }

    fn root(&self) -> Cell {
        // The prefix ending at n, or the last interval ending at n, starts at 0.
        self.count - 1
    }

    fn rules_at(
        &self,
        rank: Cell,
        emit: impl FnMut(Self::Op, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if rank >= self.count {
            return Err(Error::CellOutOfRange(rank));
        }
        let (start, end) = if PREFIX {
            (0, rank)
        } else {
            let end = self.offsets.partition_point(|&offset| offset <= rank) - 1;
            (end - (rank - self.offsets[end]), end)
        };
        self.emit(rank, start, end, &mut Visit(emit))
    }
}

struct Visit<F>(F);

impl<O, F: FnMut(O, &[Cell]) -> Result<(), Error>> ProductionSink<O> for Visit<F> {
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        (self.0)(operator, children)
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        Ok(())
    }
}

impl<T, O, R, const PREFIX: bool> sealed::Sealed for Generated<'_, T, O, R, PREFIX> {}

impl<T, O: Operator, R: Rules<T, O, PREFIX>, const PREFIX: bool> Program
    for Generated<'_, T, O, R, PREFIX>
{
    #[inline]
    fn fill(&self, output: &mut impl ProductionSink<O>) -> Result<(), Error> {
        let mut rank = 0;
        for end in 0..=self.input.len() {
            if PREFIX {
                self.emit(rank, 0, end, output)?;
                output.finish_cell()?;
                rank += 1;
            } else {
                for start in (0..=end).rev() {
                    self.emit(rank, start, end, output)?;
                    output.finish_cell()?;
                    rank += 1;
                }
            }
        }
        Ok(())
    }
}

/// A cell emitter. Its methods accept only predecessors in the declared layout.
pub struct AtCell<'a, O, S, const PREFIX: bool> {
    rank: Cell,
    start: usize,
    end: usize,
    offsets: &'a [usize],
    sink: &'a mut S,
    operator: PhantomData<fn(O)>,
}

impl<O: Operator, S: ProductionSink<O>, const PREFIX: bool> AtCell<'_, O, S, PREFIX> {
    #[inline]
    fn rule<const N: usize>(
        &mut self,
        site: &str,
        operator: O,
        children: [Cell; N],
    ) -> Result<(), Error> {
        // The layout constructs only descending child ranks. Arity still
        // comes from the caller-supplied payload and is checked on emission.
        validate_arity(self.rank, &operator, N)?;
        self.sink.rule(site, operator, children)
    }
}
