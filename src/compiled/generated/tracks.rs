//! Static prefix schedules over a positive number of sequence tracks.

use std::marker::PhantomData;

use crate::{validate_rule, Cell, Error, Operator};

use super::{Layout, Ranked};
use crate::compiled::{ProductionSink, Program};

pub fn bind<'a, T: 'a, O: Operator + 'a, R: TrackRules<T, O, N> + 'a, const N: usize>(
    name: &'static str,
    inputs: [&'a [T]; N],
    mut rules: R,
) -> Result<impl Program<Op = O> + 'a, Error> {
    if N == 0 {
        return Err(refusal(name, "expected at least one input track"));
    }
    let mut widths = [0; N];
    let mut strides = [0; N];
    let mut count = 1usize;
    for axis in (0..N).rev() {
        widths[axis] = inputs[axis].len().checked_add(1).ok_or(Error::Overflow)?;
        strides[axis] = count;
        count = count.checked_mul(widths[axis]).ok_or(Error::Overflow)?;
    }
    rules.prepare(&widths, &strides)?;
    Ok(Ranked(Prefixes {
        name,
        inputs,
        widths,
        count,
        rules,
        output: PhantomData::<fn() -> O>,
    }))
}

fn refusal(name: &str, reason: &'static str) -> Error {
    Error::UnsupportedGrammar {
        name: name.to_owned(),
        reason,
    }
}

struct Prefixes<'a, T, O, R, const N: usize> {
    name: &'static str,
    inputs: [&'a [T]; N],
    widths: [usize; N],
    count: usize,
    rules: R,
    output: PhantomData<fn() -> O>,
}

impl<T, O: Operator, R: TrackRules<T, O, N>, const N: usize> Prefixes<'_, T, O, R, N> {
    #[inline]
    fn emit_at(
        &self,
        cell: Cell,
        ends: [usize; N],
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error> {
        let mut checked = TrackCell {
            name: self.name,
            cell,
            sink,
            failure: None,
        };
        let result = self.rules.emit(self.inputs, cell, ends, &mut checked);
        checked.failure.map_or(result, Err)
    }
}

impl<T, O: Operator, R: TrackRules<T, O, N>, const N: usize> Layout for Prefixes<'_, T, O, R, N> {
    type Op = O;

    fn cell_count(&self) -> usize {
        self.count
    }

    fn root(&self) -> Cell {
        self.count - 1
    }

    #[inline]
    fn emit(&self, cell: Cell, sink: &mut impl ProductionSink<O>) -> Result<(), Error> {
        let mut remainder = cell;
        let mut ends = [0; N];
        for axis in (0..N).rev() {
            ends[axis] = remainder % self.widths[axis];
            remainder /= self.widths[axis];
        }
        self.emit_at(cell, ends, sink)
    }
    #[inline]
    fn fill(&self, sink: &mut impl ProductionSink<O>) -> Result<(), Error> {
        let mut ends = [0; N];
        for cell in 0..self.count {
            self.emit_at(cell, ends, sink)?;
            sink.finish_cell()?;
            for (end, &width) in ends.iter_mut().zip(&self.widths).rev() {
                *end += 1;
                if *end < width {
                    break;
                }
                *end = 0;
            }
        }
        Ok(())
    }
}

struct TrackCell<'a, S> {
    name: &'static str,
    cell: Cell,
    sink: &'a mut S,
    failure: Option<Error>,
}

impl<S> TrackCell<'_, S> {
    #[inline]
    fn forward<O: Operator>(
        &mut self,
        operator: O,
        children: &[Cell],
        emit: impl FnOnce(&mut S, O) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        if let Err(error) =
            validate_rule(self.cell, &operator, children).and_then(|()| emit(self.sink, operator))
        {
            self.failure = Some(error.clone());
            return Err(error);
        }
        Ok(())
    }
}

impl<O: Operator, S: ProductionSink<O>> ProductionSink<O> for TrackCell<'_, S> {
    #[inline]
    fn rule<const N: usize>(
        &mut self,
        site: &str,
        operator: O,
        children: [Cell; N],
    ) -> Result<(), Error> {
        self.forward(operator, &children, |sink, operator| {
            sink.rule(site, operator, children)
        })
    }

    #[inline]
    fn rule_slice(&mut self, site: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        self.forward(operator, children, |sink, operator| {
            sink.rule_slice(site, operator, children)
        })
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        let error = self
            .failure
            .get_or_insert_with(|| refusal(self.name, "a track emitter cannot finish a cell"));
        Err(error.clone())
    }
}

/// Macro implementation hook for emitting one multi-track prefix cell.
/// Emit in source order and propagate sink errors. The binder validates
/// arity and rank descent and owns cell completion.
pub trait TrackRules<T, O, const N: usize> {
    fn prepare(&mut self, widths: &[usize; N], strides: &[usize; N]) -> Result<(), Error>;

    fn emit(
        &self,
        inputs: [&[T]; N],
        cell: Cell,
        ends: [usize; N],
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error>;
}

impl<T, O, A: TrackRules<T, O, N>, B: TrackRules<T, O, N>, const N: usize> TrackRules<T, O, N>
    for (A, B)
{
    fn prepare(&mut self, widths: &[usize; N], strides: &[usize; N]) -> Result<(), Error> {
        self.0.prepare(widths, strides)?;
        self.1.prepare(widths, strides)
    }

    #[inline]
    fn emit(
        &self,
        inputs: [&[T]; N],
        cell: Cell,
        ends: [usize; N],
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error> {
        self.0.emit(inputs, cell, ends, sink)?;
        self.1.emit(inputs, cell, ends, sink)
    }
}

pub struct Empty<F>(pub &'static str, pub F);

impl<T, O: Operator, F, const N: usize> TrackRules<T, O, N> for Empty<F>
where
    F: Fn([&[T]; N], [usize; N]) -> Result<Option<O>, Error>,
{
    fn prepare(&mut self, _: &[usize; N], _: &[usize; N]) -> Result<(), Error> {
        Ok(())
    }

    #[inline]
    fn emit(
        &self,
        inputs: [&[T]; N],
        cell: Cell,
        ends: [usize; N],
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error> {
        if cell == 0 {
            if let Some(operator) = (self.1)(inputs, ends)? {
                sink.rule(self.0, operator, [])?;
            }
        }
        Ok(())
    }
}

pub struct Step<F, const N: usize> {
    name: &'static str,
    consume: [bool; N],
    operator: F,
    lag: Option<usize>,
}

impl<F, const N: usize> Step<F, N> {
    pub fn new(name: &'static str, consume: [bool; N], operator: F) -> Self {
        Self {
            name,
            consume,
            operator,
            lag: None,
        }
    }
}

impl<T, O: Operator, F, const N: usize> TrackRules<T, O, N> for Step<F, N>
where
    F: Fn([&[T]; N], [usize; N]) -> Result<Option<O>, Error>,
{
    fn prepare(&mut self, widths: &[usize; N], strides: &[usize; N]) -> Result<(), Error> {
        if !self.consume.iter().any(|&consume| consume) {
            return Err(refusal(self.name, "a step must consume at least one track"));
        }
        if self
            .consume
            .iter()
            .zip(widths)
            .any(|(&consume, &width)| consume && width == 1)
        {
            return Ok(());
        }
        // Each changed digit can advance. The sum cannot exceed the full rank.
        self.lag = Some(
            self.consume
                .iter()
                .zip(strides)
                .filter_map(|(&consume, &stride)| consume.then_some(stride))
                .sum(),
        );
        Ok(())
    }

    #[inline]
    fn emit(
        &self,
        inputs: [&[T]; N],
        cell: Cell,
        ends: [usize; N],
        sink: &mut impl ProductionSink<O>,
    ) -> Result<(), Error> {
        if let Some(lag) = self.lag {
            if self
                .consume
                .iter()
                .zip(ends)
                .all(|(&consume, end)| !consume || end != 0)
            {
                if let Some(operator) = (self.operator)(inputs, ends)? {
                    sink.rule(self.name, operator, [cell - lag])?;
                }
            }
        }
        Ok(())
    }
}
