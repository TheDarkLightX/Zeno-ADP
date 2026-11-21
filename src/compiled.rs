//! Ordered production schedules, table filling and replay for sequence grammars.

#[doc(hidden)]
pub mod generated;
mod grammar_macro;
mod sequence;

pub use sequence::{
    Atom, Grammar, Matched, Nonterminal, Production, Sequence, SequenceConstructor, TokenAtom,
    TokenGrammar, TokenMatched, TokenProduction, TokenSequence,
};

use std::collections::BTreeMap;

use crate::algebras::{Additive, ScoredOperator};
use crate::fast::{BestTable, Fold, RuleSource, Table};
use crate::grammars::{self, Align};
use crate::{reserve_table, Cell, Chart, Error, Rule};

#[doc(hidden)]
pub trait ProductionSink<O> {
    fn rule<const N: usize>(
        &mut self,
        site: &str,
        operator: O,
        children: [Cell; N],
    ) -> Result<(), Error> {
        self.rule_slice(site, operator, &children)
    }
    fn rule_slice(&mut self, site: &str, operator: O, children: &[Cell]) -> Result<(), Error>;
    fn finish_cell(&mut self) -> Result<(), Error>;
}

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// An input-bound grammar with a compiled, dependency-ordered schedule.
/// Ranks and production order agree with its per-cell replay source.
pub trait Program: RuleSource + sealed::Sealed {
    #[doc(hidden)]
    fn fill(&self, output: &mut impl ProductionSink<Self::Op>) -> Result<(), Error>;
}

macro_rules! schedule {
    ($source:ty, $op:ty, |$grammar:ident, $output:ident| $body:block) => {
        impl $crate::compiled::sealed::Sealed for $source {}
        impl $crate::compiled::Program for $source {
            fn fill(
                &self,
                $output: &mut impl $crate::compiled::ProductionSink<$op>,
            ) -> Result<(), $crate::Error> {
                let $grammar = self;
                $body
            }
        }
    };
}

pub(crate) use schedule;

/// Visit each emitted production in order, including repetitions and
/// productions disabled by an absent child. A guard returning `None` emits nothing.
/// The ordinal starts at zero in each logical cell. Repeated clause labels
/// identify occurrences from the same site, such as different split points.
pub fn replay<G: Program>(
    grammar: &G,
    visit: impl FnMut(Cell, usize, &str, G::Op, &[Cell]) -> Result<(), Error>,
) -> Result<(), Error> {
    let mut sink = Replay {
        cell: 0,
        ordinal: 0,
        visit,
    };
    grammar.fill(&mut sink)
}

struct Replay<F> {
    cell: Cell,
    ordinal: usize,
    visit: F,
}

impl<O, F> ProductionSink<O> for Replay<F>
where
    F: FnMut(Cell, usize, &str, O, &[Cell]) -> Result<(), Error>,
{
    fn rule_slice(&mut self, site: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        (self.visit)(self.cell, self.ordinal, site, operator, children)?;
        self.ordinal += 1;
        Ok(())
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        self.cell += 1;
        self.ordinal = 0;
        Ok(())
    }
}

/// Reconstruct the ordered chart for reference evaluation or auditing.
pub fn reference_chart<G: Program>(grammar: &G) -> Result<Chart<G::Op>, Error> {
    let mut cells = reserve_table(grammar.cell_count())?;
    cells.resize_with(grammar.cell_count(), Vec::new);
    replay(grammar, |cell, _, _, operator, children| {
        cells[cell].push(Rule::new(operator, children));
        Ok(())
    })?;
    Chart::new(cells, grammar.root())
}

/// Fill all logical cells in rank order without retaining productions.
/// The fold must implement its corresponding reference algebra's choice
/// and have at most one summary per cell.
pub fn tabulate<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
) -> Result<Table<A::Value>, Error> {
    let mut sink = Tabulation {
        cells: reserve_table(grammar.cell_count())?,
        chosen: Ok(None),
        algebra,
    };
    if let Err(error) = grammar.fill(&mut sink) {
        // Reference evaluation constructs and validates the entire chart first.
        // On a failed fast path, check the source before returning an algebra error.
        replay(grammar, |_, _, _, _, _| Ok(()))?;
        return Err(error);
    }
    Ok(Table::new(sink.cells, grammar.root()))
}

struct Tabulation<'a, V, A> {
    cells: Vec<Option<V>>,
    chosen: Result<Option<V>, Error>,
    algebra: &'a A,
}

impl<O, A: Fold<O>> ProductionSink<O> for Tabulation<'_, A::Value, A> {
    #[inline]
    fn rule<const N: usize>(
        &mut self,
        site: &str,
        operator: O,
        children: [Cell; N],
    ) -> Result<(), Error> {
        if let [child] = children.as_slice() {
            let value = self.cells[*child].as_ref();
            crate::fast::fold_rule(
                self.algebra,
                &mut self.chosen,
                &operator,
                std::iter::once(value),
            )
        } else {
            self.rule_slice(site, operator, &children)
        }
    }

    #[inline]
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        crate::fast::fold_rule(
            self.algebra,
            &mut self.chosen,
            &operator,
            children.iter().map(|&child| self.cells[child].as_ref()),
        )
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        self.cells
            .push(std::mem::replace(&mut self.chosen, Ok(None))?);
        Ok(())
    }
}

/// Fill every logical cell, retaining its summary only through its last
/// scheduled read. Return the root summary, if inhabited.
///
/// A preliminary replay validates the schedule and plans retention without
/// storing productions. The constructor callbacks must be deterministic.
/// The observer sees each completed cell in rank order, including absent
/// cells. An evaluation error can follow observations of earlier cells.
/// Prefer [`tabulate`] for table inspection or [`best`] for tree recovery.
pub fn tabulate_root<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
    observe: impl FnMut(Cell, Option<&A::Value>),
) -> Result<Option<A::Value>, Error> {
    let mut last_use = reserve_table(grammar.cell_count())?;
    last_use.extend(0..grammar.cell_count());
    replay(grammar, |cell, _, _, _, children| {
        for &child in children {
            last_use[child] = cell;
        }
        Ok(())
    })?;
    let mut sink = LiveTabulation {
        root: grammar.root(),
        cell: 0,
        last_use,
        live: BTreeMap::new(),
        retire: Vec::new(),
        chosen: Ok(None),
        algebra,
        observe,
    };
    grammar.fill(&mut sink)?;
    Ok(sink.live.remove(&sink.root))
}

struct LiveTabulation<'a, V, A, F> {
    root: Cell,
    cell: Cell,
    last_use: Vec<Cell>,
    live: BTreeMap<Cell, V>,
    retire: Vec<Cell>,
    chosen: Result<Option<V>, Error>,
    algebra: &'a A,
    observe: F,
}

impl<O, A: Fold<O>, F: FnMut(Cell, Option<&A::Value>)> ProductionSink<O>
    for LiveTabulation<'_, A::Value, A, F>
{
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        crate::fast::fold_rule(
            self.algebra,
            &mut self.chosen,
            &operator,
            children.iter().map(|child| self.live.get(child)),
        )?;
        for &child in children {
            if child != self.root && self.last_use[child] == self.cell {
                self.retire.push(child);
                // Repeated child ranks must remain readable until the whole
                // cell has finished. Schedule each retirement only once.
                self.last_use[child] = child;
            }
        }
        Ok(())
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        let next = std::mem::replace(&mut self.chosen, Ok(None))?;
        for child in self.retire.drain(..) {
            self.live.remove(&child);
        }
        (self.observe)(self.cell, next.as_ref());
        if self.cell == self.root || self.last_use[self.cell] > self.cell {
            if let Some(value) = next {
                self.live.insert(self.cell, value);
            }
        }
        self.cell += 1;
        Ok(())
    }
}

/// Fill a finite minimum table and retain its grammar for tree recovery.
/// Exact exhaustive ranking requires representable ordered sums on all
/// derivations. Use the reference audit to check a concrete bounded domain.
pub fn best<G: Program>(grammar: &G) -> Result<BestTable<'_, G>, Error>
where
    G::Op: ScoredOperator + Ord,
{
    Ok(BestTable::from_scores(
        grammar,
        tabulate(grammar, &Additive::default())?,
    ))
}

/// A scored cell of the root-only global alignment evaluation can be
/// observed as it finishes. The function retains only the live scores.
/// It returns the same minimum as the full table at the root.
pub fn alignment_rolling(
    left: &[u8],
    right: &[u8],
    observe: impl FnMut(Cell, i64),
) -> Result<i64, Error> {
    let grammar = grammars::alignment_source(left, right)?;
    let width = right.len() + 1;
    // Diagonal lag is width + 1, read before overwriting its slot.
    // A single-row or single-column alignment reads only the preceding slot.
    let length = if left.is_empty() || right.is_empty() {
        1
    } else {
        width + 1
    };
    let mut slots = reserve_table(length)?;
    slots.resize(length, 0);
    let mut sink = RollingAlignment {
        slots,
        slot: 0,
        cell: 0,
        selected: None,
        last: 0,
        observe,
    };
    grammar.fill(&mut sink)?;
    Ok(sink.last)
}

struct RollingAlignment<F> {
    slots: Vec<i64>,
    slot: usize,
    cell: Cell,
    selected: Option<i64>,
    last: i64,
    observe: F,
}

impl<F: FnMut(Cell, i64)> ProductionSink<Align> for RollingAlignment<F> {
    #[inline]
    fn rule_slice(&mut self, _: &str, operator: Align, children: &[Cell]) -> Result<(), Error> {
        let crate::algebras::Cost::Finite(weight) = operator.cost() else {
            return Err(Error::InfinityDisabled);
        };
        let score = if let [child] = *children {
            let lag = self.cell - child;
            let slot = self
                .slot
                .checked_sub(lag)
                .unwrap_or_else(|| self.slots.len() - (lag - self.slot));
            weight
                .checked_add(self.slots[slot])
                .ok_or(Error::Overflow)?
        } else {
            debug_assert!(children.is_empty());
            weight
        };
        self.selected = Some(self.selected.map_or(score, |best| best.min(score)));
        Ok(())
    }

    #[inline]
    fn finish_cell(&mut self) -> Result<(), Error> {
        self.last = self.selected.take().expect("alignment cells are inhabited");
        self.slots[self.slot] = self.last;
        (self.observe)(self.cell, self.last);
        self.cell += 1;
        self.slot += 1;
        if self.slot == self.slots.len() {
            self.slot = 0;
        }
        Ok(())
    }
}
