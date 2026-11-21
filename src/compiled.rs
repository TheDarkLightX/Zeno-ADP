//! Ordered production schedules, table filling and replay for ranked grammars.

#[doc(hidden)]
pub mod generated;
mod grammar_macro;
mod parallel;
mod selection;
mod sequence;

pub use parallel::tabulate_parallel;
pub(crate) use parallel::Layout as ParallelLayout;
pub use selection::{tabulate_joint, tabulate_root, tabulate_selected, JointSelection, Selection};
pub use sequence::{
    Atom, Grammar, Matched, Nonterminal, Production, Sequence, SequenceConstructor, TokenAtom,
    TokenGrammar, TokenMatched, TokenProduction, TokenSequence,
};

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
    pub trait Sealed {
        // An associated function keeps internal dispatch out of downstream
        // method lookup through the public Program bound.
        fn parallel_layout(_: &Self) -> super::ParallelLayout<'_> {
            super::ParallelLayout::Replay
        }
    }
}

/// An input-bound grammar with a compiled, dependency-ordered schedule.
/// Ranks and production order agree with its per-cell replay source.
pub trait Program: RuleSource + sealed::Sealed {
    #[doc(hidden)]
    fn fill(&self, output: &mut impl ProductionSink<Self::Op>) -> Result<(), Error>;
}

macro_rules! schedule {
    ($source:ty, $op:ty, |$grammar:ident, $output:ident| $body:block
        $(, |$owner:ident| $layout:expr)?) => {
        impl $crate::compiled::sealed::Sealed for $source {
            $(
                fn parallel_layout($owner: &Self) -> $crate::compiled::ParallelLayout<'_> {
                    $layout
                }
            )?
        }
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
/// The algebra must satisfy the ordered, deterministic [`Fold`] contract.
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
        // Fixed-arity rules can check presence once and feed their exact
        // child count directly to the fold.
        match children.as_slice() {
            [] => crate::fast::fold_present(
                self.algebra,
                &mut self.chosen,
                &operator,
                std::iter::empty(),
            ),
            [child] => {
                if let Some(value) = self.cells[*child].as_ref() {
                    crate::fast::fold_present(
                        self.algebra,
                        &mut self.chosen,
                        &operator,
                        std::iter::once(value),
                    )?;
                }
                Ok(())
            }
            [left, right] => {
                if let (Some(left), Some(right)) = (&self.cells[*left], &self.cells[*right]) {
                    crate::fast::fold_present(
                        self.algebra,
                        &mut self.chosen,
                        &operator,
                        [left, right].into_iter(),
                    )?;
                }
                Ok(())
            }
            _ => self.rule_slice(site, operator, &children),
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

    #[inline]
    fn finish_cell(&mut self) -> Result<(), Error> {
        self.cells
            .push(std::mem::replace(&mut self.chosen, Ok(None))?);
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
