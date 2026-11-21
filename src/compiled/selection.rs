use std::collections::{BTreeMap, BTreeSet};

use crate::fast::{fold_rule, Fold};
use crate::{reserve_table, Cell, Error};

use super::{replay, ProductionSink, Program};

/// Fill every logical cell, retaining its summary only through its last
/// scheduled read. Return the root summary, if inhabited.
///
/// A preliminary replay validates the schedule and plans retention without
/// storing productions. The constructor callbacks must be deterministic.
/// The algebra must satisfy the ordered, deterministic [`Fold`] contract.
/// The observer sees each completed cell in rank order, including absent
/// cells. An evaluation error can follow observations of earlier cells.
/// Prefer [`super::tabulate`] for table inspection or [`super::best`] for tree recovery.
pub fn tabulate_root<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
    observe: impl FnMut(Cell, Option<&A::Value>),
) -> Result<Option<A::Value>, Error> {
    let root = grammar.root();
    Ok(tabulate_selected(grammar, algebra, &[root], observe)?
        .answers
        .remove(&root)
        .flatten())
}

/// Summaries requested from a shared schedule, indexed by logical rank.
#[derive(Debug, PartialEq, Eq)]
pub struct Selection<V> {
    /// An empty cell is recorded as `None`. Repeated requests share one value.
    pub answers: BTreeMap<Cell, Option<V>>,
    /// Maximum number of inhabited summaries stored after completing any
    /// cell, including requested outputs. This counts no planning metadata.
    pub peak_retained: usize,
}

/// Fill all cells while retaining only summaries with a future scheduled
/// read or a request in `ranks`.
///
/// As with [`tabulate_root`], the observer sees every completed cell and the
/// constructor callbacks must be deterministic. The algebra must satisfy the
/// ordered, deterministic [`Fold`] contract. Planning uses a rank-indexed
/// last-read vector. It counts structural reads, including reads by a rule
/// that will turn out to have an absent child.
pub fn tabulate_selected<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
    ranks: &[Cell],
    observe: impl FnMut(Cell, Option<&A::Value>),
) -> Result<Selection<A::Value>, Error> {
    let wanted = requested(grammar, ranks)?;
    let mut sink = Single {
        plan: Retention::new(grammar)?,
        fold: Retained::new(algebra, wanted),
        observe,
    };
    grammar.fill(&mut sink)?;
    Ok(sink.fold.selection())
}

/// Two independent projections from one schedule, each preserving its
/// requested ranks and its own fold's answers.
#[derive(Debug, PartialEq, Eq)]
pub struct JointSelection<L, R> {
    pub left: Selection<L>,
    pub right: Selection<R>,
    /// Maximum simultaneous number of inhabited values retained across both
    /// algebras after a cell completes. Planning metadata is excluded.
    pub peak_retained: usize,
}

/// Evaluate two folds over one replay and one fill, with independent
/// output ranks. Request a rank on both sides to retain its full pair
/// of values. A field whose final structural read has passed is
/// released unless its own side requested it.
///
/// The observer receives both answers at every completed rank. Within each
/// algebra all contributions keep source order. Constructors must be
/// deterministic and both algebras must satisfy the [`Fold`] contract.
/// Source errors take priority. Algebra errors are returned
/// at the earliest failing rank, with the left error first at a tie.
pub fn tabulate_joint<G: Program, L: Fold<G::Op>, R: Fold<G::Op>>(
    grammar: &G,
    left: (&L, &[Cell]),
    right: (&R, &[Cell]),
    observe: impl FnMut(Cell, Option<&L::Value>, Option<&R::Value>),
) -> Result<JointSelection<L::Value, R::Value>, Error> {
    let left_wanted = requested(grammar, left.1)?;
    let right_wanted = requested(grammar, right.1)?;
    let mut sink = Joint {
        plan: Retention::new(grammar)?,
        left: Retained::new(left.0, left_wanted),
        right: Retained::new(right.0, right_wanted),
        observe,
        peak_retained: 0,
    };
    grammar.fill(&mut sink)?;
    Ok(JointSelection {
        left: sink.left.selection(),
        right: sink.right.selection(),
        peak_retained: sink.peak_retained,
    })
}

fn requested(grammar: &impl Program, ranks: &[Cell]) -> Result<BTreeSet<Cell>, Error> {
    let wanted: BTreeSet<_> = ranks.iter().copied().collect();
    if let Some(&rank) = wanted.last().filter(|&&rank| rank >= grammar.cell_count()) {
        return Err(Error::CellOutOfRange(rank));
    }
    Ok(wanted)
}

struct Retention {
    cell: Cell,
    last_use: Vec<Cell>,
    retire: Vec<Cell>,
}

impl Retention {
    fn new(grammar: &impl Program) -> Result<Self, Error> {
        let mut last_use = reserve_table(grammar.cell_count())?;
        last_use.extend(0..grammar.cell_count());
        replay(grammar, |cell, _, _, _, children| {
            for &child in children {
                last_use[child] = cell;
            }
            Ok(())
        })?;
        Ok(Self {
            cell: 0,
            last_use,
            retire: Vec::new(),
        })
    }

    fn read(&mut self, children: &[Cell]) {
        for &child in children {
            if self.last_use[child] == self.cell {
                self.retire.push(child);
                // A repeated child stays readable through the entire cell,
                // with a single retirement afterwards.
                self.last_use[child] = child;
            }
        }
    }

    fn advance(&mut self) {
        self.retire.clear();
        self.cell += 1;
    }
}

struct Retained<'a, V, A> {
    algebra: &'a A,
    wanted: BTreeSet<Cell>,
    live: BTreeMap<Cell, V>,
    chosen: Result<Option<V>, Error>,
    apply_error: Option<Error>,
    peak_retained: usize,
}

impl<'a, V, A> Retained<'a, V, A> {
    fn new(algebra: &'a A, wanted: BTreeSet<Cell>) -> Self {
        Self {
            algebra,
            wanted,
            live: BTreeMap::new(),
            chosen: Ok(None),
            apply_error: None,
            peak_retained: 0,
        }
    }

    fn rule<O>(&mut self, operator: &O, children: &[Cell]) -> Result<(), Error>
    where
        A: Fold<O, Value = V>,
    {
        fold_rule(
            self.algebra,
            &mut self.chosen,
            operator,
            children.iter().map(|child| self.live.get(child)),
        )
    }

    fn rule_deferred<O>(&mut self, operator: &O, children: &[Cell])
    where
        A: Fold<O, Value = V>,
    {
        if self.apply_error.is_none() {
            self.apply_error = self.rule(operator, children).err();
        }
    }

    fn finish(&mut self) -> Result<Option<V>, Error> {
        if let Some(error) = self.apply_error.take() {
            return Err(error);
        }
        std::mem::replace(&mut self.chosen, Ok(None))
    }

    fn store(&mut self, plan: &Retention, value: Option<V>) {
        if let Some(value) = value {
            if plan.last_use[plan.cell] > plan.cell || self.wanted.contains(&plan.cell) {
                self.live.insert(plan.cell, value);
            }
        }
        self.peak_retained = self.peak_retained.max(self.live.len());
    }

    fn release(&mut self, plan: &Retention) {
        for child in &plan.retire {
            if !self.wanted.contains(child) {
                self.live.remove(child);
            }
        }
    }

    fn selection(mut self) -> Selection<V> {
        Selection {
            answers: self
                .wanted
                .into_iter()
                .map(|rank| (rank, self.live.remove(&rank)))
                .collect(),
            peak_retained: self.peak_retained,
        }
    }
}

struct Single<'a, V, A, F> {
    plan: Retention,
    fold: Retained<'a, V, A>,
    observe: F,
}

impl<O, A: Fold<O>, F: FnMut(Cell, Option<&A::Value>)> ProductionSink<O>
    for Single<'_, A::Value, A, F>
{
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        self.fold.rule(&operator, children)?;
        self.plan.read(children);
        Ok(())
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        let value = self.fold.finish()?;
        self.fold.release(&self.plan);
        (self.observe)(self.plan.cell, value.as_ref());
        self.fold.store(&self.plan, value);
        self.plan.advance();
        Ok(())
    }
}

struct Joint<'a, V, W, L, R, F> {
    plan: Retention,
    left: Retained<'a, V, L>,
    right: Retained<'a, W, R>,
    observe: F,
    peak_retained: usize,
}

impl<O, L, R, F> ProductionSink<O> for Joint<'_, L::Value, R::Value, L, R, F>
where
    L: Fold<O>,
    R: Fold<O>,
    F: FnMut(Cell, Option<&L::Value>, Option<&R::Value>),
{
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        self.left.rule_deferred(&operator, children);
        self.right.rule_deferred(&operator, children);
        self.plan.read(children);
        Ok(())
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        let left = self.left.finish()?;
        let right = self.right.finish()?;
        self.left.release(&self.plan);
        self.right.release(&self.plan);
        (self.observe)(self.plan.cell, left.as_ref(), right.as_ref());
        self.left.store(&self.plan, left);
        self.right.store(&self.plan, right);
        self.peak_retained = self
            .peak_retained
            .max(self.left.live.len() + self.right.live.len());
        self.plan.advance();
        Ok(())
    }
}
