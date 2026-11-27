//! Fused folds over ranked rules and specialized minima for built-in grammars.
//!
//! A [`RuleSource`] regenerates one cell's ordered rules for a fast fold or
//! tree recovery. Use [`reference_chart`] to evaluate general algebras and audit.

mod alignment_path;
/// Optimum-unanimous interval decisions and single-row counterfactuals.
pub mod interval_choice;
pub mod interval_cover;
mod backtrack;
mod stream;
mod tree_product;

pub use alignment_path::{alignment_linear_space, AlignmentPath};
pub use backtrack::{BestTable, Recovery};
pub(crate) use stream::{fold_present, fold_rule};
pub use stream::{reference_chart, tabulate, Fold, RuleSource, Table};

pub use tree_product::{OptimalTrees, ScoreTrees};

use crate::algebras::{Cost, ScoredOperator};
use crate::compiled::Program;
use crate::grammars::{self, Item, RankedRules};
use crate::{reserve_table, Cell, Error};

/// Minimum scores in the corresponding reference chart's cell order.
#[derive(Debug, PartialEq, Eq)]
pub struct MinimumTable {
    cells: Vec<Option<i64>>,
    root: Cell,
}

impl MinimumTable {
    pub fn cells(&self) -> &[Option<i64>] {
        &self.cells
    }

    pub fn root(&self) -> Cell {
        self.root
    }

    /// The minimum score, or `None` when there is no candidate.
    pub fn minimum(&self) -> Option<i64> {
        self.cells[self.root]
    }
}

struct MinimumBuilder {
    cells: Vec<Option<i64>>,
    best: Option<i64>,
}

impl MinimumBuilder {
    fn build<G: Program>(source: G) -> Result<MinimumTable, Error>
    where
        G::Op: ScoredOperator,
    {
        let mut builder = Self {
            cells: reserve_table(source.cell_count())?,
            best: None,
        };
        source.fill(&mut builder)?;
        Ok(MinimumTable {
            cells: builder.cells,
            root: source.root(),
        })
    }
}

impl<O: ScoredOperator> RankedRules<O> for MinimumBuilder {
    #[inline]
    fn rule<const N: usize>(
        &mut self,
        _: &str,
        operator: O,
        children: [Cell; N],
    ) -> Result<(), Error> {
        let costs = children.map(|child| self.cells[child]);
        update_minimum(&mut self.best, operator, costs.into_iter())
    }

    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        let cells = &self.cells;
        update_minimum(
            &mut self.best,
            operator,
            children.iter().map(|&child| cells[child]),
        )
    }

    #[inline]
    fn finish_cell(&mut self) -> Result<(), Error> {
        self.cells.push(self.best.take());
        Ok(())
    }
}

#[inline]
fn update_minimum(
    best: &mut Option<i64>,
    operator: impl ScoredOperator,
    costs: impl Iterator<Item = Option<i64>> + Clone,
) -> Result<(), Error> {
    if costs.clone().any(|cost| cost.is_none()) {
        return Ok(());
    }
    let Cost::Finite(weight) = operator.cost() else {
        return Err(Error::InfinityDisabled);
    };
    let cost = costs.flatten().try_fold(weight, |sum, next| {
        sum.checked_add(next).ok_or(Error::Overflow)
    })?;
    *best = Some(best.map_or(cost, |old| old.min(cost)));
    Ok(())
}

/// Finite minimum over the candidates in [`grammars::nussinov`].
pub fn nussinov(sequence: &[u8], min_loop: usize) -> Result<MinimumTable, Error> {
    MinimumBuilder::build(grammars::nussinov_source(sequence, min_loop)?)
}

/// Finite minimum over the candidates in [`grammars::alignment`].
pub fn alignment(left: &[u8], right: &[u8]) -> Result<MinimumTable, Error> {
    MinimumBuilder::build(grammars::alignment_source(left, right)?)
}

/// Finite minimum over the candidates in [`grammars::local_alignment`].
pub fn local_alignment(left: &[u8], right: &[u8]) -> Result<MinimumTable, Error> {
    MinimumBuilder::build(grammars::local_alignment_source(left, right)?)
}

/// Finite minimum over the candidates in [`grammars::matrix_chain`].
pub fn matrix_chain(dimensions: &[u32]) -> Result<MinimumTable, Error> {
    MinimumBuilder::build(grammars::matrix_chain_source(dimensions)?)
}

/// Finite minimum over the candidates in [`grammars::knapsack`].
pub fn knapsack(items: &[Item], capacity: usize) -> Result<MinimumTable, Error> {
    MinimumBuilder::build(grammars::knapsack_source(items, capacity)?)
}
