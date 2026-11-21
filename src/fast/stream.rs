use crate::algebras::{
    Additive, Cost, Count, DerivationSummary, Maximum, MinimumWithMultiplicity, ScoredOperator,
};
use crate::{reserve_table, Cell, Chart, Error, Operator, Rule};

/// An input-bound grammar whose alternatives can be regenerated one cell at a time.
///
/// Cell IDs are consecutive ranks starting at zero. Emit each cell's rules in
/// derivation order, including duplicates, and propagate callback errors.
/// Reject out-of-range ranks with [`Error::CellOutOfRange`] before emitting.
/// Keep the layout and emissions deterministic for the life of a table.
pub trait RuleSource {
    type Op: Operator;

    fn cell_count(&self) -> usize;
    fn root(&self) -> Cell;
    fn rules_at(
        &self,
        cell: Cell,
        emit: impl FnMut(Self::Op, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error>;
}

impl<O: Operator> RuleSource for Chart<O> {
    type Op = O;

    fn cell_count(&self) -> usize {
        self.cells().len()
    }

    fn root(&self) -> Cell {
        self.root()
    }

    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let rules = self.cells().get(cell).ok_or(Error::CellOutOfRange(cell))?;
        for rule in rules {
            emit(rule.operator.clone(), &rule.children)?;
        }
        Ok(())
    }
}

pub(super) fn checked_rules<G: RuleSource>(
    source: &G,
    cell: Cell,
    mut visit: impl FnMut(G::Op, &[Cell]) -> Result<(), Error>,
) -> Result<(), Error> {
    source.rules_at(cell, |operator, children| {
        crate::validate_rule(cell, &operator, children)?;
        visit(operator, children)
    })
}

/// Collect a replayable source into the reference representation for auditing
/// or for evaluating algebras with a general choice function.
pub fn reference_chart<G: RuleSource>(source: &G) -> Result<Chart<G::Op>, Error> {
    let n = source.cell_count();
    let root = source.root();
    if root >= n {
        return Err(Error::MissingRoot(root));
    }
    let mut cells = reserve_table(n)?;
    for cell in 0..n {
        let mut rules = Vec::new();
        source.rules_at(cell, |operator, children| {
            rules.push(Rule::new(operator, children));
            Ok(())
        })?;
        cells.push(rules);
    }
    Chart::new(cells, root)
}

/// A streaming algebra with one summary per inhabited cell.
///
/// Implement `apply` using only the operator and the ordered sequence of
/// child summaries. Implement `merge` using only its accumulator and the
/// next contribution. These operations must be deterministic and independent
/// of the evaluator, call order across cells, thread identity, and side effects.
/// A rule with an absent child contributes nothing and never calls `apply`.
///
/// For agreement with an equivalent reference algebra, reducing an ordered
/// stream of contributions must agree with its batch choice, and applying the
/// operator to selected child summaries must implement the same question.
/// Exactness against exhaustive trees additionally requires the relevant
/// Bellman laws.
pub trait Fold<O> {
    type Value;

    /// Consume child summaries in constructor argument order, including
    /// repeated children. Library evaluators provide an exact-size iterator.
    /// `size_hint()` returns `(remaining, Some(remaining))`. Cloning preserves
    /// the current position.
    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a Self::Value> + Clone,
    ) -> Result<Self::Value, Error>
    where
        Self::Value: 'a;

    /// Incorporate the next contribution in source order. A successful
    /// reduction of a nonempty prefix must leave an inhabited summary.
    fn merge(&self, selected: &mut Option<Self::Value>, next: Self::Value) -> Result<(), Error>;
}

/// Fused answers in source cell order.
#[derive(Debug, PartialEq, Eq)]
pub struct Table<V> {
    cells: Vec<Option<V>>,
    root: Cell,
}

impl<V> Table<V> {
    pub(crate) fn new(cells: Vec<Option<V>>, root: Cell) -> Self {
        Self { cells, root }
    }

    pub fn cells(&self) -> &[Option<V>] {
        &self.cells
    }

    pub fn root(&self) -> Cell {
        self.root
    }

    pub fn answer(&self) -> Option<&V> {
        self.cells[self.root].as_ref()
    }
}

/// Evaluate and discard each emitted rule immediately. Source and evaluation
/// errors are encountered in traversal order. The algebra must satisfy the
/// ordered, deterministic [`Fold`] contract.
pub fn tabulate<G: RuleSource, A: Fold<G::Op>>(
    source: &G,
    algebra: &A,
) -> Result<Table<A::Value>, Error> {
    let n = source.cell_count();
    let root = source.root();
    if root >= n {
        return Err(Error::MissingRoot(root));
    }

    let mut cells: Vec<Option<A::Value>> = reserve_table(n)?;
    for cell in 0..n {
        let mut chosen = Ok(None);
        checked_rules(source, cell, |operator, children| {
            fold_rule(
                algebra,
                &mut chosen,
                &operator,
                children.iter().map(|&child| cells[child].as_ref()),
            )
        })?;
        cells.push(chosen?);
    }
    Ok(Table { cells, root })
}

#[inline]
pub(crate) fn fold_rule<'a, O, A: Fold<O>>(
    algebra: &A,
    chosen: &mut Result<Option<A::Value>, Error>,
    operator: &'a O,
    values: impl ExactSizeIterator<Item = Option<&'a A::Value>> + Clone,
) -> Result<(), Error>
where
    A::Value: 'a,
{
    if values.clone().any(|value| value.is_none()) {
        return Ok(());
    }
    let present = values.map(|value| value.expect("all child summaries are present"));
    fold_present(algebra, chosen, operator, present)
}

#[inline]
pub(crate) fn fold_present<'a, O, A: Fold<O>>(
    algebra: &A,
    chosen: &mut Result<Option<A::Value>, Error>,
    operator: &'a O,
    values: impl ExactSizeIterator<Item = &'a A::Value> + Clone,
) -> Result<(), Error>
where
    A::Value: 'a,
{
    let next = algebra.apply(operator, values)?;
    // Reference evaluation applies every alternative before choice.
    if let Ok(selected) = chosen {
        if let Err(error) = algebra.merge(selected, next) {
            *chosen = Err(error);
        }
    }
    Ok(())
}

impl<O: ScoredOperator> Fold<O> for Additive {
    type Value = Cost;

    #[inline]
    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a Cost> + Clone,
    ) -> Result<Cost, Error> {
        self.sum(operator.cost(), children.copied())
    }

    fn merge(&self, selected: &mut Option<Cost>, next: Cost) -> Result<(), Error> {
        *selected = Some(selected.map_or(next, |best| best.min(next)));
        Ok(())
    }
}

impl<O: ScoredOperator> Fold<O> for Maximum {
    type Value = Cost;

    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a Cost> + Clone,
    ) -> Result<Cost, Error> {
        Additive::default().sum(operator.cost(), children.copied())
    }

    fn merge(&self, selected: &mut Option<Cost>, next: Cost) -> Result<(), Error> {
        *selected = Some(selected.map_or(next, |best| best.max(next)));
        Ok(())
    }
}

impl<O> Fold<O> for Count {
    type Value = u128;

    fn apply<'a>(
        &self,
        _: &'a O,
        children: impl Iterator<Item = &'a u128> + Clone,
    ) -> Result<u128, Error> {
        crate::algebras::count_product(children.copied())
    }

    fn merge(&self, selected: &mut Option<u128>, next: u128) -> Result<(), Error> {
        *selected = Some(
            selected
                .unwrap_or(0)
                .checked_add(next)
                .ok_or(Error::Overflow)?,
        );
        Ok(())
    }
}

impl<O: ScoredOperator> Fold<O> for MinimumWithMultiplicity {
    type Value = DerivationSummary;

    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a DerivationSummary> + Clone,
    ) -> Result<DerivationSummary, Error> {
        self.summarize(operator.cost(), children)
    }

    fn merge(
        &self,
        selected: &mut Option<DerivationSummary>,
        next: DerivationSummary,
    ) -> Result<(), Error> {
        let Some(best) = selected else {
            *selected = Some(next);
            return Ok(());
        };
        best.total_derivations = best
            .total_derivations
            .checked_add(next.total_derivations)
            .ok_or(Error::Overflow)?;
        use std::cmp::Ordering;
        match next.cost.cmp(&best.cost) {
            Ordering::Less => {
                best.cost = next.cost;
                best.optimal_derivations = next.optimal_derivations;
            }
            Ordering::Equal => {
                best.optimal_derivations = best
                    .optimal_derivations
                    .checked_add(next.optimal_derivations)
                    .ok_or(Error::Overflow)?;
            }
            Ordering::Greater => {}
        }
        Ok(())
    }
}
