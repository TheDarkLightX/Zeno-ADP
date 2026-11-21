use std::marker::PhantomData;

use crate::compiled::{self, Program};
use crate::fast::Fold;
use crate::{reserve_table, Cell, Error};

use super::{add_contexts, InsideOutside, LogWeight, Mass, Rational, WeightedOperator};

/// Inside and outside weights attached to their replayable grammar.
/// Only cell weights are retained. Constructors and weights must be
/// deterministic across fills, reverse traversal and queries.
pub struct CompiledInsideOutside<'a, G, M> {
    grammar: &'a G,
    weights: InsideOutside<M>,
}

impl<G, M> CompiledInsideOutside<'_, G, M> {
    pub fn weights(&self) -> &InsideOutside<M> {
        &self.weights
    }
}

impl<G: Program> CompiledInsideOutside<'_, G, Rational>
where
    G::Op: WeightedOperator,
{
    /// Unnormalized mass of one replay occurrence, identified by its
    /// logical parent rank and zero-based rule ordinal. An absent ordinal
    /// returns `None`. An emitted occurrence may have zero mass.
    pub fn rule_mass(&self, cell: Cell, ordinal: usize) -> Result<Option<Rational>, Error> {
        let mut current = 0;
        let mut result = None;
        self.grammar.rules_at(cell, |operator, children| {
            if current == ordinal {
                result = Some(self.occurrence_mass(cell, &operator, children)?);
            }
            current += 1;
            Ok(())
        })?;
        Ok(result)
    }

    /// Sum the unnormalized mass of all replay occurrences accepted by
    /// `matches`. The predicate sees rank, ordinal, clause name, operator
    /// and ordered child ranks. Each use of a matched occurrence in a
    /// derivation contributes its full derivation weight.
    pub fn event_mass(
        &self,
        mut matches: impl FnMut(Cell, usize, &str, &G::Op, &[Cell]) -> bool,
    ) -> Result<Rational, Error> {
        let mut total = Rational::ZERO;
        compiled::replay(self.grammar, |cell, ordinal, site, operator, children| {
            if matches(cell, ordinal, site, &operator, children) {
                total = total.checked_add(self.occurrence_mass(cell, &operator, children)?)?;
            }
            Ok(())
        })?;
        Ok(total)
    }

    /// Normalize a weighted occurrence count by the root partition.
    /// Returns `Ok(None)` for zero partition. The result can exceed one.
    pub fn expected_visits(
        &self,
        matches: impl FnMut(Cell, usize, &str, &G::Op, &[Cell]) -> bool,
    ) -> Result<Option<Rational>, Error> {
        let partition = *self.weights.partition();
        if partition == Rational::ZERO {
            return Ok(None);
        }
        self.event_mass(matches)?.checked_div(partition)
    }

    fn occurrence_mass(
        &self,
        cell: Cell,
        operator: &G::Op,
        children: &[Cell],
    ) -> Result<Rational, Error> {
        let factors = std::iter::once(operator.weight())
            .chain(children.iter().map(|&child| self.weights.inside[child]));
        Rational::product(self.weights.outside[cell], factors)
    }
}

/// Exact weighted analysis of a compiled schedule, with occurrence and
/// event queries. Retains inside and outside weights by logical rank.
/// Arithmetic uses checked `u128` rationals.
pub fn inside_outside<G: Program>(
    grammar: &G,
) -> Result<CompiledInsideOutside<'_, G, Rational>, Error>
where
    G::Op: WeightedOperator,
{
    analyze(grammar)
}

/// Weighted analysis in log space, in the same rule and child order as
/// the corresponding chart pass.
pub fn log_inside_outside<G: Program>(
    grammar: &G,
) -> Result<CompiledInsideOutside<'_, G, LogWeight>, Error>
where
    G::Op: WeightedOperator,
{
    analyze(grammar)
}

fn analyze<G, M>(grammar: &G) -> Result<CompiledInsideOutside<'_, G, M>, Error>
where
    G: Program,
    G::Op: WeightedOperator,
    M: Mass,
{
    let table = compiled::tabulate(grammar, &InsideFold::<M>(PhantomData))?;
    let root = table.root();
    let mut inside = reserve_table(grammar.cell_count())?;
    inside.extend(
        table
            .into_cells()
            .into_iter()
            .map(|cell| cell.unwrap_or(M::ZERO)),
    );
    let mut outside = reserve_table(inside.len())?;
    outside.resize(inside.len(), M::ZERO);
    outside[root] = M::ONE;
    let mut suffix = Vec::new();
    for cell in (0..inside.len()).rev() {
        if outside[cell] == M::ZERO {
            continue;
        }
        grammar.rules_at(cell, |operator, children| {
            add_contexts(
                cell,
                &operator,
                children,
                &inside,
                &mut outside,
                &mut suffix,
            )
        })?;
    }
    Ok(CompiledInsideOutside {
        grammar,
        weights: InsideOutside {
            root,
            inside,
            outside,
        },
    })
}

struct InsideFold<M>(PhantomData<M>);

impl<O: WeightedOperator, M: Mass> Fold<O> for InsideFold<M> {
    type Value = M;

    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a M> + Clone,
    ) -> Result<M, Error>
    where
        M: 'a,
    {
        M::product(M::from_rational(operator.weight()), children.copied())
    }

    fn merge(&self, selected: &mut Option<M>, next: M) -> Result<(), Error> {
        *selected = Some(match *selected {
            Some(previous) => previous.add(next)?,
            None => next,
        });
        Ok(())
    }
}
