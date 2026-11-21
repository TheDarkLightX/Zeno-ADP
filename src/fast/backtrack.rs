use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::algebras::{Additive, Cost, ScoredOperator};
use crate::queries::{RankedTree, TreeMultiplicity};
use crate::{Cell, Error, Tree};

use super::stream::checked_rules;
use super::{tabulate, RuleSource, Table};

/// A finite additive minimum table tied to the source that produced it.
pub struct BestTable<'a, G> {
    source: &'a G,
    scores: Table<Cost>,
}

impl<'a, G: RuleSource> BestTable<'a, G>
where
    G::Op: ScoredOperator + Ord,
{
    /// Fill the score table without building productions or trees.
    ///
    /// For exact exhaustive tree answers, every ordered sum of any derivation
    /// that could be scored must fit in i64. Tabulation alone cannot check
    /// this for worse child scores eliminated during choice.
    pub fn new(source: &'a G) -> Result<Self, Error> {
        Ok(Self::from_scores(
            source,
            tabulate(source, &Additive::default())?,
        ))
    }

    pub(crate) fn from_scores(source: &'a G, scores: Table<Cost>) -> Self {
        Self { source, scores }
    }

    pub fn scores(&self) -> &Table<Cost> {
        &self.scores
    }

    /// Start a recovery query at the grammar's root.
    pub fn recover(&self) -> Recovery<'_, 'a, G> {
        Recovery {
            table: self,
            cell: self.scores.root(),
        }
    }

    /// Start a recovery query at any existing cell, including an empty one.
    pub fn recover_at(&self, cell: Cell) -> Option<Recovery<'_, 'a, G>> {
        (cell < self.scores.cells().len()).then_some(Recovery { table: self, cell })
    }
}

/// Tree queries over the finite additive table. Equal scores use the original
/// derivation order. Structural identity retains the first occurrence.
pub struct Recovery<'t, 'g, G> {
    table: &'t BestTable<'g, G>,
    cell: Cell,
}

impl<G: RuleSource> Recovery<'_, '_, G>
where
    G::Op: ScoredOperator + Ord,
{
    /// Recover the first optimal tree, if the cell is inhabited.
    pub fn first_minimum_tree(&self) -> Result<Option<RankedTree<G::Op, Cost>>, Error> {
        Ok(self
            .recover(Selection::Optimal(Some(1)), TreeMultiplicity::Derivations)?
            .pop())
    }

    /// Recover every optimal tree. Only rules whose best score equals the
    /// selected score can cause a descent to a child.
    pub fn co_minimal(
        &self,
        multiplicity: TreeMultiplicity,
    ) -> Result<Vec<RankedTree<G::Op, Cost>>, Error> {
        self.recover(Selection::Optimal(None), multiplicity)
    }

    /// Recover up to the requested number of trees in increasing score and
    /// derivation order. A later rule whose minimum cannot improve the
    /// current kth answer is skipped. The search may descend into lower-ranked alternatives.
    pub fn k_lowest(
        &self,
        k: usize,
        multiplicity: TreeMultiplicity,
    ) -> Result<Vec<RankedTree<G::Op, Cost>>, Error> {
        match k {
            0 => Ok(Vec::new()),
            1 => Ok(self.first_minimum_tree()?.into_iter().collect()),
            _ => self.recover(Selection::Ranked(k), multiplicity),
        }
    }

    fn recover(
        &self,
        selection: Selection,
        multiplicity: TreeMultiplicity,
    ) -> Result<Vec<RankedTree<G::Op, Cost>>, Error> {
        let mut traversal = Traversal {
            table: self.table,
            selection,
            multiplicity,
            memo: BTreeMap::new(),
        };
        Ok(traversal
            .visit(self.cell)?
            .iter()
            .map(|candidate| RankedTree {
                value: Cost::Finite(candidate.score),
                tree: candidate.tree.materialize(),
            })
            .collect())
    }
}

#[derive(Clone, Copy)]
enum Selection {
    Optimal(Option<usize>),
    Ranked(usize),
}

impl Selection {
    fn limit(self) -> Option<usize> {
        match self {
            Self::Optimal(limit) => limit,
            Self::Ranked(k) => Some(k),
        }
    }

    fn worth_visiting<O>(self, lower: Cost, minimum: Cost, current: &[Candidate<O>]) -> bool {
        match self {
            Self::Optimal(limit) => {
                lower == minimum && limit.is_none_or(|limit| current.len() < limit)
            }
            // All these derivations follow the ones already seen at this cell.
            Self::Ranked(k) => current
                .get(k - 1)
                .is_none_or(|last| lower < Cost::Finite(last.score)),
        }
    }
}

/// Shared during traversal. Convert to an owned public tree only on output.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Term<O> {
    operator: O,
    children: Vec<Rc<Term<O>>>,
}

impl<O: Clone> Term<O> {
    fn materialize(&self) -> Tree<O> {
        Tree {
            operator: self.operator.clone(),
            children: self
                .children
                .iter()
                .map(|child| child.materialize())
                .collect(),
        }
    }
}

/// A position in the original grammar's ordered Cartesian enumeration.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Derivation {
    alternative: usize,
    children: Vec<Rc<Derivation>>,
}

struct Candidate<O> {
    score: i64,
    tree: Rc<Term<O>>,
    order: Rc<Derivation>,
}

struct Prefix<O> {
    score: i64,
    trees: Vec<Rc<Term<O>>>,
    order: Vec<Rc<Derivation>>,
}

type RankedCell<O> = Rc<[Candidate<O>]>;

struct Traversal<'t, 'g, G: RuleSource> {
    table: &'t BestTable<'g, G>,
    selection: Selection,
    multiplicity: TreeMultiplicity,
    memo: BTreeMap<Cell, RankedCell<G::Op>>,
}

fn finite(cost: Cost) -> Result<i64, Error> {
    match cost {
        Cost::Finite(score) => Ok(score),
        Cost::Infinity => Err(Error::InfinityDisabled),
    }
}

impl<G: RuleSource> Traversal<'_, '_, G>
where
    G::Op: ScoredOperator + Ord,
{
    fn visit(&mut self, cell: Cell) -> Result<RankedCell<G::Op>, Error> {
        if let Some(cached) = self.memo.get(&cell) {
            return Ok(Rc::clone(cached));
        }
        let scores = self.table.scores.cells();
        let Some(minimum) = scores[cell] else {
            return Ok(Rc::from([]));
        };
        let mut found = Vec::new();
        let mut distinct_optima = BTreeSet::new();
        let mut ordinal = 0;
        checked_rules(self.table.source, cell, |operator, children| {
            let alternative = ordinal;
            ordinal += 1;
            let values = children.iter().map(|&child| scores[child]);
            if values.clone().any(|value| value.is_none()) {
                return Ok(());
            }
            let lower = Additive::default().sum(operator.cost(), values.flatten())?;
            if !self.selection.worth_visiting(lower, minimum, &found) {
                return Ok(());
            }

            let ranked = matches!(self.selection, Selection::Ranked(_));
            let distinct = self.multiplicity == TreeMultiplicity::DistinctTrees;
            for prefix in self.combine(finite(operator.cost())?, children)? {
                let tree = Rc::new(Term {
                    operator: operator.clone(),
                    children: prefix.trees,
                });
                if !ranked && distinct && !distinct_optima.insert(Rc::clone(&tree)) {
                    continue;
                }
                found.push(Candidate {
                    score: prefix.score,
                    tree,
                    order: Rc::new(Derivation {
                        alternative,
                        children: prefix.order,
                    }),
                });
            }
            if ranked {
                found.sort_unstable_by(|a, b| (&a.score, &a.order).cmp(&(&b.score, &b.order)));
                if distinct {
                    let mut seen = BTreeSet::new();
                    found.retain(|candidate| seen.insert(Rc::clone(&candidate.tree)));
                }
            }
            if let Some(limit) = self.selection.limit() {
                found.truncate(limit);
            }
            Ok(())
        })?;
        let found: RankedCell<_> = found.into();
        self.memo.insert(cell, Rc::clone(&found));
        Ok(found)
    }

    fn combine(&mut self, weight: i64, children: &[Cell]) -> Result<Vec<Prefix<G::Op>>, Error> {
        let mut prefixes = vec![Prefix {
            score: weight,
            trees: Vec::new(),
            order: Vec::new(),
        }];
        for &child in children {
            let candidates = self.visit(child)?;
            let mut extended = Vec::new();
            for prefix in prefixes {
                for child in candidates.iter() {
                    let mut trees = prefix.trees.clone();
                    trees.push(Rc::clone(&child.tree));
                    let mut order = prefix.order.clone();
                    order.push(Rc::clone(&child.order));
                    extended.push(Prefix {
                        score: prefix
                            .score
                            .checked_add(child.score)
                            .ok_or(Error::Overflow)?,
                        trees,
                        order,
                    });
                }
            }
            if let Selection::Ranked(k) = self.selection {
                // With the suffix fixed, a better prefix stays better. In
                // distinct mode its ordered child trees also stay distinct.
                extended.sort_unstable_by(|a, b| (&a.score, &a.order).cmp(&(&b.score, &b.order)));
                extended.truncate(k);
            }
            prefixes = extended;
        }
        Ok(prefixes)
    }
}
