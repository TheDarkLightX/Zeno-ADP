use crate::algebras::{Additive, Cost, ScoredOperator};
use crate::{build_trees, Error, Tree};

use super::Fold;

/// The eager product of finite minimum score and enumeration at that score.
/// Derivation order and duplicate trees are preserved. The number of ties
/// can be exponential, including at cells unreachable from the queried root.
pub struct ScoreTrees;

/// The score and ordered bag produced by ScoreTrees.
#[derive(Debug, PartialEq, Eq)]
pub struct OptimalTrees<O> {
    pub cost: Cost,
    pub trees: Vec<Tree<O>>,
}

impl<O: ScoredOperator + Clone> Fold<O> for ScoreTrees {
    type Value = OptimalTrees<O>;

    fn apply<'a>(
        &self,
        operator: &'a O,
        children: impl Iterator<Item = &'a Self::Value> + Clone,
    ) -> Result<Self::Value, Error>
    where
        Self::Value: 'a,
    {
        let cost =
            Additive::default().sum(operator.cost(), children.clone().map(|child| child.cost))?;
        Ok(OptimalTrees {
            cost,
            trees: build_trees(operator, children.map(|child| &child.trees)),
        })
    }

    fn merge(
        &self,
        selected: &mut Option<OptimalTrees<O>>,
        mut next: OptimalTrees<O>,
    ) -> Result<(), Error> {
        match selected {
            Some(best) if best.cost < next.cost => {}
            Some(best) if best.cost == next.cost => best.trees.append(&mut next.trees),
            _ => *selected = Some(next),
        }
        Ok(())
    }
}
