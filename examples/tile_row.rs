//! A user-defined grammar for covering a row with single and double tiles.
use zeno_adp::algebras::{Cost, Count, ScoredOperator};
use zeno_adp::fast::{self, BestTable, RuleSource, ScoreTrees};
use zeno_adp::{audit_bounded, AuditBudget, Cell, Error, Operator};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Tile {
    Empty,
    Single,
    Double,
}

impl Operator for Tile {
    fn arity(&self) -> usize {
        usize::from(*self != Self::Empty)
    }
}

impl ScoredOperator for Tile {
    fn cost(&self) -> Cost {
        Cost::Finite(match self {
            Self::Empty => 0,
            Self::Single => 2,
            Self::Double => 3,
        })
    }
}

struct Row {
    length: usize,
}

impl RuleSource for Row {
    type Op = Tile;

    fn cell_count(&self) -> usize {
        self.length + 1
    }

    fn root(&self) -> Cell {
        self.length
    }

    fn rules_at(
        &self,
        prefix: Cell,
        mut emit: impl FnMut(Tile, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if prefix >= self.cell_count() {
            return Err(Error::CellOutOfRange(prefix));
        }
        if prefix == 0 {
            return emit(Tile::Empty, &[]);
        }
        emit(Tile::Single, &[prefix - 1])?;
        if prefix >= 2 {
            emit(Tile::Double, &[prefix - 2])?;
        }
        Ok(())
    }
}

fn main() -> Result<(), Error> {
    // An odd length leaves several placements for the single tile in an optimum.
    const LENGTH: usize = 5;
    // Prefixes 0 through 5 have twenty trees of at most six nodes each.
    const AUDIT_NODES: usize = 120;
    let row = Row { length: LENGTH };
    let scores = BestTable::new(&row)?;
    let trees = scores.recover();
    let optimum = trees
        .first_minimum_tree()?
        .expect("each prefix has a tiling");
    let tied = trees.co_minimal(Default::default())?;
    let ranked = trees.k_lowest(4, Default::default())?;
    let count = fast::tabulate(&row, &Count)?;
    let eager = fast::tabulate(&row, &ScoreTrees)?;

    assert_eq!(optimum.value, Cost::Finite(8));
    assert_eq!(count.answer(), Some(&8));
    assert_eq!(tied.len(), 3);
    assert_eq!(ranked[3].value, Cost::Finite(9));
    assert!(eager
        .answer()
        .unwrap()
        .trees
        .iter()
        .eq(tied.iter().map(|answer| &answer.tree)));

    let chart = fast::reference_chart(&row)?;
    let audit = audit_bounded(
        &chart,
        &Count,
        AuditBudget {
            max_tree_nodes: AUDIT_NODES,
        },
        Default::default(),
    )?;
    assert!(audit.bellman.first_failure.is_none());
    assert!(audit.ambiguities.is_empty());
    println!(
        "Minimum {:?}, {} co-optimal tilings, {} derivations",
        optimum.value,
        tied.len(),
        count.answer().unwrap()
    );
    Ok(())
}
