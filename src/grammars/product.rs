use crate::fast::RuleSource;
use crate::{reserve_table, Cell, Chart, Error, Operator, Rule};

/// Constructors of the one-sequence prefix grammar.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prefix<T> {
    Start,
    Token(T),
}

impl<T: Clone> Operator for Prefix<T> {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Token(_)))
    }
}

/// One ranked cell per prefix, with a single derivation for each prefix.
pub fn sequence_prefixes<T: Clone>(input: &[T]) -> Result<Chart<Prefix<T>>, Error> {
    let size = input.len().checked_add(1).ok_or(Error::Overflow)?;
    let mut cells = reserve_table(size)?;
    cells.push(vec![Rule::new(Prefix::Start, [])]);
    cells.extend(
        input
            .iter()
            .cloned()
            .enumerate()
            .map(|(rank, token)| vec![Rule::new(Prefix::Token(token), [rank])]),
    );
    Chart::new(cells, input.len())
}

/// A product constructor. A gap leaves the other operand's cell unchanged.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProductColumn<L, R> {
    Start(L, R),
    Both(L, R),
    Left(L),
    Right(R),
}

impl<L: Clone, R: Clone> Operator for ProductColumn<L, R> {
    fn arity(&self) -> usize {
        usize::from(!matches!(self, Self::Start(..)))
    }
}

/// The alignment product of two ranked nullary/unary grammars.
///
/// Pairs of nullary rules terminate together. Unary rules advance both tracks
/// or only one track with a gap. The product emits paired, left-only, then
/// right-only rules, preserving operand order and duplicate occurrences.
/// Ranks are row-major with the right operand varying fastest.
///
/// Use [`crate::fast::reference_chart`] to materialize the product for an audit.
pub struct PrefixProduct<'a, L, R> {
    left: &'a Chart<L>,
    right: &'a Chart<R>,
    size: usize,
}

impl<'a, L: Operator, R: Operator> PrefixProduct<'a, L, R> {
    pub fn new(left: &'a Chart<L>, right: &'a Chart<R>) -> Result<Self, Error> {
        check_operand(left, "left product operand")?;
        check_operand(right, "right product operand")?;
        let size = left
            .cells()
            .len()
            .checked_mul(right.cells().len())
            .ok_or(Error::Overflow)?;
        Ok(Self { left, right, size })
    }

    fn rank(&self, left: Cell, right: Cell) -> Cell {
        left * self.right.cells().len() + right
    }
}

fn check_operand<O>(chart: &Chart<O>, name: &str) -> Result<(), Error> {
    if chart
        .cells()
        .iter()
        .flatten()
        .any(|rule| rule.children.len() > 1)
    {
        return Err(Error::UnsupportedGrammar {
            name: name.into(),
            reason: "the prefix product requires nullary or unary rules",
        });
    }
    Ok(())
}

impl<L: Operator, R: Operator> RuleSource for PrefixProduct<'_, L, R> {
    type Op = ProductColumn<L, R>;

    fn cell_count(&self) -> usize {
        self.size
    }

    fn root(&self) -> Cell {
        self.rank(self.left.root(), self.right.root())
    }

    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(Self::Op, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.size {
            return Err(Error::CellOutOfRange(cell));
        }
        let width = self.right.cells().len();
        let (i, j) = (cell / width, cell % width);
        let left = &self.left.cells()[i];
        let right = &self.right.cells()[j];
        for l in left {
            for r in right {
                match (l.children.as_slice(), r.children.as_slice()) {
                    ([], []) => emit(
                        ProductColumn::Start(l.operator.clone(), r.operator.clone()),
                        &[],
                    )?,
                    ([a], [b]) => emit(
                        ProductColumn::Both(l.operator.clone(), r.operator.clone()),
                        &[self.rank(*a, *b)],
                    )?,
                    _ => {}
                }
            }
        }
        for l in left {
            if let [a] = l.children.as_slice() {
                emit(ProductColumn::Left(l.operator.clone()), &[self.rank(*a, j)])?;
            }
        }
        for r in right {
            if let [b] = r.children.as_slice() {
                emit(
                    ProductColumn::Right(r.operator.clone()),
                    &[self.rank(i, *b)],
                )?;
            }
        }
        Ok(())
    }
}
