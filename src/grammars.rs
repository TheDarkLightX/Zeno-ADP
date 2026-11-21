use crate::algebras::{Cost, ScoredOperator};
pub(crate) use crate::compiled::ProductionSink as RankedRules;
use crate::compiled::{schedule, Program};
use crate::fast::RuleSource;
use crate::{reserve_table, Cell, Chart, Error, Operator, Rule};

struct Emit<F>(F);

impl<O, F: FnMut(O, &[Cell]) -> Result<(), Error>> RankedRules<O> for Emit<F> {
    #[inline]
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        (self.0)(operator, children)
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        Ok(())
    }
}

// Rank nonempty intervals by length, then by start. Some grammars reserve an
// earlier rank for their empty interval.
struct IntervalRanks {
    offsets: Vec<Cell>,
    size: usize,
}

impl IntervalRanks {
    fn new(n: usize, first: Cell) -> Result<Self, Error> {
        let mut offsets = reserve_table(n)?;
        let mut size = first;
        for length in 1..=n {
            offsets.push(size);
            size = size.checked_add(n - length + 1).ok_or(Error::Overflow)?;
        }
        Ok(Self { offsets, size })
    }

    fn rank(&self, start: usize, length: usize) -> Cell {
        self.offsets[length - 1] + start
    }

    fn interval(&self, cell: Cell) -> (usize, usize) {
        let length = self.offsets.partition_point(|&offset| offset <= cell);
        (cell - self.offsets[length - 1], length)
    }
}

struct ChartBuilder<O> {
    cells: Vec<Vec<Rule<O>>>,
    pending: Vec<Rule<O>>,
}

impl<O: Operator> ChartBuilder<O> {
    fn build(source: impl Program<Op = O>) -> Result<Chart<O>, Error> {
        let mut builder = Self {
            cells: reserve_table(source.cell_count())?,
            pending: Vec::new(),
        };
        source.fill(&mut builder)?;
        Chart::new(builder.cells, source.root())
    }
}

impl<O> RankedRules<O> for ChartBuilder<O> {
    fn rule_slice(&mut self, _: &str, operator: O, children: &[Cell]) -> Result<(), Error> {
        self.pending.push(Rule::new(operator, children));
        Ok(())
    }

    fn finish_cell(&mut self) -> Result<(), Error> {
        self.cells.push(std::mem::take(&mut self.pending));
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fold {
    Empty,
    Unpaired { at: usize },
    Pair { left: usize, right: usize },
}

impl Operator for Fold {
    fn arity(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Unpaired { .. } => 1,
            Self::Pair { .. } => 2,
        }
    }
}

impl ScoredOperator for Fold {
    fn cost(&self) -> Cost {
        Cost::Finite(match self {
            Self::Pair { .. } => -1,
            _ => 0,
        })
    }
}

fn complementary(left: u8, right: u8) -> bool {
    matches!(
        (left, right),
        (b'A', b'U') | (b'U', b'A') | (b'C', b'G') | (b'G', b'C')
    )
}

/// Nussinov pair maximization with Watson–Crick pairs and a caller-selected
/// minimum number of intervening bases. Each rule classifies the leftmost base.
pub fn nussinov(sequence: &[u8], min_loop: usize) -> Result<Chart<Fold>, Error> {
    ChartBuilder::build(nussinov_source(sequence, min_loop)?)
}

/// Replay the Nussinov grammar one cell at a time.
pub fn nussinov_source(
    sequence: &[u8],
    min_loop: usize,
) -> Result<impl Program<Op = Fold> + '_, Error> {
    NussinovSource::new(sequence, min_loop)
}

struct NussinovSource<'a> {
    sequence: &'a [u8],
    min_loop: usize,
    ranks: IntervalRanks,
}

impl<'a> NussinovSource<'a> {
    fn new(sequence: &'a [u8], min_loop: usize) -> Result<Self, Error> {
        for &base in sequence {
            if !b"AUCG".contains(&base) {
                return Err(Error::InvalidSymbol(base));
            }
        }
        Ok(Self {
            sequence,
            min_loop,
            ranks: IntervalRanks::new(sequence.len(), 1)?,
        })
    }

    fn span(&self, start: usize, length: usize) -> Cell {
        if length == 0 {
            0
        } else {
            self.ranks.rank(start, length)
        }
    }

    fn interval_rules(
        &self,
        start: usize,
        length: usize,
        output: &mut impl RankedRules<Fold>,
    ) -> Result<(), Error> {
        let end = start + length;
        output.rule(
            "fold/unpaired",
            Fold::Unpaired { at: start },
            [self.span(start + 1, length - 1)],
        )?;
        for right in start + 1..end {
            let inside = right - start - 1;
            if inside >= self.min_loop && complementary(self.sequence[start], self.sequence[right])
            {
                output.rule(
                    "fold/pair",
                    Fold::Pair { left: start, right },
                    [
                        self.span(start + 1, inside),
                        self.span(right + 1, end - right - 1),
                    ],
                )?;
            }
        }
        Ok(())
    }
}

impl RuleSource for NussinovSource<'_> {
    type Op = Fold;
    fn cell_count(&self) -> usize {
        self.ranks.size
    }
    fn root(&self) -> Cell {
        self.ranks.size - 1
    }
    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(Fold, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.cell_count() {
            return Err(Error::CellOutOfRange(cell));
        }
        if cell == 0 {
            emit(Fold::Empty, &[])
        } else {
            let (start, length) = self.ranks.interval(cell);
            self.interval_rules(start, length, &mut Emit(emit))
        }
    }
}

schedule!(NussinovSource<'_>, Fold, |source, output| {
    output.rule("fold/empty", Fold::Empty, [])?;
    output.finish_cell()?;
    for length in 1..=source.sequence.len() {
        for start in 0..=source.sequence.len() - length {
            source.interval_rules(start, length, output)?;
            output.finish_cell()?;
        }
    }
    Ok(())
});

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Align {
    Start,
    Diagonal { left: u8, right: u8 },
    Left(u8),
    Right(u8),
}

impl Operator for Align {
    fn arity(&self) -> usize {
        usize::from(*self != Self::Start)
    }
}

impl ScoredOperator for Align {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Start => 0,
            Self::Diagonal { left, right } => i64::from(left != right),
            Self::Left(_) | Self::Right(_) => 1,
        })
    }
}

/// Global alignment with unit mismatch and gap costs. Each rule extends a
/// prefix alignment by one column. Adjacent gaps on opposite sides are allowed.
pub fn alignment(left: &[u8], right: &[u8]) -> Result<Chart<Align>, Error> {
    ChartBuilder::build(alignment_source(left, right)?)
}

/// Emit diagonal, left and right columns in reference derivation order.
fn columns(
    left: &[u8],
    right: &[u8],
    i: usize,
    j: usize,
    mut extend: impl FnMut(&str, usize, usize, Align) -> Result<(), Error>,
) -> Result<(), Error> {
    if i > 0 && j > 0 {
        extend(
            "diagonal",
            i - 1,
            j - 1,
            Align::Diagonal {
                left: left[i - 1],
                right: right[j - 1],
            },
        )?;
    }
    if i > 0 {
        extend("left", i - 1, j, Align::Left(left[i - 1]))?;
    }
    if j > 0 {
        extend("right", i, j - 1, Align::Right(right[j - 1]))?;
    }
    Ok(())
}

struct AlignmentGrid<'a> {
    left: &'a [u8],
    right: &'a [u8],
    width: usize,
    height: usize,
    size: usize,
}

impl<'a> AlignmentGrid<'a> {
    fn new(left: &'a [u8], right: &'a [u8]) -> Result<Self, Error> {
        let width = right.len().checked_add(1).ok_or(Error::Overflow)?;
        let height = left.len().checked_add(1).ok_or(Error::Overflow)?;
        let size = width.checked_mul(height).ok_or(Error::Overflow)?;
        Ok(Self {
            left,
            right,
            width,
            height,
            size,
        })
    }

    #[inline]
    fn prefix_rules(
        &self,
        i: usize,
        j: usize,
        output: &mut impl RankedRules<Align>,
    ) -> Result<(), Error> {
        if (i, j) == (0, 0) {
            output.rule("alignment/start", Align::Start, [])?;
        }
        columns(self.left, self.right, i, j, |site, row, col, op| {
            output.rule(site, op, [row * self.width + col])
        })
    }
}

impl RuleSource for AlignmentGrid<'_> {
    type Op = Align;
    fn cell_count(&self) -> usize {
        self.size
    }
    fn root(&self) -> Cell {
        self.size - 1
    }
    fn rules_at(
        &self,
        cell: Cell,
        emit: impl FnMut(Align, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.cell_count() {
            return Err(Error::CellOutOfRange(cell));
        }
        self.prefix_rules(cell / self.width, cell % self.width, &mut Emit(emit))
    }
}

/// Replay the global alignment grammar one prefix pair at a time.
pub fn alignment_source<'a>(
    left: &'a [u8],
    right: &'a [u8],
) -> Result<impl Program<Op = Align> + 'a, Error> {
    AlignmentGrid::new(left, right)
}

schedule!(AlignmentGrid<'_>, Align, |source, output| {
    for i in 0..source.height {
        for j in 0..source.width {
            source.prefix_rules(i, j, output)?;
            output.finish_cell()?;
        }
    }
    Ok(())
});

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LocalAlign {
    Empty,
    Start { left: usize, right: usize },
    Column(Align),
    End,
}

impl Operator for LocalAlign {
    fn arity(&self) -> usize {
        match self {
            Self::Empty | Self::Start { .. } => 0,
            Self::Column(_) | Self::End => 1,
        }
    }
}

/// Match reward is 2. Mismatches and gaps cost 1.
impl ScoredOperator for LocalAlign {
    fn cost(&self) -> Cost {
        match self {
            Self::Column(Align::Diagonal { left, right }) if left == right => Cost::Finite(-2),
            Self::Column(column) => column.cost(),
            _ => Cost::Finite(0),
        }
    }
}

/// Local alignment with one empty candidate and all nonempty column paths
/// over any two substrings. Opposing adjacent gaps are allowed.
pub fn local_alignment(left: &[u8], right: &[u8]) -> Result<Chart<LocalAlign>, Error> {
    ChartBuilder::build(local_alignment_source(left, right)?)
}

struct LocalSource<'a> {
    grid: AlignmentGrid<'a>,
    root: Cell,
}

impl<'a> LocalSource<'a> {
    fn new(left: &'a [u8], right: &'a [u8]) -> Result<Self, Error> {
        let grid = AlignmentGrid::new(left, right)?;
        let root = grid.size.checked_add(grid.size).ok_or(Error::Overflow)?;
        Ok(Self { grid, root })
    }

    fn path_rules(
        &self,
        i: usize,
        j: usize,
        output: &mut impl RankedRules<LocalAlign>,
    ) -> Result<(), Error> {
        let grid = &self.grid;
        columns(grid.left, grid.right, i, j, |_, row, col, column| {
            let predecessor = row * grid.width + col;
            let op = LocalAlign::Column(column);
            let (start, extend) = match column {
                Align::Diagonal { .. } => ("local/diagonal-from-start", "local/diagonal-from-path"),
                Align::Left(_) => ("local/left-from-start", "local/left-from-path"),
                Align::Right(_) => ("local/right-from-start", "local/right-from-path"),
                Align::Start => unreachable!("columns only emits nonempty columns"),
            };
            output.rule(start, op, [predecessor])?;
            output.rule(extend, op, [grid.size + predecessor])
        })
    }

    fn end_rules(&self, output: &mut impl RankedRules<LocalAlign>) -> Result<(), Error> {
        output.rule("local/empty", LocalAlign::Empty, [])?;
        for endpoint in self.grid.size..self.root {
            output.rule("local/end", LocalAlign::End, [endpoint])?;
        }
        Ok(())
    }
}

impl RuleSource for LocalSource<'_> {
    type Op = LocalAlign;
    fn cell_count(&self) -> usize {
        self.root + 1
    }
    fn root(&self) -> Cell {
        self.root
    }
    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(LocalAlign, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.cell_count() {
            return Err(Error::CellOutOfRange(cell));
        }
        let (width, size) = (self.grid.width, self.grid.size);
        if cell < size {
            emit(
                LocalAlign::Start {
                    left: cell / width,
                    right: cell % width,
                },
                &[],
            )
        } else if cell < self.root {
            let prefix = cell - size;
            self.path_rules(prefix / width, prefix % width, &mut Emit(emit))
        } else {
            self.end_rules(&mut Emit(emit))
        }
    }
}

/// Replay the positional local alignment grammar one cell at a time.
pub fn local_alignment_source<'a>(
    left: &'a [u8],
    right: &'a [u8],
) -> Result<impl Program<Op = LocalAlign> + 'a, Error> {
    LocalSource::new(left, right)
}

schedule!(LocalSource<'_>, LocalAlign, |source, output| {
    for i in 0..source.grid.height {
        for j in 0..source.grid.width {
            output.rule("local/start", LocalAlign::Start { left: i, right: j }, [])?;
            output.finish_cell()?;
        }
    }
    for i in 0..source.grid.height {
        for j in 0..source.grid.width {
            source.path_rules(i, j, output)?;
            output.finish_cell()?;
        }
    }
    source.end_rules(output)?;
    output.finish_cell()?;
    Ok(())
});

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MatrixChain {
    Matrix {
        at: usize,
    },
    Multiply {
        left: usize,
        split: usize,
        right: usize,
        cost: i64,
    },
}

impl Operator for MatrixChain {
    fn arity(&self) -> usize {
        match self {
            Self::Matrix { .. } => 0,
            Self::Multiply { .. } => 2,
        }
    }
}

impl ScoredOperator for MatrixChain {
    fn cost(&self) -> Cost {
        match *self {
            Self::Matrix { .. } => Cost::Finite(0),
            Self::Multiply { cost, .. } => Cost::Finite(cost),
        }
    }
}

/// All parenthesizations of a matrix chain. Adjacent dimensions describe
/// one matrix. Each split pays the number of scalar multiplications.
pub fn matrix_chain(dimensions: &[u32]) -> Result<Chart<MatrixChain>, Error> {
    ChartBuilder::build(matrix_chain_source(dimensions)?)
}

struct MatrixSource<'a> {
    dimensions: &'a [u32],
    ranks: IntervalRanks,
}

impl<'a> MatrixSource<'a> {
    fn new(dimensions: &'a [u32]) -> Result<Self, Error> {
        if dimensions.len() < 2 || dimensions.contains(&0) {
            return Err(Error::InvalidDimensions);
        }
        Ok(Self {
            dimensions,
            ranks: IntervalRanks::new(dimensions.len() - 1, 0)?,
        })
    }

    #[inline]
    fn splits(
        &self,
        left: usize,
        length: usize,
        output: &mut impl RankedRules<MatrixChain>,
    ) -> Result<(), Error> {
        let right = left + length;
        for split in left + 1..right {
            let cost = i64::from(self.dimensions[left])
                .checked_mul(i64::from(self.dimensions[split]))
                .and_then(|cost| cost.checked_mul(i64::from(self.dimensions[right])))
                .ok_or(Error::Overflow)?;
            output.rule(
                "matrix/multiply",
                MatrixChain::Multiply {
                    left,
                    split,
                    right,
                    cost,
                },
                [
                    self.ranks.rank(left, split - left),
                    self.ranks.rank(split, right - split),
                ],
            )?;
        }
        Ok(())
    }
}

impl RuleSource for MatrixSource<'_> {
    type Op = MatrixChain;
    fn cell_count(&self) -> usize {
        self.ranks.size
    }
    fn root(&self) -> Cell {
        self.ranks.size - 1
    }
    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(MatrixChain, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.cell_count() {
            return Err(Error::CellOutOfRange(cell));
        }
        if cell < self.dimensions.len() - 1 {
            emit(MatrixChain::Matrix { at: cell }, &[])
        } else {
            let (left, length) = self.ranks.interval(cell);
            self.splits(left, length, &mut Emit(emit))
        }
    }
}

/// Replay the matrix-chain grammar one interval at a time.
pub fn matrix_chain_source(
    dimensions: &[u32],
) -> Result<impl Program<Op = MatrixChain> + '_, Error> {
    MatrixSource::new(dimensions)
}

schedule!(MatrixSource<'_>, MatrixChain, |source, output| {
    let n = source.dimensions.len() - 1;
    for at in 0..n {
        output.rule("matrix/leaf", MatrixChain::Matrix { at }, [])?;
        output.finish_cell()?;
    }
    for length in 2..=n {
        for left in 0..=n - length {
            source.splits(left, length, output)?;
            output.finish_cell()?;
        }
    }
    Ok(())
});

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Item {
    pub weight: usize,
    pub value: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Knapsack {
    Empty,
    Skip { item: usize },
    Pick { item: usize, value: u32 },
}

impl Operator for Knapsack {
    fn arity(&self) -> usize {
        usize::from(*self != Self::Empty)
    }
}

impl ScoredOperator for Knapsack {
    fn cost(&self) -> Cost {
        match *self {
            Self::Pick { value, .. } => Cost::Finite(-i64::from(value)),
            _ => Cost::Finite(0),
        }
    }
}

/// All subsets satisfying a capacity in 0/1 knapsack. The score is the
/// negated sum of selected values. Identical items are distinct by index.
pub fn knapsack(items: &[Item], capacity: usize) -> Result<Chart<Knapsack>, Error> {
    ChartBuilder::build(knapsack_source(items, capacity)?)
}

struct KnapsackSource<'a> {
    items: &'a [Item],
    width: usize,
    size: usize,
}

impl<'a> KnapsackSource<'a> {
    fn new(items: &'a [Item], capacity: usize) -> Result<Self, Error> {
        let width = capacity.checked_add(1).ok_or(Error::Overflow)?;
        let height = items.len().checked_add(1).ok_or(Error::Overflow)?;
        let size = height.checked_mul(width).ok_or(Error::Overflow)?;
        Ok(Self { items, width, size })
    }

    fn item_rules(
        &self,
        item: usize,
        remaining: usize,
        output: &mut impl RankedRules<Knapsack>,
    ) -> Result<(), Error> {
        let Item { weight, value } = self.items[item];
        let base = item * self.width;
        output.rule("knapsack/skip", Knapsack::Skip { item }, [base + remaining])?;
        if weight <= remaining {
            output.rule(
                "knapsack/pick",
                Knapsack::Pick { item, value },
                [base + remaining - weight],
            )?;
        }
        Ok(())
    }
}

impl RuleSource for KnapsackSource<'_> {
    type Op = Knapsack;
    fn cell_count(&self) -> usize {
        self.size
    }
    fn root(&self) -> Cell {
        self.size - 1
    }
    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(Knapsack, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if cell >= self.cell_count() {
            return Err(Error::CellOutOfRange(cell));
        }
        let row = cell / self.width;
        if row == 0 {
            emit(Knapsack::Empty, &[])
        } else {
            self.item_rules(row - 1, cell % self.width, &mut Emit(emit))
        }
    }
}

/// Replay the 0/1 knapsack grammar one item prefix and capacity at a time.
pub fn knapsack_source(
    items: &[Item],
    capacity: usize,
) -> Result<impl Program<Op = Knapsack> + '_, Error> {
    KnapsackSource::new(items, capacity)
}

schedule!(KnapsackSource<'_>, Knapsack, |source, output| {
    for _ in 0..source.width {
        output.rule("knapsack/empty", Knapsack::Empty, [])?;
        output.finish_cell()?;
    }
    for item in 0..source.items.len() {
        for remaining in 0..source.width {
            source.item_rules(item, remaining, output)?;
            output.finish_cell()?;
        }
    }
    Ok(())
});
