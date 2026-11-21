use std::mem::size_of;

use crate::fast::{Fold, Table};
use crate::{reserve_table, Cell, Error};

use super::{fill_dense, fill_table, CellStore, Program, Tabulation};

#[derive(Debug, PartialEq, Eq)]
struct Run {
    first: Cell,
    offset: usize,
}

/// Compiled summaries in logical rank order, packed into inhabited runs.
/// Rank lookup uses a binary search over run starts.
#[derive(Debug, PartialEq, Eq)]
pub struct CompactTable<V> {
    values: Vec<V>,
    runs: Vec<Run>,
    count: usize,
    root: Cell,
    previous_inhabited: bool,
}

impl<V> CompactTable<V> {
    /// Number of logical ranks, including absent cells.
    pub fn cell_count(&self) -> usize {
        self.count
    }

    pub fn root(&self) -> Cell {
        self.root
    }

    pub fn answer(&self) -> Option<&V> {
        self.get(self.root)
    }

    /// Lookup by original logical rank. Absent and out-of-range ranks
    /// return `None`.
    pub fn get(&self, cell: Cell) -> Option<&V> {
        let (last, earlier) = self.runs.split_last()?;
        if let Some(displacement) = cell.checked_sub(last.first) {
            return self.values[last.offset..].get(displacement);
        }
        let index = earlier.partition_point(|run| run.first <= cell);
        let run = earlier.get(index.checked_sub(1)?)?;
        let limit = self.runs[index].offset;
        let displacement = cell - run.first;
        if displacement < limit - run.offset {
            Some(&self.values[run.offset + displacement])
        } else {
            None
        }
    }

    /// Number of stored summaries. An inhabited zero is stored.
    pub fn stored_cells(&self) -> usize {
        self.values.len()
    }

    /// Number of contiguous inhabited runs indexed by the table.
    pub fn run_count(&self) -> usize {
        self.runs.len()
    }
}

/// A compiled table selected under a caller-declared slot byte budget.
#[derive(Debug, PartialEq, Eq)]
pub enum BudgetedTable<V> {
    Dense(Table<V>),
    Packed(CompactTable<V>),
}

impl<V> BudgetedTable<V> {
    /// Number of logical ranks, including absent cells.
    pub fn cell_count(&self) -> usize {
        match self {
            Self::Dense(table) => table.cells().len(),
            Self::Packed(table) => table.cell_count(),
        }
    }

    pub fn root(&self) -> Cell {
        match self {
            Self::Dense(table) => table.root(),
            Self::Packed(table) => table.root(),
        }
    }

    pub fn answer(&self) -> Option<&V> {
        self.get(self.root())
    }

    /// Lookup by original logical rank. Absent and out-of-range ranks return `None`.
    pub fn get(&self, cell: Cell) -> Option<&V> {
        match self {
            Self::Dense(table) => table.cells().get(cell)?.as_ref(),
            Self::Packed(table) => table.get(cell),
        }
    }

    /// Bytes in the table's reported allocation capacities, including unused slots
    /// and packed run indices. See [`tabulate_with_budget`] for the budget scope.
    pub fn storage_bytes(&self) -> usize {
        match self {
            Self::Dense(table) => table.storage_bytes(),
            Self::Packed(table) => {
                table.values.capacity() * size_of::<V>() + table.runs.capacity() * size_of::<Run>()
            }
        }
    }
}

struct PackedStore<V> {
    table: CompactTable<V>,
    max_bytes: Option<usize>,
}

impl<V> CellStore<V> for PackedStore<V> {
    #[inline]
    fn get(&self, cell: Cell) -> Option<&V> {
        self.table.get(cell)
    }

    fn push(&mut self, value: Option<V>) -> Result<(), Error> {
        let table = &mut self.table;
        let inhabited = value.is_some();
        if let Some(value) = value {
            let starts_run = !table.previous_inhabited;
            if let Some(max_bytes) = self.max_bytes {
                let values = table.values.capacity().max(table.values.len() + 1);
                let runs = table
                    .runs
                    .capacity()
                    .max(table.runs.len() + usize::from(starts_run));
                check_packed_bytes::<V>(values, runs, max_bytes)?;
                if starts_run {
                    table
                        .runs
                        .try_reserve_exact(1)
                        .map_err(|_| Error::AllocationFailed)?;
                    check_packed_bytes::<V>(values, table.runs.capacity(), max_bytes)?;
                }
                table
                    .values
                    .try_reserve_exact(1)
                    .map_err(|_| Error::AllocationFailed)?;
                check_packed_bytes::<V>(table.values.capacity(), table.runs.capacity(), max_bytes)?;
            } else {
                if starts_run {
                    table
                        .runs
                        .try_reserve(1)
                        .map_err(|_| Error::AllocationFailed)?;
                }
                table
                    .values
                    .try_reserve(1)
                    .map_err(|_| Error::AllocationFailed)?;
            }
            if starts_run {
                table.runs.push(Run {
                    first: table.count,
                    offset: table.values.len(),
                });
            }
            table.values.push(value);
        }
        table.previous_inhabited = inhabited;
        table.count += 1;
        Ok(())
    }
}

fn check_packed_bytes<V>(values: usize, runs: usize, max_bytes: usize) -> Result<(), Error> {
    let bytes = values
        .checked_mul(size_of::<V>())
        .and_then(|value_bytes| value_bytes.checked_add(runs.checked_mul(size_of::<Run>())?));
    if bytes.is_some_and(|bytes| bytes <= max_bytes) {
        Ok(())
    } else {
        Err(Error::TableBudgetExceeded { max_bytes })
    }
}

/// Fill all logical ranks with the ordered, deterministic [`Fold`] contract.
/// Infer contiguous inhabited runs as cells finish and store one summary per
/// inhabited cell. Production order, ranks and evaluation errors match
/// [`super::tabulate`] with sufficient storage. Each run adds two indices.
/// Dense tables offer constant-time rank access.
pub fn tabulate_compact<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
) -> Result<CompactTable<A::Value>, Error> {
    fill_packed(grammar, algebra, None)
}

/// Fill every logical rank with the ordered, deterministic [`Fold`] contract.
/// Use dense storage if its slot capacity fits. Otherwise try packing inhabited
/// runs, checking both allocation capacities as the table grows. Packed
/// growth requests only the slots needed so far. If those slots cannot fit,
/// return [`Error::TableBudgetExceeded`].
///
/// The budget counts the two layouts' Vec slot capacity, including run indices
/// and padding within each slot. It excludes allocator bookkeeping, transient
/// reallocation, the grammar, evaluation scratch and allocations owned by values
/// (for example a value's nested Vec buffer). Allocation can also fail within budget.
pub fn tabulate_with_budget<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
    max_bytes: usize,
) -> Result<BudgetedTable<A::Value>, Error> {
    let slots = grammar.cell_count();
    let slot_bytes = size_of::<Option<A::Value>>();
    if slots
        .checked_mul(slot_bytes)
        .is_some_and(|bytes| bytes <= max_bytes)
    {
        let cells = reserve_table(slots)?;
        if cells.capacity() * slot_bytes <= max_bytes {
            return fill_dense(grammar, algebra, cells).map(BudgetedTable::Dense);
        }
    }
    fill_packed(grammar, algebra, Some(max_bytes)).map(BudgetedTable::Packed)
}

fn fill_packed<G: Program, A: Fold<G::Op>>(
    grammar: &G,
    algebra: &A,
    max_bytes: Option<usize>,
) -> Result<CompactTable<A::Value>, Error> {
    let store = fill_table(
        grammar,
        Tabulation {
            cells: PackedStore {
                table: CompactTable {
                    values: Vec::new(),
                    runs: Vec::new(),
                    count: 0,
                    root: grammar.root(),
                    previous_inhabited: false,
                },
                max_bytes,
            },
            chosen: Ok(None),
            algebra,
        },
    )?;
    Ok(store.table)
}
