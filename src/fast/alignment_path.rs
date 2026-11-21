use crate::grammars::Align;
use crate::{reserve_table, Error, Tree};

/// A minimum unit-cost global alignment and its ordered columns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlignmentPath {
    distance: usize,
    columns: Vec<Align>,
}

impl AlignmentPath {
    pub fn distance(&self) -> usize {
        self.distance
    }

    /// Alignment columns from the start of the input to the end.
    /// The implicit nullary `Align::Start` is excluded.
    pub fn columns(&self) -> &[Align] {
        &self.columns
    }

    /// Materialize the corresponding unary witness tree.
    pub fn into_tree(self) -> Tree<Align> {
        self.columns.into_iter().fold(
            Tree {
                operator: Align::Start,
                children: Vec::new(),
            },
            |child, operator| Tree {
                operator,
                children: vec![child],
            },
        )
    }
}

/// Find the first minimum derivation of [`crate::grammars::alignment`].
///
/// Uses unit mismatch and gap costs. Ties use the reference predecessor
/// order (diagonal, left, right) during traceback. The returned path is
/// compact even for a long skinny alignment. For input lengths `m,n` the
/// algorithm uses `O(min(m,n) + 1)` row space and logarithmic recursion
/// space, excluding the output. Time is `O(mn + m + n + 1)`.
pub fn alignment_linear_space(left: &[u8], right: &[u8]) -> Result<AlignmentPath, Error> {
    let max_columns = left.len().checked_add(right.len()).ok_or(Error::Overflow)?;
    let mut columns = reserve_table(max_columns)?;
    let transposed = left.len() < right.len();
    let (rows, cols) = if transposed {
        (right, left)
    } else {
        (left, right)
    };
    let width = cols.len().checked_add(1).ok_or(Error::Overflow)?;
    let mut scratch = reserve_table(width)?;
    scratch.resize(width, TraceCell::default());
    let distance = recover(rows, cols, !transposed, &mut scratch, &mut columns);
    if transposed {
        for column in &mut columns {
            *column = match *column {
                Align::Diagonal { left, right } => Align::Diagonal {
                    left: right,
                    right: left,
                },
                Align::Left(token) => Align::Right(token),
                Align::Right(token) => Align::Left(token),
                Align::Start => unreachable!("a path has only alignment columns"),
            };
        }
    }
    Ok(AlignmentPath { distance, columns })
}

#[derive(Clone, Copy, Default)]
struct Crossing {
    before: usize,
    after: usize,
}

#[derive(Clone, Copy, Default)]
struct TraceCell {
    distance: usize,
    crossing: Crossing,
}

fn recover(
    rows: &[u8],
    cols: &[u8],
    vertical_first: bool,
    scratch: &mut [TraceCell],
    path: &mut Vec<Align>,
) -> usize {
    if rows.is_empty() {
        path.extend(cols.iter().copied().map(Align::Right));
        return cols.len();
    }
    if cols.is_empty() {
        path.extend(rows.iter().copied().map(Align::Left));
        return rows.len();
    }

    let middle = rows.len().div_ceil(2);
    let answer = midpoint_edge(rows, cols, middle, vertical_first, scratch);
    let Crossing { before, after } = answer.crossing;
    recover(
        &rows[..middle - 1],
        &cols[..before],
        vertical_first,
        scratch,
        path,
    );
    let left = rows[middle - 1];
    path.push(if before == after {
        Align::Left(left)
    } else {
        Align::Diagonal {
            left,
            right: cols[before],
        }
    });
    recover(
        &rows[middle..],
        &cols[after..],
        vertical_first,
        scratch,
        path,
    );
    answer.distance
}

fn midpoint_edge(
    rows: &[u8],
    cols: &[u8],
    middle: usize,
    vertical_first: bool,
    scratch: &mut [TraceCell],
) -> TraceCell {
    let row = &mut scratch[..=cols.len()];
    for (j, cell) in row.iter_mut().enumerate() {
        *cell = TraceCell {
            distance: j,
            crossing: Crossing::default(),
        };
    }
    for (index, &left) in rows.iter().enumerate() {
        let at_middle = index + 1 == middle;
        let mut northwest = row[0];
        // The first column can cross only at column zero.
        row[0].distance = index + 1;
        let mut west = row[0];
        for (j, (&right, slot)) in cols.iter().zip(&mut row[1..]).enumerate() {
            let north = *slot;
            let diagonal = northwest.distance + usize::from(left != right);
            let vertical = north.distance + 1;
            let horizontal = west.distance + 1;
            // The selected predecessor carries its first crossing of the
            // middle row. At a crossing, this edge supplies the label.
            let (distance, crossing) = if diagonal <= vertical && diagonal <= horizontal {
                (
                    diagonal,
                    if at_middle {
                        Crossing {
                            before: j,
                            after: j + 1,
                        }
                    } else {
                        northwest.crossing
                    },
                )
            } else if vertical < horizontal || (vertical_first && vertical == horizontal) {
                (
                    vertical,
                    if at_middle {
                        Crossing {
                            before: j + 1,
                            after: j + 1,
                        }
                    } else {
                        north.crossing
                    },
                )
            } else {
                (horizontal, west.crossing)
            };
            west = TraceCell { distance, crossing };
            *slot = west;
            northwest = north;
        }
    }
    row[cols.len()]
}
