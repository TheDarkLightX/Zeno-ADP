//! Exact minimization of binary factors on a supplied tree decomposition.
//!
//! This scaling demonstration compiles bag assignments and separator messages
//! into the existing ranked engine. A feasible witness is an original assignment.

use std::fmt;

use num_bigint::BigInt;

use crate::fast::{self, Fold, RuleSource};
use crate::{Algebra, Cell, Operator};

/// A local integer cost table. Index a variable by `false = 0` or `true = 1`.
/// A `None` entry forbids that local assignment.
#[derive(Clone, Debug)]
pub enum Factor {
    Unary {
        variable: usize,
        costs: [Option<BigInt>; 2],
    },
    Pair {
        left: usize,
        right: usize,
        costs: [[Option<BigInt>; 2]; 2],
    },
}

impl Factor {
    fn scope(&self) -> (usize, Option<usize>) {
        match *self {
            Self::Unary { variable, .. } => (variable, None),
            Self::Pair { left, right, .. } => (left, Some(right)),
        }
    }

    fn cost(&self, first: bool, second: bool) -> Option<&BigInt> {
        match self {
            Self::Unary { costs, .. } => costs[usize::from(first)].as_ref(),
            Self::Pair { costs, .. } => costs[usize::from(first)][usize::from(second)].as_ref(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Bag {
    pub variables: Vec<usize>,
    /// Indices in the original factor array. Each factor has exactly one owner.
    pub factors: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct Decomposition {
    pub bags: Vec<Bag>,
    /// Undirected edges in the bag tree. Each edge occurs once.
    pub edges: Vec<(usize, usize)>,
    pub root: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    BagTree,
    UnknownVariable { bag: usize, variable: usize },
    RepeatedVariable { bag: usize, variable: usize },
    MissingVariable(usize),
    RunningIntersection(usize),
    InvalidFactor(usize),
    DuplicateOwnership(usize),
    MissingOwnership(usize),
    UncoveredFactor { bag: usize, factor: usize },
    TableSize,
    Ranked(crate::Error),
    CertificateSize { expected: usize, actual: usize },
    CellValue(Cell),
    Assignment,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::BagTree => write!(f, "bags and edges must form a rooted tree"),
            Self::UnknownVariable { bag, variable } => {
                write!(f, "bag {bag} contains absent variable {variable}")
            }
            Self::RepeatedVariable { bag, variable } => {
                write!(f, "bag {bag} repeats variable {variable}")
            }
            Self::MissingVariable(variable) => {
                write!(f, "variable {variable} is absent from all bags")
            }
            Self::RunningIntersection(variable) => {
                write!(f, "bags containing variable {variable} are disconnected")
            }
            Self::InvalidFactor(factor) => write!(f, "invalid factor or factor index {factor}"),
            Self::DuplicateOwnership(factor) => write!(f, "factor {factor} has multiple owners"),
            Self::MissingOwnership(factor) => write!(f, "factor {factor} has no owner"),
            Self::UncoveredFactor { bag, factor } => {
                write!(f, "bag {bag} does not contain the scope of factor {factor}")
            }
            Self::TableSize => write!(f, "assignment rank count exceeds addressable storage"),
            Self::Ranked(ref source) => source.fmt(f),
            Self::CertificateSize { expected, actual } => {
                write!(f, "certificate gives {actual} values for {expected} ranks")
            }
            Self::CellValue(cell) => {
                write!(f, "certificate disagrees with the reference at rank {cell}")
            }
            Self::Assignment => write!(
                f,
                "assignment is infeasible or does not attain the certified optimum"
            ),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Ranked(source) => Some(source),
            _ => None,
        }
    }
}

impl From<crate::Error> for Error {
    fn from(source: crate::Error) -> Self {
        Self::Ranked(source)
    }
}

#[derive(Clone, Debug)]
pub struct BagLayout {
    variables: Vec<usize>,
    separator_len: usize,
    first: Cell,
    assignment_count: usize,
    separator_count: usize,
    owned: Vec<(usize, usize, usize)>,
    children: Vec<(usize, Vec<usize>)>,
}

impl BagLayout {
    /// Variable order for the bag mask, from the least significant bit.
    /// The parent separator comes first, then the remaining variables in
    /// ascending ID order.
    pub fn variables(&self) -> &[usize] {
        &self.variables
    }

    /// Variable order for the separator mask, from the least significant bit.
    /// Shared variable IDs are ascending. The root separator is empty.
    pub fn separator(&self) -> &[usize] {
        &self.variables[..self.separator_len]
    }

    pub fn assignment_count(&self) -> usize {
        self.assignment_count
    }

    pub fn separator_count(&self) -> usize {
        self.separator_count
    }

    pub fn assignment_cell(&self, mask: usize) -> Option<Cell> {
        (mask < self.assignment_count).then(|| self.first + mask)
    }

    pub fn separator_cell(&self, mask: usize) -> Option<Cell> {
        (mask < self.separator_count).then(|| self.first + self.assignment_count + mask)
    }

    fn assignments_extending(&self, separator: usize) -> impl Iterator<Item = usize> {
        (separator..self.assignment_count).step_by(self.separator_count)
    }

    fn variable_position(&self, variable: usize) -> usize {
        self.variables
            .iter()
            .position(|&id| id == variable)
            .unwrap()
    }
}

/// An **Exact** result after verification against the compiled instance.
/// The table includes every bag-assignment and separator cell, with `None`
/// for infeasible subproblems. An infeasible instance has no assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    pub table: Vec<Option<BigInt>>,
    pub assignment: Option<Vec<bool>>,
}

#[derive(Clone, Debug)]
pub struct Compiled {
    variable_count: usize,
    factors: Vec<Factor>,
    bags: Vec<BagLayout>,
    postorder: Vec<usize>,
    cell_count: usize,
}

fn bit(mask: usize, position: usize) -> bool {
    mask & (1 << position) != 0
}

fn project(mask: usize, positions: &[usize]) -> usize {
    positions.iter().enumerate().fold(0, |bits, (next, &old)| {
        bits | (usize::from(bit(mask, old)) << next)
    })
}

fn binary_rows(variables: usize) -> Result<usize, Error> {
    // A mask has one bit per binary variable, and the number of rows must
    // itself fit in a rank. Reject the count before allocating any table.
    u32::try_from(variables)
        .ok()
        .and_then(|width| 1usize.checked_shl(width))
        .ok_or(Error::TableSize)
}

fn rooted_tree(tree: &Decomposition) -> Result<(Vec<usize>, Vec<usize>), Error> {
    let n = tree.bags.len();
    if tree.root >= n || tree.edges.len() != n - 1 {
        return Err(Error::BagTree);
    }
    let mut neighbors = vec![Vec::new(); n];
    for &(a, b) in &tree.edges {
        if a >= n || b >= n || a == b {
            return Err(Error::BagTree);
        }
        neighbors[a].push(b);
        neighbors[b].push(a);
    }
    let mut parents = vec![None; n];
    parents[tree.root] = Some(tree.root);
    let mut order = vec![tree.root];
    let mut cursor = 0;
    while cursor < order.len() {
        let bag = order[cursor];
        for &next in &neighbors[bag] {
            if parents[bag] == Some(next) {
                continue;
            }
            if parents[next].replace(bag).is_some() {
                return Err(Error::BagTree);
            }
            order.push(next);
        }
        cursor += 1;
    }
    if order.len() != n {
        return Err(Error::BagTree);
    }
    order.reverse();
    Ok((parents.into_iter().map(Option::unwrap).collect(), order))
}

impl Compiled {
    /// Check the supplied tree, variable coverage and running intersection,
    /// and assign every factor to exactly one bag containing its full scope.
    pub fn new(
        variable_count: usize,
        factors: Vec<Factor>,
        tree: Decomposition,
    ) -> Result<Self, Error> {
        let (parents, postorder) = rooted_tree(&tree)?;
        for (id, factor) in factors.iter().enumerate() {
            let (a, b) = factor.scope();
            if a >= variable_count || b.is_some_and(|b| b >= variable_count || a == b) {
                return Err(Error::InvalidFactor(id));
            }
        }

        let mut variables = Vec::with_capacity(tree.bags.len());
        for (id, bag) in tree.bags.iter().enumerate() {
            let mut sorted = bag.variables.clone();
            sorted.sort_unstable();
            if let Some(&variable) = sorted.last().filter(|&&v| v >= variable_count) {
                return Err(Error::UnknownVariable { bag: id, variable });
            }
            if let Some(repeat) = sorted.windows(2).find(|pair| pair[0] == pair[1]) {
                return Err(Error::RepeatedVariable {
                    bag: id,
                    variable: repeat[0],
                });
            }
            variables.push(sorted);
        }

        let mut introduced = crate::reserve_table(variable_count)?;
        introduced.resize(variable_count, false);
        let mut ownership = vec![false; factors.len()];
        let mut layouts = Vec::with_capacity(tree.bags.len());
        for (id, bag) in tree.bags.iter().enumerate() {
            let (mut ordered, private): (Vec<_>, Vec<_>) =
                variables[id].iter().copied().partition(|variable| {
                    id != tree.root && variables[parents[id]].binary_search(variable).is_ok()
                });
            // In a rooted tree the bags of a variable form a connected
            // region exactly when it is introduced once.
            for &variable in &private {
                if std::mem::replace(&mut introduced[variable], true) {
                    return Err(Error::RunningIntersection(variable));
                }
            }
            let separator_len = ordered.len();
            ordered.extend(private);
            let mut owned = Vec::with_capacity(bag.factors.len());
            for &factor in &bag.factors {
                let marked = ownership
                    .get_mut(factor)
                    .ok_or(Error::InvalidFactor(factor))?;
                if std::mem::replace(marked, true) {
                    return Err(Error::DuplicateOwnership(factor));
                }
                let (first, second) = factors[factor].scope();
                let locate = |variable| {
                    ordered
                        .iter()
                        .position(|&v| v == variable)
                        .ok_or(Error::UncoveredFactor { bag: id, factor })
                };
                let first = locate(first)?;
                let second = second.map(locate).transpose()?.unwrap_or(first);
                owned.push((factor, first, second));
            }
            layouts.push(BagLayout {
                assignment_count: binary_rows(ordered.len())?,
                separator_count: binary_rows(separator_len)?,
                variables: ordered,
                separator_len,
                first: 0,
                owned,
                children: Vec::new(),
            });
        }
        if let Some(variable) = introduced.iter().position(|&present| !present) {
            return Err(Error::MissingVariable(variable));
        }
        if let Some(factor) = ownership.iter().position(|&present| !present) {
            return Err(Error::MissingOwnership(factor));
        }

        let mut cell_count = 0usize;
        for &bag in &postorder {
            let layout = &mut layouts[bag];
            layout.first = cell_count;
            cell_count = cell_count
                .checked_add(layout.assignment_count)
                .and_then(|size| size.checked_add(layout.separator_count))
                .ok_or(Error::TableSize)?;
            let parent = parents[bag];
            if parent != bag {
                // Position i in this list supplies bit i of the child's
                // separator mask, regardless of the parent's bag order.
                let positions = layouts[bag]
                    .separator()
                    .iter()
                    .map(|&variable| layouts[parent].variable_position(variable))
                    .collect();
                layouts[parent].children.push((bag, positions));
            }
        }
        Ok(Self {
            variable_count,
            factors,
            bags: layouts,
            postorder,
            cell_count,
        })
    }

    pub fn bag(&self, bag: usize) -> Option<&BagLayout> {
        self.bags.get(bag)
    }

    /// Solve with the ranked fold, lift one original assignment when feasible,
    /// and check every rank against the bag and separator equations.
    pub fn solve(&self) -> Result<crate::Exact<Certificate>, Error> {
        let table = fast::tabulate(self, &MinCost)?.into_cells();
        let assignment = self.lift(&table)?;
        let certificate = Certificate { table, assignment };
        self.verify(&certificate)?;
        Ok(crate::Exact(certificate))
    }

    /// Check the certificate against this compiled instance. Visit every rank
    /// in order, checking bag rows from owned factors and earlier child
    /// messages, then each separator minimum. Score the proposed assignment
    /// directly with the original factors.
    pub fn verify(&self, certificate: &Certificate) -> Result<(), Error> {
        if certificate.table.len() != self.cell_count {
            return Err(Error::CertificateSize {
                expected: self.cell_count,
                actual: certificate.table.len(),
            });
        }
        self.verify_rows(&certificate.table)?;
        match (&certificate.table[self.root()], &certificate.assignment) {
            (None, None) => Ok(()),
            (Some(expected), Some(assignment)) if assignment.len() == self.variable_count => {
                let score = self.factors.iter().try_fold(BigInt::ZERO, |sum, factor| {
                    let (left, right) = factor.scope();
                    Some(
                        sum + factor
                            .cost(assignment[left], right.is_some_and(|v| assignment[v]))?,
                    )
                });
                if score.as_ref() == Some(expected) {
                    Ok(())
                } else {
                    Err(Error::Assignment)
                }
            }
            _ => Err(Error::Assignment),
        }
    }

    fn verify_rows(&self, table: &[Option<BigInt>]) -> Result<(), Error> {
        for &bag in &self.postorder {
            let layout = &self.bags[bag];
            let (earlier, rows) = table.split_at(layout.first);
            let (assignments, rest) = rows.split_at(layout.assignment_count);
            for (mask, actual) in assignments.iter().enumerate() {
                let value = |variable| bit(mask, layout.variable_position(variable));
                let expected = layout
                    .owned
                    .iter()
                    .try_fold(BigInt::ZERO, |sum, &(id, _, _)| {
                        let factor = &self.factors[id];
                        let (left, right) = factor.scope();
                        Some(sum + factor.cost(value(left), right.is_some_and(value))?)
                    });
                let expected = expected.and_then(|cost| {
                    layout.children.iter().try_fold(cost, |sum, &(child, _)| {
                        let child = &self.bags[child];
                        // Read the original variable IDs. The verifier must
                        // catch a misordered vector in rule emission.
                        let separator = child.separator().iter().enumerate().fold(
                            0,
                            |key, (position, &variable)| {
                                key | (usize::from(value(variable)) << position)
                            },
                        );
                        Some(sum + earlier[child.separator_cell(separator).unwrap()].as_ref()?)
                    })
                });
                if expected.as_ref() != actual.as_ref() {
                    return Err(Error::CellValue(layout.first + mask));
                }
            }
            for (separator, actual) in rest[..layout.separator_count].iter().enumerate() {
                // Each consecutive block has the separator mask in its low bits.
                let expected = assignments
                    .chunks_exact(layout.separator_count)
                    .filter_map(|block| block[separator].as_ref())
                    .min();
                if expected != actual.as_ref() {
                    return Err(Error::CellValue(layout.separator_cell(separator).unwrap()));
                }
            }
        }
        Ok(())
    }

    fn lift(&self, table: &[Option<BigInt>]) -> Result<Option<Vec<bool>>, Error> {
        if table[self.root()].is_none() {
            return Ok(None);
        }
        let mut assignment = vec![false; self.variable_count];
        let mut pending = vec![(*self.postorder.last().unwrap(), 0)];
        while let Some((bag, separator)) = pending.pop() {
            let layout = &self.bags[bag];
            let target = table[layout.separator_cell(separator).unwrap()]
                .as_ref()
                .ok_or(Error::Assignment)?;
            let mask = layout
                .assignments_extending(separator)
                .find(|&mask| table[layout.first + mask].as_ref() == Some(target))
                .ok_or(Error::Assignment)?;
            for (position, &variable) in layout.variables.iter().enumerate() {
                assignment[variable] = bit(mask, position);
            }
            pending.extend(
                layout
                    .children
                    .iter()
                    .map(|(child, positions)| (*child, project(mask, positions))),
            );
        }
        Ok(Some(assignment))
    }
}

/// Operator emitted by the separator-state compiler.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CostRule {
    cell: Cell,
    assignment: Cell,
    cost: BigInt,
    arity: usize,
}

impl Operator for CostRule {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl RuleSource for Compiled {
    type Op = CostRule;

    fn cell_count(&self) -> usize {
        self.cell_count
    }

    fn root(&self) -> Cell {
        self.cell_count - 1
    }

    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(Self::Op, &[Cell]) -> Result<(), crate::Error>,
    ) -> Result<(), crate::Error> {
        if cell >= self.cell_count {
            return Err(crate::Error::CellOutOfRange(cell));
        }
        let index = self
            .postorder
            .partition_point(|&bag| self.bags[bag].first <= cell)
            - 1;
        let layout = &self.bags[self.postorder[index]];
        let mask = cell - layout.first;
        if mask < layout.assignment_count {
            let cost =
                layout
                    .owned
                    .iter()
                    .try_fold(BigInt::ZERO, |sum, &(factor, first, second)| {
                        Some(sum + self.factors[factor].cost(bit(mask, first), bit(mask, second))?)
                    });
            if let Some(cost) = cost {
                let children: Vec<_> = layout
                    .children
                    .iter()
                    .map(|(child, positions)| {
                        self.bags[*child]
                            .separator_cell(project(mask, positions))
                            .unwrap()
                    })
                    .collect();
                emit(
                    CostRule {
                        cell,
                        assignment: cell,
                        cost,
                        arity: children.len(),
                    },
                    &children,
                )?;
            }
        } else {
            let separator = mask - layout.assignment_count;
            for assignment in layout.assignments_extending(separator) {
                emit(
                    CostRule {
                        cell,
                        assignment: layout.first + assignment,
                        cost: BigInt::ZERO,
                        arity: 1,
                    },
                    &[layout.first + assignment],
                )?;
            }
        }
        Ok(())
    }
}

/// Additive minimum in arbitrary-precision integers for compiled factor rules.
pub struct MinCost;

impl Fold<CostRule> for MinCost {
    type Value = BigInt;

    fn apply<'a>(
        &self,
        operator: &'a CostRule,
        children: impl Iterator<Item = &'a BigInt> + Clone,
    ) -> Result<BigInt, crate::Error> {
        Ok(children.fold(operator.cost.clone(), |sum, value| sum + value))
    }

    fn merge(&self, selected: &mut Option<BigInt>, next: BigInt) -> Result<(), crate::Error> {
        if selected.as_ref().is_none_or(|old| &next < old) {
            *selected = Some(next);
        }
        Ok(())
    }
}

impl Algebra<CostRule> for MinCost {
    type Value = BigInt;

    fn apply(&self, operator: &CostRule, children: &[&BigInt]) -> Result<BigInt, crate::Error> {
        Fold::apply(self, operator, children.iter().copied())
    }

    fn choose(&self, candidates: &[BigInt]) -> Result<Vec<BigInt>, crate::Error> {
        Ok(candidates.iter().min().cloned().into_iter().collect())
    }
}
