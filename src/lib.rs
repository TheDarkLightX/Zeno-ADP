//! Algebraic dynamic programming (ADP) over finite tree grammars.
//!
//! Define a signature with [`Operator`], instantiate a [`Chart`] from your input,
//! and interpret its rules with an [`Algebra`]. Use [`exhaustive`] for end-only
//! choice or [`tabulate`] to move choice to each subproblem when its laws hold.
//! [`audit_bounded`] can check those laws on a concrete chart and report duplicates.

#![forbid(unsafe_code)]

pub mod algebras;
pub mod assurance;
mod audit;
pub mod classification;
pub mod common_optimum;
pub mod compiled;
pub mod cyclic;
pub mod decomposition;
pub mod distinct;
pub mod fast;
pub mod forests;
pub mod grammars;
pub mod mcfg;
pub mod mdp;
pub mod probability;
pub mod provenance;
pub mod queries;
pub mod robust_prefix;
pub mod sets;
pub mod state_discovery;

pub use audit::{
    audit, audit_bounded, audit_bounded_classified, grammar_growth, Ambiguity, AnswerOrder, Audit,
    AuditBudget, BoundedAudit, Counterexample, Expansion, GrammarGrowth, Law,
};

use std::collections::BTreeMap;
use std::fmt::Debug;

/// A result checked against the model and semantics of the solver that returned it.
/// The certificate can be borrowed or extracted for independent replay.
///
/// ```compile_fail
/// // Only a solver can attach this label to its checked result.
/// let _ = zeno_adp::Exact(vec![123]);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exact<T>(T);

impl<T> Exact<T> {
    pub fn label(&self) -> &'static str {
        "Exact"
    }

    /// Extract the raw certificate. Replay it against the intended model
    /// after transfer or editing.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> AsRef<T> for Exact<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

pub type Cell = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    MissingRoot(Cell),
    CellOutOfRange(Cell),
    /// Table storage could not be reserved.
    AllocationFailed,
    /// Neither compiled table layout fits within the caller's slot byte budget.
    TableBudgetExceeded {
        max_bytes: usize,
    },
    NonDescendingChild {
        cell: Cell,
        child: Cell,
    },
    Arity {
        cell: Cell,
        expected: usize,
        actual: usize,
    },
    InvalidSymbol(u8),
    InvalidDimensions,
    InvalidNonterminal(usize),
    LeafCountOutOfRange(usize),
    /// A named declaration falls outside the compiled sequence grammar class.
    UnsupportedGrammar {
        name: String,
        reason: &'static str,
    },
    InfinityDisabled,
    AuditBudgetExceeded {
        cell: Cell,
        max_tree_nodes: usize,
    },
    /// A bounded audit stopped; its Bellman and ambiguity verdicts are incomplete.
    AuditEvaluation {
        cell: Cell,
        law: Law,
        source: Box<Error>,
    },
    Overflow,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingRoot(cell) => write!(f, "root cell {cell} does not exist"),
            Self::CellOutOfRange(cell) => write!(f, "cell rank {cell} is out of range"),
            Self::AllocationFailed => write!(f, "could not reserve table storage"),
            Self::TableBudgetExceeded { max_bytes } => write!(
                f,
                "neither dense nor packed table storage fits in {max_bytes} bytes"
            ),
            Self::NonDescendingChild { cell, child } => {
                write!(f, "child {child} must precede cell {cell}")
            }
            Self::Arity {
                cell,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "cell {cell} has a rule with {actual} children, expected {expected}"
                )
            }
            Self::InvalidSymbol(symbol) => write!(f, "invalid symbol byte {symbol}"),
            Self::InvalidDimensions => {
                write!(f, "a matrix chain needs at least two positive dimensions")
            }
            Self::InvalidNonterminal(index) => write!(f, "nonterminal {index} does not exist"),
            Self::LeafCountOutOfRange(leaves) => {
                write!(f, "leaf count {leaves} is outside the table")
            }
            Self::UnsupportedGrammar { name, reason } => {
                write!(f, "cannot compile grammar declaration {name}: {reason}")
            }
            Self::InfinityDisabled => write!(f, "this algebra requires finite costs"),
            Self::AuditBudgetExceeded {
                cell,
                max_tree_nodes,
            } => {
                write!(
                    f,
                    "exhaustive tree nodes exceed budget {max_tree_nodes} at cell {cell}"
                )
            }
            Self::AuditEvaluation { cell, law, source } => {
                write!(f, "audit stopped at cell {cell} while {law}. {source}")
            }
            Self::Overflow => write!(f, "arithmetic overflow"),
        }
    }
}

pub(crate) fn reserve_table<T>(length: usize) -> Result<Vec<T>, Error> {
    let mut table = Vec::new();
    table
        .try_reserve_exact(length)
        .map_err(|_| Error::AllocationFailed)?;
    Ok(table)
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::AuditEvaluation { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// A constructor and its payload. Include every part of a term's identity in
/// equality and ordering if you use the tree-counting or ambiguity APIs.
pub trait Operator: Clone {
    fn arity(&self) -> usize;
}

/// An ordered constructor tree. Destruction walks the tree iteratively.
/// Payload destructors must provide their own stack bounds.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tree<O> {
    pub operator: O,
    pub children: Vec<Tree<O>>,
}

impl<O> Tree<O> {
    /// Move out the operator and children, dropping a default operator in their place.
    pub fn into_parts(self) -> (O, Vec<Self>)
    where
        O: Default,
    {
        self.into_parts_with_replacement(O::default())
    }

    /// Move out the operator and children, dropping the supplied replacement.
    pub fn into_parts_with_replacement(mut self, replacement: O) -> (O, Vec<Self>) {
        let operator = std::mem::replace(&mut self.operator, replacement);
        let children = std::mem::take(&mut self.children);
        (operator, children)
    }
}

impl<O> Drop for Tree<O> {
    fn drop(&mut self) {
        // Reuse the root's child buffer. A unary path needs only one slot.
        let mut pending = std::mem::take(&mut self.children);
        pending.reverse();
        while let Some(mut node) = pending.pop() {
            pending.extend(node.children.drain(..).rev());
            // Dropping node here runs no further traversal: its children are empty.
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule<O> {
    pub operator: O,
    pub children: Vec<Cell>,
}

impl<O> Rule<O> {
    pub fn new(operator: O, children: impl Into<Vec<Cell>>) -> Self {
        Self {
            operator,
            children: children.into(),
        }
    }
}

/// A finite, ordered instance of a grammar. Equal productions retain their multiplicity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chart<O> {
    cells: Vec<Vec<Rule<O>>>,
    root: Cell,
}

impl<O: Operator> Chart<O> {
    pub fn new(cells: Vec<Vec<Rule<O>>>, root: Cell) -> Result<Self, Error> {
        if root >= cells.len() {
            return Err(Error::MissingRoot(root));
        }
        for (cell, rules) in cells.iter().enumerate() {
            for rule in rules {
                validate_rule(cell, &rule.operator, &rule.children)?;
            }
        }
        Ok(Self { cells, root })
    }
}

fn validate_arity(cell: Cell, operator: &impl Operator, actual: usize) -> Result<(), Error> {
    let expected = operator.arity();
    if actual != expected {
        return Err(Error::Arity {
            cell,
            expected,
            actual,
        });
    }
    Ok(())
}

fn validate_rule(cell: Cell, operator: &impl Operator, children: &[Cell]) -> Result<(), Error> {
    validate_arity(cell, operator, children.len())?;
    for &child in children {
        if child >= cell {
            return Err(Error::NonDescendingChild { cell, child });
        }
    }
    Ok(())
}

impl<O> Chart<O> {
    pub fn cells(&self) -> &[Vec<Rule<O>>] {
        &self.cells
    }

    pub fn root(&self) -> Cell {
        self.root
    }
}

/// Interpret one signature. Use deterministic, side-effect-free operations.
/// Choice receives ordered bags, including multiplicities, and must preserve
/// the empty bag. Audit order options change observation equality only.
pub trait Algebra<O> {
    type Value: Clone + Debug + Eq;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error>;
    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error>;
}

fn rule_values<O, A: Algebra<O>>(
    rule: &Rule<O>,
    algebra: &A,
    cells: &[Vec<A::Value>],
) -> Result<Vec<A::Value>, Error> {
    fn visit<'a, O, A: Algebra<O>>(
        rule: &Rule<O>,
        algebra: &A,
        cells: &'a [Vec<A::Value>],
        args: &mut Vec<&'a A::Value>,
        values: &mut Vec<A::Value>,
    ) -> Result<(), Error> {
        if args.len() == rule.children.len() {
            values.push(algebra.apply(&rule.operator, args)?);
        } else {
            for value in &cells[rule.children[args.len()]] {
                args.push(value);
                visit(rule, algebra, cells, args, values)?;
                args.pop();
            }
        }
        Ok(())
    }

    let mut values = Vec::new();
    if rule.children.iter().any(|&child| cells[child].is_empty()) {
        return Ok(values);
    }
    visit(rule, algebra, cells, &mut Vec::new(), &mut values)?;
    Ok(values)
}

pub(crate) fn tabulate_with<O, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
    locate: impl Fn(Cell, Law, Error) -> Error,
) -> Result<Vec<Vec<A::Value>>, Error> {
    let mut cells = Vec::with_capacity(chart.cells.len());
    for (cell, rules) in chart.cells.iter().enumerate() {
        let mut candidates = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            candidates.extend(
                rule_values(rule, algebra, &cells)
                    .map_err(|source| locate(cell, Law::Operation { rule: index }, source))?,
            );
        }
        cells.push(
            algebra
                .choose(&candidates)
                .map_err(|source| locate(cell, Law::Tabulation, source))?,
        );
    }
    Ok(cells)
}

/// Apply choice at each cell in ascending rank, returning every cell's answer.
/// Callers need Bellman justification for the chart and algebra in use.
/// Errors can come from any cell, including cells the root cannot reach.
/// A successful table checks the arithmetic it executed. Agreement with
/// exhaustive execution also requires operations and choice to succeed on
/// the corresponding unpruned inputs.
pub fn tabulate_cells<O, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
) -> Result<Vec<Vec<A::Value>>, Error> {
    tabulate_with(chart, algebra, |_, _, error| error)
}

/// Apply choice during tabulation and return the root's answer.
/// This visits the same cells and has the same error scope as [`tabulate_cells`].
pub fn tabulate<O, A: Algebra<O>>(chart: &Chart<O>, algebra: &A) -> Result<Vec<A::Value>, Error> {
    Ok(std::mem::take(
        &mut tabulate_cells(chart, algebra)?[chart.root],
    ))
}

/// A function or type that instantiates a ranked grammar from an input.
pub trait Grammar<I: ?Sized> {
    type Op: Operator;

    fn chart(&self, input: &I) -> Result<Chart<Self::Op>, Error>;
}

impl<I: ?Sized, O: Operator, F> Grammar<I> for F
where
    F: Fn(&I) -> Result<Chart<O>, Error>,
{
    type Op = O;

    fn chart(&self, input: &I) -> Result<Chart<O>, Error> {
        self(input)
    }
}

/// Select where to apply the user's choice.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Evaluation {
    /// Generate derivations and apply choice once at the root.
    #[default]
    Exhaustive,
    /// Apply choice at each cell. Requires applicable Bellman laws.
    Tabulated,
}

/// Instantiate and evaluate one input. Both strategies pass ordered derivations
/// to choice. For distinct tree counts or tree ranking, see [`queries`].
pub fn run<I: ?Sized, G: Grammar<I>, A: Algebra<G::Op>>(
    grammar: &G,
    input: &I,
    algebra: &A,
    evaluation: Evaluation,
) -> Result<Vec<A::Value>, Error> {
    let chart = grammar.chart(input)?;
    match evaluation {
        Evaluation::Exhaustive => exhaustive(&chart, algebra),
        Evaluation::Tabulated => tabulate(&chart, algebra),
    }
}

fn expand_rule<O: Clone>(
    rule: &Rule<O>,
    mut children_at: impl FnMut(Cell) -> Vec<Tree<O>>,
) -> Vec<Tree<O>> {
    let arguments = rule.children.iter().map(|&cell| children_at(cell));
    build_trees(&rule.operator, arguments)
}

fn build_trees<O: Clone, T: AsRef<[Tree<O>]>>(
    operator: &O,
    children: impl IntoIterator<Item = T>,
) -> Vec<Tree<O>> {
    let mut arguments = vec![Vec::new()];
    for terms in children {
        let terms = terms.as_ref();
        arguments = arguments
            .into_iter()
            .flat_map(|prefix| {
                terms.iter().map(move |child| {
                    let mut args = prefix.clone();
                    args.push(child.clone());
                    args
                })
            })
            .collect();
    }
    arguments
        .into_iter()
        .map(|children| Tree {
            operator: operator.clone(),
            children,
        })
        .collect()
}

fn cell_trees<O: Clone>(chart: &Chart<O>, cell: Cell) -> Vec<Tree<O>> {
    chart.cells[cell]
        .iter()
        .flat_map(|rule| expand_rule(rule, |child| cell_trees(chart, child)))
        .collect()
}

/// Enumerate complete trees before applying any algebraic choices.
pub fn enumerate<O: Clone>(chart: &Chart<O>) -> Vec<Tree<O>> {
    cell_trees(chart, chart.root)
}

fn evaluate_tree<O, A: Algebra<O>>(tree: &Tree<O>, algebra: &A) -> Result<A::Value, Error> {
    let children = tree
        .children
        .iter()
        .map(|child| evaluate_tree(child, algebra))
        .collect::<Result<Vec<_>, _>>()?;
    algebra.apply(&tree.operator, &children.iter().collect::<Vec<_>>())
}

/// Evaluate every derivation of the root and pass the ordered results to
/// the algebra's chooser once. Arithmetic is evaluated on each complete
/// derivation, including candidates the chooser would eliminate. Unreachable
/// cells are outside the evaluation.
pub fn exhaustive<O: Clone, A: Algebra<O>>(
    chart: &Chart<O>,
    algebra: &A,
) -> Result<Vec<A::Value>, Error> {
    let candidates = enumerate(chart)
        .iter()
        .map(|tree| evaluate_tree(tree, algebra))
        .collect::<Result<Vec<_>, _>>()?;
    algebra.choose(&candidates)
}

/// Two derivation occurrences with the same constructor term or canonical answer.
#[derive(Debug, PartialEq, Eq)]
pub struct Duplicate<K, O> {
    pub answer: K,
    pub occurrences: usize,
    pub indices: [usize; 2],
    pub first: Tree<O>,
    pub second: Tree<O>,
}

fn first_duplicate<O: Clone, K: Ord>(
    trees: &[Tree<O>],
    identity: impl Fn(&Tree<O>) -> Result<K, Error>,
) -> Result<Option<Duplicate<K, O>>, Error> {
    let mut groups = BTreeMap::new();
    for (index, tree) in trees.iter().enumerate() {
        let (_, second, count) = groups.entry(identity(tree)?).or_insert((index, index, 0));
        if *count == 1 {
            *second = index;
        }
        *count += 1;
    }
    Ok(groups
        .into_iter()
        .find_map(|(answer, (first, second, occurrences))| {
            (occurrences > 1).then(|| Duplicate {
                answer,
                occurrences,
                indices: [first, second],
                first: trees[first].clone(),
                second: trees[second].clone(),
            })
        }))
}
