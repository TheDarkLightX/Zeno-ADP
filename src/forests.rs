//! Ranked grammars for ordered forest edit and alignment.

use std::ops::Range;

use crate::algebras::{Cost, ScoredOperator};
use crate::{Cell, Chart, Error, Operator, Rule};

/// A labeled tree. Use a slice of trees for an ordered forest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<L> {
    pub label: L,
    pub children: Vec<Node<L>>,
}

impl<L> Node<L> {
    pub fn new(label: L, children: Vec<Self>) -> Self {
        Self { label, children }
    }
}

/// Constructors carry zero-based preorder occurrence indices on their own sides.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ForestOp {
    Empty,
    DeleteLeft(usize),
    DeleteRight(usize),
    /// Child forests, then remaining siblings.
    Match {
        left: usize,
        right: usize,
        different: bool,
    },
    /// One child-forest comparison per pair. Outside the retained subtrees,
    /// every node is deleted or inserted with promotion.
    Cut {
        pairs: Vec<(usize, usize)>,
        cost: i64,
    },
    /// Left root aligned to a gap. Children are the inside and suffix comparisons.
    GapRight(usize),
    /// Right root aligned to a gap. Children are the inside and suffix comparisons.
    GapLeft(usize),
}

impl Operator for ForestOp {
    fn arity(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::DeleteLeft(_) | Self::DeleteRight(_) => 1,
            Self::Match { .. } | Self::GapRight(_) | Self::GapLeft(_) => 2,
            Self::Cut { pairs, .. } => pairs.len(),
        }
    }
}

impl ScoredOperator for ForestOp {
    fn cost(&self) -> Cost {
        Cost::Finite(match self {
            Self::Empty => 0,
            Self::DeleteLeft(_) | Self::DeleteRight(_) | Self::GapRight(_) | Self::GapLeft(_) => 1,
            Self::Match { different, .. } => i64::from(*different),
            Self::Cut { cost, .. } => *cost,
        })
    }
}

/// The chart and its rank-indexed preorder intervals. Empty intervals retain
/// their position, so witnesses can always be related to input coordinates.
#[derive(Debug)]
pub struct Comparison {
    chart: Chart<ForestOp>,
    spans: Vec<(Range<usize>, Range<usize>)>,
}

impl Comparison {
    pub fn chart(&self) -> &Chart<ForestOp> {
        &self.chart
    }

    pub fn spans(&self) -> &[(Range<usize>, Range<usize>)] {
        &self.spans
    }
}

/// The promoting-cut reference for ordered edit. Every derivation is one
/// order- and ancestry-preserving partial matching of node occurrences.
/// Deliberately enumerates frontier pairs for bounded inputs.
pub fn edit_reference<L: PartialEq>(
    left: &[Node<L>],
    right: &[Node<L>],
) -> Result<Comparison, Error> {
    let left = Side::new(left);
    let right = Side::new(right);
    let left_frontiers = left.frontiers();
    let right_frontiers = right.frontiers();
    build(&left, &right, |a, b, rank| {
        let mut rules = Vec::new();
        for x in &left_frontiers[left.rank(a)] {
            for y in &right_frontiers[right.rank(b)] {
                if x.nodes.len() != y.nodes.len() {
                    continue;
                }
                let pairs: Vec<_> = x
                    .nodes
                    .iter()
                    .copied()
                    .zip(y.nodes.iter().copied())
                    .collect();
                let mut children = Vec::with_capacity(pairs.len());
                let mut cost = (a.len() - x.covered) + (b.len() - y.covered);
                for &(i, j) in &pairs {
                    cost += usize::from(left.labels[i] != right.labels[j]);
                    children.push(rank(&left.children(i), &right.children(j)));
                }
                let cost = i64::try_from(cost).map_err(|_| Error::Overflow)?;
                rules.push(Rule::new(ForestOp::Cut { pairs, cost }, children));
            }
        }
        Ok(rules)
    })
}

/// The first-root edit recurrence with promotion. It gives the same unit-cost
/// minimum as [the cut reference](edit_reference). Distinct deletion orders
/// can represent the same edit matching. Use the cut reference for mapping counts.
pub fn edit<L: PartialEq>(left: &[Node<L>], right: &[Node<L>]) -> Result<Comparison, Error> {
    let left = Side::new(left);
    let right = Side::new(right);
    build(&left, &right, |a, b, rank| {
        let mut rules = Vec::new();
        if !a.is_empty() {
            rules.push(Rule::new(
                ForestOp::DeleteLeft(a.start),
                [rank(&(a.start + 1..a.end), b)],
            ));
        }
        if !b.is_empty() {
            rules.push(Rule::new(
                ForestOp::DeleteRight(b.start),
                [rank(a, &(b.start + 1..b.end))],
            ));
        }
        finish_roots(&left, &right, a, b, rank, &mut rules);
        Ok(rules)
    })
}

/// Align two ordered forests as a common superforest. Each alignment node has
/// a left occurrence, a right occurrence, or both. Deleting gaps and
/// promoting children projects the alignment to either input.
pub fn alignment<L: PartialEq>(left: &[Node<L>], right: &[Node<L>]) -> Result<Comparison, Error> {
    let left = Side::new(left);
    let right = Side::new(right);
    build(&left, &right, |a, b, rank| {
        let mut rules = Vec::new();
        if !a.is_empty() {
            let children = left.children(a.start);
            let rest = children.end..a.end;
            for split in right.boundaries(b) {
                rules.push(Rule::new(
                    ForestOp::GapRight(a.start),
                    [
                        rank(&children, &(b.start..split)),
                        rank(&rest, &(split..b.end)),
                    ],
                ));
            }
        }
        if !b.is_empty() {
            let children = right.children(b.start);
            let rest = children.end..b.end;
            for split in left.boundaries(a) {
                rules.push(Rule::new(
                    ForestOp::GapLeft(b.start),
                    [
                        rank(&(a.start..split), &children),
                        rank(&(split..a.end), &rest),
                    ],
                ));
            }
        }
        finish_roots(&left, &right, a, b, rank, &mut rules);
        Ok(rules)
    })
}

type Rank<'a> = dyn Fn(&Range<usize>, &Range<usize>) -> Cell + 'a;

fn finish_roots<L: PartialEq>(
    left: &Side<'_, L>,
    right: &Side<'_, L>,
    a: &Range<usize>,
    b: &Range<usize>,
    rank: &Rank<'_>,
    rules: &mut Vec<Rule<ForestOp>>,
) {
    if a.is_empty() && b.is_empty() {
        rules.push(Rule::new(ForestOp::Empty, []));
    } else if !a.is_empty() && !b.is_empty() {
        let first = left.children(a.start);
        let second = right.children(b.start);
        rules.push(Rule::new(
            ForestOp::Match {
                left: a.start,
                right: b.start,
                different: left.labels[a.start] != right.labels[b.start],
            },
            [
                rank(&first, &second),
                rank(&(first.end..a.end), &(second.end..b.end)),
            ],
        ));
    }
}

fn build<L>(
    left: &Side<'_, L>,
    right: &Side<'_, L>,
    rules: impl Fn(&Range<usize>, &Range<usize>, &Rank<'_>) -> Result<Vec<Rule<ForestOp>>, Error>,
) -> Result<Comparison, Error> {
    let size = left
        .spans
        .len()
        .checked_mul(right.spans.len())
        .ok_or(Error::Overflow)?;
    let rank =
        |a: &Range<usize>, b: &Range<usize>| left.rank(a) * right.spans.len() + right.rank(b);
    let mut cells = Vec::new();
    let mut spans = Vec::new();
    cells.try_reserve_exact(size).map_err(|_| Error::Overflow)?;
    spans.try_reserve_exact(size).map_err(|_| Error::Overflow)?;
    for a in &left.spans {
        for b in &right.spans {
            cells.push(rules(a, b, &rank)?);
            spans.push((a.clone(), b.clone()));
        }
    }
    let root = rank(&(0..left.labels.len()), &(0..right.labels.len()));
    Ok(Comparison {
        chart: Chart::new(cells, root)?,
        spans,
    })
}

struct Side<'a, L> {
    labels: Vec<&'a L>,
    ends: Vec<usize>,
    spans: Vec<Range<usize>>,
}

impl<'a, L> Side<'a, L> {
    fn new(forest: &'a [Node<L>]) -> Self {
        enum Visit<'a, L> {
            Enter(&'a Node<L>),
            Exit(usize),
        }
        let mut pending: Vec<_> = forest.iter().rev().map(Visit::Enter).collect();
        let mut side = Self {
            labels: Vec::new(),
            ends: Vec::new(),
            spans: Vec::new(),
        };
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Enter(node) => {
                    pending.push(Visit::Exit(side.labels.len()));
                    pending.extend(node.children.iter().rev().map(Visit::Enter));
                    side.labels.push(&node.label);
                    side.ends.push(0);
                }
                Visit::Exit(index) => side.ends[index] = side.labels.len(),
            }
        }
        for begin in 0..=side.labels.len() {
            let mut end = begin;
            side.spans.push(begin..end);
            while let Some(&next) = side.ends.get(end) {
                end = next;
                side.spans.push(begin..end);
            }
        }
        side.spans
            .sort_unstable_by_key(|span| (span.len(), span.start));
        side
    }

    fn boundaries(&self, span: &Range<usize>) -> impl Iterator<Item = usize> + '_ {
        let end = span.end;
        std::iter::successors(Some(span.start), move |&index| {
            (index < end).then(|| self.ends[index])
        })
    }

    fn children(&self, root: usize) -> Range<usize> {
        root + 1..self.ends[root]
    }

    fn rank(&self, span: &Range<usize>) -> Cell {
        self.spans
            .binary_search_by_key(&(span.len(), span.start), |span| (span.len(), span.start))
            .expect("span consists of complete subtrees")
    }

    fn frontiers(&self) -> Vec<Vec<Frontier>> {
        let mut table: Vec<Vec<Frontier>> = Vec::with_capacity(self.spans.len());
        for span in &self.spans {
            if span.is_empty() {
                table.push(vec![Frontier::default()]);
                continue;
            }
            // Skip the first root with promotion, or retain its whole
            // subtree and continue at the next sibling.
            let mut choices = table[self.rank(&(span.start + 1..span.end))].clone();
            let next = self.ends[span.start];
            choices.extend(table[self.rank(&(next..span.end))].iter().map(|rest| {
                let mut nodes = Vec::with_capacity(rest.nodes.len() + 1);
                nodes.push(span.start);
                nodes.extend(&rest.nodes);
                Frontier {
                    nodes,
                    covered: next - span.start + rest.covered,
                }
            }));
            table.push(choices);
        }
        table
    }
}

#[derive(Clone, Default)]
struct Frontier {
    nodes: Vec<usize>,
    covered: usize,
}

/// Bind the first-root edit schedule. Counts describe scripts. Use
/// [`edit_reference`] to audit counts of distinct edit mappings.
pub fn edit_source<'a, L: PartialEq>(
    left: &'a [Node<L>],
    right: &'a [Node<L>],
) -> Result<impl crate::compiled::Program<Op = ForestOp> + 'a, Error> {
    ComparisonLayout::<_, false>::bind(left, right)
}

/// Bind the gapped forest alignment schedule without retaining productions.
pub fn alignment_source<'a, L: PartialEq>(
    left: &'a [Node<L>],
    right: &'a [Node<L>],
) -> Result<impl crate::compiled::Program<Op = ForestOp> + 'a, Error> {
    ComparisonLayout::<_, true>::bind(left, right)
}

struct ComparisonLayout<'a, L, const ALIGN: bool> {
    left: RankedSide<'a, L, ALIGN>,
    right: RankedSide<'a, L, ALIGN>,
    count: usize,
    root: Cell,
}

struct RankedSide<'a, L, const ALIGN: bool> {
    side: Side<'a, L>,
    transitions: Vec<Option<RootRanks>>,
    next_prefix: Vec<Option<Cell>>,
    empty_prefix: Vec<Cell>,
}

#[derive(Clone, Copy)]
struct RootRanks {
    promote: Cell,
    children: Cell,
    siblings: Cell,
}

impl<'a, L, const ALIGN: bool> RankedSide<'a, L, ALIGN> {
    fn new(side: Side<'a, L>) -> Result<Self, Error> {
        let mut transitions = crate::reserve_table(side.spans.len())?;
        transitions.extend(side.spans.iter().map(|span| {
            if span.is_empty() {
                return None;
            }
            let children = side.children(span.start);
            Some(RootRanks {
                promote: side.rank(&(span.start + 1..span.end)),
                children: side.rank(&children),
                siblings: side.rank(&(children.end..span.end)),
            })
        }));
        let mut next_prefix = Vec::new();
        let mut empty_prefix = Vec::new();
        if ALIGN {
            next_prefix = crate::reserve_table(side.spans.len())?;
            empty_prefix = crate::reserve_table(side.spans.len())?;
            for span in &side.spans {
                next_prefix.push(
                    side.ends
                        .get(span.end)
                        .map(|&end| side.rank(&(span.start..end))),
                );
                empty_prefix.push(side.rank(&(span.start..span.start)));
            }
        }
        Ok(Self {
            side,
            transitions,
            next_prefix,
            empty_prefix,
        })
    }

    fn splits(&self, rank: Cell) -> impl Iterator<Item = (Cell, Cell)> + '_ {
        // Start with an empty prefix. Transfer one whole first subtree
        // from the suffix to the prefix at each step.
        std::iter::successors(
            Some((self.empty_prefix[rank], rank)),
            |&(prefix, suffix)| {
                self.transitions[suffix].map(|ranks| {
                    (
                        self.next_prefix[prefix].expect("nonempty suffix has a root"),
                        ranks.siblings,
                    )
                })
            },
        )
    }
}

impl<'a, L: PartialEq, const ALIGN: bool> ComparisonLayout<'a, L, ALIGN> {
    fn bind(
        left: &'a [Node<L>],
        right: &'a [Node<L>],
    ) -> Result<crate::compiled::generated::Ranked<Self>, Error> {
        let left = Side::new(left);
        let right = Side::new(right);
        let count = left
            .spans
            .len()
            .checked_mul(right.spans.len())
            .ok_or(Error::Overflow)?;
        let root = left.rank(&(0..left.labels.len())) * right.spans.len()
            + right.rank(&(0..right.labels.len()));
        Ok(crate::compiled::generated::Ranked(Self {
            left: RankedSide::new(left)?,
            right: RankedSide::new(right)?,
            count,
            root,
        }))
    }

    #[inline]
    fn emit_pair(
        &self,
        left_rank: Cell,
        right_rank: Cell,
        sink: &mut impl crate::compiled::ProductionSink<ForestOp>,
    ) -> Result<(), Error> {
        let width = self.right.transitions.len();
        let left = self.left.side.spans[left_rank].start;
        let right = self.right.side.spans[right_rank].start;
        let a = self.left.transitions[left_rank];
        let b = self.right.transitions[right_rank];
        let rank = |x, y| x * width + y;

        if let Some(a) = a {
            if ALIGN {
                for (prefix, suffix) in self.right.splits(right_rank) {
                    sink.rule(
                        "GapRight",
                        ForestOp::GapRight(left),
                        [rank(a.children, prefix), rank(a.siblings, suffix)],
                    )?;
                }
            } else {
                sink.rule(
                    "DeleteLeft",
                    ForestOp::DeleteLeft(left),
                    [rank(a.promote, right_rank)],
                )?;
            }
        }
        if let Some(b) = b {
            if ALIGN {
                for (prefix, suffix) in self.left.splits(left_rank) {
                    sink.rule(
                        "GapLeft",
                        ForestOp::GapLeft(right),
                        [rank(prefix, b.children), rank(suffix, b.siblings)],
                    )?;
                }
            } else {
                sink.rule(
                    "DeleteRight",
                    ForestOp::DeleteRight(right),
                    [rank(left_rank, b.promote)],
                )?;
            }
        }
        match (a, b) {
            (None, None) => sink.rule("Empty", ForestOp::Empty, []),
            (Some(a), Some(b)) => sink.rule(
                "Match",
                ForestOp::Match {
                    left,
                    right,
                    different: self.left.side.labels[left] != self.right.side.labels[right],
                },
                [rank(a.children, b.children), rank(a.siblings, b.siblings)],
            ),
            _ => Ok(()),
        }
    }
}

impl<L: PartialEq, const ALIGN: bool> crate::compiled::generated::Layout
    for ComparisonLayout<'_, L, ALIGN>
{
    type Op = ForestOp;

    fn cell_count(&self) -> usize {
        self.count
    }

    fn root(&self) -> Cell {
        self.root
    }

    #[inline]
    fn emit(
        &self,
        cell: Cell,
        sink: &mut impl crate::compiled::ProductionSink<ForestOp>,
    ) -> Result<(), Error> {
        let width = self.right.transitions.len();
        self.emit_pair(cell / width, cell % width, sink)
    }

    #[inline]
    fn fill(&self, sink: &mut impl crate::compiled::ProductionSink<ForestOp>) -> Result<(), Error> {
        for left_rank in 0..self.left.transitions.len() {
            for right_rank in 0..self.right.transitions.len() {
                self.emit_pair(left_rank, right_rank, sink)?;
                sink.finish_cell()?;
            }
        }
        Ok(())
    }
}
