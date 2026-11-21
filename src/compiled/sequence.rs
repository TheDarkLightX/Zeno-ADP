use std::ops::{Range, RangeInclusive};

use crate::fast::RuleSource;
use crate::{reserve_table, Cell, Error, Operator};

use super::{sealed, ProductionSink, Program};

// The sequence compiler admits contiguous one- and two-track grammars.
const SUPPORTED_TRACKS: RangeInclusive<usize> = 1..=2;

/// Index into a grammar's declared nonterminal names.
pub type Nonterminal = usize;

/// One symbol on a production's input track.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    Byte(u8),
    Any,
    /// Index into this production's ordered children.
    Child(usize),
}

/// One symbol on a track of user-defined tokens.
pub enum TokenAtom<T> {
    /// Match one token by equality.
    Equals(T),
    /// Match one token if the deterministic predicate accepts it.
    Predicate(Box<dyn Fn(&T) -> bool>),
    /// Match any one token.
    Any,
    /// Index into this production's ordered children.
    Child(usize),
}

#[doc(hidden)]
pub trait TrackAtom<T>: sealed::Sealed {
    fn child(&self) -> Option<usize>;
    fn accepts(&self, token: &T) -> bool;
}

impl sealed::Sealed for Atom {}
impl<T> sealed::Sealed for TokenAtom<T> {}

impl TrackAtom<u8> for Atom {
    fn child(&self) -> Option<usize> {
        match *self {
            Self::Child(index) => Some(index),
            _ => None,
        }
    }

    fn accepts(&self, token: &u8) -> bool {
        match self {
            Self::Byte(value) => value == token,
            Self::Any => true,
            Self::Child(_) => false,
        }
    }
}

impl<T: Eq> TrackAtom<T> for TokenAtom<T> {
    fn child(&self) -> Option<usize> {
        match *self {
            Self::Child(index) => Some(index),
            _ => None,
        }
    }

    fn accepts(&self, token: &T) -> bool {
        match self {
            Self::Equals(value) => value == token,
            Self::Predicate(predicate) => predicate(token),
            Self::Any => true,
            Self::Child(_) => false,
        }
    }
}

/// A byte-track production. For other token types, use [`TokenProduction`].
pub type Production<O, const TRACKS: usize> = TokenProduction<O, TRACKS, u8, Atom>;

/// A byte-track grammar. For other token types, use [`TokenGrammar`].
pub type Grammar<O, const TRACKS: usize> = TokenGrammar<O, TRACKS, u8, Atom>;

/// A compiled byte-track grammar bound to input.
pub type Sequence<'a, O, const TRACKS: usize> = TokenSequence<'a, O, TRACKS, u8, Atom>;

/// Coordinates of one byte production occurrence.
pub type Matched<'a, const TRACKS: usize> = TokenMatched<'a, TRACKS, u8>;

/// Coordinates of one production occurrence. Spans are half-open token-index ranges.
pub struct TokenMatched<'a, const TRACKS: usize, T> {
    pub inputs: [&'a [T]; TRACKS],
    pub parent: &'a [Range<usize>; TRACKS],
    pub children: &'a [[Range<usize>; TRACKS]],
}

/// Builds a constructor payload from one matched production occurrence.
pub type SequenceConstructor<O, const TRACKS: usize, T = u8> =
    dyn Fn(TokenMatched<'_, TRACKS, T>) -> O;

/// An ordered constructor clause. Each child occurs once on each track.
pub struct TokenProduction<O, const TRACKS: usize, T, A = TokenAtom<T>> {
    pub name: String,
    pub parent: Nonterminal,
    pub children: Vec<Nonterminal>,
    pub tracks: [Vec<A>; TRACKS],
    /// Construct the payload for a match. Keep the function deterministic.
    pub operator: Box<SequenceConstructor<O, TRACKS, T>>,
}

/// A context-free grammar over one or two contiguous input tracks.
///
/// Stable nonterminal IDs index the name list. Rules are tried in declaration
/// order. Within a rule, splits are tried in increasing boundary order on
/// each track, starting with track zero. Constructor children retain their
/// declared order even when another track visits them in a different order.
pub struct TokenGrammar<O, const TRACKS: usize, T, A = TokenAtom<T>> {
    root: Nonterminal,
    order: Vec<Nonterminal>,
    positions: Vec<usize>,
    rules: Vec<Vec<Lowered<O, TRACKS, T, A>>>,
    yields: Vec<[Option<usize>; TRACKS]>,
    nullable: Vec<bool>,
    positive: Vec<[bool; TRACKS]>,
}

struct Lowered<O, const TRACKS: usize, T, A> {
    definition: TokenProduction<O, TRACKS, T, A>,
    suffix_minima: [Vec<usize>; TRACKS],
    suffix_empty: [Vec<bool>; TRACKS],
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> TokenGrammar<O, TRACKS, T, A> {
    /// Compile ordered productions and determine the dependencies between
    /// nonterminals that can use the same span. Unsupported declarations
    /// report the matching grammar, nonterminal or rule name.
    /// Returns [`Error::Overflow`] if a productive clause's final minimum
    /// yield on any track exceeds `usize`, even if another clause is shorter.
    pub fn new(
        names: &[&str],
        root: Nonterminal,
        productions: Vec<TokenProduction<O, TRACKS, T, A>>,
    ) -> Result<Self, Error> {
        if !SUPPORTED_TRACKS.contains(&TRACKS) {
            return Err(refusal("sequence", "expected one or two input tracks"));
        }
        if root >= names.len() {
            return Err(refusal("root", "unknown nonterminal"));
        }
        for (i, name) in names.iter().enumerate() {
            if name.is_empty() || names[..i].contains(name) {
                return Err(refusal(name, "expected a unique nonempty nonterminal name"));
            }
        }
        for (i, rule) in productions.iter().enumerate() {
            if rule.name.is_empty() || productions[..i].iter().any(|prev| prev.name == rule.name) {
                return Err(refusal(
                    &rule.name,
                    "expected a unique nonempty production name",
                ));
            }
            if rule.parent >= names.len() || rule.children.iter().any(|&child| child >= names.len())
            {
                return Err(refusal(&rule.name, "unknown nonterminal"));
            }
            for track in &rule.tracks {
                let mut seen = vec![false; rule.children.len()];
                for atom in track {
                    if let Some(index) = atom.child() {
                        let Some(used) = seen.get_mut(index) else {
                            return Err(refusal(&rule.name, "unknown child on input track"));
                        };
                        if std::mem::replace(used, true) {
                            return Err(refusal(
                                &rule.name,
                                "a child occurs twice on an input track",
                            ));
                        }
                    }
                }
                if seen.contains(&false) {
                    return Err(refusal(
                        &rule.name,
                        "each child must occur on each input track",
                    ));
                }
            }
        }

        let yields = minimum_yields(names.len(), &productions)?;
        let nullable = nullable_nonterminals(names.len(), &productions);
        let order = dependency_order(names, &productions, &nullable)?;
        let positive = positive_yields(&productions, &yields);
        let mut positions = vec![0; names.len()];
        for (i, &nt) in order.iter().enumerate() {
            positions[nt] = i;
        }
        let mut rules: Vec<Vec<_>> = (0..names.len()).map(|_| Vec::new()).collect();
        for rule in productions {
            // An unproductive child cannot supply a candidate on any input.
            if rule
                .children
                .iter()
                .any(|&child| yields[child].contains(&None))
            {
                continue;
            }
            let mut suffix_minima = std::array::from_fn(|_| Vec::new());
            let mut suffix_empty = std::array::from_fn(|_| Vec::new());
            for (track, suffix) in suffix_minima.iter_mut().enumerate() {
                let atoms = &rule.tracks[track];
                *suffix = vec![0usize; atoms.len() + 1];
                let empty = &mut suffix_empty[track];
                *empty = vec![true; atoms.len() + 1];
                for i in (0..atoms.len()).rev() {
                    let width = atom_minimum(&atoms[i], &rule.children, &yields, track).unwrap();
                    suffix[i] = suffix[i + 1].checked_add(width).ok_or(Error::Overflow)?;
                    empty[i] = empty[i + 1]
                        && atoms[i]
                            .child()
                            .is_some_and(|index| !positive[rule.children[index]][track]);
                }
            }
            rules[rule.parent].push(Lowered {
                definition: rule,
                suffix_minima,
                suffix_empty,
            });
        }
        Ok(Self {
            root,
            order,
            positions,
            rules,
            yields,
            nullable,
            positive,
        })
    }

    /// Independent structural lower bounds by track. Each terminal
    /// contributes one token regardless of its predicate. An unknown
    /// nonterminal returns outer `None`. An unproductive one has absent bounds.
    pub fn minimum_yields(&self, nonterminal: Nonterminal) -> Option<[Option<usize>; TRACKS]> {
        self.yields.get(nonterminal).copied()
    }

    /// Bind a reusable grammar to its concrete inputs and calculate its ranks.
    /// A rank-count overflow is reported before allocating any track offsets.
    pub fn bind<'a>(
        &'a self,
        inputs: [&'a [T]; TRACKS],
    ) -> Result<TokenSequence<'a, O, TRACKS, T, A>, Error> {
        let mut boundaries = [0; TRACKS];
        let mut sizes = [0; TRACKS];
        let mut cell_count = self.order.len();
        for (track, input) in inputs.iter().enumerate() {
            let count = input.len().checked_add(1).ok_or(Error::Overflow)?;
            let triangular = (count as u128) * (count as u128 + 1) / 2;
            let size = usize::try_from(triangular).map_err(|_| Error::Overflow)?;
            boundaries[track] = count;
            sizes[track] = size;
            cell_count = cell_count.checked_mul(size).ok_or(Error::Overflow)?;
        }

        let mut offsets = std::array::from_fn(|_| Vec::new());
        for (offsets, boundaries) in offsets.iter_mut().zip(boundaries) {
            *offsets = reserve_table(boundaries)?;
            let mut next = 0;
            for length in 0..boundaries {
                offsets.push(next);
                next += boundaries - length;
            }
        }
        let mut bound = TokenSequence {
            grammar: self,
            inputs,
            offsets,
            sizes,
            cell_count,
            root: 0,
        };
        bound.root = bound.rank(self.root, &std::array::from_fn(|t| 0..inputs[t].len()));
        Ok(bound)
    }
}

fn refusal(name: &str, reason: &'static str) -> Error {
    Error::UnsupportedGrammar {
        name: name.to_owned(),
        reason,
    }
}

fn atom_minimum<const TRACKS: usize, T>(
    atom: &impl TrackAtom<T>,
    children: &[Nonterminal],
    yields: &[[Option<usize>; TRACKS]],
    track: usize,
) -> Option<usize> {
    match atom.child() {
        Some(index) => yields[children[index]][track],
        None => Some(1),
    }
}

// In increasing order of minimum width. An oversized width is productive
// and can improve during relaxation. Unproductive means no derivation yet.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum YieldWidth {
    Finite(usize),
    Oversized,
    Unproductive,
}

impl YieldWidth {
    fn add(self, other: Self) -> Self {
        use YieldWidth::*;
        match (self, other) {
            (Unproductive, _) | (_, Unproductive) => Unproductive,
            (Finite(a), Finite(b)) => a.checked_add(b).map_or(Oversized, Finite),
            _ => Oversized,
        }
    }
}

fn minimum_yields<O, const TRACKS: usize, T, A: TrackAtom<T>>(
    nonterminals: usize,
    productions: &[TokenProduction<O, TRACKS, T, A>],
) -> Result<Vec<[Option<usize>; TRACKS]>, Error> {
    use YieldWidth::*;
    let mut yields = vec![[Unproductive; TRACKS]; nonterminals];
    loop {
        let mut changed = false;
        for rule in productions {
            for track in 0..TRACKS {
                let mut length = Finite(0);
                for atom in &rule.tracks[track] {
                    let width = match atom.child() {
                        Some(index) => yields[rule.children[index]][track],
                        None => Finite(1),
                    };
                    length = length.add(width);
                    if length == Unproductive {
                        break;
                    }
                }
                let current = &mut yields[rule.parent][track];
                if length < *current {
                    *current = length;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    yields
        .into_iter()
        .map(|tracks| {
            let mut result = [None; TRACKS];
            for (result, width) in result.iter_mut().zip(tracks) {
                *result = match width {
                    Finite(n) => Some(n),
                    Unproductive => None,
                    Oversized => return Err(Error::Overflow),
                };
            }
            Ok(result)
        })
        .collect()
}

fn positive_yields<O, const TRACKS: usize, T, A: TrackAtom<T>>(
    rules: &[TokenProduction<O, TRACKS, T, A>],
    minima: &[[Option<usize>; TRACKS]],
) -> Vec<[bool; TRACKS]> {
    let mut positive = vec![[false; TRACKS]; minima.len()];
    loop {
        let mut changed = false;
        for rule in rules {
            if rule
                .children
                .iter()
                .any(|&child| minima[child].contains(&None))
            {
                continue;
            }
            for track in 0..TRACKS {
                if !positive[rule.parent][track]
                    && rule.tracks[track].iter().any(|atom| {
                        atom.child()
                            .is_none_or(|index| positive[rule.children[index]][track])
                    })
                {
                    positive[rule.parent][track] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return positive;
        }
    }
}

fn nullable_nonterminals<O, const TRACKS: usize, T, A: TrackAtom<T>>(
    nonterminals: usize,
    rules: &[TokenProduction<O, TRACKS, T, A>],
) -> Vec<bool> {
    let mut nullable = vec![false; nonterminals];
    loop {
        let mut changed = false;
        for rule in rules {
            if !nullable[rule.parent]
                && rule
                    .tracks
                    .iter()
                    .flatten()
                    .all(|atom| atom.child().is_some())
                && rule.children.iter().all(|&child| nullable[child])
            {
                nullable[rule.parent] = true;
                changed = true;
            }
        }
        if !changed {
            return nullable;
        }
    }
}

fn dependency_order<O, const TRACKS: usize, T, A: TrackAtom<T>>(
    names: &[&str],
    rules: &[TokenProduction<O, TRACKS, T, A>],
    nullable: &[bool],
) -> Result<Vec<Nonterminal>, Error> {
    let mut dependencies = vec![Vec::new(); names.len()];
    for rule in rules {
        if rule
            .tracks
            .iter()
            .flatten()
            .any(|atom| atom.child().is_none())
        {
            continue;
        }
        for (i, &child) in rule.children.iter().enumerate() {
            let siblings_nullable = rule
                .children
                .iter()
                .enumerate()
                .all(|(j, &sibling)| i == j || nullable[sibling]);
            if siblings_nullable {
                dependencies[rule.parent].push(child);
            }
        }
    }
    let mut order = Vec::with_capacity(names.len());
    let mut finished = vec![false; names.len()];
    while order.len() < names.len() {
        let Some(next) = (0..names.len())
            .find(|&nt| !finished[nt] && dependencies[nt].iter().all(|&child| finished[child]))
        else {
            let blocked = finished.iter().position(|&done| !done).unwrap();
            return Err(refusal(names[blocked], "cyclic same-span dependencies"));
        };
        finished[next] = true;
        order.push(next);
    }
    Ok(order)
}

/// A compiled sequence grammar bound to token slices.
pub struct TokenSequence<'a, O, const TRACKS: usize, T, A = TokenAtom<T>> {
    grammar: &'a TokenGrammar<O, TRACKS, T, A>,
    inputs: [&'a [T]; TRACKS],
    offsets: [Vec<usize>; TRACKS],
    sizes: [usize; TRACKS],
    cell_count: usize,
    root: Cell,
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> TokenSequence<'_, O, TRACKS, T, A> {
    fn rank(&self, nonterminal: Nonterminal, spans: &[Range<usize>; TRACKS]) -> Cell {
        let mut rank = 0;
        for (track, span) in spans.iter().enumerate() {
            rank = rank * self.sizes[track] + self.offsets[track][span.len()] + span.start;
        }
        rank * self.grammar.order.len() + self.grammar.positions[nonterminal]
    }

    /// The nonterminal ID and spans of a logical table cell.
    pub fn cell(&self, mut rank: Cell) -> Option<(Nonterminal, [Range<usize>; TRACKS])> {
        if rank >= self.cell_count {
            return None;
        }
        let nonterminal = self.grammar.order[rank % self.grammar.order.len()];
        rank /= self.grammar.order.len();
        let mut spans = std::array::from_fn(|_| 0..0);
        for (track, span) in spans.iter_mut().enumerate().rev() {
            let id = rank % self.sizes[track];
            rank /= self.sizes[track];
            let length = self.offsets[track].partition_point(|&offset| offset <= id) - 1;
            let start = id - self.offsets[track][length];
            *span = start..start + length;
        }
        Some((nonterminal, spans))
    }

    fn emit_cell(
        &self,
        cell: Cell,
        scratch: &mut MatchScratch<TRACKS>,
        mut emit: impl FnMut(&str, O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let (nonterminal, spans) = self.cell(cell).ok_or(Error::CellOutOfRange(cell))?;
        for rule in &self.grammar.rules[nonterminal] {
            if spans.iter().enumerate().any(|(track, span)| {
                let len = span.len();
                rule.suffix_minima[track][0] > len || (len != 0 && rule.suffix_empty[track][0])
            }) {
                continue;
            }
            let arity = rule.definition.children.len();
            if scratch.children.len() < arity {
                scratch.children.resize(arity, 0);
                scratch
                    .spans
                    .resize_with(arity, || std::array::from_fn(|_| 0..0));
            }
            let mut matcher = MatchRule {
                sequence: self,
                rule,
                parent: &spans,
                // Each track binds each child exactly once before a complete
                // match, and all ranks are calculated before emitting.
                child_spans: &mut scratch.spans[..arity],
                children: &mut scratch.children[..arity],
            };
            matcher.visit(0, 0, spans[0].start, &mut |operator, children| {
                crate::validate_rule(cell, &operator, children)?;
                emit(&rule.definition.name, operator, children)
            })?;
        }
        Ok(())
    }
}

#[derive(Default)]
struct MatchScratch<const TRACKS: usize> {
    spans: Vec<[Range<usize>; TRACKS]>,
    children: Vec<Cell>,
}

struct MatchRule<'a, 'input, O, const TRACKS: usize, T, A> {
    sequence: &'a TokenSequence<'input, O, TRACKS, T, A>,
    rule: &'a Lowered<O, TRACKS, T, A>,
    parent: &'a [Range<usize>; TRACKS],
    child_spans: &'a mut [[Range<usize>; TRACKS]],
    children: &'a mut [Cell],
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> MatchRule<'_, '_, O, TRACKS, T, A> {
    fn visit(
        &mut self,
        track: usize,
        atom: usize,
        start: usize,
        emit: &mut impl FnMut(O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if track == TRACKS {
            let rule = &self.rule.definition;
            for (i, &nt) in rule.children.iter().enumerate() {
                let spans = &self.child_spans[i];
                // Independent per-track bounds may both be zero even when
                // the nonterminal cannot match both empty tracks together.
                if !self.sequence.grammar.nullable[nt] && spans.iter().all(Range::is_empty) {
                    return Ok(());
                }
                self.children[i] = self.sequence.rank(nt, spans);
            }
            let operator = (rule.operator)(TokenMatched {
                inputs: self.sequence.inputs,
                parent: self.parent,
                children: self.child_spans,
            });
            return emit(operator, self.children);
        }
        let end = self.parent[track].end;
        let bounds = &self.rule.suffix_minima[track];
        if bounds[atom] > end - start {
            return Ok(());
        }
        let Some(symbol) = self.rule.definition.tracks[track].get(atom) else {
            if start != end {
                return Ok(());
            }
            let next = self.parent.get(track + 1).map_or(0, |span| span.start);
            return self.visit(track + 1, 0, next, emit);
        };
        match symbol.child() {
            Some(child) => {
                let minimum = bounds[atom] - bounds[atom + 1];
                let suffix_empty = self.rule.suffix_empty[track][atom + 1];
                let child_positive =
                    self.sequence.grammar.positive[self.rule.definition.children[child]][track];
                let first = if suffix_empty { end } else { start + minimum };
                let last = if child_positive {
                    end - bounds[atom + 1]
                } else {
                    start
                };
                for split in first..=last {
                    self.child_spans[child][track] = start..split;
                    self.visit(track, atom + 1, split, emit)?;
                }
            }
            None if symbol.accepts(&self.sequence.inputs[track][start]) => {
                self.visit(track, atom + 1, start + 1, emit)?;
            }
            None => {}
        }
        Ok(())
    }
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> RuleSource
    for TokenSequence<'_, O, TRACKS, T, A>
{
    type Op = O;

    fn cell_count(&self) -> usize {
        self.cell_count
    }

    fn root(&self) -> Cell {
        self.root
    }

    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        self.emit_cell(
            cell,
            &mut MatchScratch::default(),
            |_, operator, children| emit(operator, children),
        )
    }
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> sealed::Sealed
    for TokenSequence<'_, O, TRACKS, T, A>
{
}

impl<O: Operator, const TRACKS: usize, T: Eq, A: TrackAtom<T>> Program
    for TokenSequence<'_, O, TRACKS, T, A>
{
    fn fill(&self, output: &mut impl ProductionSink<O>) -> Result<(), Error> {
        let mut scratch = MatchScratch::default();
        for cell in 0..self.cell_count {
            self.emit_cell(cell, &mut scratch, |site, op, children| {
                output.rule_slice(site, op, children)
            })?;
            output.finish_cell()?;
        }
        Ok(())
    }
}
