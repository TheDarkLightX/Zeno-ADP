use std::ops::Range;

use crate::fast::RuleSource;
use crate::{Cell, Error, Operator};

use super::{sealed, ProductionSink, Program};

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

/// Coordinates of one production occurrence. Spans are half-open byte ranges.
pub struct Matched<'a, const TRACKS: usize> {
    pub inputs: [&'a [u8]; TRACKS],
    pub parent: &'a [Range<usize>; TRACKS],
    pub children: &'a [[Range<usize>; TRACKS]],
}

/// An ordered constructor clause. Each child occurs once on each track.
pub struct Production<O, const TRACKS: usize> {
    pub name: String,
    pub parent: Nonterminal,
    pub children: Vec<Nonterminal>,
    pub tracks: [Vec<Atom>; TRACKS],
    /// Construct the payload for a match. Keep the function deterministic.
    pub operator: Box<dyn Fn(Matched<'_, TRACKS>) -> O>,
}

/// A context-free grammar over one or two contiguous input tracks.
///
/// Stable nonterminal IDs index the name list. Rules are tried in declaration
/// order. Within a rule, splits are tried in increasing boundary order on
/// each track, starting with track zero. Constructor children retain their
/// declared order even when another track visits them in a different order.
pub struct Grammar<O, const TRACKS: usize> {
    root: Nonterminal,
    order: Vec<Nonterminal>,
    positions: Vec<usize>,
    rules: Vec<Vec<Lowered<O, TRACKS>>>,
    yields: Vec<[Option<usize>; TRACKS]>,
    nullable: Vec<bool>,
    positive: Vec<[bool; TRACKS]>,
}

struct Lowered<O, const TRACKS: usize> {
    definition: Production<O, TRACKS>,
    suffix_minima: [Vec<usize>; TRACKS],
    suffix_empty: [Vec<bool>; TRACKS],
}

impl<O: Operator, const TRACKS: usize> Grammar<O, TRACKS> {
    /// Compile ordered productions and determine the dependencies between
    /// nonterminals that can use the same span. Unsupported declarations
    /// report the matching grammar, nonterminal or rule name.
    /// Returns [`Error::Overflow`] if a productive clause's final minimum
    /// yield on any track exceeds `usize`, even if another clause is shorter.
    pub fn new(
        names: &[&str],
        root: Nonterminal,
        productions: Vec<Production<O, TRACKS>>,
    ) -> Result<Self, Error> {
        if !(1..=2).contains(&TRACKS) {
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
                    if let Atom::Child(index) = *atom {
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
                    let width = atom_minimum(atoms[i], &rule.children, &yields, track).unwrap();
                    suffix[i] = suffix[i + 1].checked_add(width).ok_or(Error::Overflow)?;
                    empty[i] = empty[i + 1]
                        && match atoms[i] {
                            Atom::Child(index) => !positive[rule.children[index]][track],
                            Atom::Byte(_) | Atom::Any => false,
                        };
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

    /// The lower bound on each track, independently. An unproductive
    /// nonterminal has no finite bound. Returns None for an unknown ID.
    pub fn minimum_yields(&self, nonterminal: Nonterminal) -> Option<[Option<usize>; TRACKS]> {
        self.yields.get(nonterminal).copied()
    }

    /// Bind a reusable grammar to its concrete inputs and calculate its ranks.
    pub fn bind<'a>(
        &'a self,
        inputs: [&'a [u8]; TRACKS],
    ) -> Result<Sequence<'a, O, TRACKS>, Error> {
        let mut offsets = std::array::from_fn(|_| Vec::new());
        let mut sizes = [0; TRACKS];
        let mut cell_count = self.order.len();
        for (track, input) in inputs.iter().enumerate() {
            let n = input.len();
            let boundaries = n.checked_add(1).ok_or(Error::Overflow)?;
            let triangular = (boundaries as u128) * (boundaries as u128 + 1) / 2;
            let size = usize::try_from(triangular).map_err(|_| Error::Overflow)?;
            sizes[track] = size;
            cell_count = cell_count.checked_mul(size).ok_or(Error::Overflow)?;
            let mut next = 0;
            for length in 0..=n {
                offsets[track].push(next);
                next += boundaries - length;
            }
        }
        let mut bound = Sequence {
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

fn atom_minimum<const TRACKS: usize>(
    atom: Atom,
    children: &[Nonterminal],
    yields: &[[Option<usize>; TRACKS]],
    track: usize,
) -> Option<usize> {
    match atom {
        Atom::Child(index) => yields[children[index]][track],
        Atom::Byte(_) | Atom::Any => Some(1),
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

fn minimum_yields<O, const TRACKS: usize>(
    nonterminals: usize,
    productions: &[Production<O, TRACKS>],
) -> Result<Vec<[Option<usize>; TRACKS]>, Error> {
    use YieldWidth::*;
    let mut yields = vec![[Unproductive; TRACKS]; nonterminals];
    loop {
        let mut changed = false;
        for rule in productions {
            for track in 0..TRACKS {
                let mut length = Finite(0);
                for &atom in &rule.tracks[track] {
                    let width = match atom {
                        Atom::Child(index) => yields[rule.children[index]][track],
                        Atom::Byte(_) | Atom::Any => Finite(1),
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

fn positive_yields<O, const TRACKS: usize>(
    rules: &[Production<O, TRACKS>],
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
                    && rule.tracks[track].iter().any(|atom| match *atom {
                        Atom::Child(index) => positive[rule.children[index]][track],
                        Atom::Byte(_) | Atom::Any => true,
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

fn nullable_nonterminals<O, const TRACKS: usize>(
    nonterminals: usize,
    rules: &[Production<O, TRACKS>],
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
                    .all(|atom| matches!(atom, Atom::Child(_)))
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

fn dependency_order<O, const TRACKS: usize>(
    names: &[&str],
    rules: &[Production<O, TRACKS>],
    nullable: &[bool],
) -> Result<Vec<Nonterminal>, Error> {
    let mut dependencies = vec![Vec::new(); names.len()];
    for rule in rules {
        if rule
            .tracks
            .iter()
            .flatten()
            .any(|atom| !matches!(atom, Atom::Child(_)))
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

/// A compiled sequence grammar bound to byte slices.
pub struct Sequence<'a, O, const TRACKS: usize> {
    grammar: &'a Grammar<O, TRACKS>,
    inputs: [&'a [u8]; TRACKS],
    offsets: [Vec<usize>; TRACKS],
    sizes: [usize; TRACKS],
    cell_count: usize,
    root: Cell,
}

impl<O: Operator, const TRACKS: usize> Sequence<'_, O, TRACKS> {
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

struct MatchRule<'a, 'input, O, const TRACKS: usize> {
    sequence: &'a Sequence<'input, O, TRACKS>,
    rule: &'a Lowered<O, TRACKS>,
    parent: &'a [Range<usize>; TRACKS],
    child_spans: &'a mut [[Range<usize>; TRACKS]],
    children: &'a mut [Cell],
}

impl<O: Operator, const TRACKS: usize> MatchRule<'_, '_, O, TRACKS> {
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
            let operator = (rule.operator)(Matched {
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
        match *symbol {
            Atom::Child(child) => {
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
            Atom::Byte(byte) if self.sequence.inputs[track][start] != byte => {}
            Atom::Byte(_) | Atom::Any => self.visit(track, atom + 1, start + 1, emit)?,
        }
        Ok(())
    }
}

impl<O: Operator, const TRACKS: usize> RuleSource for Sequence<'_, O, TRACKS> {
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

impl<O: Operator, const TRACKS: usize> sealed::Sealed for Sequence<'_, O, TRACKS> {}

impl<O: Operator, const TRACKS: usize> Program for Sequence<'_, O, TRACKS> {
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
