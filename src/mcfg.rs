//! Multiple context-free grammars over one byte string and nonempty components.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::ops::Range;

use crate::{Cell, Chart, Error, Operator, Rule};

/// Stable index into the declared nonterminal list.
pub type Nonterminal = usize;

/// Half-open coordinates of one component on the input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// A literal byte, wildcard byte or variable for one component of a child.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    Byte(u8),
    Any,
    Component { child: usize, component: usize },
}

pub struct Symbol<'a> {
    pub name: &'a str,
    pub components: usize,
}

/// A scheduled cell's nonterminal and component spans in declaration order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Item {
    pub nonterminal: Nonterminal,
    pub spans: Vec<Span>,
}

/// Coordinates of the parent and ordered children of one rule occurrence.
pub struct Matched<'a> {
    pub input: &'a [u8],
    pub parent: &'a Item,
    pub children: &'a [&'a Item],
}

/// One ordered production. Every component of every child must appear
/// exactly once across the parent component patterns.
pub struct Production<O> {
    pub name: String,
    pub parent: Nonterminal,
    pub children: Vec<Nonterminal>,
    pub patterns: Vec<Vec<Atom>>,
    /// Supply a deterministic constructor with the declared child arity.
    pub operator: Box<dyn Fn(Matched<'_>) -> O>,
}

/// Proper linear, nonerasing MCFG. Every component is nonempty and the
/// start symbol has one component. Same-yield unary dependencies must be
/// acyclic. Components are disjoint and may occur in any physical order.
pub struct Grammar<O> {
    start: Nonterminal,
    rules: Vec<Vec<Production<O>>>,
    order: Vec<usize>,
    components: Vec<usize>,
}

/// The reference chart and its semantic coordinates, indexed by rank.
#[derive(Debug)]
pub struct Instance<O> {
    chart: Chart<O>,
    items: Vec<Item>,
}

impl<O> Instance<O> {
    pub fn chart(&self) -> &Chart<O> {
        &self.chart
    }

    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

impl<O: Operator> Grammar<O> {
    pub fn new(
        symbols: &[Symbol<'_>],
        start: Nonterminal,
        productions: Vec<Production<O>>,
    ) -> Result<Self, Error> {
        if symbols.get(start).map(|symbol| symbol.components) != Some(1) {
            return Err(refusal("start", "expected one start component"));
        }
        for (index, symbol) in symbols.iter().enumerate() {
            if symbol.name.is_empty()
                || symbols[..index].iter().any(|s| s.name == symbol.name)
                || symbol.components == 0
            {
                return Err(refusal(
                    symbol.name,
                    "expected a unique nonempty symbol name and positive fan-out",
                ));
            }
        }

        let mut dependencies = vec![Vec::new(); symbols.len()];
        let mut waits = vec![0; symbols.len()];
        let mut rules: Vec<Vec<_>> = (0..symbols.len()).map(|_| Vec::new()).collect();
        let mut names = BTreeSet::new();
        for production in productions {
            let name = &production.name;
            if name.is_empty() || !names.insert(name.clone()) {
                return Err(refusal(name, "expected a unique nonempty production name"));
            }
            let Some(parent) = symbols.get(production.parent) else {
                return Err(refusal(name, "unknown parent symbol"));
            };
            if production.patterns.len() != parent.components
                || production.patterns.iter().any(Vec::is_empty)
            {
                return Err(refusal(name, "expected one nonempty pattern per component"));
            }
            let mut required = 0usize;
            for &child in &production.children {
                let Some(symbol) = symbols.get(child) else {
                    return Err(refusal(name, "unknown child symbol"));
                };
                required = required
                    .checked_add(symbol.components)
                    .ok_or_else(|| refusal(name, "each child component must occur"))?;
            }
            let mut used = BTreeSet::new();
            let mut has_terminal = false;
            for atom in production.patterns.iter().flatten() {
                match *atom {
                    Atom::Byte(_) | Atom::Any => has_terminal = true,
                    Atom::Component { child, component } => {
                        if production
                            .children
                            .get(child)
                            .is_none_or(|&nt| component >= symbols[nt].components)
                        {
                            return Err(refusal(name, "unknown child component"));
                        }
                        if !used.insert((child, component)) {
                            return Err(refusal(name, "a child component occurs twice"));
                        }
                    }
                }
            }
            if used.len() != required {
                return Err(refusal(name, "each child component must occur"));
            }
            if let [child] = production.children.as_slice() {
                if !has_terminal {
                    waits[production.parent] += 1;
                    dependencies[*child].push(production.parent);
                }
            }
            rules[production.parent].push(production);
        }

        let mut ready: VecDeque<_> = (0..symbols.len()).filter(|&nt| waits[nt] == 0).collect();
        let mut order = vec![0; symbols.len()];
        let mut next = 0;
        while let Some(child) = ready.pop_front() {
            order[child] = next;
            next += 1;
            for &parent in &dependencies[child] {
                waits[parent] -= 1;
                if waits[parent] == 0 {
                    ready.push_back(parent);
                }
            }
        }
        if let Some(blocked) = waits.iter().position(|&remaining| remaining != 0) {
            return Err(refusal(
                symbols[blocked].name,
                "blocked by a same-yield unary cycle",
            ));
        }
        Ok(Self {
            start,
            rules,
            order,
            components: symbols.iter().map(|symbol| symbol.components).collect(),
        })
    }

    /// Instantiate the start over the whole input and discover dependencies
    /// by matching production patterns. An empty input gives an absent root.
    /// Order is declaration order, then increasing split positions within
    /// each parent component in declaration order.
    pub fn instantiate(&self, input: &[u8]) -> Result<Instance<O>, Error> {
        let root = Item {
            nonterminal: self.start,
            spans: vec![Span {
                start: 0,
                end: input.len(),
            }],
        };
        let mut index = BTreeMap::from([(root.clone(), 0)]);
        let mut pending = vec![root];
        let mut emitted = Vec::new();
        while emitted.len() < pending.len() {
            let parent = &pending[emitted.len()];
            let mut occurrences = Vec::new();
            for (rule, production) in self.rules[parent.nonterminal].iter().enumerate() {
                occurrences.extend(
                    self.match_children(input, parent, production)
                        .into_iter()
                        .map(|children| (rule, children)),
                );
            }
            let rules = occurrences
                .into_iter()
                .map(|(rule, children)| {
                    let children: Vec<_> = children
                        .into_iter()
                        .map(|item| {
                            *index.entry(item.clone()).or_insert_with(|| {
                                let id = pending.len();
                                pending.push(item);
                                id
                            })
                        })
                        .collect();
                    (rule, children)
                })
                .collect::<Vec<_>>();
            emitted.push(rules);
        }

        let schedule = self.schedule(&pending);
        let mut ranks = vec![0; pending.len()];
        for (rank, &id) in schedule.iter().enumerate() {
            ranks[id] = rank;
        }
        let mut cells = Vec::with_capacity(pending.len());
        let mut items = Vec::with_capacity(pending.len());
        for id in schedule {
            let parent = &pending[id];
            let mut rules = Vec::new();
            for (rule, children) in std::mem::take(&mut emitted[id]) {
                let matched: Vec<_> = children.iter().map(|&child| &pending[child]).collect();
                let operator = (self.rules[parent.nonterminal][rule].operator)(Matched {
                    input,
                    parent,
                    children: &matched,
                });
                rules.push(Rule::new(
                    operator,
                    children
                        .into_iter()
                        .map(|child| ranks[child])
                        .collect::<Vec<Cell>>(),
                ));
            }
            items.push(parent.clone());
            cells.push(rules);
        }
        Ok(Instance {
            chart: Chart::new(cells, ranks[0])?,
            items,
        })
    }
    fn schedule(&self, items: &[Item]) -> Vec<usize> {
        let mut schedule: Vec<_> = (0..items.len()).collect();
        schedule.sort_unstable_by_key(|&id| {
            let item = &items[id];
            (
                item.spans
                    .iter()
                    .map(|span| span.end - span.start)
                    .sum::<usize>(),
                self.order[item.nonterminal],
                id,
            )
        });
        schedule
    }

    fn match_children(
        &self,
        input: &[u8],
        parent: &Item,
        production: &Production<O>,
    ) -> Vec<Vec<Item>> {
        let children = production
            .children
            .iter()
            .map(|&nonterminal| Item {
                nonterminal,
                spans: vec![Span { start: 0, end: 0 }; self.components[nonterminal]],
            })
            .collect();
        let mut matches = Matcher {
            input,
            parent,
            patterns: &production.patterns,
            children,
            matches: Vec::new(),
        };
        matches.component(0);
        matches.matches
    }
}

struct Matcher<'a> {
    input: &'a [u8],
    parent: &'a Item,
    patterns: &'a [Vec<Atom>],
    children: Vec<Item>,
    matches: Vec<Vec<Item>>,
}

impl Matcher<'_> {
    fn component(&mut self, component: usize) {
        if let Some(span) = self.parent.spans.get(component) {
            self.atoms(component, 0, span.start, span.end);
        } else {
            self.matches.push(self.children.clone());
        }
    }

    fn atoms(&mut self, component: usize, atom: usize, cursor: usize, end: usize) {
        let pattern = &self.patterns[component];
        if atom == pattern.len() {
            if cursor == end {
                self.component(component + 1);
            }
            return;
        }
        let remaining = pattern.len() - atom;
        if end - cursor < remaining {
            return;
        }
        match pattern[atom] {
            Atom::Byte(byte) if self.input[cursor] != byte => {}
            Atom::Byte(_) | Atom::Any => self.atoms(component, atom + 1, cursor + 1, end),
            Atom::Component {
                child,
                component: part,
            } => {
                let last_end = end - (remaining - 1);
                // The last atom must consume all remaining tokens.
                let first_end = if remaining == 1 { end } else { cursor + 1 };
                for split in first_end..=last_end {
                    self.children[child].spans[part] = Span {
                        start: cursor,
                        end: split,
                    };
                    self.atoms(component, atom + 1, split, end);
                }
            }
        }
    }
}

fn refusal(name: &str, reason: &'static str) -> Error {
    Error::UnsupportedGrammar {
        name: name.to_owned(),
        reason,
    }
}

/// An input-bound, reachable-item schedule. It retains child indices and
/// production indices. Constructors run when a cell is evaluated or replayed.
pub struct Compiled<'a, O, G> {
    grammar: G,
    input: &'a [u8],
    items: Vec<Item>,
    occurrences: Vec<Occurrence>,
    cell_rules: Vec<Range<usize>>,
    edges: Vec<Cell>,
    schedule: Vec<usize>,
    ranks: Vec<Cell>,
    operator: std::marker::PhantomData<fn() -> O>,
}

struct Occurrence {
    production: usize,
    children: Range<usize>,
}

struct MatchPlan {
    children: Vec<(Nonterminal, Range<usize>)>,
    patterns: Vec<Vec<MatchAtom>>,
    slots: usize,
}

enum MatchAtom {
    Token(Option<u8>),
    Span { slot: usize, last: bool },
}

impl MatchPlan {
    fn new<O>(rule: &Production<O>, components: &[usize]) -> Self {
        let mut slots = 0;
        let children: Vec<_> = rule
            .children
            .iter()
            .map(|&nt| {
                let start = slots;
                slots += components[nt];
                (nt, start..slots)
            })
            .collect();
        let patterns = rule
            .patterns
            .iter()
            .map(|pattern| {
                let last = pattern
                    .iter()
                    .rposition(|atom| matches!(atom, Atom::Component { .. }));
                pattern
                    .iter()
                    .enumerate()
                    .map(|(index, atom)| match *atom {
                        Atom::Byte(byte) => MatchAtom::Token(Some(byte)),
                        Atom::Any => MatchAtom::Token(None),
                        Atom::Component { child, component } => MatchAtom::Span {
                            slot: children[child].1.start + component,
                            last: last == Some(index),
                        },
                    })
                    .collect()
            })
            .collect();
        Self {
            children,
            patterns,
            slots,
        }
    }
}

struct MatchStream<'a, F> {
    input: &'a [u8],
    parent: &'a [Span],
    patterns: &'a [Vec<MatchAtom>],
    scratch: &'a mut [Span],
    emit: F,
}

impl<'a, F: FnMut(&[Span])> MatchStream<'a, F> {
    fn run(&mut self) {
        let span = self.parent[0];
        self.atoms(0, &self.patterns[0], span.start, span.end);
    }

    fn atoms(
        &mut self,
        mut component: usize,
        mut pattern: &'a [MatchAtom],
        mut cursor: usize,
        mut end: usize,
    ) {
        loop {
            if end - cursor < pattern.len() {
                return;
            }
            match pattern {
                [] => {
                    if cursor != end {
                        return;
                    }
                    component += 1;
                    let Some(span) = self.parent.get(component) else {
                        (self.emit)(self.scratch);
                        return;
                    };
                    (cursor, end) = (span.start, span.end);
                    pattern = &self.patterns[component];
                }
                [MatchAtom::Token(byte), rest @ ..] => {
                    if byte.is_some_and(|expected| self.input[cursor] != expected) {
                        return;
                    }
                    cursor += 1;
                    pattern = rest;
                }
                [MatchAtom::Span { slot, last }, rest @ ..] => {
                    let last_end = end - rest.len();
                    // Fixed-width tokens force the end of the final variable.
                    // Only the earlier feasible endpoints need a recursive branch.
                    if !*last {
                        for split in cursor + 1..last_end {
                            self.scratch[*slot] = Span {
                                start: cursor,
                                end: split,
                            };
                            self.atoms(component, rest, split, end);
                        }
                    }
                    self.scratch[*slot] = Span {
                        start: cursor,
                        end: last_end,
                    };
                    cursor = last_end;
                    pattern = rest;
                }
            }
        }
    }
}

// Short coordinate tuples can be indexed without allocating a second copy
// of their spans. The bound comes from the number of endpoint bits that fit
// in the key. The general index applies to every other tuple.
enum ItemIndex {
    Packed {
        bits: u32,
        entries: HashMap<u64, usize>,
    },
    Spans(HashMap<Vec<Span>, usize>),
}

impl ItemIndex {
    fn new(input_len: usize, components: usize) -> Self {
        let bits = (usize::BITS - input_len.leading_zeros()).max(1);
        if components <= (u64::BITS / bits / 2) as usize {
            Self::Packed {
                bits,
                entries: HashMap::new(),
            }
        } else {
            Self::Spans(HashMap::new())
        }
    }

    fn intern(&mut self, spans: &[Span], fresh: usize) -> usize {
        match self {
            Self::Packed { bits, entries } => {
                let key = spans.iter().fold(0, |key, span| {
                    (((key << *bits) | span.start as u64) << *bits) | span.end as u64
                });
                *entries.entry(key).or_insert(fresh)
            }
            Self::Spans(entries) => match entries.get(spans) {
                Some(&id) => id,
                None => {
                    entries.insert(spans.to_vec(), fresh);
                    fresh
                }
            },
        }
    }
}

/// Discover reachable items for a checked linear MCFG. Accepts either an
/// owned grammar or a borrowed one.
pub fn compile<O: Operator, G: std::borrow::Borrow<Grammar<O>>>(
    grammar: G,
    input: &[u8],
) -> Result<Compiled<'_, O, G>, Error> {
    let definition = grammar.borrow();
    let plans: Vec<Vec<_>> = definition
        .rules
        .iter()
        .map(|rules| {
            rules
                .iter()
                .map(|rule| MatchPlan::new(rule, &definition.components))
                .collect()
        })
        .collect();
    let root = Item {
        nonterminal: definition.start,
        spans: vec![Span {
            start: 0,
            end: input.len(),
        }],
    };
    let mut index: Vec<_> = definition
        .components
        .iter()
        .map(|&components| ItemIndex::new(input.len(), components))
        .collect();
    index[root.nonterminal].intern(&root.spans, 0);
    let mut order = BTreeMap::from([((input.len(), definition.order[root.nonterminal]), vec![0])]);
    let mut items = vec![root];
    let mut occurrences = Vec::new();
    let mut edges = Vec::new();
    let mut cell_rules = Vec::new();
    let mut discovered = Vec::new();
    let mut scratch = Vec::new();

    while cell_rules.len() < items.len() {
        let parent = &items[cell_rules.len()];
        let first = occurrences.len();
        for (production, plan) in plans[parent.nonterminal].iter().enumerate() {
            if scratch.len() < plan.slots {
                scratch.resize(plan.slots, Span { start: 0, end: 0 });
            }
            MatchStream {
                input,
                parent: &parent.spans,
                patterns: &plan.patterns,
                scratch: &mut scratch[..plan.slots],
                emit: |coordinates: &[Span]| {
                    let start = edges.len();
                    for (nonterminal, parts) in &plan.children {
                        let spans = &coordinates[parts.clone()];
                        let fresh = items.len() + discovered.len();
                        let id = index[*nonterminal].intern(spans, fresh);
                        if id == fresh {
                            let consumed = spans.iter().map(|span| span.end - span.start).sum();
                            order
                                .entry((consumed, definition.order[*nonterminal]))
                                .or_default()
                                .push(id);
                            discovered.push(Item {
                                nonterminal: *nonterminal,
                                spans: spans.to_vec(),
                            });
                        }
                        edges.push(id);
                    }
                    occurrences.push(Occurrence {
                        production,
                        children: start..edges.len(),
                    });
                },
            }
            .run();
        }
        cell_rules.push(first..occurrences.len());
        items.append(&mut discovered);
    }

    // Ordered buckets sort by yield and nonterminal. Appending to each
    // bucket retains discovery order without comparing item coordinates.
    let schedule: Vec<_> = order.into_values().flatten().collect();
    let mut ranks = vec![0; schedule.len()];
    for (rank, &id) in schedule.iter().enumerate() {
        ranks[id] = rank;
    }
    Ok(Compiled {
        grammar,
        input,
        items,
        occurrences,
        cell_rules,
        edges,
        schedule,
        ranks,
        operator: std::marker::PhantomData,
    })
}

impl<O: Operator, G: std::borrow::Borrow<Grammar<O>>> Compiled<'_, O, G> {
    /// The semantic item at a rank, including an absent root on empty input.
    pub fn item(&self, rank: Cell) -> Option<&Item> {
        self.schedule.get(rank).map(|&id| &self.items[id])
    }

    fn emit_cell<'a>(
        &'a self,
        rank: Cell,
        matched: &mut Vec<&'a Item>,
        children: &mut Vec<Cell>,
        mut emit: impl FnMut(&str, O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let &id = self.schedule.get(rank).ok_or(Error::CellOutOfRange(rank))?;
        let parent = &self.items[id];
        for rule in &self.occurrences[self.cell_rules[id].clone()] {
            matched.clear();
            children.clear();
            let ids = &self.edges[rule.children.clone()];
            matched.extend(ids.iter().map(|&child| &self.items[child]));
            children.extend(ids.iter().map(|&child| self.ranks[child]));
            let production = &self.grammar.borrow().rules[parent.nonterminal][rule.production];
            let operator = (production.operator)(Matched {
                input: self.input,
                parent,
                children: matched,
            });
            crate::validate_rule(rank, &operator, children)?;
            emit(&production.name, operator, children)?;
        }
        Ok(())
    }
}

impl<O: Operator, G: std::borrow::Borrow<Grammar<O>>> crate::fast::RuleSource
    for Compiled<'_, O, G>
{
    type Op = O;

    fn cell_count(&self) -> usize {
        self.schedule.len()
    }

    fn root(&self) -> Cell {
        self.ranks[0]
    }

    fn rules_at(
        &self,
        rank: Cell,
        mut emit: impl FnMut(O, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        self.emit_cell(rank, &mut Vec::new(), &mut Vec::new(), |_, op, children| {
            emit(op, children)
        })
    }
}

impl<O, G> crate::compiled::sealed::Sealed for Compiled<'_, O, G> {}

impl<O: Operator, G: std::borrow::Borrow<Grammar<O>>> crate::compiled::Program
    for Compiled<'_, O, G>
{
    fn fill(&self, sink: &mut impl crate::compiled::ProductionSink<O>) -> Result<(), Error> {
        let mut matched = Vec::new();
        let mut ranks = Vec::new();
        for rank in 0..self.schedule.len() {
            self.emit_cell(
                rank,
                &mut matched,
                &mut ranks,
                |site, op, children| match children {
                    [] => sink.rule(site, op, []),
                    &[child] => sink.rule(site, op, [child]),
                    &[left, right] => sink.rule(site, op, [left, right]),
                    _ => sink.rule_slice(site, op, children),
                },
            )?;
            sink.finish_cell()?;
        }
        Ok(())
    }
}
