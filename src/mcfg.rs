//! Multiple context-free grammars over one byte string and nonempty components.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Range;

use crate::{Cell, Chart, Error, Operator, Rule};

/// Stable index into the declared nonterminal list.
pub type Nonterminal = usize;

/// Half-open coordinates of one component on the input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
                occurrences.extend(matches.matches.into_iter().map(|children| (rule, children)));
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

        let mut schedule: Vec<_> = (0..pending.len()).collect();
        schedule.sort_unstable_by_key(|&id| {
            let item = &pending[id];
            (
                item.spans
                    .iter()
                    .map(|span| span.end - span.start)
                    .sum::<usize>(),
                self.order[item.nonterminal],
                id,
            )
        });
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
                for split in cursor + 1..=last_end {
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
