//! The smallest explicit history state of a reachable raw additive model.
//!
//! A scorer gives a score to every word of operations, for example the match,
//! mismatch, delete and insert steps of an alignment. A dynamic program over
//! such words needs, at each position, enough state to know every future score
//! change. Declare a finite [`Observer`] of histories that is assumed to be enough:
//! the last `k` operations, or the product of a library of feature automata.
//! [`RawModel::read`] reads the score change of every observer state and symbol from
//! the scorer. [`RawModel::check`] compares the observer with the scorer on every
//! word up to a declared length and refuses, with two words that share an observer
//! state but differ in score change, when the observer is too coarse.
//!
//! [`RawModel::quotient`] merges observer states that agree on every future score
//! change. The result is the coarsest partition that keeps equal score changes
//! and maps every symbol from a class into one class. A [`Quotient`] certificate
//! carries the class table and probe words whose score changes tell every pair of
//! classes apart, and [`Quotient::verify`] replays both conditions against the
//! raw table. [`Merging`] admits or refuses proposed merges one at a time; each
//! refusal carries a probe word.
//!
//! The `chart` method of a verified `Exact<Quotient>` turns the class table into
//! explicit chart state over a
//! [`Geometry`], such as the cells `(i, j)` of a pairwise [`Alignment`]. Its cells
//! are `(geometry cell, class)` pairs. Use [`crate::common_optimum::common`] with one
//! model on the chart for the optimum, the count of optimal move derivations and
//! ranked witnesses. A finite scorer check validates scores through its length.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt;
use std::sync::Arc;

use crate::assurance::{CertificateKind, Family, Label, QuestionKind, Shape};
use crate::common_optimum::{self, CostVector, ModelSet};
use crate::{Chart, Exact, Operator, Rule};

/// An operation, as an index into the declared alphabet.
pub type Symbol = usize;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// An observer needs at least one symbol and one state, and a valid table.
    InvalidObserver(&'static str),
    /// A score change does not fit in `i64`.
    Overflow,
    /// The declared observer is too coarse for the scorer.
    Refuted(Box<Violation>),
    /// A certificate's tables do not match the raw model.
    CertificateShape,
    /// Two states of one class differ in score change or successor class.
    Closure {
        state: usize,
        symbol: Symbol,
    },
    /// The probes do not tell two classes apart.
    Separation {
        classes: (usize, usize),
    },
    /// The geometry has a cycle among reachable cells.
    CyclicGeometry,
    /// A symbol outside the declared alphabet.
    SymbolOutOfRange {
        symbol: Symbol,
    },
    /// A state outside the declared observer.
    StateOutOfRange {
        state: usize,
    },
    /// A replayed witness does not reproduce its recorded score changes or length.
    ReplayMismatch,
    /// A checked answer differs from the cached read answer for the same word.
    ScorerDisagrees {
        word: Vec<Symbol>,
        read: i64,
        checked: i64,
    },
    /// A feature-set certificate does not match the raw model.
    FeatureSets(&'static str),
    /// Another candidate check would exceed the caller's work limit.
    FeatureWorkLimit {
        limit: usize,
    },
    /// Another retained finding would exceed the caller's storage limit.
    FeatureStorageLimit {
        limit: usize,
    },
    /// Even all features together do not determine the score changes and
    /// successor values: two product states with equal values that differ.
    InsufficientLibrary {
        states: [usize; 2],
    },
    Chart(common_optimum::Error),
    /// Storage could not be reserved.
    AllocationFailed,
}

impl From<common_optimum::Error> for Error {
    fn from(error: common_optimum::Error) -> Self {
        Self::Chart(error)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidObserver(reason) => write!(f, "invalid observer: {reason}"),
            Self::Overflow => write!(f, "a score change does not fit in i64"),
            Self::Refuted(violation) => write!(
                f,
                "the observer is too coarse: words {:?} and {:?} share a state but symbol {} changes their scores by {} and {}",
                violation.word, violation.access, violation.symbol, violation.gains[0], violation.gains[1]
            ),
            Self::CertificateShape => write!(f, "certificate tables do not match the raw model"),
            Self::Closure { state, symbol } => {
                write!(f, "state {state} disagrees with its class on symbol {symbol}")
            }
            Self::Separation { classes } => {
                write!(f, "no probe separates classes {} and {}", classes.0, classes.1)
            }
            Self::CyclicGeometry => write!(f, "the geometry has a cycle"),
            Self::SymbolOutOfRange { symbol } => {
                write!(f, "symbol {symbol} is outside the declared alphabet")
            }
            Self::StateOutOfRange { state } => {
                write!(f, "state {state} is outside the declared observer")
            }
            Self::ReplayMismatch => {
                write!(f, "the witness does not reproduce its recorded score changes or length")
            }
            Self::ScorerDisagrees {
                word,
                read,
                checked,
            } => write!(
                f,
                "the checked scorer gives {checked} on a word of length {} where the read scorer gave {read}",
                word.len()
            ),
            Self::FeatureSets(reason) => write!(f, "feature-set certificate rejected: {reason}"),
            Self::FeatureWorkLimit { limit } => {
                write!(f, "feature-set search exceeds the limit of {limit} candidate checks")
            }
            Self::FeatureStorageLimit { limit } => {
                write!(f, "feature-set search exceeds the limit of {limit} certificate slots")
            }
            Self::InsufficientLibrary { states } => write!(
                f,
                "product states {} and {} share every feature value but differ",
                states[0], states[1]
            ),
            Self::Chart(error) => write!(f, "{error}"),
            Self::AllocationFailed => write!(f, "could not reserve storage"),
        }
    }
}

impl std::error::Error for Error {}

fn reserved<T>(capacity: usize) -> Result<Vec<T>, Error> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| Error::AllocationFailed)?;
    Ok(values)
}

fn filled<T: Copy>(len: usize, value: T) -> Result<Vec<T>, Error> {
    let mut values = reserved(len)?;
    values.resize(len, value);
    Ok(values)
}

fn copied<T: Copy>(source: &[T]) -> Result<Vec<T>, Error> {
    let mut values = reserved(source.len())?;
    values.extend_from_slice(source);
    Ok(values)
}

fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), Error> {
    values.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
    values.push(value);
    Ok(())
}

fn require_alphabet(symbols: usize) -> Result<(), Error> {
    if symbols == 0 {
        return Err(Error::InvalidObserver("the alphabet is empty"));
    }
    Ok(())
}

/// A finite automaton over histories: states `0..states()`, a start state, and a
/// successor for each state and symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Observer {
    symbols: usize,
    start: usize,
    next: Vec<Vec<usize>>,
}

impl Observer {
    pub fn new(symbols: usize, start: usize, next: Vec<Vec<usize>>) -> Result<Self, Error> {
        require_alphabet(symbols)?;
        if start >= next.len() {
            return Err(Error::InvalidObserver("the start state does not exist"));
        }
        for row in &next {
            if row.len() != symbols || row.iter().any(|&state| state >= next.len()) {
                return Err(Error::InvalidObserver("a successor row is malformed"));
            }
        }
        Ok(Self {
            symbols,
            start,
            next,
        })
    }

    /// The last `horizon` symbols, or the whole word while it is shorter. State
    /// `i` is the `i`-th word in shortlex order. [`Observer::history`] returns it.
    /// Unrepresentable dimensions or a failed reservation return
    /// [`Error::AllocationFailed`].
    pub fn last_symbols(symbols: usize, horizon: usize) -> Result<Self, Error> {
        require_alphabet(symbols)?;
        // Count the shortlex blocks before allocating any rows.
        let (states, full_block) = if symbols == 1 {
            (horizon.checked_add(1).ok_or(Error::AllocationFailed)?, 1)
        } else {
            let (mut states, mut block) = (1usize, 1usize);
            for _ in 0..horizon {
                block = block.checked_mul(symbols).ok_or(Error::AllocationFailed)?;
                states = states.checked_add(block).ok_or(Error::AllocationFailed)?;
            }
            (states, block)
        };
        let entries = states.checked_mul(symbols).ok_or(Error::AllocationFailed)?;
        // A single table's dense payload must be representable as a Rust layout.
        std::alloc::Layout::array::<usize>(entries).map_err(|_| Error::AllocationFailed)?;
        let mut next = reserved(states)?;
        let full_start = states - full_block;
        for state in 0..states {
            let mut row = reserved(symbols)?;
            if horizon == 0 {
                row.resize(symbols, 0);
            } else {
                let first = if state < full_start {
                    // Extending a short history: the words following the empty word
                    // are in groups of `symbols`, indexed by their prefixes.
                    state * symbols + 1
                } else {
                    // Extending a full history: drop its most significant symbol.
                    let suffix = (state - full_start) % (full_block / symbols);
                    full_start + suffix * symbols
                };
                row.extend(first..first + symbols);
            }
            next.push(row);
        }
        Self::new(symbols, 0, next)
    }

    /// The shortlex history word for `state` in a nonempty alphabet.
    pub fn history(symbols: usize, mut state: usize) -> Result<Vec<Symbol>, Error> {
        require_alphabet(symbols)?;
        if symbols == 1 {
            return filled(state, 0);
        }
        // Shortlex: length-l words occupy a block after all shorter words.
        let mut length = 0;
        let mut block = 1usize;
        while state >= block {
            state -= block;
            length += 1;
            block = block.saturating_mul(symbols);
        }
        word_at(state, length, symbols)
    }

    /// The reachable product of several observers over one alphabet. Returns the
    /// product and, for each product state, the state of every component.
    pub fn product(components: &[Observer]) -> Result<(Self, Vec<Vec<usize>>), Error> {
        Self::product_of(components.iter())
    }

    fn product_of<'a>(
        components: impl ExactSizeIterator<Item = &'a Observer> + Clone,
    ) -> Result<(Self, Vec<Vec<usize>>), Error> {
        let first = components
            .clone()
            .next()
            .ok_or(Error::InvalidObserver("a product needs a component"))?;
        let symbols = first.symbols;
        if components.clone().any(|c| c.symbols != symbols) {
            return Err(Error::InvalidObserver("components use different alphabets"));
        }
        let width = components.len();
        let mut start = reserved(width)?;
        start.extend(components.clone().map(|c| c.start));
        let mut index: HashMap<Vec<usize>, usize> = HashMap::new();
        index.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
        index.insert(copied(&start)?, 0);
        let mut states = reserved(1)?;
        states.push(start);
        let mut next = Vec::new();
        let mut target = filled(width, 0)?;
        let mut cursor = 0;
        while cursor < states.len() {
            let mut row = reserved(symbols)?;
            for symbol in 0..symbols {
                for ((slot, &state), component) in target
                    .iter_mut()
                    .zip(&states[cursor])
                    .zip(components.clone())
                {
                    *slot = component.next[state][symbol];
                }
                let id = match index.get(target.as_slice()) {
                    Some(&id) => id,
                    None => {
                        let id = states.len();
                        index.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
                        push(&mut states, copied(&target)?)?;
                        index.insert(copied(&target)?, id);
                        id
                    }
                };
                row.push(id);
            }
            push(&mut next, row)?;
            cursor += 1;
        }
        Ok((Self::new(symbols, 0, next)?, states))
    }

    pub fn symbols(&self) -> usize {
        self.symbols
    }

    pub fn states(&self) -> usize {
        self.next.len()
    }

    pub fn start(&self) -> usize {
        self.start
    }

    /// Requires `state < self.states()` and `symbol < self.symbols()`.
    pub fn next(&self, state: usize, symbol: Symbol) -> usize {
        self.next[state][symbol]
    }

    /// Requires every symbol of `word` to be below `self.symbols()`.
    pub fn state_after(&self, word: &[Symbol]) -> usize {
        word.iter()
            .fold(self.start, |state, &symbol| self.next[state][symbol])
    }
}

/// The declared history and the score changes read for it by one call of
/// [`RawModel::read`]. A raw model, its checks, its quotients and their charts share
/// one allocation of it, so a label names the read it rests on. Two reads of
/// different scorers can give equal tables, so identity is the shared allocation,
/// not equal contents.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Table {
    observer: Observer,
    reachable: Vec<bool>,
    base: i64,
    gains: Vec<Vec<i64>>,
}

/// Whether two handles name the same read of a raw model.
fn same_table(a: &Arc<Table>, b: &Arc<Table>) -> bool {
    Arc::ptr_eq(a, b)
}

/// The score change of every reachable observer state, read from a scorer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawModel {
    observer: Observer,
    /// The shortest word reaching each state, first in symbol order; `None` if unreachable.
    access: Vec<Option<Vec<Symbol>>>,
    base: i64,
    gains: Vec<Vec<i64>>,
    // Read words and their scores, in lexicographic order for check and lookup.
    known: Vec<(Vec<Symbol>, i64)>,
    table: Arc<Table>,
}

impl RawModel {
    /// Ask the scorer for the empty word, the shortest word reaching each state and
    /// each one-symbol extension. A finite observer with `n` reachable states and
    /// `s` symbols needs exactly `n * s + 1` distinct words.
    pub fn read(
        observer: Observer,
        scorer: &mut dyn FnMut(&[Symbol]) -> i64,
    ) -> Result<Self, Error> {
        let states = observer.states();
        let mut access: Vec<Option<Vec<Symbol>>> = reserved(states)?;
        access.resize_with(states, || None);
        access[observer.start] = Some(Vec::new());
        let mut queue = VecDeque::new();
        queue.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
        queue.push_back(observer.start);
        let mut order = Vec::new();
        while let Some(state) = queue.pop_front() {
            push(&mut order, state)?;
            for symbol in 0..observer.symbols {
                let target = observer.next[state][symbol];
                if access[target].is_none() {
                    let word = access[state].as_deref().expect("visited");
                    access[target] = Some(extended_word(word, symbol)?);
                    queue.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
                    queue.push_back(target);
                }
            }
        }

        // Every nonempty access word is a one-symbol extension of an earlier
        // access word. Distinct (state, symbol) pairs give distinct extensions.
        let calls = order
            .len()
            .checked_mul(observer.symbols)
            .and_then(|n| n.checked_add(1))
            .ok_or(Error::AllocationFailed)?;
        let mut known = reserved(calls)?;
        let mut gains = reserved(states)?;
        for _ in 0..states {
            gains.push(filled(observer.symbols, 0i64)?);
        }
        let mut access_scores = filled(states, 0i64)?;
        let base = scorer(&[]);
        known.push((Vec::new(), base));
        access_scores[observer.start] = base;
        for state in order {
            let word = access[state].as_deref().expect("visited");
            let here = access_scores[state];
            for (symbol, gain) in gains[state].iter_mut().enumerate() {
                let longer = extended_word(word, symbol)?;
                let score = scorer(&longer);
                let target = observer.next[state][symbol];
                if access[target].as_deref() == Some(longer.as_slice()) {
                    access_scores[target] = score;
                }
                *gain = score.checked_sub(here).ok_or(Error::Overflow)?;
                known.push((longer, score));
            }
        }
        known.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

        let mut reachable = reserved(states)?;
        reachable.extend(access.iter().map(Option::is_some));
        let mut next = reserved(states)?;
        let mut table_gains = reserved(states)?;
        for (row, gains_row) in observer.next.iter().zip(&gains) {
            next.push(copied(row)?);
            table_gains.push(copied(gains_row)?);
        }
        let table = Arc::new(Table {
            observer: Observer {
                symbols: observer.symbols,
                start: observer.start,
                next,
            },
            reachable,
            base,
            gains: table_gains,
        });
        Ok(Self {
            observer,
            access,
            base,
            gains,
            known,
            table,
        })
    }

    pub fn observer(&self) -> &Observer {
        &self.observer
    }

    /// Distinct words the read asked of its scorer: `n * s + 1` for `n` reachable
    /// states and `s` symbols. Checks do not change it.
    pub fn scorer_calls(&self) -> usize {
        self.known.len()
    }

    pub fn is_reachable(&self, state: usize) -> bool {
        self.access.get(state).is_some_and(Option::is_some)
    }

    pub fn access(&self, state: usize) -> Option<&[Symbol]> {
        self.access.get(state)?.as_deref()
    }

    /// Requires indices in the observer's state and symbol ranges. The read
    /// measures gains only for reachable states.
    pub fn gain(&self, state: usize, symbol: Symbol) -> i64 {
        self.gains[state][symbol]
    }

    pub fn base(&self) -> i64 {
        self.base
    }

    /// The model's score of a word: the empty-word score plus the score changes
    /// along the observer's states. Requires every symbol of `word` to be
    /// in the observer's alphabet.
    pub fn score(&self, word: &[Symbol]) -> i128 {
        let mut state = self.observer.start;
        let mut total = i128::from(self.base);
        for &symbol in word {
            total += i128::from(self.gains[state][symbol]);
            state = self.observer.next[state][symbol];
        }
        total
    }

    /// Compare the model with `scorer` on every word of length at most `length`.
    /// A successful check asks `scorer` once per word, including the empty word
    /// and all words within that length whose answers were cached by the read.
    /// These cached answers are checked first. A different answer returns
    /// [`Error::ScorerDisagrees`]. The model is then checked in order of word
    /// length, so a [`Violation`] names a shortest violating word.
    pub fn check(
        &mut self,
        scorer: &mut dyn FnMut(&[Symbol]) -> i64,
        length: usize,
    ) -> Result<Exact<ObserverCheck>, Error> {
        let symbols = self.observer.symbols;
        for (word, read) in &self.known {
            let read = *read;
            if word.len() <= length {
                let checked = scorer(word);
                if checked != read {
                    return Err(Error::ScorerDisagrees {
                        word: copied(word)?,
                        read,
                        checked,
                    });
                }
            }
        }
        // One level of words of equal length: (observer state, scorer score).
        // Every cached score used here has been checked, including the base.
        let mut level: Vec<(usize, i64)> = vec![(self.observer.start, self.base)];
        let mut words_checked = 1usize;
        for depth in 0..length {
            let width = level
                .len()
                .checked_mul(symbols)
                .ok_or(Error::AllocationFailed)?;
            let mut next_level = reserved(width)?;
            for (index, &(state, score)) in level.iter().enumerate() {
                for symbol in 0..symbols {
                    let word = word_at(index * symbols + symbol, depth + 1, symbols)?;
                    let longer = match self.known.binary_search_by(|(known, _)| known.cmp(&word)) {
                        Ok(index) => self.known[index].1,
                        Err(_) => scorer(&word),
                    };
                    let gain = longer.checked_sub(score).ok_or(Error::Overflow)?;
                    if gain != self.gains[state][symbol] {
                        let prefix = copied(&word[..depth])?;
                        let access = copied(self.access[state].as_deref().expect("reachable"))?;
                        return Err(Error::Refuted(Box::new(Violation {
                            word: prefix,
                            access,
                            symbol,
                            gains: [gain, self.gains[state][symbol]],
                            checked_length: length,
                        })));
                    }
                    next_level.push((self.observer.next[state][symbol], longer));
                }
            }
            words_checked = words_checked
                .checked_add(next_level.len())
                .ok_or(Error::Overflow)?;
            level = next_level;
        }
        Ok(Exact(ObserverCheck {
            length,
            words_checked,
            table: Arc::clone(&self.table),
        }))
    }

    /// The coarsest partition of reachable states that keeps score changes and
    /// successor classes, by partition refinement (Moore). Verified before return.
    pub fn quotient(&self) -> Result<Exact<Quotient>, Error> {
        let reachable: Vec<usize> = (0..self.observer.states())
            .filter(|&state| self.is_reachable(state))
            .collect();
        // levels[r][state] is the block of `state` after r + 1 refinement rounds.
        let mut levels: Vec<Vec<usize>> = Vec::new();
        let mut blocks = number(&reachable, self.observer.states(), |state| {
            self.gains[state].clone()
        })?;
        loop {
            let count = distinct(&blocks, &reachable);
            levels.push(blocks.clone());
            let refined = number(&reachable, self.observer.states(), |state| {
                let mut key = vec![blocks[state]];
                key.extend(
                    self.observer.next[state]
                        .iter()
                        .map(|&target| blocks[target]),
                );
                key
            })?;
            if distinct(&refined, &reachable) == count {
                break;
            }
            blocks = refined;
        }
        let quotient = self.build(&blocks, |s, t| separate(self, &levels, s, t))?;
        quotient.verify(self)?;
        Ok(Exact(quotient))
    }

    /// Build the quotient for a congruent partition given by `blocks`, with probes
    /// from `separator` for pairs of representatives.
    fn build(
        &self,
        blocks: &[usize],
        mut separator: impl FnMut(usize, usize) -> Vec<Symbol>,
    ) -> Result<Quotient, Error> {
        // Number classes by first reachable state in access (breadth-first) order.
        let mut order: Vec<usize> = (0..self.observer.states())
            .filter(|&state| self.is_reachable(state))
            .collect();
        order.sort_by(|&a, &b| {
            let (x, y) = (
                self.access[a].as_ref().unwrap(),
                self.access[b].as_ref().unwrap(),
            );
            x.len().cmp(&y.len()).then_with(|| x.cmp(y))
        });
        let mut class_id: HashMap<usize, usize> = HashMap::new();
        let mut representative = Vec::new();
        let mut class_of = vec![None; self.observer.states()];
        for &state in &order {
            let fresh = class_id.len();
            let class = *class_id.entry(blocks[state]).or_insert_with(|| {
                representative.push(state);
                fresh
            });
            class_of[state] = Some(class);
        }
        let classes = representative.len();
        let gains: Vec<Vec<i64>> = representative
            .iter()
            .map(|&s| self.gains[s].clone())
            .collect();
        let next: Vec<Vec<usize>> = representative
            .iter()
            .map(|&s| {
                (0..self.observer.symbols)
                    .map(|symbol| class_of[self.observer.next[s][symbol]].expect("reachable"))
                    .collect()
            })
            .collect();
        let mut quotient = Quotient {
            symbols: self.observer.symbols,
            class_of,
            start: 0,
            base: self.base,
            gains,
            next,
            probes: Vec::new(),
            table: Arc::clone(&self.table),
        };
        quotient.start = quotient.class_of[self.observer.start].expect("start is reachable");
        // Add probes until every class has a distinct signature.
        loop {
            let mut groups: BTreeMap<Vec<i128>, usize> = BTreeMap::new();
            let mut clash = None;
            for class in 0..classes {
                let signature = quotient.signature(class);
                if let Some(&other) = groups.get(&signature) {
                    clash = Some((other, class));
                    break;
                }
                groups.insert(signature, class);
            }
            let Some((a, b)) = clash else { break };
            let probe = separator(representative[a], representative[b]);
            if quotient.gain_from(a, &probe) == quotient.gain_from(b, &probe) {
                return Err(Error::Separation { classes: (a, b) });
            }
            quotient.probes.push(probe);
        }
        Ok(quotient)
    }

    /// Explicit chart state over the declared observer itself, one class per
    /// reachable state, before any merge. Its scores equal the quotient chart's.
    /// Maximizing returns [`Error::Overflow`] for an `i64::MIN` base or gain
    /// used by a rule.
    pub fn raw_chart<G: Geometry>(
        &self,
        geometry: &G,
        sense: Sense,
    ) -> Result<StateChart<G::Cell>, Error> {
        let mut states = reserved(self.observer.states())?;
        states.extend((0..self.observer.states()).filter(|&state| self.is_reachable(state)));
        let mut class_of = filled(self.observer.states(), None)?;
        for (class, &state) in states.iter().enumerate() {
            class_of[state] = Some(class);
        }
        let mut gains = reserved(states.len())?;
        let mut next = reserved(states.len())?;
        for state in states {
            gains.push(copied(&self.gains[state])?);
            let mut row = reserved(self.observer.symbols)?;
            row.extend(self.observer.next[state].iter().map(|&target| {
                class_of[target].expect("successors of reachable states are reachable")
            }));
            next.push(row);
        }
        let table = Quotient {
            symbols: self.observer.symbols,
            start: class_of[self.observer.start].expect("start is reachable"),
            base: self.base,
            gains,
            next,
            class_of,
            probes: Vec::new(),
            table: Arc::clone(&self.table),
        };
        table.chart_of_table(geometry, sense)
    }

    /// Start counterexample-guided merging from the partition into single states.
    pub fn merging(&self) -> Merging<'_> {
        Merging {
            raw: self,
            parent: (0..self.observer.states()).collect(),
            refusals: Vec::new(),
        }
    }
}

/// Refuse any symbol outside an alphabet of `symbols` symbols.
fn check_symbols<'a>(
    word: impl IntoIterator<Item = &'a Symbol>,
    symbols: usize,
) -> Result<(), Error> {
    match word.into_iter().find(|&&symbol| symbol >= symbols) {
        Some(&symbol) => Err(Error::SymbolOutOfRange { symbol }),
        None => Ok(()),
    }
}

/// The word with the given index among words of one length, first symbol most significant.
fn word_at(mut index: usize, length: usize, symbols: usize) -> Result<Vec<Symbol>, Error> {
    let mut word = filled(length, 0)?;
    for slot in word.iter_mut().rev() {
        *slot = index % symbols;
        index /= symbols;
    }
    Ok(word)
}

fn extended_word(word: &[Symbol], symbol: Symbol) -> Result<Vec<Symbol>, Error> {
    let capacity = word.len().checked_add(1).ok_or(Error::AllocationFailed)?;
    let mut extended = reserved(capacity)?;
    extended.extend_from_slice(word);
    extended.push(symbol);
    Ok(extended)
}

/// Number the reachable states by key, in order of first appearance.
fn number<K: Ord>(
    reachable: &[usize],
    states: usize,
    key: impl Fn(usize) -> K,
) -> Result<Vec<usize>, Error> {
    let mut ids: BTreeMap<K, usize> = BTreeMap::new();
    let mut blocks = filled(states, usize::MAX)?;
    for &state in reachable {
        let fresh = ids.len();
        blocks[state] = *ids.entry(key(state)).or_insert(fresh);
    }
    Ok(blocks)
}

fn distinct(blocks: &[usize], reachable: &[usize]) -> usize {
    reachable
        .iter()
        .map(|&state| blocks[state])
        .collect::<std::collections::BTreeSet<_>>()
        .len()
}

/// A word whose score change differs from states `s` and `t`, read from the
/// refinement levels: split at round one by a symbol, or at round r by a symbol
/// whose successors split at round r - 1.
fn separate(raw: &RawModel, levels: &[Vec<usize>], mut s: usize, mut t: usize) -> Vec<Symbol> {
    let mut word = Vec::new();
    loop {
        let round = levels
            .iter()
            .position(|level| level[s] != level[t])
            .expect("representatives of distinct classes split at some round");
        if round == 0 {
            let symbol = (0..raw.observer.symbols)
                .find(|&a| raw.gains[s][a] != raw.gains[t][a])
                .expect("round one splits by a score change");
            word.push(symbol);
            return word;
        }
        let symbol = (0..raw.observer.symbols)
            .find(|&a| {
                let (x, y) = (raw.observer.next[s][a], raw.observer.next[t][a]);
                levels[round - 1][x] != levels[round - 1][y]
            })
            .expect("round r splits by successors split at round r - 1");
        word.push(symbol);
        s = raw.observer.next[s][symbol];
        t = raw.observer.next[t][symbol];
    }
}

/// Two words that reach one observer state, and a symbol that changes their
/// scores differently. It refutes the declared observer for this scorer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Violation {
    pub word: Vec<Symbol>,
    /// An access word reaching the same observer state. The producer records
    /// the shortest one.
    pub access: Vec<Symbol>,
    pub symbol: Symbol,
    /// The score changes of `symbol` after `word` and after `access`.
    pub gains: [i64; 2],
    pub checked_length: usize,
}

impl Violation {
    pub const QUESTION: QuestionKind = QuestionKind::Existence;
    pub const FAMILY: Family = Family::AllCandidates;
    /// One replayed witness answers the existence question: a weak certificate.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Weak;
    pub const SHAPE: Shape = Shape::SetLevel;

    /// Ask the scorer again for the four words and the observer for both states.
    /// All symbols must be in range and both extended words must lie within
    /// the recorded checked length.
    pub fn replay(
        &self,
        observer: &Observer,
        scorer: &mut dyn FnMut(&[Symbol]) -> i64,
    ) -> Result<(), Error> {
        check_symbols(
            self.word.iter().chain(&self.access).chain([&self.symbol]),
            observer.symbols,
        )?;
        if self.word.len() >= self.checked_length || self.access.len() >= self.checked_length {
            return Err(Error::ReplayMismatch);
        }
        let gain = |scorer: &mut dyn FnMut(&[Symbol]) -> i64, word: &[Symbol]| {
            let longer = extended_word(word, self.symbol)?;
            Ok::<_, Error>(scorer(&longer).checked_sub(scorer(word)))
        };
        let replayed = observer.state_after(&self.word) == observer.state_after(&self.access)
            && gain(scorer, &self.word)? == Some(self.gains[0])
            && gain(scorer, &self.access)? == Some(self.gains[1])
            && self.gains[0] != self.gains[1];
        if replayed {
            Ok(())
        } else {
            Err(Error::ReplayMismatch)
        }
    }
}

/// The declared history reproduced the checked scorer on every word up to
/// `length()`. Only [`RawModel::check`] makes one, and it remembers the raw model it
/// checked, so a chart built from another raw model is never labelled by it.
///
/// ```compile_fail
/// // The fields are private: a check is made only by running it, and read
/// // only through its methods.
/// fn f(c: &zeno_adp::state_discovery::ObserverCheck) -> usize { c.length }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObserverCheck {
    length: usize,
    words_checked: usize,
    table: Arc<Table>,
}

impl ObserverCheck {
    pub const QUESTION: QuestionKind = QuestionKind::Existence;
    pub const FAMILY: Family = Family::AllCandidates;
    pub const CERTIFICATE: CertificateKind = CertificateKind::FullEnumeration;
    pub const SHAPE: Shape = Shape::SetLevel;

    /// The checked length: every word up to it was compared.
    pub fn length(&self) -> usize {
        self.length
    }

    /// Words compared, including the empty word: one scorer call each.
    pub fn words_checked(&self) -> u64 {
        self.words_checked as u64
    }

    /// Calls to the scorer during this check.
    pub fn scorer_calls(&self) -> usize {
        self.words_checked
    }

    /// Whether this check ran on `raw` (the same read, or a clone of it).
    pub fn is_for(&self, raw: &RawModel) -> bool {
        same_table(&self.table, &raw.table)
    }

    /// Exact for a word of this length, Unchecked beyond the checked length.
    pub fn label_for(&self, word_length: usize) -> Label {
        if word_length <= self.length {
            Label::Exact
        } else {
            Label::Unchecked
        }
    }
}

/// The class table of the coarsest congruence and its separating probes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quotient {
    symbols: usize,
    /// The class of each observer state; `None` for unreachable states.
    pub class_of: Vec<Option<usize>>,
    pub start: usize,
    pub base: i64,
    /// `[class][symbol]` score changes.
    pub gains: Vec<Vec<i64>>,
    /// `[class][symbol]` successor classes.
    pub next: Vec<Vec<usize>>,
    /// Words whose score changes differ between every two classes.
    pub probes: Vec<Vec<Symbol>>,
    /// The raw table this class table was built or checked against.
    table: Arc<Table>,
}

impl Quotient {
    /// The quotient maps each word to one class path and keeps its score, so it
    /// preserves every question about words and their scores.
    pub const QUESTIONS: [QuestionKind; 6] = [
        QuestionKind::OneOptimum,
        QuestionKind::AllTies,
        QuestionKind::OrderedMinimizers,
        QuestionKind::Count,
        QuestionKind::WitnessIdentity,
        QuestionKind::Existence,
    ];
    pub const FAMILY: Family = Family::AllCandidates;
    pub const CERTIFICATE: CertificateKind = CertificateKind::ExactReplay;
    pub const SHAPE: Shape = Shape::LiteralFilter;
    pub const LABEL: Label = Label::Exact;

    pub fn classes(&self) -> usize {
        self.gains.len()
    }

    pub fn symbols(&self) -> usize {
        self.symbols
    }

    /// The score change of a word read from a class. Requires a verified table,
    /// `class < self.classes()` and symbols below `self.symbols()`.
    pub fn gain_from(&self, class: usize, word: &[Symbol]) -> i128 {
        let mut state = class;
        let mut total = 0i128;
        for &symbol in word {
            total += i128::from(self.gains[state][symbol]);
            state = self.next[state][symbol];
        }
        total
    }

    fn signature(&self, class: usize) -> Vec<i128> {
        self.probes
            .iter()
            .map(|probe| self.gain_from(class, probe))
            .collect()
    }

    /// The score of a word. Requires a verified table and symbols below
    /// `self.symbols()`.
    pub fn score(&self, word: &[Symbol]) -> i128 {
        i128::from(self.base) + self.gain_from(self.start, word)
    }

    /// A probe that tells two classes apart, with both score changes: the reason a
    /// merge of the two classes is refused.
    pub fn separating_probe(&self, a: usize, b: usize) -> Option<(&[Symbol], [i128; 2])> {
        self.probes.iter().find_map(|probe| {
            let gains = [self.gain_from(a, probe), self.gain_from(b, probe)];
            (gains[0] != gains[1]).then_some((probe.as_slice(), gains))
        })
    }

    /// Replay the closure conditions for every reachable state and symbol, and
    /// check that the probes give every class a distinct signature.
    pub fn verify(&self, raw: &RawModel) -> Result<(), Error> {
        let observer = &raw.observer;
        let classes = self.gains.len();
        if self.class_of.len() != observer.states()
            || self.next.len() != classes
            || self.symbols != observer.symbols
            || self.gains.iter().any(|row| row.len() != observer.symbols)
            || self
                .next
                .iter()
                .any(|row| row.len() != observer.symbols || row.iter().any(|&c| c >= classes))
            || self.base != raw.base
            || self.class_of.get(observer.start).copied().flatten() != Some(self.start)
        {
            return Err(Error::CertificateShape);
        }
        let mut members = vec![0usize; classes];
        for state in 0..observer.states() {
            match (self.class_of[state], raw.is_reachable(state)) {
                (None, false) => continue,
                (Some(class), true) if class < classes => members[class] += 1,
                _ => return Err(Error::CertificateShape),
            }
            let class = self.class_of[state].expect("reachable");
            for symbol in 0..observer.symbols {
                let successor = self.class_of[observer.next[state][symbol]];
                if raw.gains[state][symbol] != self.gains[class][symbol]
                    || successor != Some(self.next[class][symbol])
                {
                    return Err(Error::Closure { state, symbol });
                }
            }
        }
        if members.contains(&0) {
            return Err(Error::CertificateShape);
        }
        check_symbols(self.probes.iter().flatten(), observer.symbols)?;
        let mut seen: BTreeMap<Vec<i128>, usize> = BTreeMap::new();
        for class in 0..classes {
            if let Some(&other) = seen.get(&self.signature(class)) {
                return Err(Error::Separation {
                    classes: (other, class),
                });
            }
            seen.insert(self.signature(class), class);
        }
        Ok(())
    }

    /// Verify against a raw model and return the class table as checked for it.
    /// An edited table is charted only after this.
    pub fn checked(mut self, raw: &RawModel) -> Result<Exact<Quotient>, Error> {
        self.verify(raw)?;
        self.table = Arc::clone(&raw.table);
        Ok(Exact(self))
    }

    fn chart_of_table<G: Geometry>(
        &self,
        geometry: &G,
        sense: Sense,
    ) -> Result<StateChart<G::Cell>, Error> {
        let sign = |value: i64| -> Result<i64, Error> {
            match sense {
                Sense::Minimize => Ok(value),
                Sense::Maximize => value.checked_neg().ok_or(Error::Overflow),
            }
        };
        // Depth-first post-order over reachable pairs gives children lower ranks.
        // A pair met again while it is still open lies on a cycle.
        enum Mark {
            Open,
            Done(usize),
        }
        enum Visit<C> {
            Enter((C, usize)),
            Finish((C, usize), Vec<(Symbol, C)>),
        }

        let start = (geometry.start(), self.start);
        let mut marks: HashMap<(G::Cell, usize), Mark> = HashMap::new();
        let mut cells: Vec<Vec<Rule<Move>>> = Vec::new();
        let mut labels = Vec::new();
        let mut stack = reserved(1)?;
        stack.push(Visit::Enter(start));
        while let Some(visit) = stack.pop() {
            let key = match visit {
                Visit::Enter(key) => key,
                Visit::Finish(key, moves) => {
                    let final_cell = geometry.is_final(&key.0);
                    let rule_count = moves
                        .len()
                        .checked_add(usize::from(final_cell))
                        .ok_or(Error::AllocationFailed)?;
                    let mut rules = reserved(rule_count)?;
                    if final_cell {
                        rules.push(Rule::new(
                            Move {
                                symbol: None,
                                costs: [sign(self.base)?],
                            },
                            [],
                        ));
                    }
                    for (symbol, target) in moves {
                        let child_key = (target, self.next[key.1][symbol]);
                        let Some(Mark::Done(child)) = marks.get(&child_key) else {
                            return Err(Error::CyclicGeometry);
                        };
                        let children = copied(&[*child])?;
                        rules.push(Rule::new(
                            Move {
                                symbol: Some(symbol),
                                costs: [sign(self.gains[key.1][symbol])?],
                            },
                            children,
                        ));
                    }
                    let rank = cells.len();
                    push(&mut cells, rules)?;
                    *marks.get_mut(&key).expect("the cell is open") = Mark::Done(rank);
                    push(&mut labels, key)?;
                    continue;
                }
            };
            match marks.get(&key) {
                Some(Mark::Done(_)) => continue,
                Some(Mark::Open) => return Err(Error::CyclicGeometry),
                None => {}
            }
            let moves = geometry.moves(&key.0);
            check_symbols(moves.iter().map(|(symbol, _)| symbol), self.symbols)?;
            marks.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
            marks.insert(key.clone(), Mark::Open);
            // Keep the checked move list for emission in its original order.
            let extra = moves.len().checked_add(1).ok_or(Error::AllocationFailed)?;
            stack
                .try_reserve(extra)
                .map_err(|_| Error::AllocationFailed)?;
            let pending = stack.len();
            for (symbol, target) in &moves {
                let child_key = (target.clone(), self.next[key.1][*symbol]);
                if !matches!(marks.get(&child_key), Some(Mark::Done(_))) {
                    stack.push(Visit::Enter(child_key));
                }
            }
            stack.insert(pending, Visit::Finish(key, moves));
        }
        let root = cells.len() - 1;
        let chart = Chart::new(cells, root).map_err(|_| Error::CyclicGeometry)?;
        Ok(StateChart {
            chart,
            labels,
            table: Arc::clone(&self.table),
            sense,
        })
    }
}

/// Whether higher or lower scores are better.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sense {
    Minimize,
    /// Negate rule scores. An `i64::MIN` base or gain used by a rule is refused.
    Maximize,
}

/// A chart rule: one operation, or the finish (`symbol: None`), with its cost.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Move {
    pub symbol: Option<Symbol>,
    pub costs: [i64; 1],
}

impl Operator for Move {
    fn arity(&self) -> usize {
        usize::from(self.symbol.is_some())
    }
}

impl CostVector for Move {
    fn costs(&self) -> &[i64] {
        &self.costs
    }
}

impl Exact<Quotient> {
    /// Explicit chart state over a geometry: one cell per reachable
    /// `(geometry cell, class)` pair, one rule per move in the geometry's order,
    /// and, first at final cells, a finishing rule of the empty-word score. With
    /// `Sense::Maximize` the chart's costs are negated scores, so its minimum is the
    /// highest score. Negating a base or gain of `i64::MIN` used by a rule
    /// returns [`Error::Overflow`].
    ///
    /// ```compile_fail
    /// // An unverified class table has no chart.
    /// fn chart(q: &zeno_adp::state_discovery::Quotient, x: &[u8]) {
    ///     let _ = q.chart(&zeno_adp::state_discovery::Alignment { x, y: x },
    ///         zeno_adp::state_discovery::Sense::Maximize);
    /// }
    /// ```
    pub fn chart<G: Geometry>(
        &self,
        geometry: &G,
        sense: Sense,
    ) -> Result<StateChart<G::Cell>, Error> {
        self.0.chart_of_table(geometry, sense)
    }
}

/// A chart over `(geometry cell, class)` pairs, its cell labels by rank, and its
/// sense. It remembers the raw table its class table was checked against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateChart<C> {
    chart: Chart<Move>,
    labels: Vec<(C, usize)>,
    sense: Sense,
    table: Arc<Table>,
}

/// The best score of an instance, the number of optimal move derivations (a
/// word count when each word determines its derivation, as in `Alignment`) and
/// the first best word, with the label against the scorer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Solved {
    pub score: i128,
    pub count: num_bigint::BigUint,
    pub word: Vec<Symbol>,
    /// The longest word of the geometry.
    pub longest: usize,
    /// Exact against the checked scorer when the check ran on this chart's raw
    /// table and every word of the geometry is within the checked length;
    /// Unchecked otherwise. Against the declared history it is Exact.
    pub scorer_label: Label,
}

impl<C> StateChart<C> {
    /// The chart, with one model.
    pub fn chart(&self) -> &Chart<Move> {
        &self.chart
    }

    /// The `(geometry cell, class)` label of each cell, by rank.
    pub fn labels(&self) -> &[(C, usize)] {
        &self.labels
    }

    pub fn sense(&self) -> Sense {
        self.sense
    }

    /// Solve with [`crate::common_optimum::common`] over the chart's one model.
    /// The count is of optimal move derivations, including distinct derivations
    /// that yield equal words. See [`Solved::scorer_label`] for scorer assurance.
    pub fn solve(&self, check: Option<&Exact<ObserverCheck>>) -> Result<Exact<Solved>, Error> {
        let answer = common_optimum::common(&self.chart, 1, &ModelSet::all(1)?)?.into_inner();
        let witness = answer
            .witness(&self.chart, &num_bigint::BigUint::ZERO)?
            .ok_or(Error::CertificateShape)?;
        answer.verify_witness(&self.chart, &witness)?;
        let word: Vec<Symbol> = witness
            .preorder
            .iter()
            .filter_map(|&(cell, rule)| self.chart.cells()[cell][rule].operator.symbol)
            .collect();
        let cost = answer.root_optima()[0]
            .clone()
            .ok_or(Error::CertificateShape)?;
        let value = match self.sense {
            Sense::Minimize => cost,
            Sense::Maximize => -cost,
        };
        let score = i128::try_from(value).map_err(|_| Error::Overflow)?;
        let longest = longest_word(&self.chart);
        let scorer_label = match check {
            Some(check) if same_table(&check.as_ref().table, &self.table) => {
                check.as_ref().label_for(longest)
            }
            _ => Label::Unchecked,
        };
        Ok(Exact(Solved {
            score,
            count: answer.count().clone(),
            word,
            longest,
            scorer_label,
        }))
    }
}

fn longest_word(chart: &Chart<Move>) -> usize {
    let mut longest: Vec<Option<usize>> = Vec::with_capacity(chart.cells().len());
    for rules in chart.cells() {
        let best = rules
            .iter()
            .filter_map(|rule| match rule.children.first() {
                Some(&child) => longest[child].map(|l| l + 1),
                None => Some(0),
            })
            .max();
        longest.push(best);
    }
    longest[chart.root()].unwrap_or(0)
}

/// Positions and moves of a dynamic program over words. Supply a finite,
/// stable geometry with moves in the observer's alphabet. Counts are move
/// derivations. They also count words when each word determines its move sequence,
/// as in [`Alignment`].
pub trait Geometry {
    type Cell: Clone + Eq + std::hash::Hash;
    fn start(&self) -> Self::Cell;
    /// The operations allowed at a cell and the cell each one reaches.
    fn moves(&self, cell: &Self::Cell) -> Vec<(Symbol, Self::Cell)>;
    /// Whether a word may end at this cell.
    fn is_final(&self, cell: &Self::Cell) -> bool;
}

/// Pairwise alignment of two sequences over cells `(i, j)`.
#[derive(Clone, Debug)]
pub struct Alignment<'a, T> {
    pub x: &'a [T],
    pub y: &'a [T],
}

impl Alignment<'_, ()> {
    /// Symbol of a match.
    pub const MATCH: Symbol = 0;
    /// Symbol of a mismatch.
    pub const MISMATCH: Symbol = 1;
    /// Symbol of a deletion from `x`.
    pub const DELETE: Symbol = 2;
    /// Symbol of an insertion from `y`.
    pub const INSERT: Symbol = 3;
    /// The alphabet size.
    pub const SYMBOLS: usize = 4;
}

impl<T: PartialEq> Geometry for Alignment<'_, T> {
    type Cell = (usize, usize);

    fn start(&self) -> (usize, usize) {
        (0, 0)
    }

    fn moves(&self, &(i, j): &(usize, usize)) -> Vec<(Symbol, (usize, usize))> {
        let mut moves = Vec::with_capacity(3);
        if i < self.x.len() && j < self.y.len() {
            let symbol = if self.x[i] == self.y[j] {
                Alignment::MATCH
            } else {
                Alignment::MISMATCH
            };
            moves.push((symbol, (i + 1, j + 1)));
        }
        if i < self.x.len() {
            moves.push((Alignment::DELETE, (i + 1, j)));
        }
        if j < self.y.len() {
            moves.push((Alignment::INSERT, (i, j + 1)));
        }
        moves
    }

    fn is_final(&self, &(i, j): &(usize, usize)) -> bool {
        i == self.x.len() && j == self.y.len()
    }
}

/// A merge proposal's verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The two states, and every pair their merge forces, agree on every future
    /// score change. `pairs` is the number of state pairs the closure merged.
    Admitted {
        pairs: usize,
    },
    AlreadyMerged,
    Refused(Refusal),
}

/// A refused merge: a probe word whose score changes from the two states differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    pub states: [usize; 2],
    pub probe: Vec<Symbol>,
    pub gains: [i128; 2],
}

impl Refusal {
    pub const QUESTION: QuestionKind = QuestionKind::Existence;
    pub const FAMILY: Family = Family::AllCandidates;
    /// One replayed probe answers the existence question: a weak certificate.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Weak;
    pub const SHAPE: Shape = Shape::SetLevel;

    /// Replay the probe on the raw table. A state or symbol outside the raw model
    /// is refused before anything is evaluated.
    pub fn replay(&self, raw: &RawModel) -> Result<(), Error> {
        check_symbols(&self.probe, raw.observer.symbols)?;
        for &state in &self.states {
            if !raw.is_reachable(state) {
                return Err(Error::StateOutOfRange { state });
            }
        }
        let gain = |state: usize| {
            let mut at = state;
            let mut total = 0i128;
            for &symbol in &self.probe {
                total += i128::from(raw.gains[at][symbol]);
                at = raw.observer.next[at][symbol];
            }
            total
        };
        if gain(self.states[0]) == self.gains[0]
            && gain(self.states[1]) == self.gains[1]
            && self.gains[0] != self.gains[1]
        {
            Ok(())
        } else {
            Err(Error::ReplayMismatch)
        }
    }
}

/// Counterexample-guided merging. Each proposal merges two states together with
/// every pair of successors the merge forces (the union-find closure of Hopcroft
/// and Karp). A proposal is refused, and nothing is merged, when the closure
/// meets two states whose score changes differ.
pub struct Merging<'a> {
    raw: &'a RawModel,
    parent: Vec<usize>,
    refusals: Vec<Refusal>,
}

fn find(parent: &mut [usize], mut state: usize) -> usize {
    while parent[state] != state {
        parent[state] = parent[parent[state]];
        state = parent[state];
    }
    state
}

impl Merging<'_> {
    pub fn propose(&mut self, s: usize, t: usize) -> Result<Verdict, Error> {
        if !self.raw.is_reachable(s) || !self.raw.is_reachable(t) {
            return Err(Error::CertificateShape);
        }
        if find(&mut self.parent, s) == find(&mut self.parent, t) {
            return Ok(Verdict::AlreadyMerged);
        }
        let symbols = self.raw.observer.symbols;
        let mut parent = self.parent.clone();
        // Breadth-first over forced pairs; each entry keeps the entry and symbol it
        // came from, so a refusal can rebuild its probe word.
        type Forced = (usize, usize, Option<(usize, Symbol)>);
        let mut paths: Vec<Forced> = vec![(s, t, None)];
        let mut cursor = 0;
        let mut pairs = 0;
        while cursor < paths.len() {
            let (x, y, _) = paths[cursor];
            let (rx, ry) = (find(&mut parent, x), find(&mut parent, y));
            if rx != ry {
                if let Some(symbol) =
                    (0..symbols).find(|&a| self.raw.gains[x][a] != self.raw.gains[y][a])
                {
                    let mut probe = vec![symbol];
                    let mut at = cursor;
                    while let Some((previous, symbol)) = paths[at].2 {
                        probe.push(symbol);
                        at = previous;
                    }
                    probe.reverse();
                    let refusal = Refusal {
                        states: [s, t],
                        gains: [
                            gain_along(self.raw, s, &probe),
                            gain_along(self.raw, t, &probe),
                        ],
                        probe,
                    };
                    self.refusals.push(refusal.clone());
                    return Ok(Verdict::Refused(refusal));
                }
                parent[ry] = rx;
                pairs += 1;
                for symbol in 0..symbols {
                    let (nx, ny) = (
                        self.raw.observer.next[x][symbol],
                        self.raw.observer.next[y][symbol],
                    );
                    paths.push((nx, ny, Some((cursor, symbol))));
                }
            }
            cursor += 1;
        }
        self.parent = parent;
        Ok(Verdict::Admitted { pairs })
    }

    pub fn refusals(&self) -> &[Refusal] {
        &self.refusals
    }

    /// Propose every remaining pair of classes, then return the verified quotient,
    /// which is the coarsest congruence whatever the earlier proposals were.
    pub fn finish(mut self) -> Result<Exact<Quotient>, Error> {
        let reachable: Vec<usize> = (0..self.raw.observer.states())
            .filter(|&state| self.raw.is_reachable(state))
            .collect();
        loop {
            let mut roots: Vec<usize> = reachable
                .iter()
                .map(|&s| find(&mut self.parent, s))
                .collect();
            roots.sort_unstable();
            roots.dedup();
            let mut changed = false;
            'pairs: for (i, &a) in roots.iter().enumerate() {
                for &b in &roots[i + 1..] {
                    let known = self.refusals.iter().any(|refusal| {
                        gain_along(self.raw, a, &refusal.probe)
                            != gain_along(self.raw, b, &refusal.probe)
                    });
                    if known {
                        continue;
                    }
                    if let Verdict::Admitted { .. } = self.propose(a, b)? {
                        changed = true;
                        break 'pairs;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut blocks = filled(self.raw.observer.states(), usize::MAX)?;
        for &state in &reachable {
            blocks[state] = find(&mut self.parent, state);
        }
        let refusals = self.refusals.clone();
        let raw = self.raw;
        let quotient = raw.build(&blocks, |a, b| {
            refusals
                .iter()
                .find(|r| gain_along(raw, a, &r.probe) != gain_along(raw, b, &r.probe))
                .map(|r| r.probe.clone())
                .unwrap_or_default()
        })?;
        quotient.verify(raw)?;
        Ok(Exact(quotient))
    }
}

fn gain_along(raw: &RawModel, mut state: usize, word: &[Symbol]) -> i128 {
    let mut total = 0i128;
    for &symbol in word {
        total += i128::from(raw.gains[state][symbol]);
        state = raw.observer.next[state][symbol];
    }
    total
}

/// A feature of histories: an automaton and the value it reports in each state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Feature {
    pub automaton: Observer,
    pub value: Vec<usize>,
}

impl Feature {
    pub fn new(automaton: Observer, value: Vec<usize>) -> Result<Self, Error> {
        Self::check_values(&automaton, &value)?;
        Ok(Self { automaton, value })
    }

    fn check_values(automaton: &Observer, value: &[usize]) -> Result<(), Error> {
        if value.len() != automaton.states() {
            return Err(Error::InvalidObserver(
                "a feature needs one value per state",
            ));
        }
        Ok(())
    }

    /// The product observer of a library and, for each product state, every
    /// feature's value.
    pub fn library(features: &[Feature]) -> Result<(Observer, Vec<Vec<usize>>), Error> {
        for feature in features {
            Self::check_values(&feature.automaton, &feature.value)?;
        }
        let (product, states) = Observer::product_of(features.iter().map(|f| &f.automaton))?;
        let mut values = reserved(states.len())?;
        for parts in states {
            let mut row = reserved(features.len())?;
            row.extend(parts.iter().zip(features).map(|(&s, f)| f.value[s]));
            values.push(row);
        }
        Ok((product, values))
    }
}

/// The feature sets of smallest size whose values can serve as chart state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FeatureSets {
    pub size: usize,
    /// Every sufficient set of that size, as sorted feature indices.
    pub sets: Vec<Vec<usize>>,
    /// For every smaller set, two reachable product states with equal values of
    /// its features and different score changes or different successor values.
    pub collisions: Vec<(Vec<usize>, [usize; 2])>,
}

/// The number of features, after checking one value row per observer state.
fn feature_count(raw: &RawModel, values: &[Vec<usize>]) -> Result<usize, Error> {
    let features = values.first().map_or(0, Vec::len);
    if values.len() != raw.observer.states() || values.iter().any(|v| v.len() != features) {
        return Err(Error::CertificateShape);
    }
    Ok(features)
}

fn same_feature_row(
    raw: &RawModel,
    values: &[Vec<usize>],
    set: &[usize],
    a: usize,
    b: usize,
) -> bool {
    raw.gains[a] == raw.gains[b]
        && raw.observer.next[a]
            .iter()
            .zip(&raw.observer.next[b])
            .all(|(&x, &y)| set.iter().all(|&f| values[x][f] == values[y][f]))
}

/// Two reachable states with equal values of `set` and different rows, if any.
fn feature_collision(
    raw: &RawModel,
    values: &[Vec<usize>],
    set: &[usize],
) -> Result<Option<[usize; 2]>, Error> {
    let mut seen = HashMap::new();
    for state in (0..raw.observer.states()).filter(|&s| raw.is_reachable(s)) {
        let mut key = reserved(set.len())?;
        key.extend(set.iter().map(|&f| values[state][f]));
        if let Some(&other) = seen.get(&key) {
            if !same_feature_row(raw, values, set, other, state) {
                return Ok(Some([other, state]));
            }
        } else {
            seen.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
            seen.insert(key, state);
        }
    }
    Ok(None)
}

/// Does the count of valid, distinct submitted sets cover all smaller sets?
fn covers_smaller_sets(n: usize, size: usize, mut count: usize) -> bool {
    let mut coefficient = 1usize; // C(n, 0)
    for k in 0..size {
        let Some(rest) = count.checked_sub(coefficient) else {
            return false;
        };
        count = rest;
        if k + 1 < size {
            // C(n, k+1) = C(n, k) * (n-k) / (k+1). Both factors fit in
            // usize, so their product fits in u128 on 32- and 64-bit targets.
            let next = (coefficient as u128) * ((n - k) as u128) / ((k + 1) as u128);
            let Ok(next) = usize::try_from(next) else {
                return false;
            };
            coefficient = next;
        }
    }
    count == 0
}

/// Caller limits for [`minimum_feature_sets`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeatureSetBudget {
    /// Total subset tests. One test may scan the raw model's states and symbols.
    pub max_candidates: usize,
    /// Peak logical slots for retained findings. Each finding uses one slot plus
    /// one per feature index, and a collision uses two more for its state indices.
    pub max_certificate_slots: usize,
}

struct FeatureWork {
    limit: usize,
    remaining: usize,
}

impl FeatureWork {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            remaining: limit,
        }
    }

    fn take(&mut self) -> Result<(), Error> {
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(Error::FeatureWorkLimit { limit: self.limit })?;
        Ok(())
    }
}

impl FeatureSets {
    pub const QUESTIONS: [QuestionKind; 2] = [QuestionKind::OneOptimum, QuestionKind::AllTies];
    pub const FAMILY: Family = Family::AllCandidates;
    /// Every sufficient set of smallest size is kept.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Strict;
    /// The verifier checks membership of the listed sets and coverage by the
    /// collisions independently of either list's order.
    pub const SHAPE: Shape = Shape::SetLevel;

    /// Replay the certificate. The distinct valid collisions must cover every
    /// smaller set. The verifier then streams the sets of the stated size.
    /// `max_candidates` bounds the sum of collision replays and streamed subset
    /// tests. Exceeding it returns [`Error::FeatureWorkLimit`].
    pub fn verify(
        &self,
        raw: &RawModel,
        values: &[Vec<usize>],
        max_candidates: usize,
    ) -> Result<(), Error> {
        if self.sets.is_empty() {
            return Err(Error::FeatureSets("no sufficient set is listed"));
        }
        let features = feature_count(raw, values)?;
        if self.size > features {
            return Err(Error::FeatureSets("the size exceeds the library"));
        }
        let well_formed = |set: &[usize]| {
            set.windows(2).all(|pair| pair[0] < pair[1]) && set.iter().all(|&f| f < features)
        };
        let mut work = FeatureWork::new(max_candidates);
        let mut covered: HashSet<&[usize]> = HashSet::new();
        for (set, [a, b]) in &self.collisions {
            work.take()?;
            if !well_formed(set) || set.len() >= self.size {
                return Err(Error::FeatureSets(
                    "a collision names a set that is not smaller",
                ));
            }
            if a == b || !raw.is_reachable(*a) || !raw.is_reachable(*b) {
                return Err(Error::FeatureSets("a collision names an unreachable state"));
            }
            let same_values = set.iter().all(|&f| values[*a][f] == values[*b][f]);
            if !same_values || same_feature_row(raw, values, set, *a, *b) {
                return Err(Error::FeatureSets("a collision does not replay"));
            }
            covered
                .try_reserve(1)
                .map_err(|_| Error::AllocationFailed)?;
            if !covered.insert(set) {
                return Err(Error::FeatureSets("a collision is listed twice"));
            }
        }
        if !covers_smaller_sets(features, self.size, covered.len()) {
            return Err(Error::FeatureSets("some smaller set has no collision"));
        }
        drop(covered);
        // Each distinct listed set will need to be checked among the candidates.
        if self.sets.len() > work.remaining {
            return Err(Error::FeatureWorkLimit {
                limit: max_candidates,
            });
        }
        let mut listed: HashSet<&[usize]> = HashSet::new();
        listed
            .try_reserve(self.sets.len())
            .map_err(|_| Error::AllocationFailed)?;
        for set in &self.sets {
            if !well_formed(set) || set.len() != self.size || !listed.insert(set) {
                return Err(Error::FeatureSets(
                    "a listed set is malformed or of another size",
                ));
            }
        }
        visit_combinations(features, self.size, &mut work, |set| {
            let sufficient = feature_collision(raw, values, set)?.is_none();
            if sufficient != listed.contains(set) {
                return Err(Error::FeatureSets(
                    "the listed sets differ from the sufficient sets",
                ));
            }
            Ok(())
        })
    }
}

/// A set of features is sufficient when reachable product states with equal values
/// of those features have equal score changes and, for every symbol, successors
/// with equal values. The values then form a class table: equal values give equal
/// score changes for every future word. Sufficiency is not monotone in the set (an
/// added feature's next value may depend on a feature left out), so every smaller
/// set is checked and given a collision. Limits apply before the next test or
/// retained finding. The storage limit includes tentative collisions at the
/// current size until a sufficient set is found.
pub fn minimum_feature_sets(
    raw: &RawModel,
    values: &[Vec<usize>],
    budget: FeatureSetBudget,
) -> Result<FeatureSets, Error> {
    let features = feature_count(raw, values)?;
    let mut work = FeatureWork::new(budget.max_candidates);
    let mut collisions = Vec::new();
    let mut slots = 0usize;
    for size in 0..=features {
        let earlier_collisions = collisions.len();
        let earlier_slots = slots;
        let mut sets = Vec::new();
        visit_combinations(features, size, &mut work, |set| {
            let charge = |slots: &mut usize, state_indices| -> Result<(), Error> {
                *slots = slots
                    .checked_add(set.len())
                    .and_then(|n| n.checked_add(1 + state_indices))
                    .filter(|&n| n <= budget.max_certificate_slots)
                    .ok_or(Error::FeatureStorageLimit {
                        limit: budget.max_certificate_slots,
                    })?;
                Ok(())
            };
            match feature_collision(raw, values, set)? {
                None => {
                    if sets.is_empty() {
                        collisions.truncate(earlier_collisions);
                        slots = earlier_slots;
                    }
                    charge(&mut slots, 0)?;
                    push(&mut sets, copied(set)?)?;
                }
                Some(states) if size == features => {
                    return Err(Error::InsufficientLibrary { states });
                }
                Some(pair) if sets.is_empty() => {
                    charge(&mut slots, pair.len())?;
                    push(&mut collisions, (copied(set)?, pair))?;
                }
                Some(_) => {}
            }
            Ok(())
        })?;
        if !sets.is_empty() {
            return Ok(FeatureSets {
                size,
                sets,
                collisions,
            });
        }
    }
    Err(Error::CertificateShape)
}

/// Visit the k-subsets in lexicographic order, retaining one index vector.
fn visit_combinations(
    n: usize,
    k: usize,
    work: &mut FeatureWork,
    mut visit: impl FnMut(&[usize]) -> Result<(), Error>,
) -> Result<(), Error> {
    work.take()?;
    let mut set = reserved(k)?;
    set.extend(0..k);
    loop {
        visit(&set)?;
        let Some(i) = (0..k).rev().find(|&i| set[i] < n - k + i) else {
            return Ok(());
        };
        work.take()?;
        let first = set[i] + 1;
        for (offset, feature) in set[i..].iter_mut().enumerate() {
            *feature = first + offset;
        }
    }
}
