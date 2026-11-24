//! Derivations that are optimal in several additive cost models at once.
//!
//! A [`Chart`] whose operators carry one integer cost per model defines one
//! additive score per model over the same derivations. For any nonempty set of
//! models, [`common`] answers whether some derivation of the root is optimal in
//! every selected model, how many derivations are, and which one has a given rank
//! in derivation order. Counts are derivation occurrences, not distinct outputs.
//!
//! The method keeps, at each cell, the rules that attain the cell's optimum in
//! every selected model. With finite additive costs a derivation is optimal in a
//! model exactly when every one of its nodes uses such a rule, so a count over
//! the restricted chart counts the common optima.

use std::collections::BTreeMap;
use std::fmt;

use num_bigint::{BigInt, BigUint};

use crate::assurance::{CertificateKind, Family, Label, QuestionKind, Shape};
use crate::{Cell, Chart, Exact, Operator, Rule, Tree};

/// An operator with one finite integer cost per model. The cost slice must
/// remain stable during a query or replay.
pub trait CostVector {
    fn costs(&self) -> &[i64];
}

/// A plain operator: a cost per model and an arity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Costed {
    pub costs: Vec<i64>,
    pub arity: usize,
}

impl Operator for Costed {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl CostVector for Costed {
    fn costs(&self) -> &[i64] {
        &self.costs
    }
}

impl Costed {
    /// A rule whose operator has these costs and whose children are these cells.
    pub fn rule(costs: impl Into<Vec<i64>>, children: impl Into<Vec<Cell>>) -> Rule<Self> {
        let children = children.into();
        Rule::new(
            Self {
                costs: costs.into(),
                arity: children.len(),
            },
            children,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// A chart must declare at least one model.
    NoModels,
    /// A selection must name at least one model.
    EmptySelection,
    ModelOutOfRange {
        model: usize,
        models: usize,
    },
    CostLength {
        cell: Cell,
        rule: usize,
        expected: usize,
        actual: usize,
    },
    /// A certificate's tables do not match the chart's shape.
    CertificateShape,
    /// A recorded optimum does not satisfy its cell equation.
    Optimum {
        cell: Cell,
        model: usize,
    },
    /// A recorded count does not satisfy its cell equation.
    Count {
        cell: Cell,
    },
    /// A witness is not a derivation of the root, is not optimal, or has another rank.
    Witness(&'static str),
    /// The requested selection is unlisted. The generic collision shows that
    /// the retained keys cannot determine the new count on every chart.
    NotRetained(Box<Collision>),
    /// Building the collision would exceed the caller's rule or cost-entry limit.
    CollisionBudgetExceeded,
    /// Storage could not be reserved.
    AllocationFailed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoModels => write!(f, "a chart needs at least one cost model"),
            Self::EmptySelection => write!(f, "select at least one model"),
            Self::ModelOutOfRange { model, models } => {
                write!(f, "model {model} is outside the {models} declared models")
            }
            Self::CostLength {
                cell,
                rule,
                expected,
                actual,
            } => write!(
                f,
                "cell {cell}, rule {rule} has {actual} costs; the chart declares {expected} models"
            ),
            Self::CertificateShape => write!(f, "certificate tables do not match the chart"),
            Self::Optimum { cell, model } => {
                write!(f, "recorded optimum of model {model} fails at cell {cell}")
            }
            Self::Count { cell } => write!(f, "recorded common-optimum count fails at cell {cell}"),
            Self::Witness(reason) => write!(f, "witness rejected: {reason}"),
            Self::NotRetained(collision) => write!(
                f,
                "the retained summary cannot answer models {:?}; two charts share it and answer {} and {}",
                collision.selection.models(),
                collision.answers[0],
                collision.answers[1]
            ),
            Self::CollisionBudgetExceeded => write!(f, "collision construction exceeds its budget"),
            Self::AllocationFailed => write!(f, "could not reserve storage"),
        }
    }
}

impl std::error::Error for Error {}

/// A nonempty, sorted set of model indices.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModelSet(Vec<usize>);

impl ModelSet {
    pub fn new(models: impl IntoIterator<Item = usize>, declared: usize) -> Result<Self, Error> {
        let mut set = Vec::new();
        for model in models {
            set.try_reserve(1).map_err(|_| Error::AllocationFailed)?;
            set.push(model);
        }
        set.sort_unstable();
        set.dedup();
        if set.is_empty() {
            return Err(Error::EmptySelection);
        }
        let set = Self(set);
        set.check_width(declared)?;
        Ok(set)
    }

    /// Every declared model.
    pub fn all(declared: usize) -> Result<Self, Error> {
        if declared == 0 {
            return Err(Error::EmptySelection);
        }
        let mut set = Vec::new();
        set.try_reserve_exact(declared)
            .map_err(|_| Error::AllocationFailed)?;
        set.extend(0..declared);
        Ok(Self(set))
    }

    pub fn models(&self) -> &[usize] {
        &self.0
    }

    fn check_width(&self, models: usize) -> Result<(), Error> {
        if let Some(&model) = self.0.iter().find(|&&model| model >= models) {
            return Err(Error::ModelOutOfRange { model, models });
        }
        Ok(())
    }
}

/// Check every rule's cost vector against the declared model count.
pub fn check_costs<O: CostVector>(chart: &Chart<O>, models: usize) -> Result<(), Error> {
    if models == 0 {
        return Err(Error::NoModels);
    }
    for (cell, rules) in chart.cells().iter().enumerate() {
        for (index, rule) in rules.iter().enumerate() {
            let actual = rule.operator.costs().len();
            if actual != models {
                return Err(Error::CostLength {
                    cell,
                    rule: index,
                    expected: models,
                    actual,
                });
            }
        }
    }
    Ok(())
}

fn reserved<T>(capacity: usize) -> Result<Vec<T>, Error> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| Error::AllocationFailed)?;
    Ok(values)
}

/// A rule's cost plus its children's optima in one model, or `None` when a
/// child has no derivation.
fn rule_value<O: CostVector>(
    rule: &Rule<O>,
    model: usize,
    value: impl Fn(Cell) -> Option<BigInt>,
) -> Option<BigInt> {
    let mut sum = BigInt::from(rule.operator.costs()[model]);
    for &child in &rule.children {
        sum += value(child)?;
    }
    Some(sum)
}

fn minimum(values: impl Iterator<Item = Option<BigInt>>) -> Option<BigInt> {
    values.flatten().min()
}

/// The optimum of every model at every cell (`None` for a cell without derivations).
/// Retaining this table is the "cost charts" schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Optima {
    models: usize,
    values: Vec<Vec<Option<BigInt>>>,
}

impl Optima {
    /// Tabulate every model in ascending rank.
    pub fn of<O: CostVector>(chart: &Chart<O>, models: usize) -> Result<Self, Error> {
        check_costs(chart, models)?;
        let mut values: Vec<Vec<Option<BigInt>>> = reserved(chart.cells().len())?;
        for rules in chart.cells() {
            let mut row = reserved(models)?;
            row.extend((0..models).map(|model| {
                minimum(
                    rules
                        .iter()
                        .map(|rule| rule_value(rule, model, |child| values[child][model].clone())),
                )
            }));
            values.push(row);
        }
        Ok(Self { models, values })
    }

    pub fn models(&self) -> usize {
        self.models
    }

    pub fn value(&self, cell: Cell, model: usize) -> Option<&BigInt> {
        self.values.get(cell)?.get(model)?.as_ref()
    }

    /// Check each recorded value against its cell equation in every model.
    pub fn verify<O: CostVector>(&self, chart: &Chart<O>) -> Result<(), Error> {
        check_costs(chart, self.models)?;
        if self.values.len() != chart.cells().len()
            || self.values.iter().any(|row| row.len() != self.models)
        {
            return Err(Error::CertificateShape);
        }
        for (cell, rules) in chart.cells().iter().enumerate() {
            for model in 0..self.models {
                let expected = minimum(rules.iter().map(|rule| {
                    rule_value(rule, model, |child| self.values[child][model].clone())
                }));
                if expected != self.values[cell][model] {
                    return Err(Error::Optimum { cell, model });
                }
            }
        }
        Ok(())
    }

    /// Payload bits of the table: one inhabitation bit per entry, plus one sign
    /// bit and at least one magnitude bit for each inhabited value. For example,
    /// an entry containing `-1` uses three bits.
    /// For nonnegative values, use [`Optima::unsigned_bits`].
    pub fn storage_bits(&self) -> u64 {
        self.values
            .iter()
            .flatten()
            .map(|value| 1 + value.as_ref().map_or(0, signed_bits))
            .sum()
    }

    /// Payload bits when every value is a nonnegative integer and every cell is
    /// inhabited: the bit length of each value, at least one. Returns `None` otherwise.
    pub fn unsigned_bits(&self) -> Option<u64> {
        self.values.iter().flatten().try_fold(0u64, |sum, value| {
            let value = value.as_ref()?;
            (value.sign() != num_bigint::Sign::Minus).then(|| sum + value.bits().max(1))
        })
    }
}

fn signed_bits(value: &BigInt) -> u64 {
    // Bits of the magnitude plus a sign bit.
    value.magnitude().bits().max(1) + 1
}

/// Bit masks of the rules that attain each model's optimum at each cell.
/// Retaining these masks and the chart's child lists is the "winner masks" schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WinnerMasks {
    models: usize,
    /// `[cell][model]`, one bit per rule in cell order.
    masks: Vec<Vec<Mask>>,
    rules: Vec<usize>,
}

/// A set of rule ordinals within one cell.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Mask(Vec<u64>);

const WORD: usize = u64::BITS as usize;

impl Mask {
    fn empty(rules: usize) -> Self {
        Self(vec![0; rules.div_ceil(WORD)])
    }

    fn full(rules: usize) -> Self {
        let mut mask = Self::empty(rules);
        for rule in 0..rules {
            mask.insert(rule);
        }
        mask
    }

    fn insert(&mut self, rule: usize) {
        self.0[rule / WORD] |= 1 << (rule % WORD);
    }

    pub fn contains(&self, rule: usize) -> bool {
        self.0
            .get(rule / WORD)
            .is_some_and(|word| word >> (rule % WORD) & 1 == 1)
    }

    fn intersect(&mut self, other: &Self) {
        for (word, other) in self.0.iter_mut().zip(&other.0) {
            *word &= other;
        }
    }

    pub fn len(&self) -> usize {
        self.0.iter().map(|word| word.count_ones() as usize).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.0.iter().all(|&word| word == 0)
    }

    /// Rule ordinals in ascending order.
    pub fn rules(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(index, &word)| {
            (0..WORD)
                .filter(move |bit| word >> bit & 1 == 1)
                .map(move |bit| index * WORD + bit)
        })
    }

    fn words(&self) -> usize {
        self.0.len()
    }
}

impl WinnerMasks {
    /// Winners of every model, derived from checked optima.
    pub fn of<O: CostVector>(chart: &Chart<O>, optima: &Optima) -> Result<Self, Error> {
        optima.verify(chart)?;
        let models = optima.models;
        let masks = chart
            .cells()
            .iter()
            .enumerate()
            .map(|(cell, rules)| {
                (0..models)
                    .map(|model| winners(chart, rules, cell, model, &optima.values))
                    .collect()
            })
            .collect();
        let rules = chart.cells().iter().map(Vec::len).collect();
        Ok(Self {
            models,
            masks,
            rules,
        })
    }

    pub fn models(&self) -> usize {
        self.models
    }

    pub fn mask(&self, cell: Cell, model: usize) -> Option<&Mask> {
        self.masks.get(cell)?.get(model)
    }

    /// One bit per rule and model.
    pub fn storage_bits(&self) -> u64 {
        self.rules
            .iter()
            .map(|&rules| (rules * self.models) as u64)
            .sum()
    }

    /// Distinct masks per cell stored once, plus a per-model index into them.
    pub fn coalesced_bits(&self) -> u64 {
        self.masks
            .iter()
            .zip(&self.rules)
            .map(|(masks, &rules)| {
                let distinct = masks
                    .iter()
                    .collect::<std::collections::BTreeSet<_>>()
                    .len();
                let index_bits = u64::from(usize::BITS - (distinct - 1).leading_zeros());
                (distinct * rules) as u64 + self.models as u64 * index_bits
            })
            .sum()
    }

    /// Bits of an enumerative code for each tie set when its size is known:
    /// the sum of ceil(log2 C(R, c)) over cells and models.
    pub fn conditional_bits(&self) -> u64 {
        self.masks
            .iter()
            .zip(&self.rules)
            .flat_map(|(masks, &rules)| {
                masks
                    .iter()
                    .map(move |mask| ceil_log2(&binomial(rules, mask.len())))
            })
            .sum()
    }
}

fn winners<O: CostVector>(
    _chart: &Chart<O>,
    rules: &[Rule<O>],
    _cell: Cell,
    model: usize,
    values: &[Vec<Option<BigInt>>],
) -> Mask {
    let mut mask = Mask::empty(rules.len());
    let cell_value = rules
        .iter()
        .map(|rule| rule_value(rule, model, |child| values[child][model].clone()))
        .collect::<Vec<_>>();
    let best = cell_value.iter().flatten().min().cloned();
    for (index, value) in cell_value.iter().enumerate() {
        if value.is_some() && *value == best {
            mask.insert(index);
        }
    }
    mask
}

/// C(n, k) as a big integer.
pub fn binomial(n: usize, k: usize) -> BigUint {
    if k > n {
        return BigUint::ZERO;
    }
    let k = k.min(n - k);
    let mut value = BigUint::from(1u32);
    for i in 0..k {
        value = value * BigUint::from(n - i) / BigUint::from(i + 1);
    }
    value
}

/// ceil(log2(n)) for n >= 1, and 0 for n <= 1.
pub fn ceil_log2(n: &BigUint) -> u64 {
    if *n <= BigUint::from(1u32) {
        return 0;
    }
    (n - 1u32).bits()
}

/// Evaluation and counting work, in machine-independent units. Validation
/// scans and elapsed time are outside these counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    /// Rules evaluated in one model (a cost plus child optima).
    pub cost_evaluations: u64,
    /// Rules scanned at a visited cell (each scan evaluates up to one cost per selected model).
    pub rule_scans: u64,
    /// Common-winning rules visited by a mask traversal.
    pub rule_visits: u64,
    /// 64-bit mask words combined.
    pub mask_words: u64,
    /// Cells whose answer was computed.
    pub cells: u64,
}

impl std::ops::AddAssign for Work {
    fn add_assign(&mut self, other: Self) {
        self.cost_evaluations += other.cost_evaluations;
        self.rule_scans += other.rule_scans;
        self.rule_visits += other.rule_visits;
        self.mask_words += other.mask_words;
        self.cells += other.cells;
    }
}

/// The certificate of a common-optimum query. Tables are indexed by cell, and the
/// optima by position in `selection`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Common {
    pub selection: ModelSet,
    pub optima: Vec<Vec<Option<BigInt>>>,
    /// Derivations of each cell that are optimal in every selected model.
    pub counts: Vec<BigUint>,
    pub root: Cell,
}

impl Common {
    /// The questions this certificate answers.
    pub const QUESTIONS: [QuestionKind; 4] = [
        QuestionKind::Existence,
        QuestionKind::Count,
        QuestionKind::OrderedMinimizers,
        QuestionKind::WitnessIdentity,
    ];
    pub const FAMILY: Family = Family::OptimalInEveryModel;
    /// The filter preserves the order and multiplicity of every derivation
    /// optimal in all selected models.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Strict;
    pub const SHAPE: Shape = Shape::LiteralFilter;
    pub const LABEL: Label = Label::Exact;

    /// Derivations of the root that are optimal in every selected model.
    /// Use on a solver result or after verifying the raw certificate.
    pub fn count(&self) -> &BigUint {
        &self.counts[self.root]
    }

    /// Whether the checked count is positive. See [`Common::count`].
    pub fn exists(&self) -> bool {
        *self.count() != BigUint::ZERO
    }

    /// The root optimum of each selected model, in selection order. Use on a
    /// solver result or after verifying the raw certificate.
    pub fn root_optima(&self) -> &[Option<BigInt>] {
        &self.optima[self.root]
    }

    fn common_mask<O: CostVector>(&self, rules: &[Rule<O>], cell: Cell) -> Mask {
        let mut mask = Mask::full(rules.len());
        for (position, &model) in self.selection.models().iter().enumerate() {
            let values = |child: Cell| self.optima[child][position].clone();
            let best = self.optima[cell][position].clone();
            let mut winners = Mask::empty(rules.len());
            if best.is_some() {
                for (index, rule) in rules.iter().enumerate() {
                    if rule_value(rule, model, values) == best {
                        winners.insert(index);
                    }
                }
            }
            mask.intersect(&winners);
        }
        mask
    }

    /// Check the recorded optima and counts against the chart, cell by cell.
    pub fn verify<O: CostVector>(&self, chart: &Chart<O>, models: usize) -> Result<(), Error> {
        check_costs(chart, models)?;
        let cells = chart.cells().len();
        let width = self.selection.models().len();
        if self.root != chart.root()
            || self.optima.len() != cells
            || self.counts.len() != cells
            || self.optima.iter().any(|row| row.len() != width)
            || self.selection.models().iter().any(|&model| model >= models)
        {
            return Err(Error::CertificateShape);
        }
        for (cell, rules) in chart.cells().iter().enumerate() {
            for (position, &model) in self.selection.models().iter().enumerate() {
                let expected = minimum(rules.iter().map(|rule| {
                    rule_value(rule, model, |child| self.optima[child][position].clone())
                }));
                if expected != self.optima[cell][position] {
                    return Err(Error::Optimum { cell, model });
                }
            }
            let mask = self.common_mask(rules, cell);
            let expected: BigUint = mask
                .rules()
                .map(|index| {
                    rules[index]
                        .children
                        .iter()
                        .map(|&child| &self.counts[child])
                        .product::<BigUint>()
                })
                .sum();
            if expected != self.counts[cell] {
                return Err(Error::Count { cell });
            }
        }
        Ok(())
    }

    /// [`Common::verify`], after checking that the certificate's selection is
    /// `selection`. `verify` alone checks the answer to the selection recorded in
    /// the certificate.
    pub fn verify_for<O: CostVector>(
        &self,
        chart: &Chart<O>,
        models: usize,
        selection: &ModelSet,
    ) -> Result<(), Error> {
        if self.selection != *selection {
            return Err(Error::Witness("the certificate answers another selection"));
        }
        self.verify(chart, models)
    }

    fn verify_for_witness<O: CostVector>(&self, chart: &Chart<O>) -> Result<(), Error> {
        // Infer the chart width, with enough columns for the recorded selection.
        // ModelSet admission ensures each index is strictly below usize::MAX.
        let selected_width = self.selection.0.last().map_or(0, |model| model + 1);
        let models = chart
            .cells()
            .iter()
            .flatten()
            .next()
            .map_or(selected_width, |rule| {
                selected_width.max(rule.operator.costs().len())
            });
        self.verify(chart, models)
    }

    /// The common optimum of the given rank in derivation order: rules in cell
    /// order, then the children's ranks with the first child most significant.
    /// This is the order of [`crate::enumerate`] restricted to common optima.
    /// The chart's cost dimensions and the full certificate are checked first.
    pub fn witness<O: CostVector>(
        &self,
        chart: &Chart<O>,
        rank: &BigUint,
    ) -> Result<Option<Witness>, Error> {
        self.verify_for_witness(chart)?;
        if rank >= self.count() {
            return Ok(None);
        }
        let mut preorder = Vec::new();
        let mut pending = vec![(self.root, rank.clone())];
        while let Some((cell, mut remaining)) = pending.pop() {
            let rules = &chart.cells()[cell];
            let mask = self.common_mask(rules, cell);
            let mut chosen = None;
            for index in mask.rules() {
                let block: BigUint = rules[index]
                    .children
                    .iter()
                    .map(|&child| &self.counts[child])
                    .product();
                if remaining < block {
                    chosen = Some(index);
                    break;
                }
                remaining -= block;
            }
            let index = chosen.ok_or(Error::Count { cell })?;
            preorder.push((cell, index));
            let children = &rules[index].children;
            let mut ranks = vec![BigUint::ZERO; children.len()];
            for (position, &child) in children.iter().enumerate().rev() {
                let size = &self.counts[child];
                ranks[position] = &remaining % size;
                remaining /= size;
            }
            for (&child, child_rank) in children.iter().zip(ranks).rev() {
                pending.push((child, child_rank));
            }
        }
        let costs = self.tree_costs(chart, &preorder)?;
        Ok(Some(Witness {
            rank: rank.clone(),
            preorder,
            costs,
        }))
    }

    fn tree_costs<O: CostVector>(
        &self,
        chart: &Chart<O>,
        preorder: &[(Cell, usize)],
    ) -> Result<Vec<BigInt>, Error> {
        let mut costs = vec![BigInt::ZERO; self.selection.models().len()];
        for &(cell, rule) in preorder {
            let rule = chart
                .cells()
                .get(cell)
                .and_then(|rules| rules.get(rule))
                .ok_or(Error::Witness("a node names a missing rule"))?;
            for (cost, &model) in costs.iter_mut().zip(self.selection.models()) {
                *cost += rule.operator.costs()[model];
            }
        }
        Ok(costs)
    }

    /// Check that a witness is a derivation of the root, optimal in every
    /// selected model, and has the stated rank. The full certificate is
    /// checked against the supplied chart before replaying the witness.
    pub fn verify_witness<O: CostVector>(
        &self,
        chart: &Chart<O>,
        witness: &Witness,
    ) -> Result<(), Error> {
        self.verify_for_witness(chart)?;
        // Parse the preorder as a derivation and compute its rank bottom-up.
        struct Frame {
            cell: Cell,
            rule: usize,
            next_child: usize,
            ranks: Vec<BigUint>,
        }
        let mut position = 0;
        let mut stack: Vec<Frame> = Vec::new();
        let mut expected_cell = Some(self.root);
        let mut root_rank = None;
        loop {
            if let Some(cell) = expected_cell.take() {
                let &(at, rule) = witness
                    .preorder
                    .get(position)
                    .ok_or(Error::Witness("the derivation ends early"))?;
                if at != cell {
                    return Err(Error::Witness("a node is not at its parent's child cell"));
                }
                chart.cells()[cell]
                    .get(rule)
                    .ok_or(Error::Witness("a node names a missing rule"))?;
                position += 1;
                stack.push(Frame {
                    cell,
                    rule,
                    next_child: 0,
                    ranks: Vec::new(),
                });
            }
            let Some(frame) = stack.last_mut() else { break };
            let children = &chart.cells()[frame.cell][frame.rule].children;
            if frame.next_child < children.len() {
                expected_cell = Some(children[frame.next_child]);
                frame.next_child += 1;
                continue;
            }
            let frame = stack.pop().expect("frame is present");
            let rank = self.rank_of(chart, frame.cell, frame.rule, &frame.ranks)?;
            match stack.last_mut() {
                Some(parent) => parent.ranks.push(rank),
                None => {
                    root_rank = Some(rank);
                    break;
                }
            }
        }
        if position != witness.preorder.len() {
            return Err(Error::Witness("the derivation has extra nodes"));
        }
        let costs = self.tree_costs(chart, &witness.preorder)?;
        let optimal = costs
            .iter()
            .zip(self.root_optima())
            .all(|(cost, best)| Some(cost) == best.as_ref());
        if !optimal || costs != witness.costs {
            return Err(Error::Witness(
                "its cost differs from the optimum of a selected model",
            ));
        }
        if root_rank.as_ref() != Some(&witness.rank) {
            return Err(Error::Witness("its rank differs from the stated rank"));
        }
        Ok(())
    }

    fn rank_of<O: CostVector>(
        &self,
        chart: &Chart<O>,
        cell: Cell,
        rule: usize,
        child_ranks: &[BigUint],
    ) -> Result<BigUint, Error> {
        let rules = &chart.cells()[cell];
        let mask = self.common_mask(rules, cell);
        if !mask.contains(rule) {
            return Err(Error::Witness(
                "a node's rule is not optimal in every selected model",
            ));
        }
        let mut rank = BigUint::ZERO;
        for index in mask.rules().take_while(|&index| index < rule) {
            rank += rules[index]
                .children
                .iter()
                .map(|&child| &self.counts[child])
                .product::<BigUint>();
        }
        let mut within = BigUint::ZERO;
        for (&child, child_rank) in rules[rule].children.iter().zip(child_ranks) {
            if child_rank >= &self.counts[child] {
                return Err(Error::Witness("a child rank is out of range"));
            }
            within = within * &self.counts[child] + child_rank;
        }
        Ok(rank + within)
    }
}

/// A common optimum: its rank, its nodes in preorder as `(cell, rule ordinal)`,
/// and its cost in each selected model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub rank: BigUint,
    pub preorder: Vec<(Cell, usize)>,
    pub costs: Vec<BigInt>,
}

impl Witness {
    /// Rebuild the derivation as a constructor tree of the chart's operators.
    pub fn tree<O: Clone>(&self, chart: &Chart<O>, root: Cell) -> Result<Tree<O>, Error> {
        let mut nodes = self.preorder.iter();
        // Each open node: its operator, its child cells and the children built so far.
        type Open<'a, O> = (O, &'a [Cell], Vec<Tree<O>>);
        let mut stack: Vec<Open<'_, O>> = Vec::new();
        let mut expected = root;
        loop {
            let &(cell, rule) = nodes
                .next()
                .ok_or(Error::Witness("the derivation ends early"))?;
            if cell != expected {
                return Err(Error::Witness("a node is not at its parent's child cell"));
            }
            let rule = chart
                .cells()
                .get(cell)
                .and_then(|rules| rules.get(rule))
                .ok_or(Error::Witness("a node names a missing rule"))?;
            stack.push((rule.operator.clone(), &rule.children, Vec::new()));
            // Close every completed node, then descend into the next missing child.
            loop {
                let top = stack.last().expect("stack is nonempty");
                if top.2.len() < top.1.len() {
                    expected = top.1[top.2.len()];
                    break;
                }
                let (operator, _, children) = stack.pop().expect("stack is nonempty");
                let tree = Tree { operator, children };
                match stack.last_mut() {
                    Some(parent) => parent.2.push(tree),
                    None => {
                        if nodes.next().is_some() {
                            return Err(Error::Witness("the derivation has extra nodes"));
                        }
                        return Ok(tree);
                    }
                }
            }
        }
    }
}

/// Answer the common-optimum questions for `selection` over a chart with
/// `models` declared cost models. The certificate is verified before return.
pub fn common<O: CostVector>(
    chart: &Chart<O>,
    models: usize,
    selection: &ModelSet,
) -> Result<Exact<Common>, Error> {
    check_costs(chart, models)?;
    selection.check_width(models)?;
    let cells = chart.cells().len();
    let mut optima: Vec<Vec<Option<BigInt>>> = reserved(cells)?;
    let mut counts: Vec<BigUint> = reserved(cells)?;
    for rules in chart.cells() {
        let mut row = reserved(selection.0.len())?;
        row.extend(selection.0.iter().enumerate().map(|(position, &model)| {
            minimum(
                rules
                    .iter()
                    .map(|rule| rule_value(rule, model, |child| optima[child][position].clone())),
            )
        }));
        let mut mask = Mask::full(rules.len());
        for (position, &model) in selection.models().iter().enumerate() {
            let mut winners = Mask::empty(rules.len());
            if row[position].is_some() {
                for (index, rule) in rules.iter().enumerate() {
                    if rule_value(rule, model, |child| optima[child][position].clone())
                        == row[position]
                    {
                        winners.insert(index);
                    }
                }
            }
            mask.intersect(&winners);
        }
        let count = mask
            .rules()
            .map(|index| {
                rules[index]
                    .children
                    .iter()
                    .map(|&child| &counts[child])
                    .product::<BigUint>()
            })
            .sum();
        optima.push(row);
        counts.push(count);
    }
    let answer = Common {
        selection: selection.clone(),
        optima,
        counts,
        root: chart.root(),
    };
    answer.verify(chart, models)?;
    Ok(Exact(answer))
}

/// Count common optima of the root lazily: visit only cells reached through rules
/// that win in every selected model. `winners` returns the common winners of a
/// cell and adds its work.
fn lazy_count<O>(
    chart: &Chart<O>,
    mut winners: impl FnMut(Cell, &mut Work) -> Vec<usize>,
) -> (BigUint, Work) {
    let mut work = Work::default();
    let cells = chart.cells();
    let mut memo: Vec<Option<BigUint>> = vec![None; cells.len()];
    let mut expanded: Vec<Option<Vec<usize>>> = vec![None; cells.len()];
    let mut stack = vec![chart.root()];
    while let Some(&cell) = stack.last() {
        if memo[cell].is_some() {
            stack.pop();
            continue;
        }
        if expanded[cell].is_none() {
            let rules = winners(cell, &mut work);
            work.rule_visits += rules.len() as u64;
            let mut missing = false;
            for &rule in &rules {
                for &child in &cells[cell][rule].children {
                    if memo[child].is_none() {
                        stack.push(child);
                        missing = true;
                    }
                }
            }
            expanded[cell] = Some(rules);
            if missing {
                continue;
            }
        }
        let rules = expanded[cell].as_ref().expect("expanded");
        let mut ready = true;
        for &rule in rules {
            for &child in &cells[cell][rule].children {
                if memo[child].is_none() {
                    stack.push(child);
                    ready = false;
                }
            }
        }
        if !ready {
            continue;
        }
        let count: BigUint = rules
            .iter()
            .map(|&rule| {
                cells[cell][rule]
                    .children
                    .iter()
                    .map(|&child| memo[child].as_ref().expect("child counted"))
                    .product::<BigUint>()
            })
            .sum();
        memo[cell] = Some(count);
        work.cells += 1;
        stack.pop();
    }
    (memo[chart.root()].take().unwrap_or_default(), work)
}

impl WinnerMasks {
    /// Count common optima from retained masks and the chart's child lists.
    /// Supply the same chart and rule order used to build the masks. This method
    /// checks shape and selection bounds. [`Work`] excludes those checks.
    pub fn count_common<O>(
        &self,
        chart: &Chart<O>,
        selection: &ModelSet,
    ) -> Result<(BigUint, Work), Error> {
        self.check(chart, selection)?;
        Ok(lazy_count(chart, |cell, work| {
            let models = selection.models();
            let mut mask = self.masks[cell][models[0]].clone();
            for &model in &models[1..] {
                mask.intersect(&self.masks[cell][model]);
                work.mask_words += mask.words() as u64;
            }
            mask.rules().collect()
        }))
    }

    fn check<O>(&self, chart: &Chart<O>, selection: &ModelSet) -> Result<(), Error> {
        if chart.cells().len() != self.masks.len()
            || chart
                .cells()
                .iter()
                .zip(&self.rules)
                .any(|(rules, &count)| rules.len() != count)
        {
            return Err(Error::CertificateShape);
        }
        match selection.models().iter().find(|&&m| m >= self.models) {
            Some(&model) => Err(Error::ModelOutOfRange {
                model,
                models: self.models,
            }),
            None => Ok(()),
        }
    }
}

impl Optima {
    /// Count common optima from retained optima and the chart's costs, scanning
    /// every rule of each visited cell. Supply the same chart used to compute
    /// the optima. [`Work`] excludes the shape, selection and cost-width checks.
    pub fn count_common<O: CostVector>(
        &self,
        chart: &Chart<O>,
        selection: &ModelSet,
    ) -> Result<(BigUint, Work), Error> {
        check_costs(chart, self.models)?;
        if self.values.len() != chart.cells().len() {
            return Err(Error::CertificateShape);
        }
        if let Some(&model) = selection.models().iter().find(|&&m| m >= self.models) {
            return Err(Error::ModelOutOfRange {
                model,
                models: self.models,
            });
        }
        Ok(lazy_count(chart, |cell, work| {
            let mut common = Vec::new();
            for (index, rule) in chart.cells()[cell].iter().enumerate() {
                work.rule_scans += 1;
                let mut wins = true;
                for &model in selection.models() {
                    work.cost_evaluations += 1;
                    let best = &self.values[cell][model];
                    if best.is_none()
                        || rule_value(rule, model, |child| self.values[child][model].clone())
                            != *best
                    {
                        wins = false;
                        break;
                    }
                }
                if wins {
                    common.push(index);
                }
            }
            common
        }))
    }
}

/// Count common optima with nothing retained: tabulate the selected models over
/// the whole chart, then count from the root.
pub fn count_common_rescan<O: CostVector>(
    chart: &Chart<O>,
    models: usize,
    selection: &ModelSet,
) -> Result<(BigUint, Work), Error> {
    check_costs(chart, models)?;
    let picked: Vec<usize> = selection.models().to_vec();
    if let Some(&model) = picked.iter().find(|&&m| m >= models) {
        return Err(Error::ModelOutOfRange { model, models });
    }
    let mut work = Work::default();
    let mut values: Vec<Vec<Option<BigInt>>> = Vec::with_capacity(chart.cells().len());
    let mut masks: Vec<Mask> = Vec::with_capacity(chart.cells().len());
    for rules in chart.cells() {
        let mut row = Vec::with_capacity(picked.len());
        let mut mask = Mask::full(rules.len());
        for (position, &model) in picked.iter().enumerate() {
            let rule_values: Vec<Option<BigInt>> = rules
                .iter()
                .map(|rule| {
                    work.cost_evaluations += 1;
                    rule_value(rule, model, |child| values[child][position].clone())
                })
                .collect();
            let best = rule_values.iter().flatten().min().cloned();
            let mut winners = Mask::empty(rules.len());
            for (index, value) in rule_values.iter().enumerate() {
                if value.is_some() && *value == best {
                    winners.insert(index);
                }
            }
            mask.intersect(&winners);
            row.push(best);
        }
        values.push(row);
        masks.push(mask);
    }
    let (count, query) = lazy_count(chart, |cell, _| masks[cell].rules().collect());
    work += query;
    Ok((count, work))
}

/// Root common-optimum counts for a declared family of selections and every
/// singleton. Retaining these counts is the "answer table" schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnswerTable {
    models: usize,
    entries: BTreeMap<ModelSet, BigUint>,
}

impl AnswerTable {
    /// Build the table from retained masks. Singletons are always included.
    pub fn build<O>(
        masks: &WinnerMasks,
        chart: &Chart<O>,
        family: &[ModelSet],
    ) -> Result<(Self, Work), Error> {
        let mut work = Work::default();
        let mut entries = BTreeMap::new();
        let singletons = (0..masks.models).map(|model| ModelSet(vec![model]));
        for selection in singletons.chain(family.iter().cloned()) {
            if entries.contains_key(&selection) {
                continue;
            }
            let (count, query) = masks.count_common(chart, &selection)?;
            work += query;
            entries.insert(selection, count);
        }
        Ok((
            Self {
                models: masks.models,
                entries,
            },
            work,
        ))
    }

    /// The retained count for `selection`, or `None` when the table does not
    /// list it. A lookup needs no construction budget.
    pub fn get(&self, selection: &ModelSet) -> Option<&BigUint> {
        self.entries.get(selection)
    }

    /// The retained count, or, for an unlisted selection,
    /// [`Error::NotRetained`] with a generic collision if it fits `budget`.
    /// An unlisted selection whose collision does not fit returns
    /// [`Error::CollisionBudgetExceeded`]; [`AnswerTable::get`] tests
    /// membership without a budget. A fresh model extends the model universe
    /// of that collision.
    pub fn answer(&self, selection: &ModelSet, budget: CollisionBudget) -> Result<&BigUint, Error> {
        if let Some(count) = self.entries.get(selection) {
            return Ok(count);
        }
        // A ModelSet can only contain indices strictly below usize::MAX.
        let declared = self
            .models
            .max(selection.0.last().map_or(0, |model| model + 1));
        Err(Error::NotRetained(Box::new(Collision::construct(
            declared, selection, budget,
        )?)))
    }

    pub fn selections(&self) -> impl Iterator<Item = &ModelSet> {
        self.entries.keys()
    }

    /// Bit length of each count, at least one bit.
    pub fn storage_bits(&self) -> u64 {
        self.entries.values().map(|count| count.bits().max(1)).sum()
    }
}

/// Caller limits for constructing both charts of a [`Collision`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CollisionBudget {
    /// Total rule occurrences to build, including both base rules.
    pub max_rules: usize,
    /// Total dense cost entries to initialize.
    pub max_cost_entries: usize,
}

/// Two one-cell charts over the same models with equal answers for every
/// selection except `selection`, where the answers differ. Any summary made only of
/// other selections' answers, root optima and tie counts takes the same value on
/// both, so no function of it answers `selection`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Collision {
    pub models: usize,
    pub selection: ModelSet,
    pub charts: [Chart<Costed>; 2],
    pub answers: [BigUint; 2],
}

impl Collision {
    pub const QUESTION: QuestionKind = QuestionKind::Existence;
    pub const FAMILY: Family = Family::AllCandidates;
    /// One replayed pair of charts answers the existence question: a weak certificate.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Weak;
    pub const SHAPE: Shape = Shape::SetLevel;

    /// Rules of both charts are indexed by subsets of `selection` plus one base
    /// rule of cost zero in every model. The subset rule `T` costs zero exactly on
    /// the models of `T` and one elsewhere in one chart, and one everywhere in the
    /// other, according to the parity of the models of `selection` missing from
    /// `T`. Every model's root optimum is zero in both charts. A selection `U`
    /// counts the base rule plus the active subsets that contain `U`, so the two
    /// counts differ by the alternating sum over `U ⊆ T ⊆ selection`, which is one
    /// when `U` is the selection and zero otherwise.
    ///
    /// With `k` selected models, construction uses `2 * (2^k + 1)` rules
    /// and that many dense cost rows of width `models`. Both limits are
    /// checked before constructing the charts.
    pub fn construct(
        models: usize,
        selection: &ModelSet,
        budget: CollisionBudget,
    ) -> Result<Self, Error> {
        selection.check_width(models)?;
        let selected = selection.models();
        let shift = u32::try_from(selected.len()).map_err(|_| Error::CollisionBudgetExceeded)?;
        let subsets = 1usize
            .checked_shl(shift)
            .ok_or(Error::CollisionBudgetExceeded)?;
        let per_chart = subsets + 1;
        let rule_count = per_chart
            .checked_mul(2)
            .ok_or(Error::CollisionBudgetExceeded)?;
        if rule_count > budget.max_rules || models > budget.max_cost_entries / rule_count {
            return Err(Error::CollisionBudgetExceeded);
        }
        let mut charts = [reserved(per_chart)?, reserved(per_chart)?];
        for chart in &mut charts {
            let mut costs = reserved(models)?;
            costs.resize(models, 0);
            chart.push(Costed::rule(costs, []));
        }
        for subset in 0..subsets {
            let missing = selected.len() - subset.count_ones() as usize;
            let active = missing % 2;
            for (which, chart) in charts.iter_mut().enumerate() {
                let mut costs = reserved(models)?;
                costs.resize(models, 1);
                if which == active {
                    for (bit, &model) in selected.iter().enumerate() {
                        if subset >> bit & 1 == 1 {
                            costs[model] = 0;
                        }
                    }
                }
                chart.push(Costed::rule(costs, []));
            }
        }
        let [first, second] = charts;
        let charts = [
            Chart::new(vec![first], 0).map_err(|_| Error::CertificateShape)?,
            Chart::new(vec![second], 0).map_err(|_| Error::CertificateShape)?,
        ];
        // Only the base rule and the active full subset can win for selection.
        let answers = [BigUint::from(2u32), BigUint::from(1u32)];
        let mut selected_copy = reserved(selected.len())?;
        selected_copy.extend_from_slice(selected);
        Ok(Self {
            models,
            selection: ModelSet(selected_copy),
            charts,
            answers,
        })
    }

    /// Check that both charts have equal root optima in every model and equal
    /// answers for each retained selection, and different answers for the
    /// collision's selection. List singletons in `retained` to include tie counts.
    pub fn verify(&self, retained: &[ModelSet]) -> Result<(), Error> {
        for chart in &self.charts {
            check_costs(chart, self.models)?;
        }
        self.selection.check_width(self.models)?;
        for selection in retained {
            selection.check_width(self.models)?;
            if *selection == self.selection {
                return Err(Error::Witness("the retained family contains the selection"));
            }
        }
        let [left, right] = &self.charts;
        if self
            .charts
            .iter()
            .all(|chart| chart.cells()[chart.root()].is_empty())
        {
            return Err(Error::Witness("the answers do not differ as recorded"));
        }
        let left_optima = Optima::of(left, self.models)?;
        let right_optima = Optima::of(right, self.models)?;
        if left_optima.values[left.root()] != right_optima.values[right.root()] {
            return Err(Error::Witness("the root optima differ"));
        }
        for selection in retained {
            if left_optima.count_common(left, selection)?.0
                != right_optima.count_common(right, selection)?.0
            {
                return Err(Error::Witness("the summaries differ"));
            }
        }
        let first = left_optima.count_common(left, &self.selection)?.0;
        let second = right_optima.count_common(right, &self.selection)?.0;
        if first == second || [first, second] != self.answers {
            return Err(Error::Witness("the answers do not differ as recorded"));
        }
        Ok(())
    }
}
