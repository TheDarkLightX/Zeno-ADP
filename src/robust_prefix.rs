//! Plan prefixes that keep an optimal completion in every world.
//!
//! A plan chart is a [`Chart`] whose rules are steps (one child) or finishes (no
//! child). Each rule has a cost per world and a nonnegative credit for the useful
//! work it does. Every world shares the same rules. A plan is a rule sequence from
//! the root that ends with a finish. A prefix is any rule sequence from the root,
//! including the empty one, that some plan extends.
//!
//! In world `w` let `V_w(x)` be the least cost of finishing from cell `x`. The
//! slack of a rule from `x` to `y` is `cost_w + V_w(y) - V_w(x)`, which is never
//! negative. Committing to a prefix and then finishing optimally costs the world's
//! optimum plus the sum of the prefix's slacks in that world. So a prefix keeps an
//! optimal completion in every world exactly when each of its rules has zero
//! slack in every world, and it keeps a completion within budget `b_w` exactly
//! when its slacks in each world sum to at most `b_w`. A single budget shared by
//! the worlds does not express this condition.
//!
//! [`zero_regret`] returns the greatest credit attainable with zero slack, the
//! count and first prefix of that credit, an optimal completion per world, and
//! whether a whole plan is optimal in every world. [`within_budget`] returns the
//! greatest credit within the per-world budgets, the count and first prefix of
//! that credit, its regret and a completion per world. The budgeted credit
//! problem contains 0/1 knapsack and uses a dynamic program over the remaining
//! budget of each world.

use std::collections::HashMap;
use std::fmt;

use num_bigint::{BigInt, BigUint};

use crate::assurance::{CertificateKind, Family, Label, QuestionKind, Shape};
use crate::common_optimum::{self, CostVector, Optima};
use crate::{Cell, Chart, Exact, Operator, Rule};

/// A plan rule with a credit for useful work.
pub trait PlanStep: CostVector {
    fn credit(&self) -> u64;
}

/// A step to one child or a finish, with a cost per world and a credit.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Step {
    pub costs: Vec<i64>,
    pub credit: u64,
    pub arity: usize,
}

impl Operator for Step {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl CostVector for Step {
    fn costs(&self) -> &[i64] {
        &self.costs
    }
}

impl PlanStep for Step {
    fn credit(&self) -> u64 {
        self.credit
    }
}

impl Step {
    /// A step to `child`.
    pub fn to(costs: impl Into<Vec<i64>>, credit: u64, child: Cell) -> Rule<Self> {
        Rule::new(
            Self {
                costs: costs.into(),
                credit,
                arity: 1,
            },
            vec![child],
        )
    }

    /// A rule that ends the plan.
    pub fn finish(costs: impl Into<Vec<i64>>, credit: u64) -> Rule<Self> {
        Rule::new(
            Self {
                costs: costs.into(),
                credit,
                arity: 0,
            },
            vec![],
        )
    }
}

/// Credit sums use `u128`: a prefix visits each cell at most once, so it has fewer
/// than 2^64 rules on a 64-bit target, each with credit below 2^64, and the sum is
/// below 2^128.
pub type Credit = u128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Model(common_optimum::Error),
    /// A plan rule must have zero or one child.
    Arity {
        cell: Cell,
        rule: usize,
        arity: usize,
    },
    /// Some world has no plan from the root.
    NoPlan {
        world: usize,
    },
    /// The budget vector must give one budget per world.
    BudgetLength {
        worlds: usize,
        actual: usize,
    },
    CertificateShape,
    /// A recorded credit or count fails its cell equation.
    Equation {
        cell: Cell,
    },
    /// A prefix or completion fails a check.
    Plan(&'static str),
    /// The budget program or its verifier would keep more states than the caller allowed.
    StateLimit {
        limit: usize,
    },
    /// The certificate answers another question (another budget).
    Question,
}

impl From<common_optimum::Error> for Error {
    fn from(error: common_optimum::Error) -> Self {
        Self::Model(error)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Model(error) => write!(f, "{error}"),
            Self::Arity { cell, rule, arity } => write!(
                f,
                "cell {cell}, rule {rule} has {arity} children; plan rules have at most one"
            ),
            Self::NoPlan { world } => write!(f, "world {world} has no plan from the root"),
            Self::BudgetLength { worlds, actual } => {
                write!(f, "{actual} budgets given for {worlds} worlds")
            }
            Self::CertificateShape => write!(f, "certificate tables do not match the chart"),
            Self::Equation { cell } => write!(f, "recorded credit or count fails at cell {cell}"),
            Self::Plan(reason) => write!(f, "plan rejected: {reason}"),
            Self::StateLimit { limit } => write!(
                f,
                "the budget program needs more than the {limit} states the caller allowed"
            ),
            Self::Question => write!(f, "the certificate answers another budget"),
        }
    }
}

impl std::error::Error for Error {}

/// A rule sequence from the root as `(cell, rule ordinal)` pairs.
pub type Rules = Vec<(Cell, usize)>;

fn check_plan_chart<O: PlanStep>(chart: &Chart<O>, worlds: usize) -> Result<Optima, Error> {
    common_optimum::check_costs(chart, worlds)?;
    for (cell, rules) in chart.cells().iter().enumerate() {
        for (index, rule) in rules.iter().enumerate() {
            if rule.children.len() > 1 {
                return Err(Error::Arity {
                    cell,
                    rule: index,
                    arity: rule.children.len(),
                });
            }
        }
    }
    let values = Optima::of(chart, worlds)?;
    for world in 0..worlds {
        if values.value(chart.root(), world).is_none() {
            return Err(Error::NoPlan { world });
        }
    }
    Ok(values)
}

/// The slack of a rule in one world, or `None` when its child has no plan.
fn slack<O: PlanStep>(rule: &Rule<O>, cell: Cell, world: usize, values: &Optima) -> Option<BigInt> {
    let mut total = BigInt::from(rule.operator.costs()[world]);
    if let Some(&child) = rule.children.first() {
        total += values.value(child, world)?;
    }
    Some(total - values.value(cell, world)?)
}

fn zero_slack<O: PlanStep>(rule: &Rule<O>, cell: Cell, values: &Optima) -> bool {
    (0..values.models()).all(|world| slack(rule, cell, world, values) == Some(BigInt::ZERO))
}

/// The certificate of a zero-regret query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZeroRegret {
    /// The least finishing cost of each cell in each world.
    pub values: Optima,
    /// The greatest credit of a zero-slack continuation from each cell, stopping allowed.
    pub credit: Vec<Credit>,
    /// The number of zero-slack continuations of that credit from each cell.
    pub counts: Vec<BigUint>,
    /// The first prefix of greatest credit in prefix order.
    pub prefix: Rules,
    /// For each world, a plan that extends the prefix and is optimal in that world.
    pub completions: Vec<Rules>,
    /// Whether a zero-slack continuation from each cell reaches a finish.
    pub reach: Vec<bool>,
    /// The first whole plan optimal in every world, if one exists.
    pub common_plan: Option<Rules>,
}

impl ZeroRegret {
    pub const QUESTIONS: [QuestionKind; 4] = [
        QuestionKind::OneOptimum,
        QuestionKind::Count,
        QuestionKind::WitnessIdentity,
        QuestionKind::Existence,
    ];
    pub const FAMILY: Family = Family::WithinBudgetInEveryWorld;
    /// Over the prefixes with an optimal completion in every world: keeping the
    /// rules with zero slack in every world drops none of them and keeps their order.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Strict;
    pub const SHAPE: Shape = Shape::LiteralFilter;
    pub const LABEL: Label = Label::Exact;

    /// The greatest credit of a robust prefix.
    pub fn best_credit(&self, root: Cell) -> Credit {
        self.credit[root]
    }

    /// The number of robust prefixes with the greatest credit.
    pub fn count(&self, root: Cell) -> &BigUint {
        &self.counts[root]
    }

    /// Whether some whole plan is optimal in every world.
    pub fn common_plan_exists(&self) -> bool {
        self.common_plan.is_some()
    }

    /// Check every equation and witness against the chart.
    pub fn verify<O: PlanStep>(&self, chart: &Chart<O>, worlds: usize) -> Result<(), Error> {
        check_plan_chart(chart, worlds)?;
        self.values.verify(chart)?;
        if self.values.models() != worlds
            || self.credit.len() != chart.cells().len()
            || self.counts.len() != chart.cells().len()
            || self.completions.len() != worlds
            || self.reach.len() != chart.cells().len()
        {
            return Err(Error::CertificateShape);
        }
        for (cell, rules) in chart.cells().iter().enumerate() {
            let (credit, count) =
                continuation(rules, cell, &self.values, &self.credit, &self.counts);
            if credit != self.credit[cell]
                || count != self.counts[cell]
                || reaches(rules, cell, &self.values, &self.reach) != self.reach[cell]
            {
                return Err(Error::Equation { cell });
            }
        }
        if self.common_plan != first_common_plan(chart, &self.values, &self.reach) {
            return Err(Error::Plan(
                "the common plan is not the first zero-slack plan",
            ));
        }
        if let Some(plan) = &self.common_plan {
            if walk(chart, plan, |rule, cell| {
                zero_slack(rule, cell, &self.values)
            })?
            .is_some()
            {
                return Err(Error::Plan("the common plan does not finish"));
            }
        }
        let end = walk(chart, &self.prefix, |rule, cell| {
            zero_slack(rule, cell, &self.values)
        })?;
        let credit = prefix_credit(chart, &self.prefix);
        if credit != self.credit[chart.root()] {
            return Err(Error::Plan("the prefix does not have the greatest credit"));
        }
        if self.prefix != first_prefix(chart, &self.values, &self.credit) {
            return Err(Error::Plan(
                "the prefix is not the first of greatest credit",
            ));
        }
        if end.is_none() && self.completions.iter().any(|plan| plan != &self.prefix) {
            return Err(Error::Plan("a whole-plan prefix has another completion"));
        }
        check_completions(chart, &self.values, &self.prefix, &self.completions, None)
    }
}

/// Follow a rule sequence from the root, requiring `allowed` at every rule. Returns
/// the cell after the last step, or `None` after a finish.
fn walk<O>(
    chart: &Chart<O>,
    rules: &[(Cell, usize)],
    mut allowed: impl FnMut(&Rule<O>, Cell) -> bool,
) -> Result<Option<Cell>, Error> {
    let mut at = Some(chart.root());
    for &(cell, index) in rules {
        if at != Some(cell) {
            return Err(Error::Plan(
                "a rule is not at the cell its predecessor reaches",
            ));
        }
        let rule = chart.cells()[cell]
            .get(index)
            .ok_or(Error::Plan("a rule ordinal is out of range"))?;
        if !allowed(rule, cell) {
            return Err(Error::Plan("a rule is not allowed here"));
        }
        at = rule.children.first().copied();
    }
    Ok(at)
}

/// Whether some zero-slack continuation from a cell ends with a finish.
fn reaches<O: PlanStep>(rules: &[Rule<O>], cell: Cell, values: &Optima, reach: &[bool]) -> bool {
    rules.iter().any(|rule| {
        zero_slack(rule, cell, values) && rule.children.first().is_none_or(|&child| reach[child])
    })
}

/// The first whole zero-slack plan in rule order, if any.
fn first_common_plan<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    reach: &[bool],
) -> Option<Rules> {
    let mut plan = Vec::new();
    let mut at = Some(chart.root());
    while let Some(cell) = at {
        if !reach[cell] {
            return None;
        }
        let (index, rule) = chart.cells()[cell].iter().enumerate().find(|(_, rule)| {
            zero_slack(rule, cell, values)
                && rule.children.first().is_none_or(|&child| reach[child])
        })?;
        plan.push((cell, index));
        at = rule.children.first().copied();
    }
    Some(plan)
}

fn prefix_credit<O: PlanStep>(chart: &Chart<O>, rules: &[(Cell, usize)]) -> Credit {
    rules
        .iter()
        .map(|&(cell, rule)| Credit::from(chart.cells()[cell][rule].operator.credit()))
        .sum()
}

/// Greatest credit and its count over zero-slack continuations from one cell.
fn continuation<O: PlanStep>(
    rules: &[Rule<O>],
    cell: Cell,
    values: &Optima,
    credit: &[Credit],
    counts: &[BigUint],
) -> (Credit, BigUint) {
    let mut best: Credit = 0;
    let mut count = BigUint::from(1u32); // stopping here
    for rule in rules {
        if !zero_slack(rule, cell, values) {
            continue;
        }
        let (value, ways) = match rule.children.first() {
            Some(&child) => (
                Credit::from(rule.operator.credit()) + credit[child],
                counts[child].clone(),
            ),
            None => (Credit::from(rule.operator.credit()), BigUint::from(1u32)),
        };
        if value > best {
            best = value;
            count = ways;
        } else if value == best {
            count += ways;
        }
    }
    (best, count)
}

/// The first prefix of greatest credit: stop before any rule, then rules in
/// ordinal order, each followed by the first best continuation.
fn first_prefix<O: PlanStep>(chart: &Chart<O>, values: &Optima, credit: &[Credit]) -> Rules {
    let mut prefix = Vec::new();
    let mut at = Some(chart.root());
    while let Some(cell) = at {
        if credit[cell] == 0 {
            break;
        }
        let rules = &chart.cells()[cell];
        let chosen = rules.iter().enumerate().find(|(_, rule)| {
            zero_slack(rule, cell, values)
                && Credit::from(rule.operator.credit())
                    + rule.children.first().map_or(0, |&child| credit[child])
                    == credit[cell]
        });
        let Some((index, rule)) = chosen else { break };
        prefix.push((cell, index));
        at = rule.children.first().copied();
    }
    prefix
}

/// Extend the prefix in each world by rules of zero slack in that world, taking
/// the first such rule at each cell.
fn complete<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    prefix: &Rules,
    end: Option<Cell>,
) -> Vec<Rules> {
    (0..values.models())
        .map(|world| {
            let mut plan = prefix.clone();
            let mut at = end;
            while let Some(cell) = at {
                let rules = &chart.cells()[cell];
                let (index, rule) = rules
                    .iter()
                    .enumerate()
                    .find(|(_, rule)| slack(rule, cell, world, values) == Some(BigInt::ZERO))
                    .expect("an inhabited cell has a rule attaining its value");
                plan.push((cell, index));
                at = rule.children.first().copied();
            }
            plan
        })
        .collect()
}

/// Each completion extends the prefix, ends with a finish, and costs the world's
/// optimum plus at most the world's budget (zero when `budget` is `None`).
fn check_completions<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    prefix: &Rules,
    completions: &[Rules],
    budget: Option<&[BigUint]>,
) -> Result<(), Error> {
    for (world, plan) in completions.iter().enumerate() {
        if plan.len() < prefix.len() || plan[..prefix.len()] != prefix[..] {
            return Err(Error::Plan("a completion does not extend the prefix"));
        }
        if walk(chart, plan, |_, _| true)?.is_some() {
            return Err(Error::Plan("a completion does not finish"));
        }
        let cost: BigInt = plan
            .iter()
            .map(|&(cell, rule)| BigInt::from(chart.cells()[cell][rule].operator.costs()[world]))
            .sum();
        let optimum = values
            .value(chart.root(), world)
            .ok_or(Error::NoPlan { world })?;
        let allowed = budget.map_or(BigInt::ZERO, |budget| BigInt::from(budget[world].clone()));
        if cost < *optimum || cost - optimum > allowed {
            return Err(Error::Plan("a completion costs more than the world allows"));
        }
    }
    Ok(())
}

/// The robust prefix of greatest credit and one optimal completion per world.
pub fn zero_regret<O: PlanStep>(
    chart: &Chart<O>,
    worlds: usize,
) -> Result<Exact<ZeroRegret>, Error> {
    let values = check_plan_chart(chart, worlds)?;
    let mut credit = Vec::with_capacity(chart.cells().len());
    let mut counts = Vec::with_capacity(chart.cells().len());
    let mut reach = Vec::with_capacity(chart.cells().len());
    for (cell, rules) in chart.cells().iter().enumerate() {
        let (best, count) = continuation(rules, cell, &values, &credit, &counts);
        credit.push(best);
        counts.push(count);
        reach.push(reaches(rules, cell, &values, &reach));
    }
    let common_plan = first_common_plan(chart, &values, &reach);
    let prefix = first_prefix(chart, &values, &credit);
    let end = walk(chart, &prefix, |_, _| true)?;
    let completions = complete(chart, &values, &prefix, end);
    let answer = ZeroRegret {
        values,
        credit,
        counts,
        prefix,
        completions,
        reach,
        common_plan,
    };
    answer.verify(chart, worlds)?;
    Ok(Exact(answer))
}

/// The regret of a rule sequence from the root in each world: the sum of its
/// slacks, which equals the least cost of a plan extending it minus the optimum.
pub fn regret<O: PlanStep>(
    chart: &Chart<O>,
    worlds: usize,
    rules: &[(Cell, usize)],
) -> Result<Vec<BigInt>, Error> {
    let values = check_plan_chart(chart, worlds)?;
    let mut total = vec![BigInt::ZERO; worlds];
    let mut reachable = true;
    walk(chart, rules, |rule, cell| {
        for (world, sum) in total.iter_mut().enumerate() {
            match slack(rule, cell, world, &values) {
                Some(value) => *sum += value,
                None => reachable = false,
            }
        }
        reachable
    })?;
    Ok(total)
}

/// The certificate of a per-world budget query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WithinBudget {
    pub values: Optima,
    pub budget: Vec<BigUint>,
    /// The greatest credit of a prefix within budget in every world.
    pub best: Credit,
    /// The number of prefixes within budget with that credit.
    pub count: BigUint,
    /// The first such prefix in prefix order.
    pub prefix: Rules,
    /// Its regret in each world.
    pub regret: Vec<BigInt>,
    /// For each world, a plan extending the prefix within that world's budget.
    pub completions: Vec<Rules>,
}

impl WithinBudget {
    pub const QUESTIONS: [QuestionKind; 3] = [
        QuestionKind::OneOptimum,
        QuestionKind::Count,
        QuestionKind::WitnessIdentity,
    ];
    pub const FAMILY: Family = Family::WithinBudgetInEveryWorld;
    /// Over the prefixes whose regret is within the budget of every world: the
    /// budget program drops none of them and keeps their order.
    pub const CERTIFICATE: CertificateKind = CertificateKind::Strict;
    pub const SHAPE: Shape = Shape::LiteralFilter;
    pub const LABEL: Label = Label::Exact;

    /// Replay the values, the prefix's regret and completions, recompute the
    /// greatest credit by a forward search over per-world slack vectors, and replay
    /// the budget dynamic program for the count and the first prefix, keeping at most
    /// `max_states` states in each (see [`within_budget`]).
    ///
    /// This checks the answer to the budget recorded in the certificate. Use
    /// [`WithinBudget::verify_for`] to also check that it is the budget you asked about.
    pub fn verify<O: PlanStep>(
        &self,
        chart: &Chart<O>,
        worlds: usize,
        max_states: usize,
    ) -> Result<(), Error> {
        check_plan_chart(chart, worlds)?;
        self.values.verify(chart)?;
        if self.budget.len() != worlds
            || self.completions.len() != worlds
            || self.regret.len() != worlds
        {
            return Err(Error::CertificateShape);
        }
        let regret = regret(chart, worlds, &self.prefix)?;
        if regret != self.regret
            || regret
                .iter()
                .zip(&self.budget)
                .any(|(used, budget)| *used > BigInt::from(budget.clone()))
        {
            return Err(Error::Plan("the prefix exceeds a world's budget"));
        }
        if prefix_credit(chart, &self.prefix) != self.best {
            return Err(Error::Plan(
                "the prefix credit differs from the recorded best",
            ));
        }
        if forward_best(chart, &self.values, &self.budget, max_states)? != self.best {
            return Err(Error::Plan("a prefix within budget has more credit"));
        }
        let mut memo = HashMap::new();
        let (best, count) = budget_solve(
            chart,
            &self.values,
            chart.root(),
            &self.budget,
            &mut memo,
            max_states,
        )?;
        if best != self.best || count != self.count {
            return Err(Error::Plan(
                "the count of prefixes of greatest credit differs",
            ));
        }
        if first_budget_prefix(
            chart,
            &self.values,
            &self.budget,
            best,
            &mut memo,
            max_states,
        )? != self.prefix
        {
            return Err(Error::Plan(
                "the prefix is not the first of greatest credit",
            ));
        }
        check_completions(
            chart,
            &self.values,
            &self.prefix,
            &self.completions,
            Some(&self.budget),
        )
    }

    /// [`WithinBudget::verify`], after checking that the certificate's budget is `budget`.
    pub fn verify_for<O: PlanStep>(
        &self,
        chart: &Chart<O>,
        worlds: usize,
        budget: &[BigUint],
        max_states: usize,
    ) -> Result<(), Error> {
        if self.budget != budget {
            return Err(Error::Question);
        }
        self.verify(chart, worlds, max_states)
    }
}

/// The most `(cell, remaining budget)` states the budget program can visit, and the
/// most slack labels its verifier can keep: the number of cells times the product
/// of `budget[w] + 1` over the worlds. Remaining budgets and accumulated slacks are
/// integers between zero and each world's budget, so neither count exceeds it.
pub fn state_bound<O>(chart: &Chart<O>, budget: &[BigUint]) -> BigUint {
    budget
        .iter()
        .fold(BigUint::from(chart.cells().len()), |product, b| {
            product * (b + 1u32)
        })
}

/// Greatest credit within budget by forward search over prefixes, keeping at each
/// cell only slack vectors that no kept vector dominates with at least its credit.
/// This is a weak pruning certificate: a dropped label has a kept label with no
/// more slack in any world and no less credit, and the same extensions.
fn forward_best<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    budget: &[BigUint],
    max_states: usize,
) -> Result<Credit, Error> {
    if max_states == 0 {
        return Err(Error::StateLimit { limit: max_states });
    }
    let worlds = budget.len();
    let limit: Vec<BigInt> = budget.iter().map(|b| BigInt::from(b.clone())).collect();
    let mut labels: HashMap<Cell, Vec<(Vec<BigInt>, Credit)>> = HashMap::new();
    labels.insert(chart.root(), vec![(vec![BigInt::ZERO; worlds], 0)]);
    let mut kept = 1usize;
    let mut best: Credit = 0;
    // Cells are in rank order with children below parents, so visiting cells in
    // descending rank settles each cell's labels before they are extended.
    for cell in (0..chart.cells().len()).rev() {
        let Some(here) = labels.remove(&cell) else {
            continue;
        };
        for (used, credit) in &here {
            best = best.max(*credit);
            for rule in &chart.cells()[cell] {
                let mut next = used.clone();
                let mut fits = true;
                for (world, slot) in next.iter_mut().enumerate() {
                    match slack(rule, cell, world, values) {
                        Some(value) => *slot += value,
                        None => fits = false,
                    }
                    fits &= *slot <= limit[world];
                }
                if !fits {
                    continue;
                }
                let gained = credit + Credit::from(rule.operator.credit());
                match rule.children.first() {
                    None => best = best.max(gained),
                    Some(&child) => {
                        let entry = labels.entry(child).or_default();
                        if entry.iter().any(|(kept, c)| {
                            *c >= gained && kept.iter().zip(&next).all(|(k, n)| k <= n)
                        }) {
                            continue;
                        }
                        let before = entry.len();
                        entry.retain(|(kept, c)| {
                            !(gained >= *c && next.iter().zip(kept).all(|(n, k)| n <= k))
                        });
                        kept -= before - entry.len();
                        if kept >= max_states {
                            return Err(Error::StateLimit { limit: max_states });
                        }
                        entry.push((next, gained));
                        kept += 1;
                    }
                }
            }
        }
        kept -= here.len();
    }
    Ok(best)
}

/// The prefix of greatest credit whose regret in each world is within that world's
/// budget, the number of such prefixes, and one completion per world within budget.
///
/// The question is NP-hard, so the work grows with the budgets. The caller sets
/// `max_states` bounds the sum of pending frames and memoized states in each
/// budget DP pass. Each distinct `(cell, remaining budget)` occupies one slot.
/// It also bounds the total live slack labels in the separate forward pass,
/// including labels of the cell being processed. Each pass starts with an empty
/// state store. A zero limit or an admission beyond the limit returns
/// [`Error::StateLimit`]. [`state_bound`] bounds the slots needed in each pass.
pub fn within_budget<O: PlanStep>(
    chart: &Chart<O>,
    worlds: usize,
    budget: &[BigUint],
    max_states: usize,
) -> Result<Exact<WithinBudget>, Error> {
    let values = check_plan_chart(chart, worlds)?;
    if budget.len() != worlds {
        return Err(Error::BudgetLength {
            worlds,
            actual: budget.len(),
        });
    }
    let mut memo: HashMap<(Cell, Vec<BigUint>), (Credit, BigUint)> = HashMap::new();
    let (best, count) = budget_solve(chart, &values, chart.root(), budget, &mut memo, max_states)?;
    let prefix = first_budget_prefix(chart, &values, budget, best, &mut memo, max_states)?;
    drop(memo);
    let regret = regret(chart, worlds, &prefix)?;
    let end = walk(chart, &prefix, |_, _| true)?;
    let completions = complete(chart, &values, &prefix, end);
    let answer = WithinBudget {
        values,
        budget: budget.to_vec(),
        best,
        count,
        prefix,
        regret,
        completions,
    };
    answer.verify(chart, worlds, max_states)?;
    Ok(Exact(answer))
}

/// The first prefix of credit `best` within budget, in prefix order: stop when
/// nothing more is needed, otherwise take the first rule whose best continuation
/// reaches the needed credit.
fn first_budget_prefix<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    budget: &[BigUint],
    best: Credit,
    memo: &mut HashMap<(Cell, Vec<BigUint>), (Credit, BigUint)>,
    max_states: usize,
) -> Result<Rules, Error> {
    let mut prefix = Vec::new();
    let mut at = Some(chart.root());
    let mut left = budget.to_vec();
    let mut need = best;
    while let Some(cell) = at {
        if need == 0 {
            break;
        }
        let mut chosen = None;
        for (index, rule) in chart.cells()[cell].iter().enumerate() {
            let Some(rest) = spend(rule, cell, values, &left) else {
                continue;
            };
            let gained = Credit::from(rule.operator.credit());
            let value = match rule.children.first() {
                Some(&child) => {
                    gained + budget_solve(chart, values, child, &rest, memo, max_states)?.0
                }
                None => gained,
            };
            if value == need {
                chosen = Some((index, rule, rest, gained));
                break;
            }
        }
        let Some((index, rule, rest, gained)) = chosen else {
            break;
        };
        prefix.push((cell, index));
        need -= gained;
        left = rest;
        at = rule.children.first().copied();
    }
    Ok(prefix)
}

/// The remaining budgets after taking a rule, or `None` if it does not fit.
fn spend<O: PlanStep>(
    rule: &Rule<O>,
    cell: Cell,
    values: &Optima,
    left: &[BigUint],
) -> Option<Vec<BigUint>> {
    left.iter()
        .enumerate()
        .map(|(world, budget)| {
            let used = slack(rule, cell, world, values)?;
            (BigInt::from(budget.clone()) - used).to_biguint()
        })
        .collect()
}

/// Greatest credit and its count from `cell` with remaining per-world budgets.
fn budget_solve<O: PlanStep>(
    chart: &Chart<O>,
    values: &Optima,
    cell: Cell,
    left: &[BigUint],
    memo: &mut HashMap<(Cell, Vec<BigUint>), (Credit, BigUint)>,
    max_states: usize,
) -> Result<(Credit, BigUint), Error> {
    type Key = (Cell, Vec<BigUint>);

    struct Frame {
        key: Key,
        rule: usize,
        best: Credit,
        count: BigUint,
    }

    impl Frame {
        fn new(key: Key) -> Self {
            Self {
                key,
                rule: 0,
                best: 0,
                count: BigUint::from(1u32), // The option to stop here.
            }
        }
    }

    let key = (cell, left.to_vec());
    if let Some(answer) = memo.get(&key) {
        return Ok(answer.clone());
    }
    if memo.len() >= max_states {
        return Err(Error::StateLimit { limit: max_states });
    }

    // Explore one child at a time. Ranks decrease down the stack, so a
    // missing child is never pending already. Repeated edges reuse its memo.
    let mut stack = vec![Frame::new(key)];
    while let Some(frame) = stack.last_mut() {
        let (at, budget) = &frame.key;
        let Some(rule) = chart.cells()[*at].get(frame.rule) else {
            let frame = stack.pop().expect("the current frame is present");
            if stack.is_empty() {
                let answer = (frame.best, frame.count);
                memo.insert(frame.key, answer.clone());
                return Ok(answer);
            }
            memo.insert(frame.key, (frame.best, frame.count));
            continue;
        };
        let Some(rest) = spend(rule, *at, values, budget) else {
            frame.rule += 1;
            continue;
        };
        let gained = Credit::from(rule.operator.credit());
        let (value, ways) = match rule.children.first() {
            Some(&child) => {
                let child_key = (child, rest);
                let Some((value, ways)) = memo.get(&child_key) else {
                    if stack.len() >= max_states - memo.len() {
                        return Err(Error::StateLimit { limit: max_states });
                    }
                    stack.push(Frame::new(child_key));
                    continue;
                };
                (gained + value, ways.clone())
            }
            None => (gained, BigUint::from(1u32)),
        };
        if value > frame.best {
            frame.best = value;
            frame.count = ways;
        } else if value == frame.best {
            frame.count += ways;
        }
        frame.rule += 1;
    }
    Err(Error::Equation { cell })
}

#[cfg(test)]
mod budget_limit_tests {
    use super::*;

    #[test]
    fn budget_limit_counts_pending_states_and_keeps_only_one_frame_per_state() {
        let chart = Chart::new(
            vec![vec![Step::finish([0], 0)], vec![Step::to([0], 1, 0); 3]],
            1,
        )
        .unwrap();
        let values = check_plan_chart(&chart, 1).unwrap();
        let budget = [BigUint::ZERO];
        let mut memo = HashMap::new();
        assert_eq!(
            budget_solve(&chart, &values, 1, &budget, &mut memo, 1),
            Err(Error::StateLimit { limit: 1 })
        );
        assert!(
            memo.is_empty(),
            "a child completed before its frame could be admitted"
        );
        assert_eq!(state_bound(&chart, &budget), BigUint::from(2u32));
        let answer = within_budget(&chart, 1, &budget, 2).unwrap();
        assert_eq!(answer.as_ref().best, 1);
        assert_eq!(answer.as_ref().count, BigUint::from(6u32));
    }

    #[test]
    fn forward_budget_limit_refuses_the_first_label_at_zero() {
        let chart = Chart::new(vec![vec![Step::finish([0], 0)]], 0).unwrap();
        let values = check_plan_chart(&chart, 1).unwrap();
        assert_eq!(
            forward_best(&chart, &values, &[BigUint::ZERO], 0),
            Err(Error::StateLimit { limit: 0 })
        );
    }
}
