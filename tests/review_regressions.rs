//! Regression tests: scorer labels rest on a check of the same declared history,
//! verifiers refuse malformed certificates instead of panicking, and solvers agree with
//! enumeration on irregular charts.
use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};

use num_bigint::{BigInt, BigUint};
use zeno_adp::assurance::Label;
use zeno_adp::common_optimum::{common, Costed, ModelSet};
use zeno_adp::robust_prefix::{state_bound, within_budget, zero_regret, Rules, Step};
use zeno_adp::state_discovery::{
    Alignment, Error, Geometry, Observer, ObserverCheck, Quotient, RawModel, Sense, Symbol,
};
use zeno_adp::{Chart, Exact, Rule};

const A: Symbol = Alignment::MATCH;
const B: Symbol = Alignment::MISMATCH;
const D: Symbol = Alignment::DELETE;
const I: Symbol = Alignment::INSERT;

fn two_symbol_score(word: &[Symbol]) -> i64 {
    let mut out = 0;
    for (n, &a) in word.iter().enumerate() {
        let h = &word[n.saturating_sub(2)..n];
        if a == A || a == B {
            out += if a == A { 3 } else { -2 };
        } else {
            out += if h.last() == Some(&a) { -1 } else { -3 };
            if h == [a, A] {
                out += 6;
            }
            if a == D && h == [B, A] {
                out += 5;
            }
        }
    }
    out
}

fn horizon_three(word: &[Symbol]) -> i64 {
    let mut out = two_symbol_score(word);
    for n in 3..word.len() {
        if word[n] == I && word[n - 3..n] == [B, A, D] {
            out += 4;
        }
    }
    out
}

fn binary_words(max: usize) -> Vec<Vec<u8>> {
    let mut words = vec![Vec::new()];
    let mut level = vec![Vec::new()];
    for _ in 0..max {
        let mut next = Vec::new();
        for word in &level {
            for bit in [b'0', b'1'] {
                let mut longer: Vec<u8> = word.clone();
                longer.push(bit);
                next.push(longer);
            }
        }
        words.extend(next.iter().cloned());
        level = next;
    }
    words
}

/// Every alignment word of a pair, by walking the geometry.
fn alignment_words(x: &[u8], y: &[u8]) -> Vec<Vec<Symbol>> {
    let geometry = Alignment { x, y };
    let mut out = Vec::new();
    let mut stack = vec![(geometry.start(), Vec::new())];
    while let Some((cell, word)) = stack.pop() {
        if geometry.is_final(&cell) {
            out.push(word.clone());
        }
        for (symbol, next) in geometry.moves(&cell) {
            let mut longer = word.clone();
            longer.push(symbol);
            stack.push((next, longer));
        }
    }
    out
}

/// Count the pairs on which the chart's answer is labelled Exact against the scorer
/// and is wrong, and the pairs labelled Exact.
fn wrong_exact(
    quotient: &Exact<Quotient>,
    check: &Exact<ObserverCheck>,
    scorer: fn(&[Symbol]) -> i64,
    max_length: usize,
) -> (usize, usize) {
    let (mut wrong, mut exact) = (0, 0);
    let strings = binary_words(max_length);
    for x in &strings {
        for y in &strings {
            let best = alignment_words(x, y)
                .iter()
                .map(|w| scorer(w))
                .max()
                .unwrap();
            let solved = quotient
                .chart(&Alignment { x, y }, Sense::Maximize)
                .unwrap()
                .solve(Some(check))
                .unwrap()
                .into_inner();
            if solved.scorer_label == Label::Exact {
                exact += 1;
                if solved.score != i128::from(best) {
                    wrong += 1;
                }
            }
        }
    }
    (wrong, exact)
}

/// A check is made only by running it (a `compile_fail` test on `ObserverCheck`
/// covers construction). A check of the same raw model labels the short answers Exact.
#[test]
fn a_check_of_the_same_raw_model_labels_only_right_answers_exact() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let mut raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    let check = raw.check(&mut scorer, 8).unwrap();
    assert!(check.as_ref().is_for(&raw));
    let quotient = raw.quotient().unwrap();
    assert_eq!(
        wrong_exact(&quotient, &check, two_symbol_score, 4),
        (0, 961)
    );
}

/// A genuine check of another scorer's model must not make a wrong answer Exact.
#[test]
fn a_check_of_another_scorer_labels_no_wrong_answer_exact() {
    let mut honest = |w: &[Symbol]| two_symbol_score(w);
    let mut raw_a = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut honest).unwrap();
    let check_a = raw_a.check(&mut honest, 8).unwrap();
    let mut other = |w: &[Symbol]| horizon_three(w);
    let raw_b = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut other).unwrap();
    assert!(!check_a.as_ref().is_for(&raw_b));
    let quotient_b = raw_b.quotient().unwrap();
    assert_eq!(wrong_exact(&quotient_b, &check_a, horizon_three, 4), (0, 0));
}

/// An edited class table is charted only after `checked`, which refuses the edit.
#[test]
fn an_edited_quotient_is_refused_before_it_can_be_charted() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    let mut quotient = raw.quotient().unwrap().into_inner();
    let start = quotient.start;
    quotient.gains[start][A] += 100;
    assert!(quotient.verify(&raw).is_err());
    assert!(quotient.checked(&raw).is_err());
    // An unedited table that left its certificate is charted again after `checked`.
    let plain = raw.quotient().unwrap().into_inner();
    assert!(plain.checked(&raw).is_ok());
}

/// A probe naming a symbol outside the alphabet is refused, not a panic.
#[test]
fn a_probe_outside_the_alphabet_is_refused_by_verify() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    let mut quotient = raw.quotient().unwrap().into_inner();
    quotient.probes.push(vec![99]);
    let outcome = catch_unwind(AssertUnwindSafe(|| quotient.verify(&raw)));
    assert!(
        matches!(
            outcome,
            Ok(Err(zeno_adp::state_discovery::Error::SymbolOutOfRange {
                symbol: 99
            }))
        ),
        "verify must return an error"
    );
}

/// Witness replays on a symbol or state outside range refuse instead of panicking.
#[test]
fn replays_of_witnesses_outside_the_alphabet_are_refused() {
    use zeno_adp::state_discovery::{Refusal, Violation};
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let observer = Observer::last_symbols(4, 2).unwrap();
    let raw = RawModel::read(observer.clone(), &mut scorer).unwrap();
    let refusal = Refusal {
        states: [0, 1],
        probe: vec![99],
        gains: [0, 1],
    };
    let a = catch_unwind(AssertUnwindSafe(|| refusal.replay(&raw)));
    let far = Refusal {
        states: [0, 10_000],
        probe: vec![0],
        gains: [0, 1],
    };
    let b = catch_unwind(AssertUnwindSafe(|| far.replay(&raw)));
    let violation = Violation {
        word: vec![99],
        access: vec![],
        symbol: 0,
        gains: [0, 1],
        checked_length: 8,
    };
    let mut again = |w: &[Symbol]| w.len() as i64;
    let c = catch_unwind(AssertUnwindSafe(|| violation.replay(&observer, &mut again)));
    let symbol = Violation {
        word: vec![],
        access: vec![],
        symbol: 99,
        gains: [0, 1],
        checked_length: 8,
    };
    let d = catch_unwind(AssertUnwindSafe(|| symbol.replay(&observer, &mut again)));
    assert!(a.is_ok_and(|r| r.is_err()));
    assert!(b.is_ok_and(|r| r.is_err()));
    assert!(c.is_ok_and(|r| r.is_err()));
    assert!(d.is_ok_and(|r| r.is_err()));
}

/// The guide's detection statement holds for last-k observers. For other observers a
/// passed short check says less: a parity observer and a 1-local scorer pass a check of
/// length two and fail one of length three.
#[test]
fn a_one_local_scorer_passes_a_length_two_check_of_a_parity_observer() {
    let mut scorer = |w: &[Symbol]| {
        if w.is_empty() {
            0
        } else {
            5 + (w.len() as i64 - 1)
        }
    };
    let parity = Observer::new(2, 0, vec![vec![1, 1], vec![0, 0]]).unwrap();
    let mut raw = RawModel::read(parity, &mut scorer).unwrap();
    assert!(raw.check(&mut scorer, 2).is_ok());
    assert!(raw.check(&mut scorer, 3).is_err());
    assert_ne!(raw.score(&[0, 0, 0]), i128::from(scorer(&[0, 0, 0])));
}

/// A state limit the budget program never exceeds on this chart and budget.
fn bound(chart: &Chart<Step>, budget: &[BigUint]) -> usize {
    usize::try_from(state_bound(chart, budget)).expect("the bound fits in usize")
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn range(&mut self, low: i64, high: i64) -> i64 {
        low + self.below((high - low) as u64) as i64
    }
}

/// An irregular plan chart: cells with no rule, steps into dead cells, repeated
/// rules, zero credits, finishes beside steps, cells above the root.
fn irregular_plan(rng: &mut Rng, worlds: usize) -> Chart<Step> {
    let size = 2 + rng.below(6) as usize;
    let mut cells: Vec<Vec<Rule<Step>>> = Vec::new();
    for cell in 0..size {
        let mut rules = Vec::new();
        let count = if cell == 0 {
            1 + rng.below(3)
        } else {
            rng.below(5)
        };
        for _ in 0..count {
            let costs: Vec<i64> = (0..worlds).map(|_| rng.range(-2, 3)).collect();
            let credit = if rng.below(3) == 0 { 0 } else { rng.below(3) };
            let rule = if cell == 0 || rng.below(3) == 0 {
                Step::finish(costs, credit)
            } else {
                Step::to(costs, credit, rng.below(cell as u64) as usize)
            };
            if rng.below(5) == 0 {
                rules.push(rule.clone());
            }
            rules.push(rule);
        }
        cells.push(rules);
    }
    let root = size - 1 - rng.below(2).min(size as u64 - 1) as usize;
    Chart::new(cells, root).unwrap()
}

fn all_plans(chart: &Chart<Step>, worlds: usize) -> Vec<(Rules, Vec<i64>)> {
    fn go(
        chart: &Chart<Step>,
        cell: usize,
        rules: &mut Rules,
        cost: &mut Vec<i64>,
        out: &mut Vec<(Rules, Vec<i64>)>,
    ) {
        for (index, rule) in chart.cells()[cell].iter().enumerate() {
            rules.push((cell, index));
            for (total, c) in cost.iter_mut().zip(&rule.operator.costs) {
                *total += c;
            }
            match rule.children.first() {
                Some(&child) => go(chart, child, rules, cost, out),
                None => out.push((rules.clone(), cost.clone())),
            }
            for (total, c) in cost.iter_mut().zip(&rule.operator.costs) {
                *total -= c;
            }
            rules.pop();
        }
    }
    let mut out = Vec::new();
    go(
        chart,
        chart.root(),
        &mut Vec::new(),
        &mut vec![0; worlds],
        &mut out,
    );
    out
}

/// Greatest credit, number of prefixes with it, and the first one, over every prefix
/// of every plan whose cheapest extension is within budget in every world.
fn brute_prefix(
    chart: &Chart<Step>,
    worlds: usize,
    budget: &[i64],
) -> Option<(u128, usize, Rules)> {
    let plans = all_plans(chart, worlds);
    if plans.is_empty() {
        return None;
    }
    let optimum: Vec<i64> = (0..worlds)
        .map(|w| plans.iter().map(|p| p.1[w]).min().unwrap())
        .collect();
    let mut prefixes = BTreeSet::new();
    for (rules, _) in &plans {
        for length in 0..=rules.len() {
            prefixes.insert(rules[..length].to_vec());
        }
    }
    let mut best = 0u128;
    let mut winners: Vec<Rules> = Vec::new();
    for prefix in prefixes {
        let within = (0..worlds).all(|w| {
            let cheapest = plans
                .iter()
                .filter(|p| p.0.starts_with(&prefix))
                .map(|p| p.1[w])
                .min()
                .unwrap();
            cheapest - optimum[w] <= budget[w]
        });
        if !within {
            continue;
        }
        let credit: u128 = prefix
            .iter()
            .map(|&(c, r)| u128::from(chart.cells()[c][r].operator.credit))
            .sum();
        if winners.is_empty() || credit > best {
            best = credit;
            winners.clear();
        }
        if credit == best {
            winners.push(prefix);
        }
    }
    let count = winners.len();
    Some((best, count, winners.into_iter().min().unwrap()))
}

#[test]
fn robust_prefixes_match_enumeration_on_irregular_charts() {
    let mut rng = Rng(0xFAB1E);
    let (mut cases, mut no_plan, mut zero_wrong, mut budget_wrong) = (0, 0, 0, 0);
    for _ in 0..4000 {
        let worlds = 1 + rng.below(3) as usize;
        let chart = irregular_plan(&mut rng, worlds);
        let zero = vec![0i64; worlds];
        let Some((best, count, first)) = brute_prefix(&chart, worlds, &zero) else {
            assert!(zero_regret(&chart, worlds).is_err());
            no_plan += 1;
            continue;
        };
        cases += 1;
        let answer = zero_regret(&chart, worlds).unwrap().into_inner();
        answer.verify(&chart, worlds).unwrap();
        if answer.best_credit(chart.root()) != best
            || *answer.count(chart.root()) != BigUint::from(count)
            || answer.prefix != first
        {
            zero_wrong += 1;
            println!("zero-regret disagreement: {chart:?}");
        }
        let budget: Vec<i64> = (0..worlds).map(|_| rng.below(4) as i64).collect();
        let (best, count, first) = brute_prefix(&chart, worlds, &budget).unwrap();
        let big: Vec<BigUint> = budget.iter().map(|&b| BigUint::from(b as u64)).collect();
        let within = within_budget(&chart, worlds, &big, bound(&chart, &big))
            .unwrap()
            .into_inner();
        within.verify(&chart, worlds, bound(&chart, &big)).unwrap();
        if within.best != best || within.count != BigUint::from(count) || within.prefix != first {
            budget_wrong += 1;
            println!("budget disagreement: {chart:?} budget {budget:?}");
        }
    }
    println!("robust-prefix irregular: {cases} charts with a plan, {no_plan} without, zero-regret disagreements {zero_wrong}, budget disagreements {budget_wrong}");
    assert_eq!((zero_wrong, budget_wrong), (0, 0));
}

/// An irregular ranked chart: cells with no rule, rules over empty cells, repeated rules.
fn irregular_chart(rng: &mut Rng, models: usize) -> Chart<Costed> {
    let size = 2 + rng.below(5) as usize;
    let mut cells: Vec<Vec<Rule<Costed>>> = Vec::new();
    for cell in 0..size {
        let mut rules = Vec::new();
        let count = if cell == 0 {
            rng.below(3)
        } else {
            rng.below(4)
        };
        for _ in 0..count {
            let costs: Vec<i64> = (0..models).map(|_| rng.range(-1, 2)).collect();
            let arity = if cell == 0 { 0 } else { rng.below(3) };
            let children: Vec<usize> = (0..arity)
                .map(|_| rng.below(cell as u64) as usize)
                .collect();
            let rule = Costed::rule(costs, children);
            if rng.below(5) == 0 {
                rules.push(rule.clone());
            }
            rules.push(rule);
        }
        cells.push(rules);
    }
    Chart::new(cells, size - 1).unwrap()
}

/// A derivation as (preorder of `(cell, rule)`, cost per model).
type Derivation = (Vec<(usize, usize)>, Vec<i64>);

/// Every derivation of a cell as (preorder, cost per model), rules in cell order and
/// the first child most significant.
fn derivations(
    chart: &Chart<Costed>,
    cell: usize,
    models: usize,
    cap: usize,
) -> Option<Vec<Derivation>> {
    let mut out = Vec::new();
    for (index, rule) in chart.cells()[cell].iter().enumerate() {
        let mut partial = vec![(vec![(cell, index)], rule.operator.costs.clone())];
        for &child in &rule.children {
            let below = derivations(chart, child, models, cap)?;
            let mut next = Vec::new();
            for (nodes, cost) in &partial {
                for (more, extra) in &below {
                    let mut joined = nodes.clone();
                    joined.extend(more);
                    next.push((joined, cost.iter().zip(extra).map(|(a, b)| a + b).collect()));
                }
            }
            partial = next;
            if partial.len() > cap {
                return None;
            }
        }
        out.extend(partial);
        if out.len() > cap {
            return None;
        }
    }
    let _ = models;
    Some(out)
}

#[test]
fn common_optima_match_enumeration_on_irregular_charts() {
    let mut rng = Rng(0xC0FFEE);
    let (mut cases, mut witnesses, mut wrong) = (0, 0, 0);
    for _ in 0..3000 {
        let models = 1 + rng.below(3) as usize;
        let chart = irregular_chart(&mut rng, models);
        let Some(all) = derivations(&chart, chart.root(), models, 3000) else {
            continue;
        };
        for mask in 1u32..(1 << models) {
            let chosen: Vec<usize> = (0..models).filter(|m| mask >> m & 1 == 1).collect();
            let selection = ModelSet::new(chosen.clone(), models).unwrap();
            let answer = common(&chart, models, &selection).unwrap().into_inner();
            answer.verify(&chart, models).unwrap();
            let expected: Vec<_> = all
                .iter()
                .filter(|(_, cost)| {
                    chosen
                        .iter()
                        .all(|&m| all.iter().all(|(_, other)| cost[m] <= other[m]))
                })
                .collect();
            cases += 1;
            if *answer.count() != BigUint::from(expected.len()) {
                wrong += 1;
                println!("common count disagreement: {chart:?} {chosen:?}");
                continue;
            }
            for (rank, (nodes, cost)) in expected.iter().enumerate() {
                let witness = answer
                    .witness(&chart, &BigUint::from(rank))
                    .unwrap()
                    .unwrap();
                answer.verify_witness(&chart, &witness).unwrap();
                let costs: Vec<BigInt> = chosen.iter().map(|&m| BigInt::from(cost[m])).collect();
                witnesses += 1;
                if &witness.preorder != nodes || witness.costs != costs {
                    wrong += 1;
                    println!("common witness disagreement: {chart:?} {chosen:?} rank {rank}");
                }
            }
            assert!(answer
                .witness(&chart, &BigUint::from(expected.len()))
                .unwrap()
                .is_none());
        }
    }
    println!("common irregular: {cases} (chart, selection) cases, {witnesses} ranked witnesses, disagreements {wrong}");
    assert_eq!(wrong, 0);
}

/// The ordered list of best words of a state chart, up to a cap.
fn ranked_words<C>(
    chart: &zeno_adp::state_discovery::StateChart<C>,
    cap: usize,
) -> (BigUint, Vec<Vec<Symbol>>) {
    let answer = common(chart.chart(), 1, &ModelSet::all(1).unwrap())
        .unwrap()
        .into_inner();
    let mut words = Vec::new();
    let mut rank = BigUint::ZERO;
    while &rank < answer.count() && words.len() < cap {
        let witness = answer.witness(chart.chart(), &rank).unwrap().unwrap();
        words.push(
            witness
                .preorder
                .iter()
                .filter_map(|&(cell, rule)| chart.chart().cells()[cell][rule].operator.symbol)
                .collect(),
        );
        rank += 1u32;
    }
    (answer.count().clone(), words)
}

/// The chart over classes lists the same best words, in the same order, as the chart
/// over raw states: the quotient is an exact replay of the raw chart's scored list.
#[test]
fn the_quotient_chart_lists_the_raw_charts_best_words_in_order() {
    let scorers: [fn(&[Symbol]) -> i64; 2] = [two_symbol_score, horizon_three];
    let (mut pairs, mut words_compared, mut differ) = (0, 0, 0);
    for (index, scorer) in scorers.iter().enumerate() {
        let mut ask = |w: &[Symbol]| scorer(w);
        let raw = RawModel::read(Observer::last_symbols(4, 2 + index).unwrap(), &mut ask).unwrap();
        let quotient = raw.quotient().unwrap();
        for x in &binary_words(4) {
            for y in &binary_words(4) {
                let geometry = Alignment { x, y };
                let small = quotient.chart(&geometry, Sense::Maximize).unwrap();
                let large = raw.raw_chart(&geometry, Sense::Maximize).unwrap();
                let (a, b) = (ranked_words(&small, 400), ranked_words(&large, 400));
                pairs += 1;
                words_compared += a.1.len();
                if a != b {
                    differ += 1;
                }
            }
        }
    }
    println!("quotient-order: {pairs} pairs, {words_compared} ranked best words compared, {differ} pairs differ");
    assert_eq!(differ, 0);
}

/// Edit one field of a certificate at random. An edited certificate that still
/// verifies must still be right against enumeration (for example another optimal
/// completion); anything else is an accepted wrong certificate.
#[test]
fn edited_robust_prefix_certificates_are_refused_or_still_right() {
    let mut rng = Rng(0x7A3D_EE11);
    let (mut edits, mut refused, mut accepted_right, mut accepted_wrong) = (0, 0, 0, 0);
    for _ in 0..1500 {
        let worlds = 1 + rng.below(3) as usize;
        let chart = irregular_plan(&mut rng, worlds);
        let Ok(answer) = zero_regret(&chart, worlds) else {
            continue;
        };
        let answer = answer.into_inner();
        let cells = chart.cells().len();
        for _ in 0..6 {
            let mut edited = answer.clone();
            let cell = rng.below(cells as u64) as usize;
            match rng.below(8) {
                0 => edited.credit[cell] += 1,
                1 => edited.credit[cell] = edited.credit[cell].saturating_sub(1),
                2 => edited.counts[cell] += 1u32,
                3 => edited.reach[cell] = !edited.reach[cell],
                4 => {
                    edited.prefix.pop();
                }
                5 => {
                    let rules = chart.cells()[cell].len().max(1) as u64;
                    edited.prefix.push((cell, rng.below(rules) as usize));
                }
                6 => {
                    let world = rng.below(worlds as u64) as usize;
                    if let Some(last) = edited.completions[world].last_mut() {
                        last.1 = (last.1 + 1) % chart.cells()[last.0].len().max(1);
                    }
                }
                _ => {
                    edited.common_plan = match edited.common_plan {
                        Some(_) => None,
                        None => Some(edited.completions[0].clone()),
                    }
                }
            }
            if edited == answer {
                continue;
            }
            edits += 1;
            if edited.verify(&chart, worlds).is_err() {
                refused += 1;
                continue;
            }
            // Accepted: every answer field must still equal enumeration, and each
            // completion must be an optimal plan of its world that extends the prefix.
            let (best, count, first) = brute_prefix(&chart, worlds, &vec![0; worlds]).unwrap();
            let plans = all_plans(&chart, worlds);
            let completions_right = (0..worlds).all(|w| {
                let optimum = plans.iter().map(|p| p.1[w]).min().unwrap();
                plans
                    .iter()
                    .any(|p| p.0 == edited.completions[w] && p.1[w] == optimum)
                    && edited.completions[w].starts_with(&edited.prefix)
            });
            let common_right = edited.common_plan == answer.common_plan;
            if edited.best_credit(chart.root()) == best
                && *edited.count(chart.root()) == BigUint::from(count)
                && edited.prefix == first
                && edited.credit == answer.credit
                && edited.counts == answer.counts
                && edited.reach == answer.reach
                && completions_right
                && common_right
            {
                accepted_right += 1;
            } else {
                accepted_wrong += 1;
                println!("accepted wrong zero-regret certificate: {chart:?}");
            }
        }
    }
    println!("zero-regret edits: {edits} edited certificates, {refused} refused, {accepted_right} accepted and still right, {accepted_wrong} accepted and wrong");
    assert_eq!(accepted_wrong, 0);
    assert!(edits > 1000 && refused > 0);
}

#[test]
fn edited_budget_and_common_certificates_are_refused_or_still_right() {
    let mut rng = Rng(0x51CE_0B0B);
    let (mut edits, mut refused, mut accepted_right, mut accepted_wrong) = (0, 0, 0, 0);
    for _ in 0..1500 {
        let worlds = 1 + rng.below(3) as usize;
        let chart = irregular_plan(&mut rng, worlds);
        let budget: Vec<i64> = (0..worlds).map(|_| rng.below(4) as i64).collect();
        let big: Vec<BigUint> = budget.iter().map(|&b| BigUint::from(b as u64)).collect();
        let Ok(answer) = within_budget(&chart, worlds, &big, bound(&chart, &big)) else {
            continue;
        };
        let answer = answer.into_inner();
        for _ in 0..5 {
            let mut edited = answer.clone();
            let world = rng.below(worlds as u64) as usize;
            match rng.below(6) {
                0 => edited.best += 1,
                1 => edited.count += 1u32,
                2 => edited.regret[world] += 1,
                3 => {
                    edited.prefix.pop();
                }
                4 => edited.budget[world] += 1u32,
                _ => {
                    if let Some(last) = edited.completions[world].last_mut() {
                        last.1 = (last.1 + 1) % chart.cells()[last.0].len().max(1);
                    }
                }
            }
            if edited == answer {
                continue;
            }
            edits += 1;
            if edited
                .verify(&chart, worlds, bound(&chart, &edited.budget))
                .is_err()
            {
                refused += 1;
                continue;
            }
            // Accepted: it must be right for the budget written inside it.
            let own: Vec<i64> = edited
                .budget
                .iter()
                .map(|b| i64::try_from(b.clone()).unwrap())
                .collect();
            let (best, count, first) = brute_prefix(&chart, worlds, &own).unwrap();
            let plans = all_plans(&chart, worlds);
            let completions_right = (0..worlds).all(|w| {
                let optimum = plans.iter().map(|p| p.1[w]).min().unwrap();
                plans
                    .iter()
                    .any(|p| p.0 == edited.completions[w] && p.1[w] - optimum <= own[w])
                    && edited.completions[w].starts_with(&edited.prefix)
            });
            if edited.best == best
                && edited.count == BigUint::from(count)
                && edited.prefix == first
                && completions_right
            {
                accepted_right += 1;
            } else {
                accepted_wrong += 1;
                println!("accepted wrong budget certificate: {chart:?} {own:?}");
            }
        }
    }
    println!("budget edits: {edits} edited certificates, {refused} refused, {accepted_right} accepted and still right for their own budget, {accepted_wrong} accepted and wrong");
    assert_eq!(accepted_wrong, 0);

    let (mut edits, mut refused, mut accepted) = (0, 0, 0);
    for _ in 0..1500 {
        let models = 1 + rng.below(3) as usize;
        let chart = irregular_chart(&mut rng, models);
        let selection = ModelSet::all(models).unwrap();
        let answer = common(&chart, models, &selection).unwrap().into_inner();
        let cells = chart.cells().len();
        for _ in 0..4 {
            let mut edited = answer.clone();
            let cell = rng.below(cells as u64) as usize;
            match rng.below(4) {
                0 => edited.counts[cell] += 1u32,
                1 => {
                    let position = rng.below(models as u64) as usize;
                    edited.optima[cell][position] = match edited.optima[cell][position].take() {
                        Some(value) => Some(value + 1),
                        None => Some(BigInt::ZERO),
                    };
                }
                2 => edited.root = cell,
                _ => {
                    let position = rng.below(models as u64) as usize;
                    edited.optima[cell][position] = None;
                }
            }
            if edited == answer {
                continue;
            }
            edits += 1;
            if edited.verify(&chart, models).is_err() {
                refused += 1;
            } else {
                accepted += 1;
                println!("accepted edited common certificate: {chart:?}");
            }
        }
    }
    println!("common edits: {edits} edited certificates, {refused} refused, {accepted} accepted");
    assert_eq!(accepted, 0);
}

/// A certificate answers the question written inside it: `verify_for` checks that it
/// is the question asked.
#[test]
fn a_certificate_for_another_budget_is_refused_by_verify_for() {
    let chart = Chart::new(
        vec![
            vec![Step::finish([0, 5], 1), Step::finish([5, 0], 1)],
            vec![Step::to([0, 0], 1, 0)],
        ],
        1,
    )
    .unwrap();
    let asked = [BigUint::from(0u32), BigUint::from(0u32)];
    let loose = [BigUint::from(9u32), BigUint::from(9u32)];
    let limit = bound(&chart, &loose);
    let strict = within_budget(&chart, 2, &asked, limit)
        .unwrap()
        .into_inner();
    let other = within_budget(&chart, 2, &loose, limit)
        .unwrap()
        .into_inner();
    assert_ne!(strict.best, other.best);
    assert!(other.verify(&chart, 2, limit).is_ok());
    assert_eq!(
        other.verify_for(&chart, 2, &asked, limit),
        Err(zeno_adp::robust_prefix::Error::Question)
    );
    assert!(strict.verify_for(&chart, 2, &asked, limit).is_ok());
    let selection = ModelSet::all(2).unwrap();
    let costed = Chart::new(
        vec![vec![Costed::rule([0, 1], []), Costed::rule([1, 0], [])]],
        0,
    )
    .unwrap();
    let answer = common(&costed, 2, &selection).unwrap().into_inner();
    assert!(answer.verify_for(&costed, 2, &selection).is_ok());
    assert!(answer
        .verify_for(&costed, 2, &ModelSet::new([0], 2).unwrap())
        .is_err());
}

/// The budget program fails closed past the caller's state limit, and never under
/// `state_bound`.
#[test]
fn the_budget_program_fails_closed_past_the_callers_limit() {
    use zeno_adp::robust_prefix::Error;
    let chart = Chart::new(
        vec![
            vec![Step::finish([0, 0], 0)],
            vec![Step::to([1, 2], 3, 0), Step::to([0, 0], 0, 0)],
            vec![Step::to([2, 1], 3, 1), Step::to([0, 0], 0, 1)],
        ],
        2,
    )
    .unwrap();
    let budget = [BigUint::from(3u32), BigUint::from(3u32)];
    assert_eq!(
        within_budget(&chart, 2, &budget, 1),
        Err(Error::StateLimit { limit: 1 })
    );
    assert_eq!(state_bound(&chart, &budget), BigUint::from(3u32 * 16));
    let answer = within_budget(&chart, 2, &budget, bound(&chart, &budget)).unwrap();
    assert_eq!(answer.as_ref().best, 6);
}

#[test]
fn the_budget_program_needs_every_state_of_a_tight_bound() {
    use zeno_adp::robust_prefix::Error;

    // A zero budget permits just one remaining budget per cell, and this chain
    // reaches all three cells. The forward verifier keeps at most two labels
    // at once, so it cannot mask an off-by-one in the budget program's memo.
    let chart = Chart::new(
        vec![
            vec![Step::finish([0], 1)],
            vec![Step::to([0], 1, 0)],
            vec![Step::to([0], 1, 1)],
        ],
        2,
    )
    .unwrap();
    let budget = [BigUint::ZERO];
    let need = bound(&chart, &budget);
    assert_eq!(need, chart.cells().len());
    let below_need = need - 1;
    assert_eq!(
        within_budget(&chart, 1, &budget, below_need),
        Err(Error::StateLimit { limit: below_need })
    );
    let answer = within_budget(&chart, 1, &budget, need).unwrap();
    assert_eq!(answer.as_ref().best, 3);
    answer
        .as_ref()
        .verify_for(&chart, 1, &budget, need)
        .unwrap();
}

/// A check compares the model with the scorer it is given, not with the answers the
/// read cached from another scorer. Each of these scorers differs from the one the
/// raw model was read from on a word the read asked, so the check must refuse.
#[test]
fn a_check_with_another_scorer_on_the_same_raw_model_is_refused() {
    let unrelated: fn(&[Symbol]) -> i64 = |w| 100 * w.len() as i64 - horizon_three(w);
    let based = |w: &[Symbol]| two_symbol_score(w) + if w.is_empty() { 7 } else { 0 };
    let read_word = |w: &[Symbol]| two_symbol_score(w) + if w == [A] { 5 } else { 0 };
    let cases = [
        ("unrelated", unrelated, 3, 1),
        ("empty word +7", based, 8, 4),
        ("MATCH +5", read_word, 8, 4),
    ];
    let mut wrong_answers = Vec::new();
    let mut errors = Vec::new();
    for (name, truth, length, max_length) in cases {
        let mut raw =
            RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut two_symbol_score).unwrap();
        let mut calls = 0;
        let check = raw.check(
            &mut |word| {
                calls += 1;
                truth(word)
            },
            length,
        );
        let (wrong, exact) = match &check {
            Ok(check) => wrong_exact(&raw.quotient().unwrap(), check, truth, max_length),
            Err(_) => (0, 0),
        };
        println!("{name}: {calls} calls, {wrong} wrong of {exact} Exact answers");
        wrong_answers.push(wrong);
        errors.push(check.err());
    }
    assert_eq!(wrong_answers, [0, 0, 0]);
    assert!(matches!(errors[0], Some(Error::ScorerDisagrees { .. })));
    assert_eq!(
        errors[1],
        Some(Error::ScorerDisagrees {
            word: vec![],
            read: 0,
            checked: 7,
        }),
    );
    assert_eq!(
        errors[2],
        Some(Error::ScorerDisagrees {
            word: vec![A],
            read: two_symbol_score(&[A]),
            checked: two_symbol_score(&[A]) + 5,
        }),
    );

    // A different scorer that agrees within the length can still be checked.
    let mut raw =
        RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut two_symbol_score).unwrap();
    let check = raw.check(&mut horizon_three, 3).unwrap();
    let quotient = raw.quotient().unwrap();
    assert_eq!(wrong_exact(&quotient, &check, horizon_three, 1), (0, 9));
}

/// A check asks its scorer for every word up to its length, the empty word and the
/// words the read asked included, and the read's own count is unchanged.
#[test]
fn a_check_asks_its_scorer_for_every_word_up_to_its_length() {
    let mut honest = |w: &[Symbol]| two_symbol_score(w);
    let mut raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut honest).unwrap();
    assert_eq!(raw.scorer_calls(), 85);
    let mut calls = 0usize;
    let mut counted = |w: &[Symbol]| {
        calls += 1;
        two_symbol_score(w)
    };
    let check = raw.check(&mut counted, 8).unwrap();
    let every_word = (4usize.pow(9) - 1) / 3;
    assert_eq!(calls, every_word);
    assert_eq!(check.as_ref().words_checked(), every_word as u64);
    assert_eq!(check.as_ref().scorer_calls(), every_word);
    assert_eq!(raw.scorer_calls(), 85);

    let mut empty_calls = 0;
    let check = raw
        .check(
            &mut |word| {
                assert!(word.is_empty());
                empty_calls += 1;
                two_symbol_score(word)
            },
            0,
        )
        .unwrap();
    assert_eq!(empty_calls, 1);
    assert_eq!(check.as_ref().scorer_calls(), empty_calls);
    assert_eq!(raw.scorer_calls(), 85);
}
