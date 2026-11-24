use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};
use zeno_adp::common_optimum::{common, ModelSet};
use zeno_adp::robust_prefix::{
    regret, state_bound, within_budget, zero_regret, Error, Rules, Step,
};
use zeno_adp::{Chart, Rule};

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

/// Every plan from the root as (rules, cost per world), in rule order.
fn plans(chart: &Chart<Step>, worlds: usize) -> Vec<(Rules, Vec<i64>)> {
    let mut out = Vec::new();
    let mut stack = vec![(chart.root(), Vec::new(), vec![0i64; worlds])];
    while let Some((cell, rules, cost)) = stack.pop() {
        for (index, rule) in chart.cells()[cell].iter().enumerate().rev() {
            let mut next = rules.clone();
            next.push((cell, index));
            let total: Vec<i64> = cost
                .iter()
                .zip(&rule.operator.costs)
                .map(|(a, b)| a + b)
                .collect();
            match rule.children.first() {
                Some(&child) => stack.push((child, next, total)),
                None => out.push((next, total)),
            }
        }
    }
    out.sort();
    out
}

struct Brute {
    best: u128,
    count: usize,
    first: Rules,
}

/// Brute force over every prefix of every plan: a prefix is allowed when each
/// world's cheapest plan extending it is within that world's budget.
fn brute(chart: &Chart<Step>, worlds: usize, budget: &[i64]) -> Brute {
    let all = plans(chart, worlds);
    let optimum: Vec<i64> = (0..worlds)
        .map(|w| all.iter().map(|p| p.1[w]).min().unwrap())
        .collect();
    let mut prefixes = BTreeSet::new();
    for (rules, _) in &all {
        for length in 0..=rules.len() {
            prefixes.insert(rules[..length].to_vec());
        }
    }
    let mut best = 0u128;
    let mut winners: Vec<Rules> = Vec::new();
    for prefix in prefixes {
        let allowed = (0..worlds).all(|w| {
            let cheapest = all
                .iter()
                .filter(|(rules, _)| rules.starts_with(&prefix))
                .map(|p| p.1[w])
                .min()
                .unwrap();
            cheapest - optimum[w] <= budget[w]
        });
        if !allowed {
            continue;
        }
        let credit: u128 = prefix
            .iter()
            .map(|&(cell, rule)| u128::from(chart.cells()[cell][rule].operator.credit))
            .sum();
        if credit > best || winners.is_empty() {
            best = credit;
            winners.clear();
        }
        if credit == best {
            winners.push(prefix);
        }
    }
    Brute {
        best,
        count: winners.len(),
        first: winners.into_iter().min().unwrap(),
    }
}

/// A random plan tree: steps to children, and finish rules at
/// depth zero carrying the leaf cost.
fn random_tree(rng: &mut Rng, worlds: usize, depth: usize) -> Chart<Step> {
    fn grow(rng: &mut Rng, worlds: usize, depth: usize, cells: &mut Vec<Vec<Rule<Step>>>) -> usize {
        let mut rules = Vec::new();
        for _ in 0..2 + rng.below(2) {
            let cost: Vec<i64> = (0..worlds).map(|_| rng.range(-1, 3)).collect();
            let credit = 1 + rng.below(5);
            if depth == 1 {
                let leaf: Vec<i64> = cost.iter().map(|c| c + rng.range(-2, 5)).collect();
                rules.push(Step::finish(leaf, credit));
            } else {
                let child = grow(rng, worlds, depth - 1, cells);
                rules.push(Step::to(cost, credit, child));
            }
        }
        cells.push(rules);
        cells.len() - 1
    }
    let mut cells = Vec::new();
    let root = grow(rng, worlds, depth, &mut cells);
    Chart::new(cells, root).unwrap()
}

/// A random layered plan graph with shared children and occasional early finishes.
fn random_dag(rng: &mut Rng, worlds: usize) -> Chart<Step> {
    let layers = 3 + rng.below(3) as usize;
    let mut cells: Vec<Vec<Rule<Step>>> = Vec::new();
    let mut below: Vec<usize> = Vec::new();
    for layer in 0..layers {
        let width = if layer + 1 == layers {
            1
        } else {
            1 + rng.below(3) as usize
        };
        let mut here = Vec::new();
        for _ in 0..width {
            let mut rules = Vec::new();
            let finish_here = below.is_empty() || rng.below(4) == 0;
            if finish_here {
                let cost: Vec<i64> = (0..worlds).map(|_| rng.range(-2, 5)).collect();
                rules.push(Step::finish(cost, rng.below(6)));
            }
            if !below.is_empty() {
                for _ in 0..1 + rng.below(3) {
                    let child = below[rng.below(below.len() as u64) as usize];
                    let cost: Vec<i64> = (0..worlds).map(|_| rng.range(-1, 3)).collect();
                    rules.push(Step::to(cost, rng.below(6), child));
                }
            }
            cells.push(rules);
            here.push(cells.len() - 1);
        }
        below = here;
    }
    let root = cells.len() - 1;
    Chart::new(cells, root).unwrap()
}

fn check_case(chart: &Chart<Step>, worlds: usize, budget: &[i64]) {
    let zero = brute(chart, worlds, &vec![0; worlds]);
    let answer = zero_regret(chart, worlds).unwrap();
    assert_eq!(answer.label(), "Exact");
    let answer = answer.into_inner();
    let root = chart.root();
    assert_eq!(answer.best_credit(root), zero.best);
    assert_eq!(answer.count(root), &BigUint::from(zero.count));
    assert_eq!(answer.prefix, zero.first);
    let all = plans(chart, worlds);
    for (world, plan) in answer.completions.iter().enumerate() {
        let optimum = all.iter().map(|p| p.1[world]).min().unwrap();
        let cost = all.iter().find(|p| &p.0 == plan).unwrap().1[world];
        assert_eq!(cost, optimum);
        assert!(plan.starts_with(&answer.prefix));
    }
    // A whole plan optimal in every world exists iff the common-optimum query finds one.
    let shared = common(chart, worlds, &ModelSet::all(worlds).unwrap()).unwrap();
    assert_eq!(answer.common_plan_exists(), shared.as_ref().exists());

    let limits: Vec<BigUint> = budget.iter().map(|&b| BigUint::from(b as u64)).collect();
    let tolerant = brute(chart, worlds, budget);
    let within = within_budget(chart, worlds, &limits, bound(chart, &limits))
        .unwrap()
        .into_inner();
    assert_eq!(within.best, tolerant.best);
    assert_eq!(within.count, BigUint::from(tolerant.count));
    assert_eq!(within.prefix, tolerant.first);
    for (world, plan) in within.completions.iter().enumerate() {
        let optimum = all.iter().map(|p| p.1[world]).min().unwrap();
        let cost = all.iter().find(|p| &p.0 == plan).unwrap().1[world];
        assert!(cost - optimum <= budget[world]);
    }
}

#[test]
fn zero_regret_and_budgets_match_enumeration_on_trees_and_graphs() {
    let mut rng = Rng(0x0B05_7001);
    for case in 0..400 {
        let worlds = 2 + rng.below(4) as usize;
        let chart = if case % 2 == 0 {
            let depth = 1 + rng.below(4) as usize;
            random_tree(&mut rng, worlds, depth)
        } else {
            random_dag(&mut rng, worlds)
        };
        let budget: Vec<i64> = (0..worlds).map(|_| rng.range(0, 4)).collect();
        check_case(&chart, worlds, &budget);
    }
}

/// A three-way tie: each pair of worlds shares a whole optimum,
/// all three do not, and one arbitrary witness per world would hide the prefix.
fn three_way() -> Chart<Step> {
    let z = [0, 0, 0];
    Chart::new(
        vec![
            // 0 dispatch: Hash-left, Hash-right, Broadcast (leaf costs folded in)
            vec![
                Step::finish([0, 0, 2], 2),
                Step::finish([2, 0, 0], 2),
                Step::finish([0, 2, 0], 2),
            ],
            // 1 scan: push the status predicate
            vec![Step::to(z, 2, 0)],
            // 2 root: three special routes and the scan
            vec![
                Step::finish([0, 8, 8], 1),
                Step::finish([8, 0, 8], 1),
                Step::finish([8, 8, 0], 1),
                Step::to(z, 3, 1),
            ],
        ],
        2,
    )
    .unwrap()
}

#[test]
fn three_way_tie_and_canonical_tie_controls() {
    let chart = three_way();
    let answer = zero_regret(&chart, 3).unwrap().into_inner();
    assert_eq!(answer.best_credit(2), 5);
    assert_eq!(answer.prefix, vec![(2, 3), (1, 0)]);
    assert!(!answer.common_plan_exists());
    for pair in [[0, 1], [0, 2], [1, 2]] {
        assert!(common(&chart, 3, &ModelSet::new(pair, 3).unwrap())
            .unwrap()
            .as_ref()
            .exists());
    }
    assert!(!common(&chart, 3, &ModelSet::all(3).unwrap())
        .unwrap()
        .as_ref()
        .exists());
    // The first optimal plan of each world starts with a different special route,
    // so a common prefix of canonical witnesses is empty.
    let all = plans(&chart, 3);
    let firsts: Vec<&Rules> = (0..3)
        .map(|w| {
            let best = all.iter().map(|p| p.1[w]).min().unwrap();
            &all.iter().find(|p| p.1[w] == best).unwrap().0
        })
        .collect();
    assert_eq!(firsts[0][0], (2, 0));
    assert_eq!(firsts[1][0], (2, 1));
    assert_eq!(firsts[2][0], (2, 2));
}

#[test]
fn average_objective_control() {
    // Both worlds have optimum 0; the average favours the tempting action, whose
    // world-1 regret is 2.
    let chart = Chart::new(
        vec![
            vec![Step::finish([0, 4], 1), Step::finish([4, 0], 1)],
            vec![Step::to([0, 0], 1, 0), Step::finish([0, 2], 9)],
        ],
        1,
    )
    .unwrap();
    let answer = zero_regret(&chart, 2).unwrap().into_inner();
    assert_eq!(answer.prefix, vec![(1, 0)]);
    assert_eq!(answer.best_credit(1), 1);
    let all = plans(&chart, 2);
    let average = all.iter().min_by_key(|p| p.1.iter().sum::<i64>()).unwrap();
    assert_eq!(average.0, vec![(1, 1)]);
    assert_eq!(
        regret(&chart, 2, &average.0).unwrap(),
        vec![BigInt::ZERO, BigInt::from(2)]
    );
}

#[test]
fn two_step_budget_control() {
    // Cell 0 is after the first step: take the second step (to a leaf) or exit.
    let chart = Chart::new(
        vec![
            vec![Step::finish([2, 2], 4), Step::finish([0, 0], 1)],
            vec![Step::to([2, 2], 4, 0), Step::finish([0, 0], 1)],
        ],
        1,
    )
    .unwrap();
    let two = |b: u64| {
        within_budget(
            &chart,
            2,
            &[BigUint::from(b), BigUint::from(b)],
            bound(&chart, &[BigUint::from(b), BigUint::from(b)]),
        )
        .unwrap()
        .into_inner()
    };
    let tight = two(2);
    assert_eq!(tight.best, 5);
    assert_eq!(tight.prefix, vec![(1, 0), (0, 1)]);
    let loose = two(4);
    assert_eq!(loose.best, 8);
    assert_eq!(loose.prefix, vec![(1, 0), (0, 0)]);
    // Each step fits a budget of 2 alone; together they use 4 in each world.
    assert_eq!(
        regret(&chart, 2, &loose.prefix).unwrap(),
        vec![BigInt::from(4), BigInt::from(4)]
    );
}

#[test]
fn one_shared_budget_is_wrong_in_both_directions() {
    // Step slacks (3, 0) then (0, 3). Budget (2, 2).
    let unsound = Chart::new(
        vec![
            vec![Step::finish([0, 0], 0)],
            vec![Step::to([0, 3], 5, 0), Step::to([0, 0], 0, 0)],
            vec![Step::to([3, 0], 5, 1), Step::to([0, 0], 0, 1)],
        ],
        2,
    )
    .unwrap();
    let budget = [BigUint::from(2u32), BigUint::from(2u32)];
    let exact = within_budget(&unsound, 2, &budget, bound(&unsound, &budget))
        .unwrap()
        .into_inner();
    assert_eq!(exact.best, 0);
    // Charging the smallest world slack accepts both steps (charge 0), whose regret is (3, 3).
    let both = vec![(2, 0), (1, 0)];
    assert_eq!(
        regret(&unsound, 2, &both).unwrap(),
        vec![BigInt::from(3), BigInt::from(3)]
    );

    // Step slacks (2, 0) then (0, 2). Budget (2, 2): both fit per world.
    let incomplete = Chart::new(
        vec![
            vec![Step::finish([0, 0], 0)],
            vec![Step::to([0, 2], 5, 0), Step::to([0, 0], 0, 0)],
            vec![Step::to([2, 0], 5, 1), Step::to([0, 0], 0, 1)],
        ],
        2,
    )
    .unwrap();
    let exact = within_budget(&incomplete, 2, &budget, bound(&incomplete, &budget))
        .unwrap()
        .into_inner();
    assert_eq!(exact.best, 10);
    // Charging the largest world slack to one budget of 2 spends it on the first step.
    assert_eq!(
        regret(&incomplete, 2, &exact.prefix).unwrap(),
        vec![BigInt::from(2), BigInt::from(2)]
    );
}

#[test]
fn knapsack_reduces_to_a_one_world_budget_query() {
    let mut rng = Rng(0x4B4E_4150);
    for _ in 0..100 {
        let items = 1 + rng.below(8) as usize;
        let weights: Vec<i64> = (0..items).map(|_| rng.range(0, 6)).collect();
        let values: Vec<u64> = (0..items).map(|_| rng.below(9)).collect();
        let capacity = rng.range(0, 12);
        // Cell 0 finishes; cell i+1 chooses item i (slack = weight) or skips it.
        let mut cells = vec![vec![Step::finish([0], 0)]];
        for i in 0..items {
            cells.push(vec![
                Step::to([weights[i]], values[i], i),
                Step::to([0], 0, i),
            ]);
        }
        let chart = Chart::new(cells, items).unwrap();
        let answer = within_budget(
            &chart,
            1,
            &[BigUint::from(capacity as u64)],
            bound(&chart, &[BigUint::from(capacity as u64)]),
        )
        .unwrap()
        .into_inner();
        let best = (0..1u32 << items)
            .filter(|mask| {
                (0..items)
                    .filter(|i| mask >> i & 1 == 1)
                    .map(|i| weights[i])
                    .sum::<i64>()
                    <= capacity
            })
            .map(|mask| {
                (0..items)
                    .filter(|i| mask >> i & 1 == 1)
                    .map(|i| values[i])
                    .sum::<u64>()
            })
            .max()
            .unwrap();
        assert_eq!(answer.best, u128::from(best));
    }
}

#[test]
fn tampered_certificates_are_refused() {
    let chart = three_way();
    let answer = zero_regret(&chart, 3).unwrap().into_inner();
    let mut credit = answer.clone();
    credit.credit[1] += 1;
    assert_eq!(credit.verify(&chart, 3), Err(Error::Equation { cell: 1 }));
    let mut prefix = answer.clone();
    prefix.prefix = vec![(2, 0)];
    assert!(matches!(prefix.verify(&chart, 3), Err(Error::Plan(_))));
    let mut completion = answer.clone();
    completion.completions[2] = vec![(2, 3), (1, 0), (0, 0)];
    assert!(matches!(completion.verify(&chart, 3), Err(Error::Plan(_))));
    let mut count = answer;
    count.counts[2] += 1u32;
    assert_eq!(count.verify(&chart, 3), Err(Error::Equation { cell: 2 }));

    let budget = [
        BigUint::from(0u32),
        BigUint::from(0u32),
        BigUint::from(8u32),
    ];
    let within = within_budget(&chart, 3, &budget, bound(&chart, &budget))
        .unwrap()
        .into_inner();
    let mut better = within.clone();
    better.best += 1;
    assert!(matches!(
        better.verify(&chart, 3, bound(&chart, &better.budget)),
        Err(Error::Plan(_))
    ));
    // Another prefix of the same credit within budget that is not the first.
    let two = [
        BigUint::from(2u32),
        BigUint::from(2u32),
        BigUint::from(2u32),
    ];
    let tied = within_budget(&chart, 3, &two, bound(&chart, &two))
        .unwrap()
        .into_inner();
    assert_eq!((tied.best, tied.count.clone()), (7, BigUint::from(3u32)));
    assert_eq!(tied.prefix, vec![(2, 3), (1, 0), (0, 0)]);
    let mut later = tied.clone();
    later.prefix = vec![(2, 3), (1, 0), (0, 2)];
    later.regret = regret(&chart, 3, &later.prefix).unwrap();
    later.completions = vec![later.prefix.clone(); 3];
    assert_eq!(
        later.regret,
        vec![BigInt::ZERO, BigInt::from(2), BigInt::ZERO]
    );
    assert_eq!(
        later.verify(&chart, 3, bound(&chart, &later.budget)),
        Err(Error::Plan(
            "the prefix is not the first of greatest credit"
        ))
    );
    let mut more = tied;
    more.count += 1u32;
    assert_eq!(
        more.verify(&chart, 3, bound(&chart, &more.budget)),
        Err(Error::Plan(
            "the count of prefixes of greatest credit differs"
        ))
    );
}

#[test]
fn plan_charts_are_validated() {
    let branching = Chart::new(
        vec![
            vec![Step::finish([0], 0)],
            vec![Rule::new(
                Step {
                    costs: vec![0],
                    credit: 0,
                    arity: 2,
                },
                vec![0, 0],
            )],
        ],
        1,
    )
    .unwrap();
    assert_eq!(
        zero_regret(&branching, 1),
        Err(Error::Arity {
            cell: 1,
            rule: 0,
            arity: 2
        })
    );
    let stuck = Chart::new(vec![vec![], vec![Step::to([0], 1, 0)]], 1).unwrap();
    assert_eq!(zero_regret(&stuck, 1), Err(Error::NoPlan { world: 0 }));
    let chart = three_way();
    assert_eq!(
        within_budget(
            &chart,
            3,
            &[BigUint::from(1u32)],
            bound(&chart, &[BigUint::from(1u32)])
        ),
        Err(Error::BudgetLength {
            worlds: 3,
            actual: 1
        })
    );
}
