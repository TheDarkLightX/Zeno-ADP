use num_bigint::{BigInt, BigUint};
use zeno_adp::common_optimum::{
    binomial, ceil_log2, common, count_common_rescan, AnswerTable, Collision, CollisionBudget,
    Costed, Error, ModelSet, Optima, WinnerMasks,
};
use zeno_adp::{enumerate, Chart, Rule, Tree};

// The collision fixtures use at most four selected models and up to five
// declared models. Each chart needs one rule per subset plus its base rule.
const COLLISION_RULES: usize = 2 * ((1 << 4) + 1);
const COLLISION_BUDGET: CollisionBudget = CollisionBudget {
    max_rules: COLLISION_RULES,
    max_cost_entries: COLLISION_RULES * 5,
};

/// Splitmix64, so the generated charts do not depend on another crate.
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

fn random_chart(rng: &mut Rng, cells: usize, models: usize, low: i64, high: i64) -> Chart<Costed> {
    let mut rows = Vec::new();
    for cell in 0..cells {
        let mut rules = Vec::new();
        for _ in 0..1 + rng.below(4) {
            let arity = if cell == 0 { 0 } else { rng.below(3) as usize };
            let children: Vec<usize> = (0..arity)
                .map(|_| rng.below(cell as u64) as usize)
                .collect();
            let costs: Vec<i64> = (0..models).map(|_| rng.range(low, high)).collect();
            rules.push(Costed::rule(costs, children));
        }
        rows.push(rules);
    }
    Chart::new(rows, cells - 1).unwrap()
}

fn tree_cost(tree: &Tree<Costed>, model: usize) -> i128 {
    i128::from(tree.operator.costs[model])
        + tree
            .children
            .iter()
            .map(|child| tree_cost(child, model))
            .sum::<i128>()
}

/// Brute force: every root derivation in derivation order, filtered to those
/// whose cost equals the minimum in every selected model.
fn brute_common(chart: &Chart<Costed>, selection: &[usize]) -> Vec<Tree<Costed>> {
    let trees = enumerate(chart);
    let minima: Vec<Option<i128>> = selection
        .iter()
        .map(|&model| trees.iter().map(|tree| tree_cost(tree, model)).min())
        .collect();
    trees
        .into_iter()
        .filter(|tree| {
            selection
                .iter()
                .zip(&minima)
                .all(|(&model, best)| Some(tree_cost(tree, model)) == *best)
        })
        .collect()
}

fn subsets(models: usize) -> Vec<ModelSet> {
    (1..1usize << models)
        .map(|mask| ModelSet::new((0..models).filter(|m| mask >> m & 1 == 1), models).unwrap())
        .collect()
}

fn derivation_count(chart: &Chart<Costed>) -> usize {
    let mut sizes = Vec::new();
    for rules in chart.cells() {
        let total: usize = rules
            .iter()
            .map(|rule| rule.children.iter().map(|&c| sizes[c]).product::<usize>())
            .sum();
        sizes.push(total);
    }
    sizes.into_iter().max().unwrap_or(0)
}

#[test]
fn separate_minima_and_counts_cannot_answer_a_common_optimum() {
    // Both charts report minimum (0, 0) and one tie per model.
    let first = Chart::new(
        vec![vec![Costed::rule([0, 0], []), Costed::rule([1, 1], [])]],
        0,
    )
    .unwrap();
    let second = Chart::new(
        vec![vec![Costed::rule([0, 1], []), Costed::rule([1, 0], [])]],
        0,
    )
    .unwrap();
    for chart in [&first, &second] {
        for model in 0..2 {
            let single = common(chart, 2, &ModelSet::new([model], 2).unwrap())
                .unwrap()
                .into_inner();
            assert_eq!(single.root_optima(), &[Some(BigInt::ZERO)]);
            assert_eq!(single.count(), &BigUint::from(1u32));
        }
    }
    let both = ModelSet::all(2).unwrap();
    assert_eq!(
        common(&first, 2, &both).unwrap().as_ref().count(),
        &BigUint::from(1u32)
    );
    assert_eq!(
        common(&second, 2, &both).unwrap().as_ref().count(),
        &BigUint::from(0u32)
    );
}

#[test]
fn counts_and_ranked_witnesses_match_enumeration() {
    let mut rng = Rng(0x00C0_4401);
    let models = 4;
    let mut checked = 0;
    let mut nonzero = 0;
    const DRAWS: usize = 300;
    // Cap the cost of exhaustive derivation enumeration on each draw.
    const MAX_DERIVATIONS: usize = 5_000;
    let mut skipped = 0;
    for draw in 0..DRAWS {
        let spread = [1, 2, 8][draw % 3];
        let low = if draw % 2 == 0 { 0 } else { -spread };
        let chart = random_chart(&mut rng, 5, models, low, spread);
        if derivation_count(&chart) > MAX_DERIVATIONS {
            skipped += 1;
            continue;
        }
        for selection in subsets(models) {
            let expected = brute_common(&chart, selection.models());
            let answer = common(&chart, models, &selection).unwrap();
            assert_eq!(answer.label(), "Exact");
            let certificate = answer.into_inner();
            certificate.verify(&chart, models).unwrap();
            assert_eq!(certificate.count(), &BigUint::from(expected.len()));
            assert_eq!(certificate.exists(), !expected.is_empty());
            nonzero += usize::from(!expected.is_empty());
            for (rank, tree) in expected.iter().enumerate() {
                let witness = certificate
                    .witness(&chart, &BigUint::from(rank))
                    .unwrap()
                    .expect("rank below the count");
                assert_eq!(&witness.tree(&chart, chart.root()).unwrap(), tree);
                certificate.verify_witness(&chart, &witness).unwrap();
            }
            assert!(certificate
                .witness(&chart, &BigUint::from(expected.len()))
                .unwrap()
                .is_none());
            checked += 1;
        }
    }
    assert!(checked > 3_000, "checked {checked}");
    assert_eq!((DRAWS - skipped, skipped, checked), (286, 14, 4_290));
    assert!(nonzero > 100, "nonzero {nonzero}");
}

#[test]
fn tampered_certificates_and_witnesses_are_refused() {
    let chart = Chart::new(
        vec![
            vec![
                Costed::rule([0, 0], []),
                Costed::rule([0, 0], []),
                Costed::rule([0, 1], []),
            ],
            vec![Costed::rule([1, 0], [0]), Costed::rule([1, 1], [0])],
        ],
        1,
    )
    .unwrap();
    let selection = ModelSet::all(2).unwrap();
    let certificate = common(&chart, 2, &selection).unwrap().into_inner();
    assert_eq!(certificate.count(), &BigUint::from(2u32));

    let mut optimum = certificate.clone();
    optimum.optima[0][1] = Some(BigInt::from(-1));
    assert_eq!(
        optimum.verify(&chart, 2),
        Err(Error::Optimum { cell: 0, model: 1 })
    );

    let mut count = certificate.clone();
    count.counts[1] += 1u32;
    assert_eq!(count.verify(&chart, 2), Err(Error::Count { cell: 1 }));

    let witness = certificate
        .witness(&chart, &BigUint::from(1u32))
        .unwrap()
        .unwrap();
    let mut rank = witness.clone();
    rank.rank = BigUint::from(0u32);
    assert!(matches!(
        certificate.verify_witness(&chart, &rank),
        Err(Error::Witness(_))
    ));

    // The third leaf rule costs 1 in model 1, so a tree using it is not common-optimal.
    let mut swapped = witness.clone();
    swapped.preorder[1] = (0, 2);
    assert!(matches!(
        certificate.verify_witness(&chart, &swapped),
        Err(Error::Witness(_))
    ));

    let mut short = witness;
    short.preorder.pop();
    assert!(matches!(
        certificate.verify_witness(&chart, &short),
        Err(Error::Witness(_))
    ));
}

#[test]
fn retention_schedules_agree_and_masks_scan_no_more_than_costs() {
    let mut rng = Rng(0x5EED_0012);
    let models = 6;
    for draw in 0..40 {
        let chart = random_chart(&mut rng, 30, models, 0, [1, 2, 5][draw % 3]);
        let optima = Optima::of(&chart, models).unwrap();
        optima.verify(&chart).unwrap();
        let masks = WinnerMasks::of(&chart, &optima).unwrap();
        for selection in subsets(models).into_iter().step_by(7) {
            let exact = common(&chart, models, &selection).unwrap().into_inner();
            let (by_masks, mask_work) = masks.count_common(&chart, &selection).unwrap();
            let (by_costs, cost_work) = optima.count_common(&chart, &selection).unwrap();
            let (by_rescan, rescan_work) = count_common_rescan(&chart, models, &selection).unwrap();
            assert_eq!(&by_masks, exact.count());
            assert_eq!(&by_costs, exact.count());
            assert_eq!(&by_rescan, exact.count());
            assert!(mask_work.rule_visits <= cost_work.rule_scans);
            assert_eq!(mask_work.cells, cost_work.cells);
            assert!(rescan_work.cost_evaluations >= cost_work.cost_evaluations.min(1));
        }
        assert!(masks.conditional_bits() <= masks.storage_bits());
    }
}

#[test]
fn an_answer_table_refuses_unretained_selections_with_a_checked_collision() {
    let mut rng = Rng(0x7AB1E);
    let models = 4;
    let chart = random_chart(&mut rng, 12, models, 0, 2);
    let optima = Optima::of(&chart, models).unwrap();
    let masks = WinnerMasks::of(&chart, &optima).unwrap();
    let pairs: Vec<ModelSet> = subsets(models)
        .into_iter()
        .filter(|set| set.models().len() == 2)
        .collect();
    let (table, _) = AnswerTable::build(&masks, &chart, &pairs).unwrap();
    for pair in &pairs {
        let exact = common(&chart, models, pair).unwrap().into_inner();
        assert_eq!(table.answer(pair, COLLISION_BUDGET).unwrap(), exact.count());
    }
    let retained: Vec<ModelSet> = table.selections().cloned().collect();
    let triple = ModelSet::new([0, 1, 3], models).unwrap();
    let Err(Error::NotRetained(collision)) = table.answer(&triple, COLLISION_BUDGET) else {
        panic!("a triple is not in a pair table");
    };
    collision.verify(&retained).unwrap();
    assert_ne!(collision.answers[0], collision.answers[1]);

    // A fresh model 4 that the table never saw.
    let fresh = ModelSet::new([2, 4], models + 1).unwrap();
    let Err(Error::NotRetained(collision)) = table.answer(&fresh, COLLISION_BUDGET) else {
        panic!("a fresh model is not in the table");
    };
    collision.verify(&retained).unwrap();
}

#[test]
fn a_retained_lookup_needs_no_budget_and_an_unlisted_one_is_declined() {
    let mut rng = Rng(0x7AB1E);
    let models = 4;
    let chart = random_chart(&mut rng, 12, models, 0, 2);
    let optima = Optima::of(&chart, models).unwrap();
    let masks = WinnerMasks::of(&chart, &optima).unwrap();
    let pair = ModelSet::new([0, 2], models).unwrap();
    let (table, _) = AnswerTable::build(&masks, &chart, std::slice::from_ref(&pair)).unwrap();
    let exact = common(&chart, models, &pair).unwrap().into_inner();
    assert_eq!(table.get(&pair), Some(exact.count()));
    let unlisted = ModelSet::new([0, 1, 3], models).unwrap();
    assert_eq!(table.get(&unlisted), None);
    // With no construction budget the unlisted selection is still declined,
    // now because its collision does not fit.
    let none = CollisionBudget {
        max_rules: 0,
        max_cost_entries: 0,
    };
    assert!(matches!(
        table.answer(&unlisted, none),
        Err(Error::CollisionBudgetExceeded)
    ));
    assert_eq!(table.answer(&pair, none).unwrap(), exact.count());
}

#[test]
fn pairwise_common_optima_do_not_imply_a_triple_one() {
    // Each pair of the three models shares one optimum; no rule is optimal in all three.
    let chart = Chart::new(
        vec![vec![
            Costed::rule([0, 0, 1], []),
            Costed::rule([0, 1, 0], []),
            Costed::rule([1, 0, 0], []),
        ]],
        0,
    )
    .unwrap();
    for pair in [[0, 1], [0, 2], [1, 2]] {
        let answer = common(&chart, 3, &ModelSet::new(pair, 3).unwrap()).unwrap();
        assert_eq!(answer.as_ref().count(), &BigUint::from(1u32));
    }
    let all = common(&chart, 3, &ModelSet::all(3).unwrap()).unwrap();
    assert!(!all.as_ref().exists());
}

#[test]
fn collisions_exist_for_every_selection_outside_the_family() {
    let models = 4;
    for selection in subsets(models) {
        if selection.models().len() < 2 {
            continue;
        }
        let collision = Collision::construct(models, &selection, COLLISION_BUDGET).unwrap();
        let others: Vec<ModelSet> = subsets(models)
            .into_iter()
            .filter(|s| *s != selection)
            .collect();
        collision.verify(&others).unwrap();
        assert_eq!(
            collision.answers,
            [BigUint::from(2u32), BigUint::from(1u32)]
        );
    }
}

#[test]
fn tie_set_lower_bound_arithmetic() {
    // Distinct nonempty tie sets over R rules need distinct retained states:
    // ceil(log2(2^R - 1)) bits, which equals R for R >= 2.
    for rules in 2u32..=63 {
        let states = (BigUint::from(1u32) << rules) - 1u32;
        assert_eq!(ceil_log2(&states), u64::from(rules));
    }
    assert_eq!(binomial(5, 2), BigUint::from(10u32));
    assert_eq!(ceil_log2(&binomial(5, 2)), 4);
    assert_eq!(binomial(3, 5), BigUint::from(0u32));
}

#[test]
fn selections_and_cost_vectors_are_validated() {
    assert_eq!(ModelSet::new([], 3), Err(Error::EmptySelection));
    assert_eq!(
        ModelSet::new([3], 3),
        Err(Error::ModelOutOfRange {
            model: 3,
            models: 3
        })
    );
    let chart = Chart::new(vec![vec![Costed::rule([0, 0], [])]], 0).unwrap();
    assert_eq!(
        common(&chart, 3, &ModelSet::all(3).unwrap()),
        Err(Error::CostLength {
            cell: 0,
            rule: 0,
            expected: 3,
            actual: 2
        })
    );
    let empty: Chart<Costed> = Chart::new(vec![vec![], vec![Costed::rule([0], [0])]], 1).unwrap();
    let answer = common(&empty, 1, &ModelSet::all(1).unwrap())
        .unwrap()
        .into_inner();
    assert!(!answer.exists());
    assert_eq!(answer.root_optima(), &[None]);
    let _unused: Option<Rule<Costed>> = None;
}

#[test]
fn replay_refuses_a_forged_optimum() {
    use zeno_adp::common_optimum::Witness;
    let chart = Chart::new(vec![vec![Costed::rule([0], []), Costed::rule([1], [])]], 0).unwrap();
    let mut answer = common(&chart, 1, &ModelSet::all(1).unwrap())
        .unwrap()
        .into_inner();
    answer.optima[0][0] = Some(1.into());
    let witness = Witness {
        rank: BigUint::ZERO,
        preorder: vec![(0, 1)],
        costs: vec![1.into()],
    };
    assert!(matches!(
        answer.verify_witness(&chart, &witness),
        Err(Error::Optimum { .. })
    ));
}

#[test]
fn replay_refuses_out_of_range_roots() {
    let chart = Chart::new(vec![vec![Costed::rule([0], [])]], 0).unwrap();
    let mut answer = common(&chart, 1, &ModelSet::all(1).unwrap())
        .unwrap()
        .into_inner();
    let mut witness = answer.witness(&chart, &BigUint::ZERO).unwrap().unwrap();
    answer.root = usize::MAX;
    witness.preorder[0].0 = usize::MAX;
    let replay = std::panic::catch_unwind(|| answer.verify_witness(&chart, &witness));
    let extract = std::panic::catch_unwind(|| answer.witness(&chart, &BigUint::ZERO));
    assert!(matches!(replay, Ok(Err(Error::CertificateShape))));
    assert!(matches!(extract, Ok(Err(Error::CertificateShape))));
}

#[test]
fn replay_refuses_a_chart_with_missing_costs() {
    let chart = Chart::new(vec![vec![Costed::rule([0], [])]], 0).unwrap();
    let answer = common(&chart, 1, &ModelSet::all(1).unwrap())
        .unwrap()
        .into_inner();
    let witness = answer.witness(&chart, &BigUint::ZERO).unwrap().unwrap();
    let chart = Chart::new(vec![vec![Costed::rule([], [])]], 0).unwrap();
    let replay = std::panic::catch_unwind(|| answer.verify_witness(&chart, &witness));
    let extract = std::panic::catch_unwind(|| answer.witness(&chart, &BigUint::ZERO));
    assert!(matches!(replay, Ok(Err(Error::CostLength { .. }))));
    assert!(matches!(extract, Ok(Err(Error::CostLength { .. }))));
}

#[test]
fn collision_rejects_corrupt_width_before_allocating() {
    let selection = ModelSet::all(2).unwrap();
    let mut collision = Collision::construct(2, &selection, COLLISION_BUDGET).unwrap();
    collision.models = usize::MAX;
    assert!(matches!(
        collision.verify(&[]),
        Err(Error::CostLength { .. })
    ));
}

#[test]
fn answer_table_refuses_extreme_missing_model_without_allocating() {
    let chart = Chart::new(vec![vec![Costed::rule([0], [])]], 0).unwrap();
    let masks = WinnerMasks::of(&chart, &Optima::of(&chart, 1).unwrap()).unwrap();
    let (table, _) = AnswerTable::build(&masks, &chart, &[]).unwrap();
    let selection = ModelSet::new([usize::MAX - 1], usize::MAX).unwrap();
    assert!(matches!(
        table.answer(&selection, COLLISION_BUDGET),
        Err(Error::CollisionBudgetExceeded)
    ));

    // With one selected model, two charts each need two subset rules and a
    // base rule. They contain two costs per rule in this extended universe.
    let fresh = ModelSet::new([1], 2).unwrap();
    const RULES: usize = 2 * ((1 << 1) + 1);
    const COSTS: usize = 2 * RULES;
    for (rules, costs) in [(RULES - 1, COSTS), (RULES, COSTS - 1), (RULES, COSTS)] {
        let budget = CollisionBudget {
            max_rules: rules,
            max_cost_entries: costs,
        };
        match table.answer(&fresh, budget) {
            Err(Error::NotRetained(collision)) if rules == RULES && costs == COSTS => {
                collision.verify(&[ModelSet::all(1).unwrap()]).unwrap();
            }
            Err(Error::CollisionBudgetExceeded) if rules < RULES || costs < COSTS => {}
            answer => panic!("unexpected result for {budget:?}: {answer:?}"),
        }
    }
    let too_many = usize::BITS as usize;
    let wide = ModelSet::all(too_many).unwrap();
    assert!(matches!(
        Collision::construct(too_many, &wide, COLLISION_BUDGET),
        Err(Error::CollisionBudgetExceeded)
    ));
}
