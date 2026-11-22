use super::{words, Checks};
use zeno_adp::algebras::ParetoWitnesses;
use zeno_adp::{
    audit_bounded, tabulate_cells, AnswerOrder, AuditBudget, Chart, Error, Operator, Rule,
};

// Each stage must select one offer. Coordinates are (cost, resource).
type Offer = (i64, usize);
const OFFERS: [Offer; 3] = [(0, 4), (3, 2), (4, 0)];
const HULL_OFFERS: [Offer; OFFERS.len() + 1] = [OFFERS[0], OFFERS[1], OFFERS[2], (5, 2)];
const MAX_STAGES: usize = 3; // Two composition steps past the one-stage gap example.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Plan {
    Start,
    Take { index: usize, offer: Offer },
}

impl Operator for Plan {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Take { .. }))
    }
}

fn plan_chart(input: &[&[Offer]]) -> Result<Chart<Plan>, Error> {
    let mut rows = vec![vec![Rule::new(Plan::Start, [])]];
    for (previous, &menu) in input.iter().enumerate() {
        rows.push(
            menu.iter()
                .enumerate()
                .map(|(index, &offer)| Rule::new(Plan::Take { index, offer }, [previous]))
                .collect(),
        );
    }
    Chart::new(rows, input.len())
}

pub fn budgeted_plans() -> Result<Checks, Error> {
    let menus: Vec<Vec<Offer>> = (0..1 << OFFERS.len())
        .map(|mask| {
            OFFERS
                .iter()
                .enumerate()
                .filter_map(|(index, &offer)| (mask & (1 << index) != 0).then_some(offer))
                .collect()
        })
        .collect();
    let menus: Vec<_> = menus.iter().map(Vec::as_slice).collect();
    let max_spend = OFFERS.iter().map(|offer| offer.1).max().unwrap();
    let algebra = ParetoWitnesses::new(|plan: &Plan| match *plan {
        Plan::Start => (0, 0),
        Plan::Take {
            offer: (cost, spend),
            ..
        } => (cost, spend as i64),
    });
    let mut checks = Checks::default();
    for input in words(&menus, MAX_STAGES)
        .into_iter()
        .chain([vec![HULL_OFFERS.as_slice()]])
    {
        let chart = plan_chart(&input)?;
        checks.chart(&chart);
        let table = tabulate_cells(&chart, &algebra)?;
        let mut derivations = 1;
        let mut tree_nodes = 1;
        for (stage, menu) in input.iter().enumerate() {
            derivations *= menu.len();
            // Each plan has its start node and one node for every selected offer.
            tree_nodes += derivations * (stage + 2);
        }
        let audit = audit_bounded(
            &chart,
            &algebra,
            AuditBudget {
                max_tree_nodes: tree_nodes,
            },
            AnswerOrder::Ordered,
        )?;
        assert!(audit.bellman.first_failure.is_none(), "{audit}");
        assert!(audit.ambiguities.is_empty(), "{audit}");
        assert_eq!(audit.tree_nodes, tree_nodes);
        checks.audited_nodes += audit.tree_nodes;

        // Exact spend and at-most-budget are separate recurrences on raw offers.
        let mut exact = vec![Some(0)];
        let mut allowance = vec![Some(0); input.len() * max_spend + 1];
        for (prefix, row) in table.iter().enumerate() {
            if let Some(menu) = prefix.checked_sub(1).map(|i| input[i]) {
                let mut next_exact = vec![None; prefix * max_spend + 1];
                for (used, prior) in exact.into_iter().enumerate() {
                    if let Some(prior) = prior {
                        for &(cost, spend) in menu {
                            let slot = &mut next_exact[used + spend];
                            let new_cost = prior + cost;
                            *slot = Some(slot.map_or(new_cost, |old: i64| old.min(new_cost)));
                        }
                    }
                }
                exact = next_exact;
                allowance = (0..allowance.len())
                    .map(|budget| {
                        menu.iter()
                            .filter_map(|&(cost, spend)| {
                                allowance
                                    .get(budget.checked_sub(spend)?)?
                                    .map(|prior| prior + cost)
                            })
                            .min()
                    })
                    .collect();
            }
            let mut best_cost = None;
            let mut expected = Vec::new();
            for (spend, &cost) in exact.iter().enumerate() {
                if let Some(cost) = cost {
                    if best_cost.is_none_or(|best| cost < best) {
                        expected.push((cost, spend as i64));
                        best_cost = Some(cost);
                    }
                }
            }
            let mut actual: Vec<_> = row.iter().map(|answer| answer.value).collect();
            actual.sort_unstable_by_key(|&(_, spend)| spend);
            actual.dedup();
            assert_eq!(actual, expected, "front at prefix {prefix}");
            checks.oracle_values += 1;
            for answer in row {
                let mut node = &answer.tree;
                let mut replayed = (0, 0);
                for menu in input[..prefix].iter().rev() {
                    let Plan::Take { index, .. } = node.operator else {
                        panic!("expected one offer per stage");
                    };
                    let (cost, spend) = menu[index];
                    replayed.0 += cost;
                    replayed.1 += spend as i64;
                    let [child] = node.children.as_slice() else {
                        panic!("an offer must extend one plan");
                    };
                    node = child;
                }
                assert_eq!(node.operator, Plan::Start);
                assert!(node.children.is_empty());
                assert_eq!(answer.value, replayed);
            }
            for (budget, &direct) in allowance.iter().take(exact.len()).enumerate() {
                let from_front = actual
                    .iter()
                    .filter_map(|&(cost, spend)| (spend <= budget as i64).then_some(cost))
                    .min();
                assert_eq!(from_front, direct, "prefix {prefix}, budget {budget}");
                checks.oracle_values += 1;
            }
            if input.as_slice() == [HULL_OFFERS.as_slice()] && prefix == chart.root() {
                let [low_cost, middle, low_spend, dominated] = HULL_OFFERS;
                let (constrained_cost, budget) = middle;
                assert_eq!(allowance[budget], Some(constrained_cost));
                assert!(actual.contains(&(constrained_cost, budget as i64)));
                // The middle point is the centroid of the three hull vertices.
                assert_eq!(3 * constrained_cost, low_cost.0 + low_spend.0 + dominated.0);
                assert_eq!(3 * budget, low_cost.1 + low_spend.1 + dominated.1);
                // At multiplier one the two endpoints tie below the middle offer.
                let relaxed = |(cost, spend): Offer| cost + spend as i64 - budget as i64;
                let lower_bound = input[0].iter().copied().map(relaxed).min();
                assert_eq!(lower_bound, Some(2));
                assert_eq!(Some(relaxed(low_cost)), lower_bound);
                assert_eq!(Some(relaxed(low_spend)), lower_bound);
            }
        }
    }
    Ok(checks)
}
