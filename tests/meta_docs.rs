//! The code shown in docs/EXACT.md for the 0.8 query modules.

use num_bigint::BigUint;
use zeno_adp::Chart;

#[test]
fn common_optima_guide_example() -> Result<(), zeno_adp::common_optimum::Error> {
    use zeno_adp::common_optimum::{common, Costed, ModelSet};
    let chart = Chart::new(
        vec![vec![
            Costed::rule([0, 0, 1], []),
            Costed::rule([0, 1, 0], []),
            Costed::rule([1, 0, 0], []),
        ]],
        0,
    )
    .unwrap();
    let pair = common(&chart, 3, &ModelSet::new([0, 1], 3)?)?;
    assert_eq!(pair.as_ref().count(), &BigUint::from(1u32));
    let all = common(&chart, 3, &ModelSet::all(3)?)?;
    assert_eq!(all.label(), "Exact");
    assert!(!all.as_ref().exists());
    Ok(())
}

#[test]
fn robust_prefix_guide_example() -> Result<(), zeno_adp::robust_prefix::Error> {
    use zeno_adp::robust_prefix::{state_bound, within_budget, zero_regret, Step};
    let chart = Chart::new(
        vec![
            vec![Step::finish([2, 2], 4), Step::finish([0, 0], 1)],
            vec![Step::to([2, 2], 4, 0), Step::finish([0, 0], 1)],
        ],
        1,
    )
    .unwrap();
    assert_eq!(zero_regret(&chart, 2)?.as_ref().best_credit(1), 1);
    let budget = [BigUint::from(2u32), BigUint::from(2u32)];
    // The caller sets the work limit; this bound is never exceeded.
    let limit = usize::try_from(state_bound(&chart, &budget)).unwrap();
    let two = within_budget(&chart, 2, &budget, limit)?;
    assert_eq!(two.as_ref().best, 5);
    let budget = [BigUint::from(4u32), BigUint::from(4u32)];
    let limit = usize::try_from(state_bound(&chart, &budget)).unwrap();
    let four = within_budget(&chart, 2, &budget, limit)?;
    assert_eq!(four.as_ref().best, 8);
    Ok(())
}

#[test]
fn history_state_guide_example() -> Result<(), zeno_adp::state_discovery::Error> {
    use zeno_adp::state_discovery::{Alignment, Observer, RawModel, Sense, Symbol};
    let affine = |word: &[Symbol]| -> i64 {
        word.iter()
            .enumerate()
            .map(|(n, &op)| match op {
                Alignment::MATCH => 2,
                Alignment::MISMATCH => -1,
                _ if n > 0 && word[n - 1] == op => -1,
                _ => -3,
            })
            .sum()
    };
    let mut scorer = |w: &[Symbol]| affine(w);
    let mut raw = RawModel::read(Observer::last_symbols(Alignment::SYMBOLS, 2)?, &mut scorer)?;
    let check = raw.check(&mut scorer, 6)?;
    let quotient = raw.quotient()?;
    assert_eq!(quotient.as_ref().classes(), 3);
    let chart = quotient.chart(
        &Alignment {
            x: b"GAT",
            y: b"GT",
        },
        Sense::Maximize,
    )?;
    let best = chart.solve(Some(&check))?.into_inner();
    assert_eq!(best.score, 1);
    Ok(())
}

#[path = "../examples/retention.rs"]
mod retention;

/// The retention figures quoted in docs/EXACT.md, reproduced from the seeded example.
#[test]
fn retention_figures_in_the_guide() {
    let t = retention::measure().unwrap();
    assert_eq!(
        t,
        retention::Totals {
            cost_chart_bits: 254_129,
            mask_bits: 479_700,
            coalesced_mask_bits: 347_495,
            conditional_bits: 153_400,
            table_bits: 221_503,
            table_build_visits: 277_420,
            mask_query_visits: 3_478,
            cost_query_scans: 3_966,
            rescan_work: 83_428,
            masks_above_costs: 0,
        }
    );
}

#[test]
fn exact_guide_links_the_three_meta_models() {
    let guide = include_str!("../docs/EXACT.md");
    for model in ["MetaQuotient", "MetaCommon", "MetaRobust"] {
        let link = format!("](../verification/{model}.lean)");
        assert!(guide.contains(&link), "missing local link to {model}");
    }
}
