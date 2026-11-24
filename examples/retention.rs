//! Compare what to keep for later common-optimum questions about one chart.
//!
//! The example draws 200 seeded random charts of 80 cells with 12 cost models, keeps
//! each summary, and asks one random pair of models per chart. It prints the payload
//! bits of each summary and the work units of each query. Work units count rule
//! visits and evaluations. They exclude validation work and elapsed time.
//!
//! Run with `cargo run --offline --locked --release --example retention`.

use zeno_adp::common_optimum::{
    count_common_rescan, AnswerTable, Costed, Error, ModelSet, Optima, WinnerMasks,
};
use zeno_adp::Chart;

/// The drawn charts: 200 charts, 80 cells, 12 models, as in the guide.
pub const CHARTS: usize = 200;
pub const CELLS: usize = 80;
pub const MODELS: usize = 12;
/// The seed of the drawing.
pub const SEED: u64 = 0x5EED_0080;

/// Splitmix64, so the charts do not depend on another crate.
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
}

/// Totals over every chart.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Totals {
    pub cost_chart_bits: u64,
    pub mask_bits: u64,
    pub coalesced_mask_bits: u64,
    pub conditional_bits: u64,
    pub table_bits: u64,
    pub table_build_visits: u64,
    pub mask_query_visits: u64,
    pub cost_query_scans: u64,
    pub rescan_work: u64,
    /// Queries for which the masks visited more rules than the cost charts scanned.
    pub masks_above_costs: u64,
}

fn chart(rng: &mut Rng, spread: u64) -> Chart<Costed> {
    let rows = (0..CELLS)
        .map(|cell| {
            (0..1 + rng.below(4))
                .map(|_| {
                    let arity = if cell == 0 { 0 } else { rng.below(3) };
                    let children: Vec<usize> = (0..arity)
                        .map(|_| rng.below(cell as u64) as usize)
                        .collect();
                    let costs: Vec<i64> = (0..MODELS).map(|_| rng.below(spread) as i64).collect();
                    Costed::rule(costs, children)
                })
                .collect()
        })
        .collect();
    Chart::new(rows, CELLS - 1).expect("children precede their cells")
}

pub fn measure() -> Result<Totals, Error> {
    let mut rng = Rng(SEED);
    let mut totals = Totals::default();
    let pairs: Vec<ModelSet> = (0..MODELS)
        .flat_map(|a| (a + 1..MODELS).map(move |b| (a, b)))
        .map(|(a, b)| ModelSet::new([a, b], MODELS))
        .collect::<Result<_, _>>()?;
    for index in 0..CHARTS {
        let chart = chart(&mut rng, [1, 2, 5][index % 3]);
        let optima = Optima::of(&chart, MODELS)?;
        let masks = WinnerMasks::of(&chart, &optima)?;
        let (table, build) = AnswerTable::build(&masks, &chart, &pairs)?;
        totals.cost_chart_bits += optima.unsigned_bits().expect("nonnegative costs");
        totals.mask_bits += masks.storage_bits();
        totals.coalesced_mask_bits += masks.coalesced_bits();
        totals.conditional_bits += masks.conditional_bits();
        totals.table_bits += table.storage_bits();
        totals.table_build_visits += build.rule_visits;
        let pair = &pairs[rng.below(pairs.len() as u64) as usize];
        let (by_masks, mask_work) = masks.count_common(&chart, pair)?;
        let (by_costs, cost_work) = optima.count_common(&chart, pair)?;
        let (by_rescan, rescan_work) = count_common_rescan(&chart, MODELS, pair)?;
        assert!(by_masks == by_costs && by_costs == by_rescan);
        assert_eq!(table.get(pair), Some(&by_masks));
        totals.mask_query_visits += mask_work.rule_visits;
        totals.cost_query_scans += cost_work.rule_scans;
        totals.rescan_work += rescan_work.cost_evaluations + rescan_work.rule_visits;
        totals.masks_above_costs += u64::from(mask_work.rule_visits > cost_work.rule_scans);
    }
    Ok(totals)
}

#[allow(dead_code)]
fn main() -> Result<(), Error> {
    let t = measure()?;
    println!("{CHARTS} charts, {CELLS} cells, {MODELS} models, seed {SEED:#x}");
    println!("payload bits: cost charts {}, winner masks {}, coalesced masks {}, tie sets given their sizes {}, pair table {}",
        t.cost_chart_bits, t.mask_bits, t.coalesced_mask_bits, t.conditional_bits, t.table_bits);
    println!("work for one random pair per chart: masks {} rule visits, cost charts {} rule scans, rescan {} units",
        t.mask_query_visits, t.cost_query_scans, t.rescan_work);
    println!(
        "building every pair and singleton: {} rule visits",
        t.table_build_visits
    );
    println!(
        "queries where masks visited more than cost charts scanned: {}",
        t.masks_above_costs
    );
    Ok(())
}
