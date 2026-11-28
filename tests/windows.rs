//! Tests for the score-window choosers.
//!
//! Three kinds of evidence, each on a named finite domain:
//! - the chooser laws by exhaustion over every bag in `bags()`;
//! - agreement with literal evaluation at every cell of every chart in `charts()`;
//! - the reference Bellman audit on the same charts.

use zeno_adp::windows::{ClosestTo, Step, Stepped, SteppedOperator, UniqueMinimum};
use zeno_adp::{
    audit_bounded, exhaustive, tabulate_cells, Algebra, AnswerOrder, AuditBudget, Chart, Error,
    Rule,
};

/// Scores 0..=7 exercise both sides of the mirror test, including
/// scores strictly above twice the smaller tested targets.
const SCORES: u64 = 8;
/// Three occurrences are the fewest that hold a tie plus a runner-up, and a
/// score at or below the target plus two above it.
const BAG_LENGTH: usize = 3;
/// Targets 0..=4: zero has an empty lower side; four has the mirror bound
/// `2 * 4 = 8` just above the largest score.
const TARGETS: u64 = 5;
/// Floors 0..=5 include values below, at and above every tested target.
const FLOORS: u64 = 6;
/// Weights 0..=2 cover no shift, an odd shift and an even shift.
const WEIGHTS: u64 = 3;
/// Exact expansion bound for the largest fixture, with five leaves and
/// a unary choice after each binary split. A width-`k` tree has `k - 1` splits
/// and as many unary choices. With two choices at each leaf, this gives
/// Catalan(k - 1) * 2^(2k - 1) derivations of 3k - 2 nodes after the
/// unary choice. Before it there are half as many, each one node shorter.
/// The budget is the sum over both cell kinds and every interval.
const BUDGET: AuditBudget = AuditBudget {
    max_tree_nodes: 156_858,
};

/// Keep every occurrence, sorted. This is the literal bag.
struct AllScores;

impl<O: SteppedOperator> Algebra<O> for AllScores {
    type Value = u64;

    fn apply(&self, operator: &O, children: &[&u64]) -> Result<u64, Error> {
        let step = operator.step();
        let sum = u128::from(step.weight) + children.iter().map(|&&x| u128::from(x)).sum::<u128>();
        u64::try_from(sum.max(u128::from(step.floor))).map_err(|_| Error::Overflow)
    }

    fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
        let mut all = candidates.to_vec();
        all.sort_unstable();
        Ok(all)
    }
}

fn literal_closest(target: u64, bag: &[u64]) -> Option<u64> {
    bag.iter()
        .copied()
        .min_by_key(|&score| (score.abs_diff(target), score))
}

fn literal_unique(bag: &[u64]) -> Option<bool> {
    let least = bag.iter().min()?;
    Some(bag.iter().filter(|&score| score == least).count() == 1)
}

fn bags() -> Vec<Vec<u64>> {
    let mut all = vec![vec![]];
    let mut layer = vec![vec![]];
    for _ in 0..BAG_LENGTH {
        layer = layer
            .iter()
            .flat_map(|bag: &Vec<u64>| {
                let least = bag.last().copied().unwrap_or(0);
                (least..SCORES).map(move |score| {
                    let mut longer = bag.clone();
                    longer.push(score);
                    longer
                })
            })
            .collect();
        all.extend(layer.iter().cloned());
    }
    all
}

fn steps(max_floor: u64) -> Vec<Step> {
    (0..WEIGHTS)
        .flat_map(|weight| (0..=max_floor).map(move |floor| Step { weight, floor }))
        .collect()
}

fn unary(step: Step) -> Stepped {
    Stepped { step, arity: 1 }
}

fn mapped(step: Step, bag: &[u64]) -> Vec<u64> {
    bag.iter()
        .map(|&score| step.apply([score].into_iter()).unwrap())
        .collect()
}

fn summed(left: &[u64], right: &[u64]) -> Vec<u64> {
    left.iter()
        .flat_map(|a| right.iter().map(move |b| a + b))
        .collect()
}

/// Empty choice, idempotence, union, every unary step and both arguments of
/// a Cartesian sum, for one chooser on every bag of the domain.
fn chooser_laws<A: Algebra<Stepped, Value = u64>>(algebra: &A, steps: &[Step]) {
    let choose = |bag: &[u64]| algebra.choose(bag).unwrap();
    assert!(choose(&[]).is_empty());
    let all = bags();
    let chosen: Vec<_> = all.iter().map(|bag| choose(bag)).collect();
    for (bag, kept) in all.iter().zip(&chosen) {
        assert_eq!(&choose(kept), kept, "idempotence on {bag:?}");
        for &step in steps {
            assert_eq!(
                choose(&mapped(step, bag)),
                choose(&mapped(step, kept)),
                "step {step:?} on {bag:?}"
            );
        }
    }
    for (left, left_kept) in all.iter().zip(&chosen) {
        for (right, right_kept) in all.iter().zip(&chosen) {
            let union = [left.as_slice(), right.as_slice()].concat();
            let kept = [left_kept.as_slice(), right_kept.as_slice()].concat();
            assert_eq!(choose(&union), choose(&kept), "union {left:?} {right:?}");
            assert_eq!(
                choose(&summed(left, right)),
                choose(&summed(left_kept, right_kept)),
                "sum {left:?} {right:?}"
            );
        }
    }
}

#[test]
fn closest_chooser_laws_hold_on_every_bag() {
    for target in 0..TARGETS {
        chooser_laws(&ClosestTo::new(target), &steps(FLOORS - 1));
    }
}

#[test]
fn closest_readout_is_the_literal_answer_on_every_bag() {
    for target in 0..TARGETS {
        let algebra = ClosestTo::new(target);
        for bag in bags() {
            let kept = <ClosestTo as Algebra<Stepped>>::choose(&algebra, &bag).unwrap();
            assert_eq!(algebra.closest(&kept), literal_closest(target, &bag));
        }
    }
}

#[test]
fn unique_chooser_laws_hold_on_every_bag() {
    for max_floor in 0..FLOORS {
        chooser_laws(&UniqueMinimum::new(max_floor), &steps(max_floor));
    }
}

#[test]
fn unique_readout_is_the_literal_answer_on_every_bag() {
    for max_floor in 0..FLOORS {
        let algebra = UniqueMinimum::new(max_floor);
        for bag in bags() {
            let kept = <UniqueMinimum as Algebra<Stepped>>::choose(&algebra, &bag).unwrap();
            assert_eq!(UniqueMinimum::is_unique(&kept), literal_unique(&bag));
        }
    }
}

/// The mirror window keeps the least score above the target exactly when it
/// is strictly closer than the best score at or below the target.
#[test]
fn closest_keeps_what_the_mirror_test_says() {
    let choose = |target, bag: &[u64]| {
        <ClosestTo as Algebra<Stepped>>::choose(&ClosestTo::new(target), bag).unwrap()
    };
    // 1 and 4 around 3: 4 is closer, so it stays. Duplicates collapse.
    assert_eq!(choose(3, &[4, 1, 1, 9]), vec![1, 4]);
    // 1 and 5 around 3 tie; the tie goes to the lower score under every
    // later step, so 5 is dropped.
    assert_eq!(choose(3, &[5, 1]), vec![1]);
    // No score at or below the target: the least score above it stays.
    assert_eq!(choose(3, &[9, 7, 7]), vec![7]);
    // Every distinct score at or below the target stays.
    assert_eq!(choose(3, &[3, 0, 2, 2, 8]), vec![0, 2, 3]);
    // Full-width scores tie without computing twice the target.
    assert_eq!(
        choose(u64::MAX - 1, &[u64::MAX, u64::MAX - 2]),
        vec![u64::MAX - 2]
    );
}

/// The floor window keeps the runner-up only while a floor can still raise
/// the minimum to meet it.
#[test]
fn unique_keeps_what_the_floor_window_says() {
    let choose = |max_floor, bag: &[u64]| {
        <UniqueMinimum as Algebra<Stepped>>::choose(&UniqueMinimum::new(max_floor), bag).unwrap()
    };
    assert_eq!(choose(2, &[5, 0, 2]), vec![0, 2]);
    assert_eq!(choose(2, &[5, 0, 3]), vec![0]);
    assert_eq!(choose(2, &[4, 4, 4]), vec![4, 4]);
    assert_eq!(choose(0, &[1, 0]), vec![0]);
}

#[test]
fn a_floor_above_the_declared_maximum_is_refused() {
    let algebra = UniqueMinimum::new(2);
    let high = unary(Step::floor(3));
    assert_eq!(
        algebra.apply(&high, &[&0]),
        Err(Error::FloorOutsideWindow {
            floor: 3,
            max_floor: 2
        })
    );
    assert_eq!(algebra.apply(&unary(Step::floor(2)), &[&0]), Ok(2));
}

#[test]
fn score_overflow_is_reported() {
    let step = Step::add(u64::MAX);
    assert_eq!(step.apply([1].into_iter()), Err(Error::Overflow));
    assert_eq!(step.apply([0].into_iter()), Ok(u64::MAX));
}

fn leaf(weight: u64) -> Rule<Stepped> {
    Rule::new(
        Stepped {
            step: Step::add(weight),
            arity: 0,
        },
        [],
    )
}

fn one(step: Step, child: usize) -> Rule<Stepped> {
    Rule::new(unary(step), [child])
}

fn two(weight: u64, left: usize, right: usize) -> Rule<Stepped> {
    Rule::new(
        Stepped {
            step: Step::add(weight),
            arity: 2,
        },
        [left, right],
    )
}

/// Bracketings of `leaves` leaves, each leaf with two alternative weights.
/// Interval `[i, j)` is a cell; a longer interval has one binary rule per
/// split. When `floor` is nonzero, a second cell alternates a floor and
/// a shift of that interval.
fn bracketing(leaves: usize, floor: u64) -> Chart<Stepped> {
    let mut index = std::collections::BTreeMap::new();
    let mut cells = Vec::new();
    for width in 1..=leaves {
        for i in 0..=leaves - width {
            let j = i + width;
            let mut rules = Vec::new();
            if width == 1 {
                rules.push(leaf(i as u64 % WEIGHTS));
                rules.push(leaf((i as u64 + 2) % (WEIGHTS + 1)));
            } else {
                for k in i + 1..j {
                    rules.push(two((k as u64) % WEIGHTS, index[&(i, k)], index[&(k, j)]));
                }
            }
            cells.push(rules);
            if floor > 0 && width > 1 {
                let below = cells.len() - 1;
                cells.push(vec![
                    one(Step::floor(floor), below),
                    one(Step::add(1), below),
                ]);
            }
            index.insert((i, j), cells.len() - 1);
        }
    }
    let root = cells.len() - 1;
    Chart::new(cells, root).unwrap()
}

/// The named chart domain of the differential and audit tests.
fn charts(max_floor: u64) -> Vec<Chart<Stepped>> {
    let mut all = vec![
        // A floor after a near-tie.
        Chart::new(
            vec![
                vec![leaf(0), leaf(2)],
                vec![one(Step::floor(max_floor.min(2)), 0)],
            ],
            1,
        )
        .unwrap(),
        // A shift that carries a kept score across a small target while the
        // least score above it is mirror-dropped below.
        Chart::new(
            vec![
                vec![leaf(1), leaf(5), leaf(6)],
                vec![one(Step::add(2), 0), one(Step::add(0), 0)],
                vec![two(0, 0, 1), one(Step::add(1), 1)],
            ],
            2,
        )
        .unwrap(),
    ];
    // Five leaves exercise all 14 binary bracketings, including different
    // split shapes with three and four internal floor/shift choices.
    for leaves in 1..=5 {
        all.push(bracketing(leaves, 0));
        all.push(bracketing(leaves, max_floor));
    }
    all
}

/// Compare a tabulated readout with the literal one at every cell.
fn agrees_at_every_cell<A, R>(
    chart: &Chart<Stepped>,
    algebra: &A,
    checked: Vec<Vec<u64>>,
    read: impl Fn(&[u64]) -> R,
    literal: impl Fn(&[u64]) -> R,
) where
    A: Algebra<Stepped, Value = u64>,
    R: PartialEq + std::fmt::Debug,
{
    let table = tabulate_cells(chart, algebra).unwrap();
    assert_eq!(checked, table);
    for (cell, stored) in table.iter().enumerate() {
        let prefix = Chart::new(chart.cells()[..=cell].to_vec(), cell).unwrap();
        let bag = exhaustive(&prefix, &AllScores).unwrap();
        assert_eq!(read(stored), literal(&bag), "cell {cell}");
        assert_eq!(
            stored,
            &algebra.choose(&bag).unwrap(),
            "stored state at cell {cell}"
        );
    }
}

#[test]
fn closest_matches_literal_evaluation_at_every_cell() {
    // Floors up to 4 sit below, at and above the targets used here.
    for chart in charts(4) {
        // 0 and 3 are small targets inside the score range; 7 and 40 are
        // near the middle and above every score of these charts.
        for target in [0, 3, 7, 40] {
            let algebra = ClosestTo::new(target);
            agrees_at_every_cell(
                &chart,
                &algebra,
                algebra.tabulate_cells(&chart).unwrap(),
                |kept| algebra.closest(kept),
                |bag| literal_closest(target, bag),
            );
        }
    }
}

#[test]
fn unique_matches_literal_evaluation_at_every_cell() {
    for max_floor in [1, 2, 4] {
        for chart in charts(max_floor) {
            let algebra = UniqueMinimum::for_chart(&chart);
            agrees_at_every_cell(
                &chart,
                &algebra,
                algebra.tabulate_cells(&chart).unwrap(),
                UniqueMinimum::is_unique,
                literal_unique,
            );
        }
    }
}

#[test]
fn the_bellman_audit_passes_on_both_algebras() {
    for chart in charts(4) {
        for target in [0, 3, 7, 40] {
            let audit = audit_bounded(
                &chart,
                &ClosestTo::new(target),
                BUDGET,
                AnswerOrder::Ordered,
            )
            .unwrap();
            assert!(audit.bellman.first_failure.is_none(), "target {target}");
            assert_eq!(audit.bellman.oracle, audit.bellman.tabulated);
        }
        let unique = UniqueMinimum::for_chart(&chart);
        let audit = audit_bounded(&chart, &unique, BUDGET, AnswerOrder::Ordered).unwrap();
        assert!(audit.bellman.first_failure.is_none());
        assert_eq!(audit.bellman.oracle, audit.bellman.tabulated);
    }
}

/// A window that understates the largest floor fails the audit on the
/// floor-after-near-tie chart. This shows the audit exercises the risky
/// operation; a corpus without that chart would pass the wrong chooser.
#[test]
fn the_audit_refuses_an_understated_floor() {
    struct Understated(UniqueMinimum);
    impl Algebra<Stepped> for Understated {
        type Value = u64;
        fn apply(&self, operator: &Stepped, children: &[&u64]) -> Result<u64, Error> {
            operator.step().apply(children.iter().map(|&&score| score))
        }
        fn choose(&self, candidates: &[u64]) -> Result<Vec<u64>, Error> {
            <UniqueMinimum as Algebra<Stepped>>::choose(&self.0, candidates)
        }
    }
    let chart = &charts(2)[0];
    // The chart's floor is 2; a window declared for floor 1 drops score 2.
    let audit = audit_bounded(
        chart,
        &Understated(UniqueMinimum::new(1)),
        BUDGET,
        AnswerOrder::Ordered,
    )
    .unwrap();
    assert!(audit.bellman.first_failure.is_some());
    assert_ne!(audit.bellman.oracle, audit.bellman.tabulated);
}

#[test]
fn for_chart_reads_the_largest_floor() {
    let chart = bracketing(3, 4);
    assert_eq!(UniqueMinimum::for_chart(&chart).max_floor(), 4);
    assert_eq!(UniqueMinimum::for_chart(&bracketing(3, 0)).max_floor(), 0);
}
