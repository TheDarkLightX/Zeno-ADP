use core::mem::size_of;
use zeno_adp::algebras::Count;
use zeno_adp::compiled::{self, BudgetedTable, Program};
use zeno_adp::fast::Fold;
use zeno_adp::grammars::Align;
use zeno_adp::{tabulate_cells, Algebra, Error};

const RANKS: usize = 10; // All masks include alternating occupancy with five runs.

fn mask(bits: u16) -> compiled::Grammar<Align, 1> {
    let names = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"];
    compiled::Grammar::new(
        &names,
        RANKS - 1,
        (0..RANKS)
            .filter(|&i| bits & (1 << i) != 0)
            .map(|parent| compiled::Production {
                name: names[parent].into(),
                parent,
                children: vec![],
                tracks: [vec![]],
                operator: Box::new(|_| Align::Start),
            })
            .collect(),
    )
    .unwrap()
}

struct Unit;

impl Algebra<Align> for Unit {
    type Value = ();

    fn apply(&self, _: &Align, _: &[&()]) -> Result<(), Error> {
        Ok(())
    }

    fn choose(&self, values: &[()]) -> Result<Vec<()>, Error> {
        Ok(values.first().copied().into_iter().collect())
    }
}

impl Fold<Align> for Unit {
    type Value = ();

    fn apply<'a>(
        &self,
        _: &'a Align,
        _: impl Iterator<Item = &'a ()> + Clone,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn merge(&self, selected: &mut Option<()>, next: ()) -> Result<(), Error> {
        *selected = Some(next);
        Ok(())
    }
}

fn compare<V: Eq + std::fmt::Debug>(
    source: &impl Program<Op = Align>,
    algebra: &(impl Algebra<Align, Value = V> + Fold<Align, Value = V>),
    expected: &[Vec<V>],
    occupied: usize,
    runs: usize,
    counters: &mut [usize; 4],
) {
    let dense = expected.len() * size_of::<Option<V>>();
    let packed = occupied * size_of::<V>() + runs * size_of::<[usize; 2]>();
    let budgets = [dense, packed]
        .into_iter()
        .flat_map(|total| [total.checked_sub(1), Some(total), total.checked_add(1)])
        .flatten()
        .chain([0])
        .collect::<std::collections::BTreeSet<_>>();
    for budget in budgets {
        let result = compiled::tabulate_with_budget(source, algebra, budget);
        if budget < dense.min(packed) {
            assert_eq!(
                result.err(),
                Some(Error::TableBudgetExceeded { max_bytes: budget })
            );
            counters[2] += 1;
            continue;
        }
        let table = result.unwrap();
        let (bytes, arm) = if budget >= dense {
            (dense, 0)
        } else {
            (packed, 1)
        };
        assert_eq!(matches!(table, BudgetedTable::Dense(_)), arm == 0);
        assert_eq!(table.storage_bytes(), bytes);
        assert_eq!(table.cell_count(), expected.len());
        assert_eq!(table.root(), source.root());
        assert_eq!(table.answer(), expected[source.root()].first());
        assert_eq!(table.get(expected.len()), None);
        assert_eq!(table.get(usize::MAX), None);
        for (rank, bag) in expected.iter().enumerate() {
            assert_eq!(table.get(rank), bag.first());
            counters[3] += 1;
        }
        counters[arm] += 1;
    }
}

#[test]
fn budget_boundaries_match_every_rank() {
    let mut counts = [0; 4];
    // Each rank holds one nonterminal on empty input. Mask zero exercises a
    // zero-byte packed allocation.
    for bits in 0u16..1 << RANKS {
        let grammar = mask(bits);
        let source = grammar.bind([b""]).unwrap();
        let chart = compiled::reference_chart(&source).unwrap();
        assert_eq!(chart.cells().len(), RANKS);
        let observed = (0..RANKS).fold(0_u16, |mask, rank| {
            let (nonterminal, _) = source.cell(rank).unwrap();
            let inhabited = bits & (1 << nonterminal) != 0;
            assert_eq!(chart.cells()[rank].len(), usize::from(inhabited));
            mask | (u16::from(inhabited) << rank)
        });
        let occupied = bits.count_ones() as usize;
        let runs = (observed & !(observed << 1)).count_ones() as usize;
        compare(
            &source,
            &Count,
            &tabulate_cells(&chart, &Count).unwrap(),
            occupied,
            runs,
            &mut counts,
        );
        compare(
            &source,
            &Unit,
            &tabulate_cells(&chart, &Unit).unwrap(),
            occupied,
            runs,
            &mut counts,
        );
    }
    println!(
        "budget masks={} dense={} packed={} rejected={} rank_comparisons={}",
        1 << RANKS,
        counts[0],
        counts[1],
        counts[2],
        counts[3]
    );
}

#[test]
fn packed_budget_preserves_inhabited_zero() {
    use zeno_adp::algebras::{Additive, Cost, Minimum};

    let grammar = mask(1 << (RANKS - 1));
    let source = grammar.bind([b""]).unwrap();
    let chart = compiled::reference_chart(&source).unwrap();
    let expected = tabulate_cells(&chart, &Minimum).unwrap();
    let bytes = size_of::<Cost>() + size_of::<[usize; 2]>();
    let table = compiled::tabulate_with_budget(&source, &Additive::default(), bytes).unwrap();
    assert!(matches!(table, BudgetedTable::Packed(_)));
    assert_eq!(table.storage_bytes(), bytes);
    assert_eq!(table.answer(), Some(&Cost::Finite(0)));
    for (rank, bag) in expected.iter().enumerate() {
        assert_eq!(table.get(rank), bag.first());
    }
    let unbudgeted = compiled::tabulate_compact(&source, &Additive::default()).unwrap();
    println!(
        "single inhabited zero dense_bytes={} budgeted_bytes={bytes} unbudgeted_bytes={}",
        expected.len() * size_of::<Option<Cost>>(),
        BudgetedTable::Packed(unbudgeted).storage_bytes()
    );
}
