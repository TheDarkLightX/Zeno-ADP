#[path = "../examples/support/local_classes.rs"]
mod local_classes;
mod support;

use support::{classified_questions, public_questions, words};
use zeno_adp::fast;
use zeno_adp::grammars::{
    knapsack, knapsack_source, local_alignment, local_alignment_source, matrix_chain,
    matrix_chain_source, Item,
};

#[derive(Debug, Default)]
struct Coverage {
    charts: usize,
    cells: usize,
    rules: usize,
    tree_nodes: usize,
    returned_tree_comparisons: usize,
}

impl Coverage {
    fn add(&mut self, (cells, rules, tree_nodes, recovered): (usize, usize, usize, usize)) {
        self.charts += 1;
        self.cells += cells;
        self.rules += rules;
        self.tree_nodes += tree_nodes;
        self.returned_tree_comparisons += recovered;
    }
}

fn local_reference(left: &[u8], right: &[u8]) -> i64 {
    let mut table = vec![vec![0i64; right.len() + 1]; left.len() + 1];
    let mut best = 0;
    for (i, a) in left.iter().enumerate() {
        for (j, b) in right.iter().enumerate() {
            let matched = if a == b { 2 } else { -1 };
            let score = 0
                .max(table[i][j] + matched)
                .max(table[i][j + 1] - 1)
                .max(table[i + 1][j] - 1);
            table[i + 1][j + 1] = score;
            best = best.max(score);
        }
    }
    -best
}

fn paths(m: usize, n: usize) -> usize {
    if m == 0 || n == 0 {
        1
    } else {
        paths(m - 1, n) + paths(m, n - 1) + paths(m - 1, n - 1)
    }
}

fn local_count(m: usize, n: usize) -> usize {
    let mut count = 1; // A single empty alignment.
    for used_left in 0..=m {
        for used_right in 0..=n {
            if used_left != 0 || used_right != 0 {
                count += (m - used_left + 1) * (n - used_right + 1) * paths(used_left, used_right);
            }
        }
    }
    count
}

// Covers internal starts and ends on both sides.
const LOCAL_LENGTH: usize = 3;

#[test]
fn local_all_short_binary_pairs() {
    let domain = words(*b"AC", LOCAL_LENGTH);
    let mut coverage = Coverage::default();
    for left in &domain {
        for right in &domain {
            coverage.add(public_questions(
                &local_alignment(left, right).unwrap(),
                &local_alignment_source(left, right).unwrap(),
                fast::local_alignment(left, right).unwrap(),
                local_reference(left, right),
                local_count(left.len(), right.len()),
            ));
        }
    }
    assert_eq!(coverage.charts, domain.len().pow(2));
    println!("local {coverage:?}");
}

fn split_reference(dims: &[u32]) -> (i64, usize) {
    if dims.len() == 2 {
        return (0, 1);
    }
    let mut best = i64::MAX;
    let mut count = 0;
    for split in 1..dims.len() - 1 {
        let (left, left_count) = split_reference(&dims[..=split]);
        let (right, right_count) = split_reference(&dims[split..]);
        let work = i64::from(dims[0]) * i64::from(dims[split]) * i64::from(*dims.last().unwrap());
        best = best.min(left + right + work);
        count += left_count * right_count;
    }
    (best, count)
}

#[test]
fn matrix_all_short_binary_dimension_vectors() {
    // Six dimensions mean five matrices and at most Catalan(4) bracketings.
    const MATRIX_DIMENSIONS: usize = 6;
    let mut coverage = Coverage::default();
    for dimensions in words([2, 3], MATRIX_DIMENSIONS)
        .into_iter()
        .filter(|dims| dims.len() >= 2)
    {
        let (minimum, count) = split_reference(&dimensions);
        coverage.add(public_questions(
            &matrix_chain(&dimensions).unwrap(),
            &matrix_chain_source(&dimensions).unwrap(),
            fast::matrix_chain(&dimensions).unwrap(),
            minimum,
            count,
        ));
    }
    assert_eq!(coverage.charts, (1 << (MATRIX_DIMENSIONS + 1)) - 4);
    println!("matrix {coverage:?}");
}

fn subsets(items: &[Item], capacity: usize) -> (i64, usize) {
    let mut best = 0;
    let mut count = 0;
    for mask in 0..1 << items.len() {
        let (weight, value) = items
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .fold((0, 0), |(weight, value), (_, item)| {
                (weight + item.weight, value + i64::from(item.value))
            });
        if weight <= capacity {
            best = best.max(value);
            count += 1;
        }
    }
    (-best, count)
}

#[test]
fn knapsack_all_short_binary_items_and_small_capacities() {
    // Four items admit at most 16 subsets. Capacities exercise empty, exact
    // and nonbinding capacities as well as cases with multiple best subsets.
    const MAX_ITEMS: usize = 4;
    const MAX_CAPACITY: usize = 4;
    let alphabet = [
        Item {
            weight: 1,
            value: 1,
        },
        Item {
            weight: 2,
            value: 3,
        },
    ];
    let domain = words(alphabet, MAX_ITEMS);
    let mut coverage = Coverage::default();
    for items in &domain {
        for capacity in 0..=MAX_CAPACITY {
            let (minimum, count) = subsets(items, capacity);
            coverage.add(public_questions(
                &knapsack(items, capacity).unwrap(),
                &knapsack_source(items, capacity).unwrap(),
                fast::knapsack(items, capacity).unwrap(),
                minimum,
                count,
            ));
        }
    }
    assert_eq!(coverage.charts, domain.len() * (MAX_CAPACITY + 1));
    println!("knapsack {coverage:?}");
}

#[test]
fn fused_boundaries_agree_with_reference() {
    use zeno_adp::algebras::{Additive, Cost};
    use zeno_adp::{grammars, tabulate_cells, Chart, Error};

    fn check<O: zeno_adp::algebras::ScoredOperator>(
        chart: Result<Chart<O>, Error>,
        fused: Result<fast::MinimumTable, Error>,
    ) {
        let reference = chart.and_then(|chart| {
            tabulate_cells(&chart, &Additive::default()).map(|cells| (chart.root(), cells))
        });
        match (reference, fused) {
            (Ok((root, cells)), Ok(fused)) => {
                assert_eq!(root, fused.root());
                assert!(cells
                    .iter()
                    .map(|bag| bag.first().copied())
                    .eq(fused.cells().iter().map(|value| value.map(Cost::Finite))));
            }
            (Err(reference), Err(fused)) => assert_eq!(reference, fused),
            (reference, fused) => panic!("reference {reference:?}, fused {fused:?}"),
        }
    }

    // The empty local alignment has one candidate above an absent path cell.
    check(local_alignment(b"", b""), fast::local_alignment(b"", b""));
    let free = [Item {
        weight: 0,
        value: 1,
    }];
    check(knapsack(&free, 0), fast::knapsack(&free, 0));
    for (input, min_loop) in [(&b"?"[..], 0), (&b"AU"[..], usize::MAX)] {
        check(
            grammars::nussinov(input, min_loop),
            fast::nussinov(input, min_loop),
        );
    }

    for dimensions in [&[][..], &[2][..], &[2, 0][..]] {
        check(matrix_chain(dimensions), fast::matrix_chain(dimensions));
        assert_eq!(
            fast::matrix_chain(dimensions),
            Err(Error::InvalidDimensions)
        );
    }

    // Two factors of u32::MAX overflow i64 in a rule.
    let overflowing_rule = [u32::MAX, u32::MAX, 1];
    check(
        matrix_chain(&overflowing_rule),
        fast::matrix_chain(&overflowing_rule),
    );
    assert_eq!(
        matrix_chain(&overflowing_rule).unwrap_err(),
        Error::Overflow
    );

    // The cube is 8e18, which fits. One split accumulates 8e18 + 4e18,
    // which overflows even though the other split is representable.
    const LARGE: u32 = 2_000_000;
    let overflowing_sum = [LARGE, LARGE, LARGE, LARGE / 2];
    assert!(matrix_chain(&overflowing_sum).is_ok());
    check(
        matrix_chain(&overflowing_sum),
        fast::matrix_chain(&overflowing_sum),
    );
    assert_eq!(fast::matrix_chain(&overflowing_sum), Err(Error::Overflow));
}

#[test]
fn local_classes_agree_with_forward_paths() {
    use local_classes::Columns;
    use std::collections::BTreeMap;
    use zeno_adp::algebras::Cost;
    use zeno_adp::grammars::Align;

    fn extend(
        left: &[u8],
        right: &[u8],
        columns: &mut Vec<Align>,
        cost: i64,
        classes: &mut BTreeMap<Vec<Align>, (i64, u128)>,
    ) {
        if !columns.is_empty() {
            let group = classes.entry(columns.clone()).or_insert((cost, 0));
            group.0 = group.0.min(cost);
            group.1 += 1;
        }
        if let Some((&a, suffix)) = left.split_first() {
            columns.push(Align::Left(a));
            extend(suffix, right, columns, cost + 1, classes);
            columns.pop();
            if let Some((&b, suffix_right)) = right.split_first() {
                columns.push(Align::Diagonal { left: a, right: b });
                extend(
                    suffix,
                    suffix_right,
                    columns,
                    cost + if a == b { -2 } else { 1 },
                    classes,
                );
                columns.pop();
            }
        }
        if let Some((&b, suffix)) = right.split_first() {
            columns.push(Align::Right(b));
            extend(left, suffix, columns, cost + 1, classes);
            columns.pop();
        }
    }

    let domain = words(*b"AC", LOCAL_LENGTH);
    let (mut cells, mut ambiguities, mut classes) = (0, 0, 0);
    for left in &domain {
        for right in &domain {
            let chart = local_alignment(left, right).unwrap();
            let mut expected = BTreeMap::from([(Vec::new(), (0, 1))]);
            for i in 0..=left.len() {
                for j in 0..=right.len() {
                    extend(&left[i..], &right[j..], &mut Vec::new(), 0, &mut expected);
                }
            }
            let minima: Vec<_> = expected
                .iter()
                .map(|(key, (cost, _))| (key.clone(), Cost::Finite(*cost)))
                .collect();
            let (ambiguous, root) = classified_questions(&chart, Columns, &minima);
            assert!(root
                .into_iter()
                .eq(expected.into_iter().map(|(key, (_, count))| (key, count))));
            cells += chart.cells().len();
            ambiguities += ambiguous;
            classes += minima.len();
        }
    }
    println!(
        "local columns: {} charts, {cells} cells, {ambiguities} ambiguous cells, {classes} root classes",
        domain.len().pow(2)
    );
}
