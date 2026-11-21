use std::cell::RefCell;

use zeno_adp::algebras::{Cost, Count, Enumerate};
use zeno_adp::sets::{partitions, PartitionOp};
use zeno_adp::{tabulate_cells, Algebra, Error, Tree};

use super::audit_example;

// Four elements give 15 independently selectable nonempty blocks.
const ELEMENTS: u32 = 4;
const SUBSETS: usize = 1 << ELEMENTS;

struct BlockScore;

fn price(block: usize) -> i64 {
    match block.count_ones() {
        1 => 2,
        2 => -2,
        _ => 1,
    }
}

impl Algebra<PartitionOp> for BlockScore {
    type Value = Cost;

    fn apply(&self, operator: &PartitionOp, children: &[&Cost]) -> Result<Cost, Error> {
        match *operator {
            PartitionOp::Empty => Ok(Cost::Finite(0)),
            PartitionOp::Block(block) => children[0].plus(Cost::Finite(price(block))),
        }
    }

    fn choose(&self, candidates: &[Cost]) -> Result<Vec<Cost>, Error> {
        Ok(candidates.iter().copied().min().into_iter().collect())
    }
}

/// Restricted growth labels enumerate equivalence relations on the carrier.
/// Introduce a block at its least member, regardless of later membership.
fn oracle_partitions(set: usize) -> Vec<Vec<usize>> {
    fn visit(elems: &[usize], blocks: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        let Some((&element, remain)) = elems.split_first() else {
            out.push(blocks.clone());
            return;
        };
        for block in 0..blocks.len() {
            blocks[block] |= element;
            visit(remain, blocks, out);
            blocks[block] ^= element;
        }
        blocks.push(element);
        visit(remain, blocks, out);
        blocks.pop();
    }

    let members: Vec<_> = (0..ELEMENTS)
        .map(|i| 1 << i)
        .filter(|&bit| set & bit != 0)
        .collect();
    let mut out = Vec::new();
    visit(&members, &mut Vec::new(), &mut out);
    out
}

fn blocks(mut tree: &Tree<PartitionOp>) -> Vec<usize> {
    let mut answer = Vec::new();
    while let PartitionOp::Block(block) = tree.operator {
        answer.push(block);
        tree = &tree.children[0];
    }
    answer
}

#[test]
fn subset_partitions_match_all_block_families_at_every_cell() {
    let oracle: Vec<_> = (0..SUBSETS).map(oracle_partitions).collect();
    let families = 1 << (SUBSETS - 1);
    let mut cells = 0;
    let mut occurrences = 0;
    let mut maximum_rules = 0;
    for family in 0..families {
        let allowed = |block: usize| family & (1 << (block - 1)) != 0;
        let chart = partitions(ELEMENTS, allowed).unwrap();
        assert_eq!(chart.cells().len(), SUBSETS);
        assert_eq!(chart.root(), SUBSETS - 1);
        let counts = tabulate_cells(&chart, &Count).unwrap();
        let scores = tabulate_cells(&chart, &BlockScore).unwrap();
        let terms = tabulate_cells(&chart, &Enumerate).unwrap();
        for set in 0..SUBSETS {
            let mut expected: Vec<_> = oracle[set]
                .iter()
                .filter(|partition| partition.iter().all(|&block| allowed(block)))
                .cloned()
                .collect();
            let mut actual: Vec<_> = terms[set].iter().map(blocks).collect();
            actual.sort();
            expected.sort();
            assert_eq!(actual, expected, "block family {family}, subset {set}");
            assert_eq!(
                counts[set].first().copied().unwrap_or(0),
                expected.len() as u128
            );
            let min = expected
                .iter()
                .map(|partition| Cost::Finite(partition.iter().map(|&block| price(block)).sum()))
                .min();
            assert_eq!(scores[set].first().copied(), min);
            occurrences += actual.len();
        }
        cells += chart.cells().len();
        maximum_rules = maximum_rules.max(chart.cells().iter().map(Vec::len).sum::<usize>());
    }
    assert_eq!(cells, 524_288);
    let audited_nodes = audit_example(&partitions(ELEMENTS, |_| true).unwrap(), &BlockScore);
    println!("sets: {families} block families, {cells} cells, {occurrences} occurrences, {maximum_rules} max chart rules, {audited_nodes} audited tree nodes");
}

#[test]
fn subset_boundaries_and_anchor_control() {
    let called = RefCell::new(Vec::new());
    let chart = partitions(ELEMENTS, |block| {
        called.borrow_mut().push(block);
        block == 1
    })
    .unwrap();
    assert_eq!(called.into_inner(), (1..SUBSETS).collect::<Vec<_>>());
    let count = tabulate_cells(&chart, &Count).unwrap();
    assert_eq!(count[0], [1]);
    assert_eq!(count[1], [1]);
    assert!(count[2].is_empty());
    let empty = partitions(0, |_| panic!("no nonempty blocks")).unwrap();
    assert_eq!(tabulate_cells(&empty, &Count).unwrap(), [vec![1]]);
    assert!(matches!(
        partitions(usize::BITS, |_| true),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        partitions(usize::BITS - 1, |_| true),
        Err(Error::Overflow)
    ));

    // With only singleton blocks, choosing any first block adds both orders.
    let only_singletons = |mask: usize| mask.is_power_of_two();
    let unanchored = (1usize..SUBSETS)
        .filter(|&block| block & 3 == block && only_singletons(block))
        .count();
    let anchored = partitions(ELEMENTS, only_singletons).unwrap();
    assert_eq!(tabulate_cells(&anchored, &Count).unwrap()[3], [1]);
    assert_eq!(unanchored, 2);
}

#[test]
fn pivot_observation_for_finite_relation() {
    let chart = partitions(ELEMENTS, |_| true).unwrap();
    let mut observations = Vec::new();
    for rules in chart.cells().iter().skip(1) {
        for block in 1..SUBSETS {
            observations.push(usize::from(
                rules
                    .iter()
                    .any(|rule| rule.operator == PartitionOp::Block(block)),
            ));
        }
    }
    println!("pivot-observations {observations:?}");
}
