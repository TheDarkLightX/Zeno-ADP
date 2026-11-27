use zeno_adp::algebras::{Additive, Cost, Enumerate, ScoredOperator};
use zeno_adp::fast::alignment_linear_space;
use zeno_adp::grammars::{alignment, Align};
use zeno_adp::{tabulate_cells, Tree};

const MAX_LENGTH: usize = 3; // Exhaustive small domain with both transposition orientations.
                             // The review used this depth (the first beyond 16 bits) and stack size.
const LONG_ALIGNMENT: usize = u16::MAX as usize + 1;
const DROP_THREAD_STACK: usize = 2 * 1024 * 1024;

fn cost(tree: &Tree<Align>) -> usize {
    let mut node = Some(tree);
    let mut sum = 0;
    while let Some(tree) = node {
        let Cost::Finite(local) = tree.operator.cost() else {
            unreachable!()
        };
        sum += usize::try_from(local).unwrap();
        node = tree.children.first();
    }
    sum
}

#[test]
fn linear_recovery_matches_the_first_exhaustive_witness_on_every_rank() {
    let words: Vec<Vec<u8>> = (0..=MAX_LENGTH)
        .flat_map(|n| {
            (0..1_usize << n).map(move |bits| (0..n).map(|i| ((bits >> i) & 1) as u8).collect())
        })
        .collect();
    let mut ranks = 0;
    for left in &words {
        for right in &words {
            let chart = alignment(left, right).unwrap();
            let scores = tabulate_cells(&chart, &Additive::default()).unwrap();
            let trees = tabulate_cells(&chart, &Enumerate).unwrap();
            for i in 0..=left.len() {
                for j in 0..=right.len() {
                    let rank = i * (right.len() + 1) + j;
                    let path = alignment_linear_space(&left[..i], &right[..j]).unwrap();
                    assert_eq!(
                        scores[rank],
                        [Cost::Finite(i64::try_from(path.distance()).unwrap())]
                    );
                    let first = trees[rank]
                        .iter()
                        .find(|tree| cost(tree) == path.distance())
                        .unwrap();
                    assert_eq!(
                        &path.into_tree(),
                        first,
                        "prefixes {:?} vs {:?}",
                        &left[..i],
                        &right[..j]
                    );
                    ranks += 1;
                }
            }
        }
    }
    println!("first alignment witnesses: ranks={ranks}, disagreements=0");
    assert_eq!(ranks, 2401);
}

#[test]
fn skinny_alignment_uses_full_width_coordinates_and_a_flat_path() {
    // Cross the first 16-bit column boundary while keeping recurrence work linear.
    let right = vec![b'a'; LONG_ALIGNMENT];
    let path = alignment_linear_space(b"a", &right).unwrap();
    assert_eq!(path.distance(), LONG_ALIGNMENT - 1);
    assert_eq!(path.columns().len(), LONG_ALIGNMENT);
    let (last, gaps) = path.columns().split_last().unwrap();
    assert_eq!(
        *last,
        Align::Diagonal {
            left: b'a',
            right: b'a'
        }
    );
    assert!(gaps.iter().all(|&col| col == Align::Right(b'a')));
}

#[test]
fn recovered_tree_drops_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(DROP_THREAD_STACK)
        .spawn(|| {
            let input = vec![b'a'; LONG_ALIGNMENT];
            let path = alignment_linear_space(&input, &[]).unwrap();
            assert_eq!(path.distance(), LONG_ALIGNMENT);
            assert_eq!(path.columns().len(), LONG_ALIGNMENT);
            assert!(path.columns().iter().all(|&op| op == Align::Left(b'a')));
            let tree = path.into_tree();
            let mut node = &tree;
            for _ in 0..LONG_ALIGNMENT {
                assert_eq!(node.operator, Align::Left(b'a'));
                assert_eq!(node.children.len(), 1);
                node = &node.children[0];
            }
            assert_eq!(node.operator, Align::Start);
            assert!(node.children.is_empty());
            drop(tree);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn tree_drop_visits_all_payloads_even_during_unwinding() {
    use std::cell::Cell;

    struct Payload<'a> {
        drops: &'a Cell<usize>,
        panic: bool,
    }

    impl Drop for Payload<'_> {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
            assert!(!self.panic, "one payload panics");
        }
    }

    let drops = Cell::new(0);
    let node = |panic, children| Tree {
        operator: Payload {
            drops: &drops,
            panic,
        },
        children,
    };
    let tree = node(
        false,
        vec![
            node(true, vec![node(false, vec![])]),
            node(false, vec![node(false, vec![]), node(false, vec![])]),
        ],
    );
    let replacement_drops = Cell::new(0);
    let (root, children) = tree.into_parts_with_replacement(Payload {
        drops: &replacement_drops,
        panic: false,
    });
    assert_eq!(replacement_drops.get(), 1);
    assert_eq!(drops.get(), 0);
    assert_eq!(children.len(), 2);
    let rebuilt = Tree {
        operator: root,
        children,
    };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(rebuilt)));
    assert!(result.is_err());
    assert_eq!(drops.get(), 6);
}
