use std::collections::BTreeMap;
use std::ops::Range;

use zeno_adp::algebras::{Cost, Count, Enumerate, Minimum};
use zeno_adp::forests::{alignment, edit, edit_reference, ForestOp, Node};
use zeno_adp::{tabulate, tabulate_cells, Tree};

use super::audit_example;

// Four nodes replay the preceding cut research. Three on each side allow
// every projection of common superforests through six nodes.
const EDIT_NODES: usize = 4;
const ALIGNMENT_NODES: usize = 3;

struct Fixture {
    ends: Vec<usize>,
    labels: Vec<u8>,
    forest: Vec<Node<u8>>,
    spans: usize,
}

fn shapes(max: usize) -> Vec<Vec<Vec<usize>>> {
    let mut by_size = vec![vec![vec![]]];
    for size in 1..=max {
        let mut current = Vec::new();
        for first_size in 1..=size {
            for children in &by_size[first_size - 1] {
                for siblings in &by_size[size - first_size] {
                    let mut shape = vec![first_size];
                    shape.extend(children.iter().map(|end| end + 1));
                    shape.extend(siblings.iter().map(|end| end + first_size));
                    current.push(shape);
                }
            }
        }
        by_size.push(current);
    }
    by_size
}

fn fixtures(max: usize) -> Vec<Fixture> {
    fn materialize(ends: &[usize], labels: &[u8], span: Range<usize>) -> Vec<Node<u8>> {
        let mut result = Vec::new();
        let mut root = span.start;
        while root < span.end {
            result.push(Node::new(
                labels[root],
                materialize(ends, labels, root + 1..ends[root]),
            ));
            root = ends[root];
        }
        result
    }

    let mut result = Vec::new();
    for ends in shapes(max).into_iter().flatten() {
        let size = ends.len();
        let spans = (0..=size)
            .flat_map(|start| (start..=size).map(move |end| start..end))
            .filter(|span| ends[span.clone()].iter().all(|&end| end <= span.end))
            .count();
        for labeling in 0..1 << size {
            let labels: Vec<_> = (0..size).map(|bit| ((labeling >> bit) & 1) as u8).collect();
            let forest = materialize(&ends, &labels, 0..size);
            result.push(Fixture {
                ends: ends.clone(),
                labels,
                forest,
                spans,
            });
        }
    }
    result
}

struct Projection {
    kept: Vec<usize>,
    depth: Vec<usize>,
}

fn project(ends: &[usize], span: Range<usize>, selected: usize) -> Projection {
    let kept: Vec<_> = span
        .enumerate()
        .filter_map(|(bit, index)| (selected & (1 << bit) != 0).then_some(index))
        .collect();
    let depth = kept
        .iter()
        .enumerate()
        .map(|(index, &node)| {
            kept[..index]
                .iter()
                .filter(|&&ancestor| ends[ancestor] > node)
                .count()
        })
        .collect();
    Projection { kept, depth }
}

fn retained(ends: &[usize], span: Range<usize>) -> Vec<Projection> {
    (0..1 << span.len())
        .map(|mask| project(ends, span.clone(), mask))
        .collect()
}

fn edit_oracle(
    left: &Fixture,
    right: &Fixture,
    a: &Range<usize>,
    b: &Range<usize>,
    x: &[Projection],
    y: &[Projection],
) -> (u128, Cost) {
    let mut count = 0;
    let mut best = a.len() + b.len();
    for l in x {
        for r in y {
            if l.depth == r.depth {
                let changes = l
                    .kept
                    .iter()
                    .zip(&r.kept)
                    .filter(|&(i, j)| left.labels[*i] != right.labels[*j])
                    .count();
                best = best.min(a.len() + b.len() - 2 * l.kept.len() + changes);
                count += 1;
            }
        }
    }
    (count, Cost::Finite(best as i64))
}

#[test]
fn edit_minima_and_cut_multiplicities_at_every_cell() {
    let domain = fixtures(EDIT_NODES);
    assert_eq!(domain.len(), 275);
    let mut cells = 0;
    let mut local_rules = 0;
    let mut cut_rules = 0;
    let mut mapping_counts = 0;
    let mut distinct_script_counts = 0;
    for left in &domain {
        for right in &domain {
            let local = edit(&left.forest, &right.forest).unwrap();
            let cut = edit_reference(&left.forest, &right.forest).unwrap();
            assert_eq!(local.spans(), cut.spans());
            assert_eq!(cut.spans().len(), left.spans * right.spans);
            assert_eq!(
                cut.spans()[cut.chart().root()],
                (0..left.ends.len(), 0..right.ends.len())
            );
            let minimum = tabulate_cells(local.chart(), &Minimum).unwrap();
            let cut_minimum = tabulate_cells(cut.chart(), &Minimum).unwrap();
            assert_eq!(
                cut_minimum, minimum,
                "left/right ends {:?} {:?}",
                left.ends, right.ends
            );
            let cut_count = tabulate_cells(cut.chart(), &Count).unwrap();
            let script_count = tabulate_cells(local.chart(), &Count).unwrap();

            let mut left_projections = BTreeMap::new();
            let mut right_projections = BTreeMap::new();
            for (rank, (a, b)) in cut.spans().iter().enumerate() {
                assert!(left.ends[a.clone()].iter().all(|&end| end <= a.end));
                assert!(right.ends[b.clone()].iter().all(|&end| end <= b.end));
                let x = left_projections
                    .entry((a.start, a.end))
                    .or_insert_with(|| retained(&left.ends, a.clone()));
                let y = right_projections
                    .entry((b.start, b.end))
                    .or_insert_with(|| retained(&right.ends, b.clone()));
                let (count, score) = edit_oracle(left, right, a, b, x, y);
                assert_eq!(cut_minimum[rank], [score], "spans {a:?} {b:?}");
                assert_eq!(cut_count[rank], [count], "spans {a:?} {b:?}");
                mapping_counts += count;
                distinct_script_counts += usize::from(cut_count[rank] != script_count[rank]);
            }
            cells += cut.spans().len();
            local_rules += local.chart().cells().iter().map(Vec::len).sum::<usize>();
            cut_rules += cut.chart().cells().iter().map(Vec::len).sum::<usize>();
        }
    }
    assert!(local_rules < cut_rules);
    assert!(distinct_script_counts > 0);
    println!("edit: {} inputs, {cells} cells, {local_rules} first-root rules, {cut_rules} cut rules, {mapping_counts} mappings, {distinct_script_counts} cells with different script counts", domain.len().pow(2));
}

/// Independent alignment oracle. Enumerate a superforest and keep a node on
/// either side or both. Flatten each projection by counting retained ancestors.
type AlignmentKey = Vec<(usize, Option<usize>, Option<usize>)>;

struct Alignment {
    key: AlignmentKey,
    pairs: Vec<(usize, usize)>,
    gaps: usize,
}

type Alignments = BTreeMap<(Vec<usize>, Vec<usize>), Vec<Alignment>>;

fn all_alignments() -> Alignments {
    let mut result: Alignments = BTreeMap::new();
    for shape in shapes(2 * ALIGNMENT_NODES).into_iter().flatten() {
        let size = shape.len();
        let full = (1usize << size) - 1;
        let depth = project(&shape, 0..size, full).depth;
        for left in 0..=full {
            let required_on_right = full ^ left;
            let optional_on_right = left;
            for both in 0..=full {
                if both & optional_on_right != both {
                    continue;
                }
                let right = required_on_right | both;
                if left.count_ones() as usize > ALIGNMENT_NODES
                    || right.count_ones() as usize > ALIGNMENT_NODES
                {
                    continue;
                }
                let l = project(&shape, 0..size, left);
                let r = project(&shape, 0..size, right);
                let pairs = l
                    .kept
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| r.kept.binary_search(node).ok().map(|j| (i, j)))
                    .collect();
                result
                    .entry((l.depth, r.depth))
                    .or_default()
                    .push(Alignment {
                        key: depth
                            .iter()
                            .enumerate()
                            .map(|(node, &level)| {
                                (
                                    level,
                                    l.kept.binary_search(&node).ok(),
                                    r.kept.binary_search(&node).ok(),
                                )
                            })
                            .collect(),
                        pairs,
                        gaps: size - both.count_ones() as usize,
                    });
            }
        }
    }
    for candidates in result.values_mut() {
        candidates.sort_by(|first, second| first.key.cmp(&second.key));
    }
    result
}

fn alignment_key(tree: &Tree<ForestOp>, left: usize, right: usize) -> AlignmentKey {
    fn visit(
        tree: &Tree<ForestOp>,
        depth: usize,
        left: usize,
        right: usize,
        key: &mut AlignmentKey,
    ) {
        let (l, r) = match tree.operator {
            ForestOp::Empty => return,
            ForestOp::Match {
                left: a, right: b, ..
            } => (Some(a - left), Some(b - right)),
            ForestOp::GapRight(a) => (Some(a - left), None),
            ForestOp::GapLeft(b) => (None, Some(b - right)),
            _ => panic!("expected alignment constructor"),
        };
        key.push((depth, l, r));
        visit(&tree.children[0], depth + 1, left, right, key);
        visit(&tree.children[1], depth, left, right, key);
    }

    let mut key = Vec::new();
    visit(tree, 0, left, right, &mut key);
    key
}

#[test]
fn alignment_matches_all_superforest_projections() {
    let domain = fixtures(ALIGNMENT_NODES);
    assert_eq!(domain.len(), 51);
    let oracle = all_alignments();
    let candidates = oracle.values().map(Vec::len).sum::<usize>();
    let mut cells = 0;
    let mut rules = 0;
    let mut occurrences = 0;
    for left in &domain {
        for right in &domain {
            let actual = alignment(&left.forest, &right.forest).unwrap();
            assert_eq!(actual.spans().len(), left.spans * right.spans);
            let scores = tabulate_cells(actual.chart(), &Minimum).unwrap();
            let counts = tabulate_cells(actual.chart(), &Count).unwrap();
            let terms = tabulate_cells(actual.chart(), &Enumerate).unwrap();
            for (rank, (a, b)) in actual.spans().iter().enumerate() {
                let l = project(&left.ends, a.clone(), (1 << a.len()) - 1);
                let r = project(&right.ends, b.clone(), (1 << b.len()) - 1);
                let expected = &oracle[&(l.depth, r.depth)];
                let best = expected
                    .iter()
                    .map(|candidate| {
                        let changes = candidate
                            .pairs
                            .iter()
                            .filter(|&&(i, j)| {
                                left.labels[a.start + i] != right.labels[b.start + j]
                            })
                            .count();
                        candidate.gaps + changes
                    })
                    .min()
                    .unwrap();
                assert_eq!(scores[rank], [Cost::Finite(best as i64)]);
                assert_eq!(counts[rank], [expected.len() as u128]);
                let mut keys: Vec<_> = terms[rank]
                    .iter()
                    .map(|tree| alignment_key(tree, a.start, b.start))
                    .collect();
                keys.sort();
                assert!(keys
                    .iter()
                    .eq(expected.iter().map(|alignment| &alignment.key)));

                occurrences += expected.len();
            }
            cells += actual.spans().len();
            rules += actual.chart().cells().iter().map(Vec::len).sum::<usize>();
        }
    }
    println!("alignment: {} inputs, {cells} cells, {rules} rules, {candidates} unlabeled oracle candidates, {occurrences} occurrences", domain.len().pow(2));
}

#[test]
fn cut_mapping_identity_matches_retained_node_pairs() {
    fn collect_mapping(tree: &Tree<ForestOp>, mapping: &mut Vec<(usize, usize)>) {
        let ForestOp::Cut { pairs, .. } = &tree.operator else {
            panic!("expected a cut");
        };
        mapping.extend(pairs);
        for child in &tree.children {
            collect_mapping(child, mapping);
        }
    }

    let domain = fixtures(ALIGNMENT_NODES);
    let mut cells = 0;
    let mut occurrences = 0;
    for left in &domain {
        for right in &domain {
            let cut = edit_reference(&left.forest, &right.forest).unwrap();
            let derivations = tabulate_cells(cut.chart(), &Enumerate).unwrap();
            for (rank, (a, b)) in cut.spans().iter().enumerate() {
                let mut actual: Vec<_> = derivations[rank]
                    .iter()
                    .map(|tree| {
                        let mut mapping = Vec::new();
                        collect_mapping(tree, &mut mapping);
                        mapping.sort_unstable();
                        mapping
                    })
                    .collect();
                let mut expected = Vec::new();
                for l in retained(&left.ends, a.clone()) {
                    for r in retained(&right.ends, b.clone()) {
                        if l.depth == r.depth {
                            expected.push(l.kept.iter().copied().zip(r.kept).collect::<Vec<_>>());
                        }
                    }
                }
                actual.sort_unstable();
                expected.sort_unstable();
                assert_eq!(actual, expected);
                occurrences += actual.len();
            }
            cells += cut.spans().len();
        }
    }
    println!("cut mapping identity: {cells} cells, {occurrences} occurrences");
}

#[test]
fn forest_semantic_controls_and_reference_audits() {
    let leaf = |label| Node::new(label, vec![]);
    let promote = [Node::new(b'a', vec![leaf(b'b')])];
    let right = [leaf(b'b')];
    let reference = edit_reference(&promote, &right).unwrap();
    let projected = alignment(&promote, &right).unwrap();
    assert_eq!(
        tabulate(reference.chart(), &Minimum).unwrap(),
        [Cost::Finite(1)]
    );
    assert_eq!(
        tabulate(projected.chart(), &Minimum).unwrap(),
        [Cost::Finite(1)]
    );
    // A whole-root cut can only keep the original root or drop its entire
    // subtree. Keeping costs a rename and a deletion. Dropping costs three.
    let whole_root_only = usize::min(1 + 1, 2 + 1);
    assert_eq!(whole_root_only, 2);

    let in_order = [leaf(b'a'), leaf(b'b')];
    let reversed = [leaf(b'b'), leaf(b'a')];
    let compare = edit_reference(&in_order, &reversed).unwrap();
    assert_eq!(
        tabulate(compare.chart(), &Minimum).unwrap(),
        [Cost::Finite(2)]
    );
    assert_eq!(
        tabulate(
            edit_reference(&in_order, &in_order).unwrap().chart(),
            &Minimum
        )
        .unwrap(),
        [Cost::Finite(0)]
    );

    // The two unmatched z roots cover overlapping groups of leaf matches.
    let left = [Node::new(b'z', vec![leaf(b'a'), leaf(b'b')]), leaf(b'c')];
    let right = [leaf(b'a'), Node::new(b'z', vec![leaf(b'b'), leaf(b'c')])];
    let edit_distance = tabulate(edit_reference(&left, &right).unwrap().chart(), &Minimum).unwrap();
    let alignment_distance = tabulate(alignment(&left, &right).unwrap().chart(), &Minimum).unwrap();
    assert_eq!(edit_distance, [Cost::Finite(2)]);
    assert!(alignment_distance > edit_distance);
    let mut observed_promotion = Vec::new();
    for bits in 0..1 << 3 {
        let label = |index| u8::from(bits & (1 << index) != 0);
        let left = [Node::new(label(0), vec![leaf(label(1))])];
        let right = [leaf(label(2))];
        let output = edit_reference(&left, &right).unwrap();
        let [Cost::Finite(value)] = tabulate(output.chart(), &Minimum).unwrap()[..] else {
            panic!("expected a finite edit cost");
        };
        observed_promotion.push(value);
    }
    println!("promotion-observations {observed_promotion:?}");
    let cut_nodes = audit_example(reference.chart(), &Minimum);
    let edit_nodes = audit_example(
        edit(&promote, &[leaf(b'a'), leaf(b'b')]).unwrap().chart(),
        &Minimum,
    );
    let alignment_nodes = audit_example(projected.chart(), &Minimum);
    println!("forest controls: edit {edit_distance:?}, alignment {alignment_distance:?}, audits {cut_nodes}/{edit_nodes}/{alignment_nodes} tree nodes");
}
