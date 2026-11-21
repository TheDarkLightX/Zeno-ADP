use super::Checks;
use std::ops::Range;
use zeno_adp::algebras::{Additive, Cost, Count, Minimum, MinimumCount, Optimum};
use zeno_adp::compiled;
use zeno_adp::forests::{self, ForestOp, Node};
use zeno_adp::{tabulate_cells, Error, Tree};

type Forest = Vec<Node<u8>>;

fn inputs() -> Vec<(Forest, Forest)> {
    let mut tiny = vec![vec![]];
    for a in b"ab" {
        tiny.push(vec![Node::new(*a, vec![])]);
        for b in b"ab" {
            tiny.push(vec![Node::new(*a, vec![Node::new(*b, vec![])])]);
        }
    }
    let mut pairs: Vec<_> = tiny
        .iter()
        .flat_map(|a| tiny.iter().map(move |b| (a.clone(), b.clone())))
        .collect();
    let siblings = vec![Node::new(b'a', vec![]), Node::new(b'b', vec![])];
    pairs.push((vec![Node::new(b'a', siblings.clone())], siblings.clone()));
    pairs.push((
        siblings,
        vec![Node::new(b'b', vec![]), Node::new(b'a', vec![])],
    ));
    pairs
}

fn raw_align(a: &[Node<u8>], b: &[Node<u8>]) -> i64 {
    let mut best = i64::MAX;
    if let Some((root, rest)) = a.split_first() {
        for split in 0..=b.len() {
            best =
                best.min(1 + raw_align(&root.children, &b[..split]) + raw_align(rest, &b[split..]));
        }
    }
    if let Some((root, rest)) = b.split_first() {
        for split in 0..=a.len() {
            best =
                best.min(1 + raw_align(&a[..split], &root.children) + raw_align(&a[split..], rest));
        }
    }
    if let (Some((x, tail_a)), Some((y, tail_b))) = (a.split_first(), b.split_first()) {
        best = best.min(
            i64::from(x.label != y.label)
                + raw_align(&x.children, &y.children)
                + raw_align(tail_a, tail_b),
        );
    }
    if a.is_empty() && b.is_empty() {
        0
    } else {
        best
    }
}

fn flatten(forest: &[Node<u8>], depth: usize, out: &mut Vec<(u8, usize)>) {
    for node in forest {
        out.push((node.label, depth));
        flatten(&node.children, depth + 1, out);
    }
}

fn subtree_rows(input: &[(u8, usize)]) -> Vec<Node<u8>> {
    let mut forest = Vec::new();
    let mut rest = input;
    while let Some((&(label, depth), tail)) = rest.split_first() {
        let cut = tail.iter().position(|x| x.1 <= depth).unwrap_or(tail.len());
        forest.push(Node::new(label, subtree_rows(&tail[..cut])));
        rest = &tail[cut..];
    }
    forest
}

fn projection(tree: &Tree<ForestOp>, side: usize, input: &[(u8, usize)]) -> Vec<Node<u8>> {
    let occurrence = match tree.operator {
        ForestOp::Empty => return Vec::new(),
        ForestOp::Match { left, right, .. } => Some([left, right][side]),
        ForestOp::GapRight(left) => (side == 0).then_some(left),
        ForestOp::GapLeft(right) => (side == 1).then_some(right),
        _ => unreachable!(),
    };
    let inside = projection(&tree.children[0], side, input);
    let mut forest = match occurrence {
        Some(index) => vec![Node::new(input[index].0, inside)],
        None => inside,
    };
    forest.extend(projection(&tree.children[1], side, input));
    forest
}

pub fn alignment() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (a, b) in inputs() {
        let reference = forests::alignment(&a, &b)?;
        let source = forests::alignment_source(&a, &b)?;
        let chart = reference.chart();
        checks.chart(chart);
        checks.compiled(&source, chart, &Additive::default())?;
        checks.compiled(&source, chart, &Count)?;
        let table = tabulate_cells(chart, &Minimum)?;
        let mut left = Vec::new();
        let mut right = Vec::new();
        flatten(&a, 0, &mut left);
        flatten(&b, 0, &mut right);
        for ((x, y), values) in reference.spans().iter().zip(table) {
            assert_eq!(
                values,
                [Cost::Finite(raw_align(
                    &subtree_rows(&left[x.clone()]),
                    &subtree_rows(&right[y.clone()])
                ))]
            );
        }
        let best = compiled::best(&source)?;
        let witness = best.recover().first_minimum_tree()?.unwrap();
        assert_eq!(projection(&witness.tree, 0, &left), a);
        assert_eq!(projection(&witness.tree, 1, &right), b);
    }
    Ok(checks)
}

fn retained(nodes: &[(u8, usize)], mask: usize) -> Vec<(u8, usize)> {
    let mut ancestors = Vec::new();
    let mut view = Vec::new();
    for (i, &(label, depth)) in nodes.iter().enumerate() {
        while ancestors.last().is_some_and(|&d| d >= depth) {
            ancestors.pop();
        }
        if mask & (1 << i) != 0 {
            view.push((label, ancestors.len()));
            ancestors.push(depth);
        }
    }
    view
}

fn raw_mappings(a: &[(u8, usize)], b: &[(u8, usize)]) -> (Cost, u128) {
    let mut cost = i64::MAX;
    let mut count = 0;
    for left in 0..1 << a.len() {
        let x = retained(a, left);
        for right in 0..1 << b.len() {
            let y = retained(b, right);
            if !x.iter().map(|item| item.1).eq(y.iter().map(|item| item.1)) {
                continue;
            }
            count += 1;
            let changed = x.iter().zip(&y).filter(|(a, b)| a.0 != b.0).count();
            cost = cost.min((a.len() + b.len() - 2 * x.len() + changed) as i64);
        }
    }
    (Cost::Finite(cost), count)
}

// Count the shortest scripts independently by promoting the first root
// in the remaining raw sibling list and branching on the next operation.
fn raw_scripts(a: &[Node<u8>], b: &[Node<u8>]) -> (i64, u128) {
    let mut options = Vec::new();
    if let Some((x, tail)) = a.split_first() {
        let promoted: Vec<_> = x.children.iter().chain(tail).cloned().collect();
        let (cost, count) = raw_scripts(&promoted, b);
        options.push((cost + 1, count));
    }
    if let Some((y, tail)) = b.split_first() {
        let promoted: Vec<_> = y.children.iter().chain(tail).cloned().collect();
        let (cost, count) = raw_scripts(a, &promoted);
        options.push((cost + 1, count));
    }
    if let (Some((x, tail_a)), Some((y, tail_b))) = (a.split_first(), b.split_first()) {
        let (inside, inside_count) = raw_scripts(&x.children, &y.children);
        let (suffix, suffix_count) = raw_scripts(tail_a, tail_b);
        options.push((
            inside + suffix + i64::from(x.label != y.label),
            inside_count * suffix_count,
        ));
    }
    let Some(best) = options.iter().map(|&(cost, _)| cost).min() else {
        return (0, 1);
    };
    (
        best,
        options
            .into_iter()
            .filter(|x| x.0 == best)
            .map(|x| x.1)
            .sum(),
    )
}

pub fn edit() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (a, b) in inputs() {
        let cut = forests::edit_reference(&a, &b)?;
        let scripts = forests::edit(&a, &b)?;
        let source = forests::edit_source(&a, &b)?;
        checks.chart(cut.chart());
        assert_eq!(cut.spans(), scripts.spans());
        checks.compiled(&source, scripts.chart(), &Additive::default())?;
        let minimum = tabulate_cells(cut.chart(), &Minimum)?;
        let counts = tabulate_cells(cut.chart(), &Count)?;
        let edits = tabulate_cells(scripts.chart(), &MinimumCount)?;
        let mut left = Vec::new();
        let mut right = Vec::new();
        flatten(&a, 0, &mut left);
        flatten(&b, 0, &mut right);
        for (rank, (x, y)) in cut.spans().iter().enumerate() {
            let sub = |side: &[(_, _)], span: &Range<usize>| subtree_rows(&side[span.clone()]);
            let (cost, count) = raw_mappings(&left[x.clone()], &right[y.clone()]);
            let (script_cost, script_count) = raw_scripts(&sub(&left, x), &sub(&right, y));
            assert_eq!(minimum[rank], [cost]);
            assert_eq!(counts[rank], [count]);
            assert_eq!(
                edits[rank],
                [Optimum {
                    cost: Cost::Finite(script_cost),
                    count: script_count
                }]
            );
            assert_eq!(cost, Cost::Finite(script_cost));
        }
        if a.len() == 1 && b.len() == 1 && a[0].children.is_empty() && b[0].children.is_empty() {
            let total = tabulate_cells(scripts.chart(), &Count)?;
            // Matching, deleting left then right, and deleting right then left.
            assert_eq!(total[scripts.chart().root()], [3]);
            assert_eq!(counts[cut.chart().root()], [2]);
        }
    }
    Ok(checks)
}
