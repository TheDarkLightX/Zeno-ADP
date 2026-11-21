use zeno_adp::algebras::Count;
use zeno_adp::{
    audit_bounded, enumerate, grammar_growth, Algebra, AuditBudget, Chart, Error, Expansion,
    GrammarGrowth, Law, Operator, Rule, Tree,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Op {
    Leaf(i64),
    Identity,
    Reverse,
    Pair,
}
impl Operator for Op {
    fn arity(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Identity | Self::Reverse => 1,
            Self::Pair => 2,
        }
    }
}

fn nodes(tree: &Tree<Op>) -> usize {
    1 + tree.children.iter().map(nodes).sum::<usize>()
}

fn budget(max_tree_nodes: usize) -> AuditBudget {
    AuditBudget { max_tree_nodes }
}

#[test]
fn growth_agrees_with_enumeration_and_audit_on_all_ranked_fixtures() {
    let candidates = [
        vec![Rule::new(Op::Leaf(1), []), Rule::new(Op::Leaf(1), [])],
        vec![
            Rule::new(Op::Leaf(5), []),
            Rule::new(Op::Identity, [0]),
            Rule::new(Op::Pair, [0, 0]),
        ],
        vec![
            Rule::new(Op::Leaf(2), []),
            Rule::new(Op::Identity, [0]),
            Rule::new(Op::Identity, [1]),
            Rule::new(Op::Pair, [0, 1]),
        ],
    ];
    let rule_count = candidates.iter().map(Vec::len).sum::<usize>();
    let mut charts = 0;
    let mut probes = 0;
    for mask in 0..1_usize << rule_count {
        let mut index = 0;
        let rows: Vec<Vec<_>> = candidates
            .iter()
            .map(|row| {
                row.iter()
                    .filter(|_| {
                        let included = mask & (1 << index) != 0;
                        index += 1;
                        included
                    })
                    .cloned()
                    .collect()
            })
            .collect();
        let counts: Vec<_> = (0..rows.len())
            .map(|root| {
                enumerate(&Chart::new(rows.clone(), root).unwrap())
                    .iter()
                    .map(nodes)
                    .sum::<usize>()
            })
            .collect();
        let exact = counts.iter().sum::<usize>();
        let slots = rows.iter().flatten().map(|r| r.children.len()).sum();
        let limits = [0, exact.saturating_sub(1), exact]
            .into_iter()
            .chain(
                counts
                    .iter()
                    .scan(0_usize, |total, &n| {
                        *total += n;
                        Some([total.saturating_sub(1), *total])
                    })
                    .flatten(),
            )
            .collect::<Vec<_>>();
        for root in 0..rows.len() {
            let chart = Chart::new(rows.clone(), root).unwrap();
            charts += 1;
            for &limit in &limits {
                let mut cumulative = 0;
                let exceeded = counts.iter().position(|n| {
                    cumulative += n;
                    cumulative > limit
                });
                let expansion = match exceeded {
                    Some(first_cell) => Expansion::OverBudget {
                        first_cell,
                        max_tree_nodes: limit,
                    },
                    None => Expansion::WithinBudget { tree_nodes: exact },
                };
                assert_eq!(
                    grammar_growth(&chart, budget(limit)).unwrap(),
                    GrammarGrowth {
                        cells: rows.len(),
                        rules: mask.count_ones() as usize,
                        child_slots: slots,
                        expansion,
                    }
                );
                let audit = audit_bounded(&chart, &Count, budget(limit), Default::default());
                if let Some(cell) = exceeded {
                    assert!(
                        matches!(audit, Err(Error::AuditBudgetExceeded {cell: actual, max_tree_nodes}) if actual == cell && max_tree_nodes == limit)
                    );
                } else {
                    assert_eq!(audit.unwrap().tree_nodes, exact);
                }
                probes += 1;
            }
        }
    }
    println!("Grammar growth: {charts} charts, {probes} budget probes, zero disagreements");
}

struct MinimumReversed;
impl Algebra<Op> for MinimumReversed {
    type Value = i64;
    fn apply(&self, op: &Op, args: &[&i64]) -> Result<i64, Error> {
        Ok(match op {
            Op::Leaf(x) => *x,
            Op::Reverse => 10 - *args[0],
            _ => unreachable!(),
        })
    }
    fn choose(&self, candidates: &[i64]) -> Result<Vec<i64>, Error> {
        Ok(candidates.iter().copied().min().into_iter().collect())
    }
}

#[test]
fn report_explains_the_failure_and_distinguishes_ambiguity() {
    let chart = Chart::new(
        vec![
            vec![Rule::new(Op::Leaf(1), []), Rule::new(Op::Leaf(5), [])],
            vec![Rule::new(Op::Reverse, [0])],
        ],
        1,
    )
    .unwrap();
    // Two leaves and two unary trees of two nodes each.
    const REVERSAL_NODES: usize = 6;
    let report = audit_bounded(
        &chart,
        &MinimumReversed,
        budget(REVERSAL_NODES),
        Default::default(),
    )
    .unwrap();
    let message = report.to_string();
    assert!(
        message.contains("Cell 1 differs when choosing children before applying rule 0 (Reverse)")
    );
    assert!(message.contains("Expected [5], got [9]"));
    assert!(message.contains("Repeated answer identities occur in 0 cells"));
    let witness = report.bellman.first_failure.unwrap();
    assert_eq!(witness.trees.len(), 2);

    let duplicate = Chart::new(vec![vec![Rule::new(Op::Leaf(1), []); 2]], 0).unwrap();
    let report = audit_bounded(&duplicate, &Count, budget(2), Default::default()).unwrap();
    let message = report.to_string();
    assert!(message.contains("All comparisons agreed on this chart"));
    assert!(message.contains("Cell 0 has 2 derivations with the same answer identity"));
    assert!(message.contains("Witness derivations 0 and 1"));
    let message = grammar_growth(&duplicate, budget(1)).unwrap().to_string();
    assert!(message.contains("1 cell, 2 rules and 0 child positions"));
    assert!(message.contains("crosses the 1-node budget at cell 0"));
    let error = audit_bounded(&duplicate, &Count, budget(1), Default::default()).unwrap_err();
    assert_eq!(
        error.to_string(),
        "exhaustive tree nodes exceed budget 1 at cell 0"
    );

    let messages = [
        Law::EmptyChoice,
        Law::Operation { rule: 0 },
        Law::Merge,
        Law::MergeAfterChildChoice,
        Law::Tabulation,
        Law::Injectivity,
    ]
    .map(|law| law.to_string());
    assert_eq!(
        messages
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        messages.len()
    );
}

#[test]
fn matrix_chain_growth_matches_catalan_expansion() {
    // Doubling the chain shows the change in both chart and expansion work.
    const MATRIX_COUNTS: [usize; 4] = [1, 2, 4, 8];
    println!("matrices,cells,rules,child_slots,tree_nodes");
    for n in MATRIX_COUNTS {
        let chart = zeno_adp::grammars::matrix_chain(&vec![2; n + 1]).unwrap();
        let mut catalan = vec![1_usize];
        for k in 1..n {
            catalan.push((0..k).map(|a| catalan[a] * catalan[k - 1 - a]).sum());
        }
        let expected: usize = (1..=n)
            .map(|k| (n - k + 1) * (2 * k - 1) * catalan[k - 1])
            .sum();
        let growth = grammar_growth(&chart, budget(expected)).unwrap();
        let splits = (n - 1) * n * (n + 1) / 6;
        assert_eq!(growth.cells, n * (n + 1) / 2);
        assert_eq!(growth.rules, n + splits);
        assert_eq!(growth.child_slots, 2 * splits);
        assert_eq!(
            growth.expansion,
            Expansion::WithinBudget {
                tree_nodes: expected
            }
        );
        println!(
            "{n},{},{},{},{expected}",
            growth.cells, growth.rules, growth.child_slots
        );
    }
}
