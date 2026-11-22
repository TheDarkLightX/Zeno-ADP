#[path = "../examples/support/ladder.rs"]
mod ladder;

use std::time::{Duration, Instant};

use num_bigint::BigInt;
use zeno_adp::decomposition::{Bag, Certificate, Compiled, Decomposition, Error, Factor, MinCost};
use zeno_adp::fast::{self, RuleSource};
use zeno_adp::{audit_bounded, AnswerOrder, AuditBudget};

const CASES: usize = 32;
const SMALL_COLUMNS: usize = 8; // Complete raw subset enumeration is feasible at 16 vertices.
const LONG_COLUMNS: usize = 64;
const COLUMN_MASKS: usize = 1 << 2; // Two binary vertices per column.
const BAG_MASKS: usize = COLUMN_MASKS * COLUMN_MASKS;

fn assert_ranked_reference(program: &Compiled, table: &[Option<BigInt>]) {
    let chart = fast::reference_chart(program).unwrap();
    let replay = zeno_adp::tabulate_cells(&chart, &MinCost).unwrap();
    assert_eq!(replay.len(), table.len());
    for (cell, (expected, actual)) in replay.iter().zip(table).enumerate() {
        assert_eq!(expected, actual.as_slice(), "rank {cell}");
    }
}

fn raw_ladder_weight(weights: &[[i64; 2]], mask: usize) -> Option<i128> {
    let mut previous = 0;
    let mut sum = 0;
    for (column, weights) in weights.iter().enumerate() {
        let selected = (mask >> (2 * column)) % COLUMN_MASKS;
        if selected == COLUMN_MASKS - 1 || previous & selected != 0 {
            return None;
        }
        for (row, &weight) in weights.iter().enumerate() {
            if selected & (1 << row) != 0 {
                sum += i128::from(weight);
            }
        }
        previous = selected;
    }
    Some(sum)
}

fn check_boundary_ladder(weights: &[[i64; 2]]) -> usize {
    let vertices = 2 * weights.len();
    let (factors, tree) = ladder::ladder(weights);
    let program = Compiled::new(vertices, factors, tree).unwrap();
    let result = program.solve().unwrap();
    assert_eq!(result.label(), "Exact");
    let result = result.as_ref();
    let rows: Vec<_> = (0..1 << vertices)
        .map(|mask| raw_ladder_weight(weights, mask).map(|score| BigInt::from(-score)))
        .collect();
    let best = rows.iter().flatten().min().unwrap();
    assert_eq!(
        result.table[program.root()].as_ref(),
        Some(best),
        "{weights:?}"
    );
    let layout = program.bag(0).unwrap();
    assert_eq!(layout.assignment_count(), rows.len());
    for (mask, row) in rows.iter().enumerate() {
        assert_eq!(&result.table[layout.assignment_cell(mask).unwrap()], row);
    }
    let assignment = result.assignment.as_ref().unwrap();
    assert_eq!(assignment.len(), vertices);
    let mask = assignment
        .iter()
        .enumerate()
        .fold(0, |acc, (i, &selected)| acc | (usize::from(selected) << i));
    assert_eq!(rows[mask].as_ref(), Some(best));
    assert_ranked_reference(&program, &result.table);
    result.table.len()
}

#[test]
fn ladder_min_weight_regression() {
    check_boundary_ladder(&[[i64::MIN, 0], [0, 0]]);
}

#[test]
fn ladder_single_column_regression() {
    check_boundary_ladder(&[[3, 2]]);
}

#[test]
fn ladder_weight_boundary_grid() {
    const WEIGHTS: [i64; 3] = [i64::MIN, 0, i64::MAX];
    let columns: Vec<_> = WEIGHTS
        .iter()
        .flat_map(|&a| WEIGHTS.map(|b| [a, b]))
        .collect();
    let mut ranks = check_boundary_ladder(&[]);
    for &left in &columns {
        ranks += check_boundary_ladder(&[left]);
        for &right in &columns {
            ranks += check_boundary_ladder(&[left, right]);
        }
    }
    println!(
        "ladder boundary: {} grids, {ranks} ranks",
        1 + columns.len() + columns.len().pow(2)
    );
}

const PERMUTED_SCOPES: [&[usize]; 3] = [&[1], &[1, 0], &[0, 1]];
const PAIR_COSTS: [[i64; COLUMN_MASKS]; 2] = [[0, -2, 7, 1], [-3, 1, -2, 4]];
const PERMISSION_MASKS: usize = 1 << COLUMN_MASKS;
const ONLY_FALSE_TRUE: usize = 1 << 1; // One permission bit for (x0, x1) = (false, true).

fn permutation_path(permissions: [usize; 2], root: usize) -> Compiled {
    let factors = PAIR_COSTS
        .into_iter()
        .zip(permissions)
        .map(|(cost, permitted)| Factor::Pair {
            left: 0,
            right: 1,
            costs: std::array::from_fn(|a| {
                std::array::from_fn(|b| {
                    let pair = 2 * a + b;
                    (permitted & (1 << pair) != 0).then(|| cost[pair].into())
                })
            }),
        })
        .collect();
    let tree = Decomposition {
        bags: PERMUTED_SCOPES
            .iter()
            .enumerate()
            .map(|(bag, scope)| Bag {
                variables: scope.to_vec(),
                factors: bag.checked_sub(1).into_iter().collect(),
            })
            .collect(),
        edges: vec![(1, 0), (2, 1)],
        root,
    };
    Compiled::new(2, factors, tree).unwrap()
}

#[test]
fn separator_permutation_keeps_unique_feasible_assignment() {
    let program = permutation_path([ONLY_FALSE_TRUE; 2], 0);
    let result = program.solve().map(|exact| {
        let answer = exact.into_inner();
        (answer.assignment, answer.table[program.root()].clone())
    });
    assert_eq!(result, Ok((Some(vec![false, true]), Some((-1).into()))));
}

#[test]
fn verifier_rejects_false_infeasibility_from_sorted_parent_positions() {
    let program = permutation_path([ONLY_FALSE_TRUE; 2], 0);
    let mut table = vec![None; program.cell_count()];
    let leaf = program.bag(2).unwrap();
    // The leaf encodes x1 in bit one. The faulty parent uses bit zero.
    let leaf_mask = 1 << 1;
    table[leaf.assignment_cell(leaf_mask).unwrap()] = Some(1.into());
    table[leaf.separator_cell(leaf_mask).unwrap()] = Some(1.into());
    let first_wrong_rank = program.bag(1).unwrap().assignment_cell(1).unwrap();
    assert_eq!(
        program.verify(&Certificate {
            table,
            assignment: None,
        }),
        Err(Error::CellValue(first_wrong_rank))
    );
}

#[test]
fn separator_permission_grid() {
    fn original_cost(permissions: [usize; 2], pair: usize, bag: usize, root: usize) -> Option<i64> {
        let mut total = 0;
        for (factor, permitted) in permissions.into_iter().enumerate() {
            let owner = factor + 1;
            if bag == root || (bag < root && owner <= bag) || (bag > root && owner >= bag) {
                if permitted & (1 << pair) == 0 {
                    return None;
                }
                total += PAIR_COSTS[factor][pair];
            }
        }
        Some(total)
    }

    let mut ranks = 0;
    for middle in 0..PERMISSION_MASKS {
        for leaf in 0..PERMISSION_MASKS {
            let permissions = [middle, leaf];
            for root in 0..PERMUTED_SCOPES.len() {
                let program = permutation_path(permissions, root);
                let result = program.solve().unwrap().into_inner();
                let mut expected_root = None;
                for bag in 0..PERMUTED_SCOPES.len() {
                    let layout = program.bag(bag).unwrap();
                    // This path has one width-two bag with nonascending mask order.
                    let variables: &[usize] = match (bag, root) {
                        (0, _) => &[1],
                        (1, 0) => &[1, 0],
                        _ => &[0, 1],
                    };
                    let separator_len = match (bag, root) {
                        (a, b) if a == b => 0,
                        (0, _) | (1, 0) => 1,
                        _ => 2,
                    };
                    let separator = &variables[..separator_len];
                    assert_eq!(layout.variables(), variables);
                    assert_eq!(layout.separator(), separator);
                    for (scope, first_rank) in [
                        (variables, layout.assignment_cell(0).unwrap()),
                        (separator, layout.separator_cell(0).unwrap()),
                    ] {
                        for mask in 0..1 << scope.len() {
                            let expected = (0..COLUMN_MASKS)
                                .filter(|&pair| {
                                    scope.iter().enumerate().all(|(bit, &variable)| {
                                        (mask >> bit) & 1 == (pair >> (1 - variable)) & 1
                                    })
                                })
                                .filter_map(|pair| original_cost(permissions, pair, bag, root))
                                .min()
                                .map(BigInt::from);
                            let rank = first_rank + mask;
                            assert_eq!(
                                result.table[rank], expected,
                                "permissions {permissions:?}, root {root}, rank {rank}"
                            );
                            if rank == program.root() {
                                expected_root = expected;
                            }
                            ranks += 1;
                        }
                    }
                }
                let score = result.assignment.map(|assignment| {
                    let pair = 2 * usize::from(assignment[0]) + usize::from(assignment[1]);
                    BigInt::from(original_cost(permissions, pair, root, root).unwrap())
                });
                assert_eq!(score, expected_root);
                assert_ranked_reference(&program, &result.table);
            }
        }
    }
    println!(
        "separator permission grid: {} instances, {ranks} ranks",
        PERMISSION_MASKS.pow(2) * PERMUTED_SCOPES.len()
    );
}

#[test]
fn fanout_fits_a_bounded_stack() {
    use std::process::Command;
    use std::thread;

    // The reviewed stars span these degrees. A degree-64 debug replay used
    // 25,600 bytes for its child recursion alone.
    const DEGREES: std::ops::RangeInclusive<usize> = 8..=64;
    const STACK: usize = 16 * 1024;
    const CHILD_PROCESS: &str = "ZENO_ADP_FANOUT_TEST_CHILD";
    if std::env::var_os(CHILD_PROCESS).is_none() {
        let child = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "fanout_fits_a_bounded_stack", "--nocapture"])
            .env(CHILD_PROCESS, "1")
            .output()
            .unwrap();
        assert!(
            child.status.success(),
            "bounded stack replay failed: {}\n{}",
            String::from_utf8_lossy(&child.stdout),
            String::from_utf8_lossy(&child.stderr)
        );
        print!("{}", String::from_utf8_lossy(&child.stdout));
        return;
    }

    let mut ranks = 0;
    for degree in DEGREES {
        let tree = Decomposition {
            bags: vec![
                Bag {
                    variables: vec![],
                    factors: vec![]
                };
                degree + 1
            ],
            edges: (1..=degree).map(|child| (0, child)).collect(),
            root: 0,
        };
        let program = Compiled::new(0, vec![], tree).unwrap();
        let leaf_and_root_rows = program.cell_count();
        println!("fanout {degree}, {leaf_and_root_rows} ranks");
        let (program, result) = thread::Builder::new()
            .stack_size(STACK)
            .spawn(move || {
                let result = program.solve();
                (program, result)
            })
            .unwrap()
            .join()
            .unwrap();
        let result = result.unwrap().into_inner();
        assert_eq!(result.assignment, Some(vec![]));
        assert_eq!(result.table, vec![Some(BigInt::ZERO); 2 * (degree + 1)]);
        assert_ranked_reference(&program, &result.table);
        ranks += result.table.len();
    }
    println!("bounded stack: {ranks} ranks at {STACK} requested bytes");
}

fn weights(case: usize, columns: usize) -> Vec<[i64; 2]> {
    // Includes ties, zero weights and negative weights in the maximization objective.
    (0..columns)
        .map(|column| {
            std::array::from_fn(|row| {
                ((case * (column + 1) + column * column + row * (case + column + 1)) % 19) as i64
                    - 5
            })
        })
        .collect()
}

fn raw_column_cost(weights: [i64; 2], mask: usize) -> i64 {
    -(0..2)
        .filter(|&row| mask & (1 << row) != 0)
        .map(|row| weights[row])
        .sum::<i64>()
}

fn raw_witness_score(weights: &[[i64; 2]], assignment: &[bool]) -> i64 {
    assert_eq!(assignment.len(), weights.len() * 2);
    let mut score = 0;
    let mut previous = [false; 2];
    for (column, selected) in weights.iter().zip(assignment.chunks_exact(2)) {
        assert!(!(selected[0] && selected[1]));
        for row in 0..2 {
            assert!(!(selected[row] && previous[row]));
            if selected[row] {
                score -= column[row];
            }
        }
        previous.copy_from_slice(selected);
    }
    score
}

fn raw_subsets(weights: &[[i64; 2]]) -> (Vec<Vec<Option<i64>>>, usize) {
    let mut visits = 0;
    let scores = (0..weights.len() - 1)
        .map(|bag| {
            let suffix = &weights[bag..];
            let mut best = vec![None::<i64>; BAG_MASKS];
            for mask in 0..1usize << (2 * suffix.len()) {
                visits += 1;
                let mut previous = mask % COLUMN_MASKS;
                // At nonroot bags the left column is fixed by the parent and charged there.
                let mut sum = 0;
                if bag == 0 {
                    if previous == COLUMN_MASKS - 1 {
                        continue;
                    }
                    sum = raw_column_cost(suffix[0], previous);
                }
                let mut legal = true;
                for (column, &weights) in suffix.iter().enumerate().skip(1) {
                    let selected = (mask >> (2 * column)) % COLUMN_MASKS;
                    if selected == COLUMN_MASKS - 1 || previous & selected != 0 {
                        legal = false;
                        break;
                    }
                    sum += raw_column_cost(weights, selected);
                    previous = selected;
                }
                if legal {
                    let entry = &mut best[mask % BAG_MASKS];
                    *entry = Some(entry.map_or(sum, |old| old.min(sum)));
                }
            }
            best
        })
        .collect();
    (scores, visits)
}

fn raw_column_recurrence(weights: &[[i64; 2]]) -> Vec<Vec<Option<i64>>> {
    let mut rows = vec![vec![None; BAG_MASKS]; weights.len() - 1];
    let mut tail = [Some(0); COLUMN_MASKS];
    for column in (0..weights.len() - 1).rev() {
        let mut next = [None::<i64>; COLUMN_MASKS];
        for (left, best) in next.iter_mut().enumerate() {
            if column == 0 && left == COLUMN_MASKS - 1 {
                continue;
            }
            for (right, remainder) in tail.iter().enumerate().take(COLUMN_MASKS - 1) {
                if left & right != 0 {
                    continue;
                }
                if let Some(remainder) = remainder {
                    let mut score = raw_column_cost(weights[column + 1], right) + remainder;
                    if column == 0 {
                        score += raw_column_cost(weights[column], left);
                    }
                    rows[column][left + COLUMN_MASKS * right] = Some(score);
                    *best = Some(best.map_or(score, |old| old.min(score)));
                }
            }
        }
        tail = next;
    }
    rows
}

struct Measurement {
    bags: usize,
    separators: usize,
    child_references: usize,
    solve: Duration,
    reference: Duration,
}

fn check_ladder(weights: &[[i64; 2]], raw: &[Vec<Option<i64>>]) -> Measurement {
    let (factors, tree) = ladder::ladder(weights);
    let compiled = Compiled::new(weights.len() * 2, factors, tree).unwrap();
    let start = Instant::now();
    let result = compiled.solve().unwrap().into_inner();
    let solve = start.elapsed();
    let start = Instant::now();
    let reference = fast::reference_chart(&compiled).unwrap();
    let replay = zeno_adp::tabulate_cells(&reference, &MinCost).unwrap();
    let reference_time = start.elapsed();
    let mut counts = Measurement {
        bags: 0,
        separators: 0,
        child_references: 0,
        solve,
        reference: reference_time,
    };
    for (bag, expected) in raw.iter().enumerate() {
        let layout = compiled.bag(bag).unwrap();
        assert_eq!(
            layout.variables(),
            [2 * bag, 2 * bag + 1, 2 * bag + 2, 2 * bag + 3]
        );
        assert_eq!(layout.assignment_count(), BAG_MASKS);
        assert_eq!(
            layout.separator_count(),
            if bag == 0 { 1 } else { COLUMN_MASKS }
        );
        for (mask, cost) in expected.iter().enumerate() {
            let cell = layout.assignment_cell(mask).unwrap();
            assert_eq!(
                result.table[cell],
                cost.map(BigInt::from),
                "bag {bag}, mask {mask}"
            );
            counts.child_references += reference.cells()[cell]
                .iter()
                .map(|rule| rule.children.len())
                .sum::<usize>();
            counts.bags += 1;
        }
        for mask in 0..layout.separator_count() {
            let cell = layout.separator_cell(mask).unwrap();
            let best = expected
                .iter()
                .skip(mask)
                .step_by(layout.separator_count())
                .flatten()
                .min();
            assert_eq!(
                result.table[cell],
                best.copied().map(BigInt::from),
                "separator {bag}, mask {mask}"
            );
            counts.separators += 1;
        }
    }
    assert_eq!(result.table.len(), counts.bags + counts.separators);
    for (actual, expected) in result.table.iter().zip(&replay) {
        assert_eq!(actual.as_slice(), expected);
    }
    let assignment = result.assignment.unwrap();
    assert_eq!(
        result.table[compiled.root()],
        Some(BigInt::from(raw_witness_score(weights, &assignment)))
    );
    counts
}

#[test]
fn every_rank_on_short_and_long_ladders() {
    let mut subset_visits = 0;
    let mut total = Measurement {
        bags: 0,
        separators: 0,
        child_references: 0,
        solve: Duration::ZERO,
        reference: Duration::ZERO,
    };
    let start = Instant::now();
    let mut oracle = Duration::ZERO;
    for case in 0..CASES {
        let weights = weights(case, SMALL_COLUMNS);
        let oracle_start = Instant::now();
        let (raw, visits) = raw_subsets(&weights);
        oracle += oracle_start.elapsed();
        assert_eq!(raw_column_recurrence(&weights), raw);
        let got = check_ladder(&weights, &raw);
        total.bags += got.bags;
        total.separators += got.separators;
        total.child_references += got.child_references;
        total.solve += got.solve;
        total.reference += got.reference;
        subset_visits += visits;
    }
    println!("separator {CASES} ladders: {} bags rows, {} separator rows, {} child references in emitted assignment rules, {subset_visits} raw assignments, 0 disagreements", total.bags, total.separators, total.child_references);
    println!(
        "separator short solve/check {:?}, reference {:?}, subset oracle {oracle:?}, total {:?}",
        total.solve,
        total.reference,
        start.elapsed()
    );
    let weights = weights(CASES, LONG_COLUMNS);
    let start = Instant::now();
    let raw = raw_column_recurrence(&weights);
    let recurrence = start.elapsed();
    let got = check_ladder(&weights, &raw);
    assert_eq!(got.bags, (LONG_COLUMNS - 1) * BAG_MASKS);
    println!("separator long: {} bag rows, {} separator rows, {} child references in emitted assignment rules, solve/check {:?}, reference {:?}, column recurrence {recurrence:?}, 0 disagreements", got.bags, got.separators, got.child_references, got.solve, got.reference);
}

#[test]
fn a_branching_tree_with_an_empty_separator() {
    let factors = vec![
        ladder::unary(0, 2),
        ladder::unary(1, 5),
        ladder::unary(2, 7),
        ladder::unary(3, 11),
        ladder::edge(0, 1),
        ladder::edge(0, 2),
    ];
    // The root has a nonzero ID. Its third child shares no variables.
    let tree = Decomposition {
        root: 2,
        edges: vec![(2, 0), (2, 1), (3, 2)],
        bags: vec![
            Bag {
                variables: vec![1, 0],
                factors: vec![1, 4],
            },
            Bag {
                variables: vec![2, 0],
                factors: vec![2, 5],
            },
            Bag {
                variables: vec![0],
                factors: vec![0],
            },
            Bag {
                variables: vec![3],
                factors: vec![3],
            },
        ],
    };
    let program = Compiled::new(4, factors, tree).unwrap();
    let result = program.solve().unwrap();
    assert_eq!(result.label(), "Exact");
    let result = result.into_inner();
    let expectations = [
        (
            vec![Some(0), Some(0), Some(-5), None],
            vec![Some(-5), Some(0)],
        ),
        (
            vec![Some(0), Some(0), Some(-7), None],
            vec![Some(-7), Some(0)],
        ),
        (vec![Some(-23), Some(-13)], vec![Some(-23)]),
        (vec![Some(0), Some(-11)], vec![Some(-11)]),
    ];
    for (bag, (rows, messages)) in expectations.into_iter().enumerate() {
        let layout = program.bag(bag).unwrap();
        for (mask, value) in rows.into_iter().enumerate() {
            assert_eq!(
                result.table[layout.assignment_cell(mask).unwrap()],
                value.map(BigInt::from)
            );
        }
        for (mask, value) in messages.into_iter().enumerate() {
            assert_eq!(
                result.table[layout.separator_cell(mask).unwrap()],
                value.map(BigInt::from)
            );
        }
    }
    assert_eq!(result.assignment, Some(vec![false, true, true, true]));
    assert_ranked_reference(&program, &result.table);
    let chart = fast::reference_chart(&program).unwrap();
    // For this four-variable fixture all rooted subproblem derivations combined
    // fit in a few hundred constructor occurrences. Allow one kibinode.
    const TREE_NODE_ALLOWANCE: usize = 1024;
    let audit = audit_bounded(
        &chart,
        &MinCost,
        AuditBudget {
            max_tree_nodes: TREE_NODE_ALLOWANCE,
        },
        AnswerOrder::Ordered,
    )
    .unwrap();
    assert!(audit.bellman.first_failure.is_none());
    assert!(audit.ambiguities.is_empty());
    println!(
        "separator branching reference audit: {} ranks, {} rules, {} tree nodes",
        audit.bellman.cells, audit.bellman.rules, audit.tree_nodes
    );

    let mut wrong = result.clone();
    let internal = program.bag(0).unwrap().assignment_cell(0).unwrap();
    wrong.table[internal] = Some(123.into());
    assert_eq!(program.verify(&wrong), Err(Error::CellValue(internal)));
    let mut wrong = result.clone();
    wrong.assignment.as_mut().unwrap()[0] = true;
    assert_eq!(program.verify(&wrong), Err(Error::Assignment));
    let mut wrong = result;
    wrong.table.pop();
    assert!(matches!(
        program.verify(&wrong),
        Err(Error::CertificateSize { .. })
    ));
}

#[test]
fn decomposition_mutations_are_refused() {
    let (factors, tree) = ladder::ladder(&[[1; 2]; 4]);
    let vertices = 8;
    let mut wrong = tree.clone();
    let edge = factors
        .iter()
        .position(|factor| {
            matches!(
                factor,
                Factor::Pair {
                    left: 0,
                    right: 2,
                    ..
                }
            )
        })
        .unwrap();
    wrong.bags[0].factors.retain(|&factor| factor != edge);
    wrong.bags[1].factors.push(edge);
    assert!(matches!(
        Compiled::new(vertices, factors.clone(), wrong),
        Err(Error::UncoveredFactor { bag: 1, factor }) if factor == edge
    ));
    let mut wrong = tree.clone();
    wrong.bags[2].variables.push(0);
    assert!(matches!(
        Compiled::new(vertices, factors.clone(), wrong),
        Err(Error::RunningIntersection(0))
    ));
    let mut wrong = tree.clone();
    let owned = factors
        .iter()
        .position(|factor| matches!(factor, Factor::Unary { variable: 2, .. }))
        .unwrap();
    wrong.bags[1].factors.push(owned);
    assert!(
        matches!(Compiled::new(vertices, factors.clone(), wrong), Err(Error::DuplicateOwnership(id)) if id == owned)
    );
    let mut wrong = tree.clone();
    wrong.bags[0].factors.retain(|&factor| factor != owned);
    assert!(
        matches!(Compiled::new(vertices, factors.clone(), wrong), Err(Error::MissingOwnership(id)) if id == owned)
    );
    assert!(matches!(
        Compiled::new(vertices + 1, factors.clone(), tree.clone()),
        Err(Error::MissingVariable(8))
    ));
    let mut wrong = tree.clone();
    wrong.edges[1] = wrong.edges[0];
    assert!(matches!(
        Compiled::new(vertices, factors.clone(), wrong),
        Err(Error::BagTree)
    ));
    let mut wrong = tree;
    wrong.bags[0].variables.push(0);
    assert!(matches!(
        Compiled::new(vertices, factors, wrong),
        Err(Error::RepeatedVariable {
            bag: 0,
            variable: 0
        })
    ));
    println!("separator controls rejected: uncovered factor, running intersection, duplicate and missing ownership, missing variable, bad tree, repeated variable");
}

#[test]
fn infeasibility_empty_instance_and_unbounded_costs() {
    let single = |variables, factors| Decomposition {
        bags: vec![Bag { variables, factors }],
        edges: vec![],
        root: 0,
    };
    let impossible = Factor::Unary {
        variable: 0,
        costs: [None, None],
    };
    let program = Compiled::new(1, vec![impossible], single(vec![0], vec![0])).unwrap();
    let result = program.solve().unwrap().into_inner();
    assert_eq!(result.table, vec![None; 3]);
    assert!(result.assignment.is_none());

    let empty = Compiled::new(0, vec![], single(vec![], vec![])).unwrap();
    let result = empty.solve().unwrap().into_inner();
    assert_eq!(result.table, vec![Some(BigInt::ZERO); 2]);
    assert_eq!(result.assignment, Some(vec![]));

    const WIDE_SHIFT: usize = 160; // Exceeds the 128-bit scalar range.
    let wide = BigInt::from(-1) << WIDE_SHIFT;
    let force = Factor::Unary {
        variable: 0,
        costs: [None, Some(wide.clone())],
    };
    let program =
        Compiled::new(1, vec![force.clone(), force], single(vec![0], vec![0, 1])).unwrap();
    let result = program.solve().unwrap().into_inner();
    assert_eq!(result.table[program.root()], Some(2 * wide));
    assert_eq!(result.assignment, Some(vec![true]));

    // Ordered left/right indices still matter when the bag sorts its variables.
    let pair = Factor::Pair {
        left: 1,
        right: 0,
        costs: [[Some(0.into()), Some((-5).into())], [Some(7.into()), None]],
    };
    let program = Compiled::new(2, vec![pair], single(vec![1, 0], vec![0])).unwrap();
    let result = program.solve().unwrap().into_inner();
    assert_eq!(
        result.table,
        [
            Some(0.into()),
            Some((-5).into()),
            Some(7.into()),
            None,
            Some((-5).into())
        ]
    );
    assert_eq!(result.assignment, Some(vec![true, false]));

    let variables = usize::BITS as usize;
    assert!(matches!(
        Compiled::new(variables, vec![], single((0..variables).collect(), vec![])),
        Err(Error::TableSize)
    ));
}
