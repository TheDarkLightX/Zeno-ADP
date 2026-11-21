#[path = "support/stream.rs"]
mod stream;

use std::cell::RefCell;

use stream::fast_questions;
use zeno_adp::algebras::{
    Additive, Cost, CostPolicy, Count, MinimumWithMultiplicity, ScoredOperator,
};
use zeno_adp::fast::{self, BestTable, Fold, RuleSource};
use zeno_adp::{compiled, tabulate_cells, Algebra, Cell, Chart, Error, Operator, Rule};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Op {
    Leaf { label: char, weight: i64 },
    Extend(i64),
    Join,
}

impl Operator for Op {
    fn arity(&self) -> usize {
        match self {
            Self::Leaf { .. } => 0,
            Self::Extend(_) => 1,
            Self::Join => 3,
        }
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        Cost::Finite(match self {
            Self::Leaf { weight, .. } | Self::Extend(weight) => *weight,
            Self::Join => 0,
        })
    }
}

struct Caller {
    leaf_weights: [i64; 2],
    extension: i64,
    duplicate: bool,
    visits: RefCell<Vec<Cell>>,
}

impl RuleSource for Caller {
    type Op = Op;

    fn cell_count(&self) -> usize {
        5
    }

    fn root(&self) -> Cell {
        4
    }

    fn rules_at(
        &self,
        cell: Cell,
        mut emit: impl FnMut(Op, &[Cell]) -> Result<(), Error>,
    ) -> Result<(), Error> {
        self.visits.borrow_mut().push(cell);
        let [a, b] = self.leaf_weights;
        match cell {
            0 => {
                emit(
                    Op::Leaf {
                        label: 'a',
                        weight: a,
                    },
                    &[],
                )?;
                emit(
                    Op::Leaf {
                        label: 'b',
                        weight: b,
                    },
                    &[],
                )?;
                if self.duplicate {
                    emit(
                        Op::Leaf {
                            label: 'a',
                            weight: a,
                        },
                        &[],
                    )?;
                }
            }
            1 => {}
            2 => emit(Op::Extend(self.extension), &[0])?,
            3 => {
                emit(
                    Op::Leaf {
                        label: 'a',
                        weight: a,
                    },
                    &[],
                )?;
                emit(
                    Op::Leaf {
                        label: 'b',
                        weight: b,
                    },
                    &[],
                )?;
            }
            4 => {
                emit(Op::Join, &[2, 1, 0])?;
                emit(Op::Join, &[2, 0, 0])?;
                emit(Op::Join, &[2, 3, 0])?;
            }
            _ => unreachable!(),
        }
        Ok(())
    }
}

fn reference(input: &Caller) -> Chart<Op> {
    let leaves = ['a', 'b']
        .into_iter()
        .zip(input.leaf_weights)
        .map(|(label, weight)| Rule::new(Op::Leaf { label, weight }, []))
        .collect::<Vec<_>>();
    let mut first = leaves.clone();
    if input.duplicate {
        first.push(first[0].clone());
    }
    Chart::new(
        vec![
            first,
            vec![],
            vec![Rule::new(Op::Extend(input.extension), [0])],
            leaves,
            [[2, 1, 0], [2, 0, 0], [2, 3, 0]]
                .map(|children| Rule::new(Op::Join, children))
                .to_vec(),
        ],
        input.root(),
    )
    .unwrap()
}

fn declared(input: &Caller) -> compiled::Grammar<Op, 1> {
    use compiled::{Atom::Child, Grammar, Production};
    fn rule(name: &str, parent: usize, op: Op, children: Vec<usize>) -> Production<Op, 1> {
        Production {
            name: name.into(),
            parent,
            tracks: [(0..children.len()).map(Child).collect()],
            children,
            operator: Box::new(move |_| op),
        }
    }
    let [a, b] = input.leaf_weights;
    let a = Op::Leaf {
        label: 'a',
        weight: a,
    };
    let b = Op::Leaf {
        label: 'b',
        weight: b,
    };
    let mut rules = vec![rule("a", 0, a, vec![]), rule("b", 0, b, vec![])];
    if input.duplicate {
        rules.push(rule("duplicate", 0, a, vec![]));
    }
    rules.extend([
        rule("extend", 2, Op::Extend(input.extension), vec![0]),
        rule("other-a", 3, a, vec![]),
        rule("other-b", 3, b, vec![]),
        rule("absent", 4, Op::Join, vec![2, 1, 0]),
        rule("repeated", 4, Op::Join, vec![2, 0, 0]),
        rule("distinct", 4, Op::Join, vec![2, 3, 0]),
    ]);
    Grammar::new(&["Leaf", "Absent", "Extend", "Other", "Join"], 4, rules).unwrap()
}

struct Height;

impl Algebra<Op> for Height {
    type Value = usize;

    fn apply(&self, _: &Op, children: &[&usize]) -> Result<usize, Error> {
        Ok(1 + children.iter().map(|&&height| height).max().unwrap_or(0))
    }

    fn choose(&self, candidates: &[usize]) -> Result<Vec<usize>, Error> {
        Ok(candidates.iter().copied().max().into_iter().collect())
    }
}

impl Fold<Op> for Height {
    type Value = usize;

    fn apply<'a>(
        &self,
        _: &'a Op,
        children: impl Iterator<Item = &'a usize> + Clone,
    ) -> Result<usize, Error> {
        Ok(1 + children.copied().max().unwrap_or(0))
    }

    fn merge(&self, selected: &mut Option<usize>, next: usize) -> Result<(), Error> {
        *selected = Some(selected.map_or(next, |best| best.max(next)));
        Ok(())
    }
}

// One negative, one neutral and one positive cost.
const SCORES: [i64; 3] = [-1, 0, 1];

#[test]
fn caller_defined_rules_and_reducers_match_reference() {
    let mut charts = 0;
    let mut cells = 0;
    let mut trees = 0;
    for a in SCORES {
        for b in SCORES {
            for extension in SCORES {
                for duplicate in [false, true] {
                    let source = Caller {
                        leaf_weights: [a, b],
                        extension,
                        duplicate,
                        visits: RefCell::default(),
                    };
                    let chart = reference(&source);
                    let materialized = fast::reference_chart(&source).unwrap();
                    let signature = |rules: &[Rule<Op>]| {
                        rules
                            .iter()
                            .map(|rule| (rule.operator, rule.children.clone()))
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(
                        materialized
                            .cells()
                            .iter()
                            .map(|rules| signature(rules))
                            .collect::<Vec<_>>(),
                        chart
                            .cells()
                            .iter()
                            .map(|rules| signature(rules))
                            .collect::<Vec<_>>()
                    );
                    trees += fast_questions(&source, &chart);
                    let grammar = declared(&source);
                    let compiled = grammar.bind([b""]).unwrap();
                    // Yield analysis eliminates the rule with an unproductive
                    // child. Compare its map to the reduced chart and answers
                    // to the original ordered reference, including that rule.
                    let mut live = chart.cells().to_vec();
                    live[chart.root()].remove(0);
                    let live = Chart::new(live, chart.root()).unwrap();
                    assert_eq!(
                        stream::compiled_questions(&compiled, &live),
                        stream::compare_compiled_tables(&compiled, &chart),
                    );
                    let best = BestTable::new(&source).unwrap();
                    for identity in [
                        zeno_adp::queries::TreeMultiplicity::DistinctTrees,
                        zeno_adp::queries::TreeMultiplicity::Derivations,
                    ] {
                        let all = zeno_adp::queries::k_lowest(
                            &chart,
                            &Additive::default(),
                            usize::MAX,
                            identity,
                        )
                        .unwrap();
                        assert_eq!(best.recover().k_lowest(usize::MAX, identity).unwrap(), all);
                        trees += all.len();
                    }
                    let height = fast::tabulate(&source, &Height).unwrap();
                    let expected = tabulate_cells(&chart, &Height).unwrap();
                    assert!(height
                        .cells()
                        .iter()
                        .zip(expected)
                        .all(|(a, b)| a.as_slice() == b));
                    charts += 1;
                    cells += chart.cells().len();
                }
            }
        }
    }
    println!("caller: {charts} charts, {cells} cells, {trees} returned tree comparisons");
}

#[test]
fn recovery_replays_only_necessary_cells_for_the_optimum() {
    let source = Caller {
        leaf_weights: [0, 1],
        extension: 0,
        duplicate: false,
        visits: RefCell::default(),
    };
    let table = BestTable::new(&source).unwrap();
    assert_eq!(source.visits.take(), [0, 1, 2, 3, 4]);
    let recovery = table.recover();
    assert_eq!(
        recovery.first_minimum_tree().unwrap().unwrap().value,
        Cost::Finite(0)
    );
    assert_eq!(source.visits.take(), [4, 2, 0]);
    assert_eq!(recovery.co_minimal(Default::default()).unwrap().len(), 1);
    assert_eq!(source.visits.take(), [4, 2, 0, 3]);
}

#[test]
fn fused_fold_checks_costs_and_counts() {
    let source = Caller {
        leaf_weights: [i64::MAX, i64::MAX],
        extension: 1,
        duplicate: false,
        visits: RefCell::default(),
    };
    assert_eq!(
        fast::tabulate(&source, &Additive::default()),
        Err(Error::Overflow)
    );

    let leaf = Rule::new(
        Op::Leaf {
            label: 'a',
            weight: 0,
        },
        [],
    );
    let mut cells = vec![vec![leaf.clone(), leaf]];
    // At least 2^128 derivations after seven squarings. The ternary product
    // here reaches that bound no later than the binary product would.
    for child in 0..u128::BITS.ilog2() as usize {
        cells.push(vec![Rule::new(Op::Join, [child; 3])]);
    }
    let root = cells.len() - 1;
    let overflow = Chart::new(cells, root).unwrap();
    assert_eq!(fast::tabulate(&overflow, &Count), Err(Error::Overflow));
    assert_eq!(
        fast::tabulate(
            &overflow,
            &MinimumWithMultiplicity::new(CostPolicy::AttainableInfinity)
        ),
        Err(Error::Overflow)
    );
    assert_eq!(
        BestTable::new(&overflow).unwrap().scores().answer(),
        Some(&Cost::Finite(0))
    );
}

#[test]
fn malformed_callback_rules_are_rejected_before_child_lookup() {
    struct Bad(Rule<Op>, Cell);
    impl RuleSource for Bad {
        type Op = Op;
        fn cell_count(&self) -> usize {
            1
        }
        fn root(&self) -> Cell {
            self.1
        }
        fn rules_at(
            &self,
            _: Cell,
            mut emit: impl FnMut(Op, &[Cell]) -> Result<(), Error>,
        ) -> Result<(), Error> {
            emit(self.0.operator, &self.0.children)
        }
    }
    assert_eq!(
        fast::tabulate(&Bad(Rule::new(Op::Extend(0), [0]), 0), &Count),
        Err(Error::NonDescendingChild { cell: 0, child: 0 })
    );
    assert_eq!(
        fast::tabulate(&Bad(Rule::new(Op::Extend(0), []), 0), &Count),
        Err(Error::Arity {
            cell: 0,
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(
        fast::tabulate(&Bad(Rule::new(Op::Extend(0), []), 1), &Count),
        Err(Error::MissingRoot(1))
    );
}
