use std::fmt::Debug;
use zeno_adp::algebras::Enumerate;
use zeno_adp::compiled::{self, Program};
use zeno_adp::grammars::*;
use zeno_adp::{tabulate_cells, Chart, Operator, Rule};

// Each fixture instantiates the documented productions, including payloads,
// child order and alternatives that must be absent. Cover every cell.
fn check<O: Operator + Debug + Eq>(
    chart: &Chart<O>,
    source: impl Program<Op = O>,
    expected: Vec<Vec<Rule<O>>>,
) {
    let expected = Chart::new(expected, chart.cells().len() - 1).unwrap();
    assert_eq!(*chart, expected);
    assert_eq!(compiled::reference_chart(&source).unwrap(), expected);
    assert_eq!(
        tabulate_cells(chart, &Enumerate).unwrap(),
        tabulate_cells(&expected, &Enumerate).unwrap()
    );
}

#[test]
fn nussinov_derivations() {
    use Fold::{Empty, Pair, Unpaired};
    // Cell 0 is the shared empty span. AUU can pair positions 0 and 2;
    // min_loop = 1 rules out the adjacent pair.
    for (sequence, can_pair) in [(b"AUU", true), (b"AUA", false)] {
        let unpaired = |at, child| Rule::new(Unpaired { at }, [child]);
        let mut root = vec![unpaired(0, 5)];
        if can_pair {
            root.push(Rule::new(Pair { left: 0, right: 2 }, [2, 0]));
        }
        check(
            &nussinov(sequence, 1).unwrap(),
            nussinov_source(sequence, 1).unwrap(),
            vec![
                vec![Rule::new(Empty, [])],
                vec![unpaired(0, 0)],
                vec![unpaired(1, 0)],
                vec![unpaired(2, 0)],
                vec![unpaired(0, 2)],
                vec![unpaired(1, 3)],
                root,
            ],
        );
    }
}

#[test]
fn alignment_derivations() {
    use Align::{Diagonal, Left, Right, Start};
    check(
        &alignment(b"a", b"b").unwrap(),
        alignment_source(b"a", b"b").unwrap(),
        vec![
            vec![Rule::new(Start, [])],
            vec![Rule::new(Right(b'b'), [0])],
            vec![Rule::new(Left(b'a'), [0])],
            vec![
                Rule::new(
                    Diagonal {
                        left: b'a',
                        right: b'b',
                    },
                    [0],
                ),
                Rule::new(Left(b'a'), [1]),
                Rule::new(Right(b'b'), [2]),
            ],
        ],
    );
}

#[test]
fn local_alignment_derivations() {
    use LocalAlign::{Column, Empty, End, Start};
    let start = |left, right| vec![Rule::new(Start { left, right }, [])];
    let column = |op, child| Rule::new(Column(op), [child]);
    let left = Align::Left(b'a');
    let right = Align::Right(b'b');
    let both = Align::Diagonal {
        left: b'a',
        right: b'b',
    };
    check(
        &local_alignment(b"a", b"b").unwrap(),
        local_alignment_source(b"a", b"b").unwrap(),
        vec![
            start(0, 0),
            start(0, 1),
            start(1, 0),
            start(1, 1),
            vec![],
            vec![column(right, 0), column(right, 4)],
            vec![column(left, 0), column(left, 4)],
            vec![
                column(both, 0),
                column(both, 4),
                column(left, 1),
                column(left, 5),
                column(right, 2),
                column(right, 6),
            ],
            vec![
                Rule::new(Empty, []),
                Rule::new(End, [4]),
                Rule::new(End, [5]),
                Rule::new(End, [6]),
                Rule::new(End, [7]),
            ],
        ],
    );
}

#[test]
fn matrix_chain_derivations() {
    use MatrixChain::{Matrix, Multiply};
    let dimensions = [10, 30, 5, 60];
    let multiply = |left, split, right, cost, children| {
        Rule::new(
            Multiply {
                left,
                split,
                right,
                cost,
            },
            children,
        )
    };
    check(
        &matrix_chain(&dimensions).unwrap(),
        matrix_chain_source(&dimensions).unwrap(),
        vec![
            vec![Rule::new(Matrix { at: 0 }, [])],
            vec![Rule::new(Matrix { at: 1 }, [])],
            vec![Rule::new(Matrix { at: 2 }, [])],
            vec![multiply(0, 1, 2, 1_500, [0, 1])],
            vec![multiply(1, 2, 3, 9_000, [1, 2])],
            vec![
                multiply(0, 1, 3, 18_000, [0, 4]),
                multiply(0, 2, 3, 3_000, [3, 2]),
            ],
        ],
    );
}

#[test]
fn knapsack_derivations() {
    use Knapsack::{Empty, Pick, Skip};
    let items = [
        Item {
            weight: 0,
            value: 3,
        },
        Item {
            weight: 1,
            value: 5,
        },
    ];
    let skip = |item, child| Rule::new(Skip { item }, [child]);
    let pick = |item, value, child| Rule::new(Pick { item, value }, [child]);
    check(
        &knapsack(&items, 1).unwrap(),
        knapsack_source(&items, 1).unwrap(),
        vec![
            vec![Rule::new(Empty, [])],
            vec![Rule::new(Empty, [])],
            vec![skip(0, 0), pick(0, 3, 0)],
            vec![skip(0, 1), pick(0, 3, 1)],
            vec![skip(1, 2)],
            vec![skip(1, 3), pick(1, 5, 2)],
        ],
    );
}

#[test]
fn sequence_prefix_derivations() {
    use Prefix::{Start, Token};
    let chart = sequence_prefixes(&['x', 'x']).unwrap();
    let expected = Chart::new(
        vec![
            vec![Rule::new(Start, [])],
            vec![Rule::new(Token('x'), [0])],
            vec![Rule::new(Token('x'), [1])],
        ],
        2,
    )
    .unwrap();
    assert_eq!(chart, expected);
    assert_eq!(
        tabulate_cells(&chart, &Enumerate).unwrap(),
        tabulate_cells(&expected, &Enumerate).unwrap()
    );
}
