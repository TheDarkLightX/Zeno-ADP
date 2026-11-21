use zeno_adp::algebras::{Cost, Count, Enumerate, Minimum, ScoredOperator};
use zeno_adp::mcfg::{Atom, Grammar, Production, Symbol};
use zeno_adp::{tabulate, tabulate_cells, Error, Operator, Tree};

use super::audit_example;

// Six bytes admit both orders of unequal positive split lengths.
const WORD_BYTES: usize = 6;
const START: usize = 0;
const COPY: usize = 1;
const SYMBOLS: &[Symbol<'_>] = &[
    Symbol {
        name: "start",
        components: 1,
    },
    Symbol {
        name: "copy",
        components: 2,
    },
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Op {
    Base(u8),
    Extend(u8),
    Join(usize),
    Alias,
}

impl Operator for Op {
    fn arity(&self) -> usize {
        match self {
            Self::Base(_) => 0,
            Self::Extend(_) | Self::Alias => 1,
            Self::Join(_) => 2,
        }
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        Cost::Finite(match self {
            Self::Base(byte) | Self::Extend(byte) => i64::from(*byte),
            Self::Join(width) => *width as i64,
            Self::Alias => 0,
        })
    }
}

fn part(child: usize, component: usize) -> Atom {
    Atom::Component { child, component }
}

fn copies(join: Vec<Atom>) -> Grammar<Op> {
    let mut rules = vec![Production {
        name: "join".into(),
        parent: START,
        children: vec![COPY, COPY],
        patterns: vec![join],
        operator: Box::new(|m| Op::Join(m.children[0].spans[0].range().len())),
    }];
    for byte in [0, 1] {
        rules.push(Production {
            name: format!("base-{byte}"),
            parent: COPY,
            children: vec![],
            patterns: vec![vec![Atom::Byte(byte)]; 2],
            operator: Box::new(move |_| Op::Base(byte)),
        });
        rules.push(Production {
            name: format!("extend-{byte}"),
            parent: COPY,
            children: vec![COPY],
            patterns: vec![
                vec![Atom::Byte(byte), part(0, 0)],
                vec![Atom::Byte(byte), part(0, 1)],
            ],
            operator: Box::new(move |_| Op::Extend(byte)),
        });
    }
    Grammar::new(SYMBOLS, START, rules).unwrap()
}

fn crossing() -> Vec<Atom> {
    vec![part(0, 0), part(1, 0), part(0, 1), part(1, 1)]
}

fn tree_score(tree: &Tree<Op>) -> Cost {
    tree.children
        .iter()
        .fold(tree.operator.cost(), |sum, child| {
            sum.plus(tree_score(child)).unwrap()
        })
}

fn root_oracle(word: &[u8]) -> Vec<Cost> {
    let mut scores = Vec::new();
    let (first_half, second_half) = word.split_at(word.len() / 2);
    if first_half == second_half {
        for width in 1..first_half.len() {
            scores.push(Cost::Finite(
                width as i64 + first_half.iter().map(|&b| i64::from(b)).sum::<i64>(),
            ));
        }
    }
    scores
}

#[test]
fn crossing_tuple_charts_match_the_slice_oracle_at_every_cell() {
    let grammar = copies(crossing());
    let adjacent = copies(vec![part(0, 0), part(0, 1), part(1, 0), part(1, 1)]);
    let mut inputs = 0;
    let mut cells = 0;
    let mut rules = 0;
    let mut root_accepts = 0;
    let mut root_occurrences = 0;
    let mut occurrences = 0;
    let mut adjacent_disagreements = 0;
    let mut observed_crossing = Vec::new();
    for size in 0..=WORD_BYTES {
        for bits in 0..1 << size {
            let word: Vec<_> = (0..size).map(|bit| ((bits >> bit) & 1) as u8).collect();
            let instance = grammar.instantiate(&word).unwrap();
            let chart = instance.chart();
            let count = tabulate_cells(chart, &Count).unwrap();
            let score = tabulate_cells(chart, &Minimum).unwrap();
            let trees = tabulate_cells(chart, &Enumerate).unwrap();
            for (rank, item) in instance.items().iter().enumerate() {
                let expected = match item.spans.as_slice() {
                    [whole] => {
                        assert_eq!(item.nonterminal, START);
                        assert_eq!(rank, chart.root());
                        assert_eq!(whole.range(), 0..size);
                        root_oracle(&word)
                    }
                    [a, b] => {
                        assert_eq!(item.nonterminal, COPY);
                        assert!(a.start < a.end && a.end <= b.start && b.start < b.end);
                        let x = &word[a.range()];
                        let y = &word[b.range()];
                        if x == y {
                            vec![Cost::Finite(x.iter().map(|&byte| i64::from(byte)).sum())]
                        } else {
                            Vec::new()
                        }
                    }
                    _ => panic!("unexpected fan-out"),
                };
                let actual: Vec<_> = trees[rank].iter().map(tree_score).collect();
                assert_eq!(actual, expected, "{word:?} {item:?}");
                assert_eq!(
                    count[rank].first().copied().unwrap_or(0),
                    expected.len() as u128
                );
                assert_eq!(score[rank].first().copied(), expected.iter().copied().min());
                occurrences += expected.len();
            }
            let distinct = trees[chart.root()]
                .iter()
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(distinct.len(), trees[chart.root()].len());
            root_accepts += usize::from(!count[chart.root()].is_empty());
            root_occurrences += distinct.len();
            let adjacent_counts =
                tabulate(adjacent.instantiate(&word).unwrap().chart(), &Count).unwrap();
            adjacent_disagreements += usize::from(count[chart.root()] != adjacent_counts);
            if size == crossing().len() {
                observed_crossing.push(usize::from(!count[chart.root()].is_empty()));
            }
            cells += chart.cells().len();
            rules += chart.cells().iter().map(Vec::len).sum::<usize>();
            inputs += 1;
        }
    }
    assert_eq!(inputs, 127);
    println!("crossing-observations {observed_crossing:?}");
    let input = [0, 1, 0, 1];
    let cross = grammar.instantiate(&input).unwrap();
    assert_eq!(tabulate(cross.chart(), &Count).unwrap(), [1]);
    assert!(
        tabulate(adjacent.instantiate(&input).unwrap().chart(), &Count)
            .unwrap()
            .is_empty()
    );
    let audit = grammar.instantiate(&[0, 1, 0, 0, 1, 0]).unwrap();
    let audited_nodes = audit_example(audit.chart(), &Minimum);
    println!("MCFG: {inputs} inputs, {cells} cells, {rules} rules, {root_accepts} accepted roots, {root_occurrences} root occurrences, {occurrences} total occurrences, {adjacent_disagreements} adjacent-copy disagreements, {audited_nodes} audited tree nodes");
}

#[test]
fn tuple_validation_and_same_yield_order() {
    let unary = |patterns, name: &str| Production {
        name: name.into(),
        parent: START,
        children: vec![COPY],
        patterns,
        operator: Box::new(|_| Op::Alias),
    };
    let refuses = |rule, reason| match Grammar::new(SYMBOLS, START, vec![rule]) {
        Err(Error::UnsupportedGrammar { reason: actual, .. }) => assert_eq!(actual, reason),
        _ => panic!("expected declaration refusal"),
    };
    refuses(
        unary(vec![vec![part(0, 0), part(0, 0)]], "copy-variable"),
        "a child component occurs twice",
    );
    refuses(
        unary(vec![vec![part(0, 0)]], "erase-variable"),
        "each child component must occur",
    );
    refuses(
        unary(vec![vec![part(0, 2)]], "unknown-variable"),
        "unknown child component",
    );
    refuses(
        unary(vec![vec![]], "empty-component"),
        "expected one nonempty pattern per component",
    );
    let cycle = Production {
        name: "cycle".into(),
        parent: START,
        children: vec![START],
        patterns: vec![vec![part(0, 0)]],
        operator: Box::new(|_| Op::Alias),
    };
    refuses(cycle, "blocked by a same-yield unary cycle");

    let base = |name: &str, label| Production {
        name: name.into(),
        parent: COPY,
        children: vec![],
        patterns: vec![vec![Atom::Any], vec![Atom::Byte(0)]],
        operator: Box::new(move |_| Op::Base(label)),
    };
    let grammar = Grammar::new(
        SYMBOLS,
        START,
        vec![
            unary(vec![vec![part(0, 1), part(0, 0)]], "reverse-physical-order"),
            base("first", 1),
            base("second", 0),
            base("duplicate-term", 0),
        ],
    )
    .unwrap();
    let parsed = grammar.instantiate(&[0, 1]).unwrap();
    assert!(parsed.items()[0].spans[0].start > parsed.items()[0].spans[1].start);
    assert_eq!(parsed.chart().root(), 1);
    assert_eq!(tabulate(parsed.chart(), &Count).unwrap(), [3]);
    let trees = tabulate(parsed.chart(), &Enumerate).unwrap();
    let operators: Vec<_> = trees.iter().map(|tree| tree.children[0].operator).collect();
    assert_eq!(operators, [Op::Base(1), Op::Base(0), Op::Base(0)]);
    let rejected = grammar.instantiate(&[]).unwrap();
    assert_eq!(rejected.chart().cells().len(), 1);
    assert!(tabulate(rejected.chart(), &Count).unwrap().is_empty());
}

#[test]
fn all_orders_of_fanout_three_components() {
    // Two tuples of three distinguishable components cover interleaving and
    // reversed physical order beyond the fan-out-two language fixture.
    const FAN_OUT: usize = 3;
    const COMPONENTS: usize = 2 * FAN_OUT;
    let symbols = [
        Symbol {
            name: "start",
            components: 1,
        },
        Symbol {
            name: "left",
            components: FAN_OUT,
        },
        Symbol {
            name: "right",
            components: FAN_OUT,
        },
    ];
    let bytes = [[0, 1, 0], [1, 0, 1]];
    fn permutations(order: &mut [usize], start: usize, visit: &mut impl FnMut(&[usize])) {
        if start == order.len() {
            visit(order);
        }
        for next in start..order.len() {
            order.swap(start, next);
            permutations(order, start + 1, visit);
            order.swap(start, next);
        }
    }
    let mut cases = 0;
    let mut cells = 0;
    let mut accepts = 0;
    let mut order = std::array::from_fn::<_, COMPONENTS, _>(|i| i);
    permutations(&mut order, 0, &mut |order| {
        let mut rules = vec![Production {
            name: "shuffle".into(),
            parent: START,
            children: vec![1, 2],
            patterns: vec![order
                .iter()
                .map(|&id| part(id / FAN_OUT, id % FAN_OUT))
                .collect()],
            operator: Box::new(|_| Op::Join(0)),
        }];
        for (side, tuple) in bytes.iter().enumerate() {
            rules.push(Production {
                name: symbols[side + 1].name.into(),
                parent: side + 1,
                children: vec![],
                patterns: tuple.iter().map(|&byte| vec![Atom::Byte(byte)]).collect(),
                operator: Box::new(|_| Op::Base(0)),
            });
        }
        let grammar = Grammar::new(&symbols, START, rules).unwrap();
        for bits in 0..1 << COMPONENTS {
            let input: [u8; COMPONENTS] = std::array::from_fn(|i| ((bits >> i) & 1) as u8);
            let instance = grammar.instantiate(&input).unwrap();
            let count = tabulate_cells(instance.chart(), &Count).unwrap();
            let mut both_children = true;
            assert_eq!(instance.items().len(), 3);
            for (side, tuple) in bytes.iter().enumerate() {
                let rank = instance
                    .items()
                    .iter()
                    .position(|item| item.nonterminal == side + 1)
                    .unwrap();
                let mut accepted = true;
                for (component, &byte) in tuple.iter().enumerate() {
                    let index = order
                        .iter()
                        .position(|&id| id == side * FAN_OUT + component)
                        .unwrap();
                    assert_eq!(
                        instance.items()[rank].spans[component].range(),
                        index..index + 1
                    );
                    accepted &= input[index] == byte;
                }
                assert_eq!(
                    count[rank].first().copied().unwrap_or(0),
                    u128::from(accepted)
                );
                both_children &= accepted;
            }
            let root = instance.chart().root();
            assert_eq!(
                count[root].first().copied().unwrap_or(0),
                u128::from(both_children)
            );
            cases += 1;
            cells += count.len();
            accepts += usize::from(both_children);
        }
    });
    let orderings: usize = (1..=COMPONENTS).product();
    assert_eq!(cases, orderings * (1 << COMPONENTS));
    assert_eq!(accepts, orderings);
    println!("MCFG fan-out three: {cases} cases, {cells} cells, {accepts} accepted roots");
}
