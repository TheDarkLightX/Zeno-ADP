use super::{step, words, Checks, Step};
use zeno_adp::algebras::{Count, Enumerate};
use zeno_adp::mcfg::{self, Atom, Grammar, Production, Symbol};
use zeno_adp::{tabulate, tabulate_cells, Chart, Error, Tree};

const START: usize = 0;
const FIRST: usize = 1;
const SECOND: usize = 2;

fn part(child: usize, component: usize) -> Atom {
    Atom::Component { child, component }
}

fn production(
    name: &str,
    parent: usize,
    children: Vec<usize>,
    patterns: Vec<Vec<Atom>>,
    op: Step,
) -> Production<Step> {
    Production {
        name: name.into(),
        parent,
        children,
        patterns,
        operator: Box::new(move |_| op),
    }
}

fn paired_rules(parent: usize, alphabet: &[(u8, u8, &'static str)]) -> Vec<Production<Step>> {
    let mut rules = Vec::new();
    for &(a, b, name) in alphabet {
        let leaf = Step {
            name,
            cost: i64::from(a),
            arity: 0,
        };
        let extend = Step { arity: 1, ..leaf };
        rules.push(production(
            &format!("base {name}"),
            parent,
            vec![],
            vec![vec![Atom::Byte(a)], vec![Atom::Byte(b)]],
            leaf,
        ));
        rules.push(production(
            &format!("extend {name}"),
            parent,
            vec![parent],
            vec![
                vec![Atom::Byte(a), part(0, 0)],
                vec![Atom::Byte(b), part(0, 1)],
            ],
            extend,
        ));
    }
    rules
}

fn finish(name: &'static str, children: Vec<usize>, pattern: Vec<Atom>) -> Production<Step> {
    let op = Step {
        name,
        cost: 0,
        arity: children.len(),
    };
    production(name, START, children, vec![pattern], op)
}

const SYMBOLS: [Symbol<'static>; 3] = [
    Symbol {
        name: "start",
        components: 1,
    },
    Symbol {
        name: "first pair",
        components: 2,
    },
    Symbol {
        name: "second pair",
        components: 2,
    },
];

fn empty_case() -> Result<Chart<Step>, Error> {
    // MCFG components have positive width. The public recipe accepts
    // empty input via its own nullary constructor.
    Chart::new(vec![vec![step("empty input", 0, [])]], 0)
}

fn half(input: &[u8]) -> Option<&[u8]> {
    let middle = input.len() / 2;
    (input[..middle] == input[middle..]).then_some(&input[..middle])
}

fn repeated_witness(tree: &Tree<Step>, out: &mut Vec<u8>) {
    out.push(tree.operator.cost as u8);
    if let [child] = tree.children.as_slice() {
        repeated_witness(child, out);
    }
}

pub fn repeated_half() -> Result<Checks, Error> {
    const MAX_LEN: usize = 6; // Three rounds of the paired constructor.
    let mut rules = paired_rules(FIRST, &[(b'a', b'a', "a"), (b'b', b'b', "b")]);
    rules.push(finish(
        "concatenate halves",
        vec![FIRST],
        vec![part(0, 0), part(0, 1)],
    ));
    let grammar = Grammar::new(&SYMBOLS[..SECOND], START, rules)?;
    let mut checks = Checks::default();
    let empty = empty_case()?;
    checks.chart(&empty);
    assert_eq!(tabulate(&empty, &Count)?, [1]);
    assert_eq!(half(b""), Some(&b""[..]));
    for word in words(b"ab", MAX_LEN).into_iter().skip(1) {
        let reference = grammar.instantiate(&word)?;
        let program = mcfg::compile(&grammar, &word)?;
        let chart = reference.chart();
        checks.chart(chart);
        checks.compiled(&program, chart, &Count)?;
        let counts = tabulate_cells(chart, &Count)?;
        for (rank, item) in reference.items().iter().enumerate() {
            assert_eq!(program.item(rank), Some(item));
            let valid = match item.spans.as_slice() {
                [whole] => half(&word[whole.range()]).is_some(),
                [a, b] => word[a.range()] == word[b.range()],
                _ => unreachable!(),
            };
            assert!(counts[rank].iter().copied().eq(valid.then_some(1)));
        }
        let trees = tabulate(chart, &Enumerate)?;
        let found: Vec<_> = trees
            .iter()
            .map(|tree| {
                let mut decoded = Vec::new();
                repeated_witness(&tree.children[0], &mut decoded);
                decoded
            })
            .collect();
        assert!(found.iter().map(Vec::as_slice).eq(half(&word)));
    }
    Ok(checks)
}

fn run_pair(left: &[u8], right: &[u8], a: u8, b: u8) -> bool {
    left.len() == right.len() && left.iter().all(|&x| x == a) && right.iter().all(|&x| x == b)
}

fn four_runs(word: &[u8]) -> Option<(usize, usize)> {
    let mut tail = word;
    let sizes = (*b"abcd").map(|token| {
        let size = tail.iter().take_while(|&&x| x == token).count();
        tail = &tail[size..];
        size
    });
    (tail.is_empty() && sizes[0] == sizes[2] && sizes[1] == sizes[3])
        .then_some((sizes[0], sizes[1]))
}

fn depth(tree: &Tree<Step>) -> usize {
    1 + tree.children.first().map_or(0, depth)
}

pub fn cross_serial() -> Result<Checks, Error> {
    const MAX_LEN: usize = 4; // The shortest word with both crossing dependencies.
    let mut rules = paired_rules(FIRST, &[(b'a', b'c', "ac")]);
    rules.extend(paired_rules(SECOND, &[(b'b', b'd', "bd")]));
    rules.extend([
        finish("ac only", vec![FIRST], vec![part(0, 0), part(0, 1)]),
        finish("bd only", vec![SECOND], vec![part(0, 0), part(0, 1)]),
        finish(
            "crossing",
            vec![FIRST, SECOND],
            vec![part(0, 0), part(1, 0), part(0, 1), part(1, 1)],
        ),
    ]);
    let grammar = Grammar::new(&SYMBOLS, START, rules)?;
    let mut checks = Checks::default();
    let empty = empty_case()?;
    checks.chart(&empty);
    assert_eq!(tabulate(&empty, &Count)?, [1]);
    assert_eq!(four_runs(b""), Some((0, 0)));
    let additional = [b"aabccd".to_vec(), b"aabcdc".to_vec()];
    for word in words(b"abcd", MAX_LEN)
        .into_iter()
        .skip(1)
        .chain(additional)
    {
        let reference = grammar.instantiate(&word)?;
        let program = mcfg::compile(&grammar, &word)?;
        let chart = reference.chart();
        checks.chart(chart);
        checks.compiled(&program, chart, &Count)?;
        let counts = tabulate_cells(chart, &Count)?;
        for (rank, item) in reference.items().iter().enumerate() {
            assert_eq!(program.item(rank), Some(item));
            let valid = match item.spans.as_slice() {
                [full] => four_runs(&word[full.range()]).is_some(),
                [a, b] => {
                    let [x, y] = if item.nonterminal == FIRST {
                        *b"ac"
                    } else {
                        *b"bd"
                    };
                    run_pair(&word[a.range()], &word[b.range()], x, y)
                }
                _ => unreachable!(),
            };
            assert!(counts[rank].iter().copied().eq(valid.then_some(1)));
        }
        let trees = tabulate(chart, &Enumerate)?;
        let found = trees.iter().map(|tree| match tree.operator.name {
            "ac only" => (depth(&tree.children[0]), 0),
            "bd only" => (0, depth(&tree.children[0])),
            "crossing" => (depth(&tree.children[0]), depth(&tree.children[1])),
            _ => unreachable!(),
        });
        assert!(found.eq(four_runs(&word)));
    }
    Ok(checks)
}
