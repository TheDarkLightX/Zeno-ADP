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

macro_rules! generated_mcfg {
    ($name:ident, $eval:ident, $join:expr) => {
        zeno_adp::compiled_grammar! {
            fn $name(input: u8) -> Op {
                mcfg SYMBOLS; start START;
                production Join(m): START, vec![COPY, COPY], vec![$join]
                    => Op::Join(m.children[0].spans[0].range().len());
                production Base0(m): COPY, vec![], vec![vec![Atom::Byte(0)]; 2] => Op::Base(0);
                production Extend0(m): COPY, vec![COPY],
                    vec![vec![Atom::Byte(0), part(0, 0)], vec![Atom::Byte(0), part(0, 1)]]
                    => Op::Extend(0);
                production Base1(m): COPY, vec![], vec![vec![Atom::Byte(1)]; 2] => Op::Base(1);
                production Extend1(m): COPY, vec![COPY],
                    vec![vec![Atom::Byte(1), part(0, 0)], vec![Atom::Byte(1), part(0, 1)]]
                    => Op::Extend(1);
            }
            with fn $eval: Count = Count;
        }
    };
}

generated_mcfg!(generated_crossing, crossing_count, crossing());
generated_mcfg!(
    generated_reversed,
    reversed_count,
    vec![part(0, 1), part(1, 0), part(0, 0), part(1, 1)]
);

#[test]
fn generated_mcfg_replays_ranked_items_and_ordered_productions() {
    let crossing = copies(crossing());
    let reversed = copies(vec![part(0, 1), part(1, 0), part(0, 0), part(1, 1)]);
    let mut cells = 0;
    for size in 0..=WORD_BYTES {
        for bits in 0..1 << size {
            let word: Vec<_> = (0..size).map(|bit| ((bits >> bit) & 1) as u8).collect();
            for (bound, instance, paired) in [
                (
                    generated_crossing(&word).unwrap(),
                    crossing.instantiate(&word).unwrap(),
                    crossing_count(&word).unwrap(),
                ),
                (
                    generated_reversed(&word).unwrap(),
                    reversed.instantiate(&word).unwrap(),
                    reversed_count(&word).unwrap(),
                ),
            ] {
                let generated =
                    super::check_generated(&bound, instance.chart(), &Count, |_, _, op| match op {
                        Op::Join(_) => "Join",
                        Op::Base(0) => "Base0",
                        Op::Base(1) => "Base1",
                        Op::Extend(0) => "Extend0",
                        Op::Extend(1) => "Extend1",
                        _ => panic!("unexpected copying-grammar operator"),
                    });
                assert_eq!(paired, generated);
                let minimum =
                    zeno_adp::compiled::tabulate(&bound, &zeno_adp::algebras::Additive::default())
                        .unwrap();
                let expected = tabulate_cells(instance.chart(), &Minimum).unwrap();
                assert_eq!(minimum.cells().len(), expected.len());
                assert!(minimum
                    .cells()
                    .iter()
                    .zip(&expected)
                    .all(|(one, bag)| one.iter().eq(bag)));
                for (rank, item) in instance.items().iter().enumerate() {
                    assert_eq!(bound.item(rank), Some(item));
                }
                assert_eq!(bound.item(instance.items().len()), None);
                cells += instance.items().len();
            }
        }
    }

    const ALIASES: &[Symbol<'_>] = &[
        Symbol {
            name: "start",
            components: 1,
        },
        Symbol {
            name: "leaf",
            components: 1,
        },
    ];
    zeno_adp::compiled_grammar! {
        fn alias(input: u8) -> Op {
            mcfg ALIASES; start START;
            production Alias(m): START, vec![COPY], vec![vec![part(0, 0)]] => Op::Alias;
            production First(m): COPY, vec![], vec![vec![Atom::Any]] => Op::Base(m.input[0]);
            production Second(m): COPY, vec![], vec![vec![Atom::Any]] => Op::Base(m.input[0]);
        }
        with fn alias_count: Count = Count;
    }
    let bound = alias(&[1]).unwrap();
    let mut sites = Vec::new();
    zeno_adp::compiled::replay(&bound, |cell, ordinal, site, op, children| {
        sites.push((cell, ordinal, site.to_owned(), op, children.to_vec()));
        Ok(())
    })
    .unwrap();
    assert_eq!(
        sites,
        [
            (0, 0, "First".into(), Op::Base(1), vec![]),
            (0, 1, "Second".into(), Op::Base(1), vec![]),
            (1, 0, "Alias".into(), Op::Alias, vec![0]),
        ]
    );
    let alias_reference = zeno_adp::Chart::new(
        vec![
            vec![
                zeno_adp::Rule::new(Op::Base(1), []),
                zeno_adp::Rule::new(Op::Base(1), []),
            ],
            vec![zeno_adp::Rule::new(Op::Alias, [0])],
        ],
        1,
    )
    .unwrap();
    assert_eq!(
        alias_count(&[1]).unwrap(),
        super::check_generated(&bound, &alias_reference, &Count, |rank, ordinal, _| {
            [["First", "Second"][ordinal], "Alias"][rank]
        })
    );

    zeno_adp::compiled_grammar! {
        fn repeated_part(input: u8) -> Op {
            mcfg ALIASES; start START;
            production Repeated(m): START, vec![COPY], vec![vec![part(0, 0), part(0, 0)]]
                => Op::Alias;
        }
    }
    assert!(
        matches!(repeated_part(&[]), Err(Error::UnsupportedGrammar { name, .. }) if name == "Repeated")
    );
    println!(
        "generated MCFG: 254 binary-word charts, {cells} cells; alias control: 1 chart, 2 cells"
    );
}

fn crossing_with_suffix() -> Vec<Atom> {
    let mut atoms = crossing();
    atoms.extend([Atom::Any, Atom::Byte(1)]);
    atoms
}

generated_mcfg!(generated_suffix, suffix_count, crossing_with_suffix());

#[test]
fn last_variable_reserves_fixed_width_for_the_suffix() {
    let reference = copies(crossing_with_suffix());
    let mut chart_count = 0;
    let mut ranks = 0;
    let mut inhabited_roots = 0;
    for size in 0..=WORD_BYTES {
        for bits in 0..1 << size {
            let word: Vec<_> = (0..size).map(|bit| ((bits >> bit) & 1) as u8).collect();
            let bound = generated_suffix(&word).unwrap();
            let instance = reference.instantiate(&word).unwrap();
            let generated =
                super::check_generated(&bound, instance.chart(), &Count, |_, _, op| match op {
                    Op::Join(_) => "Join",
                    Op::Base(0) => "Base0",
                    Op::Base(1) => "Base1",
                    Op::Extend(0) => "Extend0",
                    Op::Extend(1) => "Extend1",
                    _ => panic!("unexpected copying-grammar operator"),
                });
            assert_eq!(suffix_count(&word).unwrap(), generated);
            for (rank, item) in instance.items().iter().enumerate() {
                assert_eq!(bound.item(rank), Some(item));
            }
            let width = crossing().len();
            let expected = word.last() == Some(&1)
                && size == width + 2
                && word[..width / 2] == word[width / 2..width];
            assert_eq!(generated.answer().copied(), expected.then_some(1));
            inhabited_roots += usize::from(expected);
            chart_count += 1;
            ranks += instance.items().len();
        }
    }
    assert_eq!(inhabited_roots, 8);
    println!(
        "MCFG fixed suffix: {chart_count} charts, {ranks} ranks, {inhabited_roots} inhabited roots"
    );
}

#[test]
fn tuple_keys_wider_than_a_word_keep_all_endpoint_bits() {
    // At this input length, six components need more than u64 endpoint bits.
    // Moving two bytes between the first two components makes their truncated
    // keys coincide. The two successful splits must remain separate.
    const FAN_OUT: usize = 6;
    const LENGTH: usize = u64::BITS as usize;
    const EXTRA_WIDTH: usize = 2;
    let symbols = [
        Symbol {
            name: "start",
            components: 1,
        },
        Symbol {
            name: "wide",
            components: FAN_OUT,
        },
    ];
    let mut pattern = vec![Atom::Byte(1); LENGTH - FAN_OUT - EXTRA_WIDTH];
    pattern.extend((0..FAN_OUT).map(|component| part(0, component)));
    let leaf = |wide: usize, name: &str| {
        let mut patterns = vec![vec![Atom::Any]; FAN_OUT];
        patterns[wide].extend([Atom::Any; EXTRA_WIDTH]);
        Production {
            name: name.into(),
            parent: COPY,
            children: vec![],
            patterns,
            operator: Box::new(move |_| Op::Base(wide as u8)),
        }
    };
    let grammar = Grammar::new(
        &symbols,
        START,
        vec![
            Production {
                name: "Wide".into(),
                parent: START,
                children: vec![COPY],
                patterns: vec![pattern],
                operator: Box::new(|_| Op::Alias),
            },
            leaf(0, "FirstWide"),
            leaf(1, "SecondWide"),
        ],
    )
    .unwrap();
    let accepted = [1; LENGTH];
    let mut refused = accepted;
    refused[0] = 0;
    let mut ranks = 0;
    for (input, count) in [(&accepted, Some(2)), (&refused, None)] {
        let reference = grammar.instantiate(input).unwrap();
        let compiled = zeno_adp::mcfg::compile(&grammar, input).unwrap();
        let table =
            super::check_generated(&compiled, reference.chart(), &Count, |_, _, op| match op {
                Op::Alias => "Wide",
                Op::Base(0) => "FirstWide",
                Op::Base(1) => "SecondWide",
                _ => panic!("unexpected wide-tuple operator"),
            });
        for (rank, item) in reference.items().iter().enumerate() {
            assert_eq!(compiled.item(rank), Some(item));
        }
        assert_eq!(table.answer().copied(), count);
        ranks += reference.items().len();
    }
    println!("MCFG wide tuple: 2 charts, {ranks} ranks");
}
