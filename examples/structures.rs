use zeno_adp::algebras::{Cost, Count, Minimum};
use zeno_adp::forests::{edit, edit_reference, Node};
use zeno_adp::mcfg::{Atom, Grammar, Production, Symbol};
use zeno_adp::sets::partitions;
use zeno_adp::{tabulate, Error, Operator};

#[derive(Clone)]
enum Crossing {
    Pair,
    Interleave,
}

impl Operator for Crossing {
    fn arity(&self) -> usize {
        match self {
            Self::Pair => 0,
            Self::Interleave => 2,
        }
    }
}

fn crossing_grammar() -> Result<Grammar<Crossing>, Error> {
    let symbols = [
        Symbol {
            name: "start",
            components: 1,
        },
        Symbol {
            name: "equal-byte pair",
            components: 2,
        },
    ];
    let component = |child, component| Atom::Component { child, component };
    let mut rules = vec![Production {
        name: "interleave".into(),
        parent: 0,
        children: vec![1, 1],
        patterns: vec![vec![
            component(0, 0),
            component(1, 0),
            component(0, 1),
            component(1, 1),
        ]],
        operator: Box::new(|_| Crossing::Interleave),
    }];
    for byte in [b'a', b'b'] {
        rules.push(Production {
            name: char::from(byte).to_string(),
            parent: 1,
            children: vec![],
            patterns: vec![vec![Atom::Byte(byte)], vec![Atom::Byte(byte)]],
            operator: Box::new(|_| Crossing::Pair),
        });
    }
    Grammar::new(&symbols, 0, rules)
}

fn main() -> Result<(), Error> {
    // The root can be deleted while its child is retained.
    let left = [Node::new('a', vec![Node::new('b', vec![])])];
    let right = [Node::new('b', vec![])];
    let comparison = edit(&left, &right)?;
    let score = tabulate(comparison.chart(), &Minimum)?;
    let cuts = edit_reference(&left, &right)?;
    let mappings = tabulate(cuts.chart(), &Count)?;
    assert_eq!(score, [Cost::Finite(1)]);
    assert_eq!(mappings, [3]);
    println!("Forest edit cost {score:?}, mappings {mappings:?}");

    let grammar = crossing_grammar()?;
    let crossing = grammar.instantiate(b"abab")?;
    assert_eq!(tabulate(crossing.chart(), &Count)?, [1]);
    let adjacent = grammar.instantiate(b"aabb")?;
    assert!(tabulate(adjacent.chart(), &Count)?.is_empty());
    println!("The crossing grammar accepts abab.");

    // Split four indexed elements into two unordered two-element blocks.
    let partitions = partitions(4, |block| block.count_ones() == 2)?;
    let count = tabulate(&partitions, &Count)?;
    assert_eq!(count, [3]);
    println!("Partitions into two pairs {count:?}");
    Ok(())
}
