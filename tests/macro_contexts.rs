use zeno_adp::algebras::Count;
use zeno_adp::compiled::{self, Program};
use zeno_adp::fast::Table;
use zeno_adp::{compiled_grammar, tabulate_cells, Chart, Error, Operator, Rule};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Node(usize);

impl Operator for Node {
    fn arity(&self) -> usize {
        self.0
    }
}

// These functions are deliberately in scope wherever a grammar with the
// same name is declared. They count a leaf on the empty word.
compiled_grammar! {
    fn prefix(input: u8) -> Node {
        prefix |tokens, start, end|;
        empty Ambient => Ok(Some(Node(0)));
    }
}
compiled_grammar! {
    fn interval(input: u8) -> Node {
        interval |tokens, start, end|;
        empty Ambient => Ok(Some(Node(0)));
    }
}

macro_rules! grammars {
    ($enabled:expr $(; $count_prefix:ident, $count_interval:ident)?) => {
        compiled_grammar! {
            fn prefix(argument: u8) -> Node {
                prefix |tokens, start, end|;
                empty Base => Ok(($enabled && tokens.first() == Some(&1)).then_some(Node(0)));
                extend Step(split) => Ok((tokens[split] == 1).then_some(Node(1)));
            }
            $(with fn $count_prefix: Count = {
                let _: &[u8] = argument;
                Count
            };)?
        }

        compiled_grammar! {
            fn interval(input: u8) -> Node {
                interval |tokens, start, end|;
                empty Base => Ok(($enabled && tokens.first() == Some(&1)).then_some(Node(0)));
                pivot Step(split) => Ok((tokens[split] == 1).then_some(Node(2)));
            }
            $(with fn $count_interval: Count = Count;)?
        }
    };
}

fn check(reference: Chart<Node>, bound: impl Program<Op = Node>, paired: Table<u128>) {
    let reconstructed = compiled::reference_chart(&bound).unwrap();
    assert_eq!(reconstructed.root(), reference.root());
    assert_eq!(reconstructed.cells().len(), reference.cells().len());
    for (actual, expected) in reconstructed.cells().iter().zip(reference.cells()) {
        assert!(actual
            .iter()
            .map(|rule| (&rule.operator, &rule.children))
            .eq(expected.iter().map(|rule| (&rule.operator, &rule.children))));
    }
    let expected = tabulate_cells(&reference, &Count).unwrap();
    assert_eq!(compiled::tabulate(&bound, &Count).unwrap(), paired);
    assert_eq!(paired.root(), reference.root());
    assert!(paired
        .cells()
        .iter()
        .zip(&expected)
        .all(|(one, bag)| one.iter().eq(bag)));
    assert_eq!(paired.cells().len(), expected.len());
}

fn reference(input: &[u8], interval: bool) -> Chart<Node> {
    let spans: Vec<_> = (0..=input.len())
        .flat_map(|end| {
            (0..=if interval { end } else { 0 })
                .rev()
                .map(move |start| (start, end))
        })
        .collect();
    let rank = |span| spans.iter().position(|&other| other == span).unwrap();
    let cells = spans
        .iter()
        .map(|&(start, end)| {
            if start == end {
                return (input.first() == Some(&1))
                    .then(|| Rule::new(Node(0), []))
                    .into_iter()
                    .collect();
            }
            (start..end)
                .filter(|&split| input[split] == 1)
                .map(|split| {
                    if interval {
                        Rule::new(Node(2), [rank((start, split)), rank((split + 1, end))])
                    } else {
                        Rule::new(Node(1), [rank((0, split))])
                    }
                })
                .collect()
        })
        .collect();
    Chart::new(cells, spans.len() - 1).unwrap()
}

macro_rules! check_positions {
    ($($scope:ident ::)? ) => {
        // Two tokens allow both child orders and both admitted and absent cells.
        const MAX_LENGTH: usize = 2;
        for len in 0..=MAX_LENGTH {
            for word in 0..1 << len {
                let input: Vec<_> = (0..len).map(|i| ((word >> i) & 1) as u8).collect();
                check(
                    reference(&input, false),
                    $($scope::)? prefix(&input).unwrap(),
                    $($scope::)? count_prefix(&input).unwrap(),
                );
                check(
                    reference(&input, true),
                    $($scope::)? interval(&input).unwrap(),
                    $($scope::)? count_interval(&input).unwrap(),
                );
            }
        }
    };
}

#[test]
fn inherent_impl_binds_its_own_grammar() {
    struct Parser;
    impl Parser {
        const ENABLED: bool = true;
        grammars!(Self::ENABLED);

        fn count_prefix(input: &[u8]) -> Result<Table<u128>, Error> {
            compiled::tabulate(&Self::prefix(input)?, &Count)
        }

        fn count_interval(input: &[u8]) -> Result<Table<u128>, Error> {
            compiled::tabulate(&Self::interval(input)?, &Count)
        }
    }
    assert_eq!(
        compiled::tabulate(&prefix(&[]).unwrap(), &Count)
            .unwrap()
            .answer(),
        Some(&1)
    );
    assert_eq!(
        compiled::tabulate(&interval(&[]).unwrap(), &Count)
            .unwrap()
            .answer(),
        Some(&1)
    );
    check_positions!(Parser::);
}

#[test]
fn trait_impl_binds_its_own_grammar() {
    trait Parsing {
        const ENABLED: bool;
        fn prefix(input: &[u8]) -> Result<impl Program<Op = Node> + '_, Error>;
        fn interval(input: &[u8]) -> Result<impl Program<Op = Node> + '_, Error>;
        fn count_prefix(input: &[u8]) -> Result<Table<u128>, Error>;
        fn count_interval(input: &[u8]) -> Result<Table<u128>, Error>;
    }
    struct Parser;
    impl Parsing for Parser {
        const ENABLED: bool = true;
        grammars!(Self::ENABLED);

        fn count_prefix(input: &[u8]) -> Result<Table<u128>, Error> {
            compiled::tabulate(&Self::prefix(input)?, &Count)
        }

        fn count_interval(input: &[u8]) -> Result<Table<u128>, Error> {
            compiled::tabulate(&Self::interval(input)?, &Count)
        }
    }
    check_positions!(Parser::);
}

mod nested {
    use super::*;

    mod grammar {
        use super::*;
        const ENABLED: bool = true;
        grammars!(ENABLED; count_prefix, count_interval);

        #[test]
        fn nested_module_binds_its_own_grammar() {
            check_positions!();
        }
    }
}

#[test]
fn function_local_items_bind_their_own_grammar() {
    const ENABLED: bool = true;
    grammars!(ENABLED; count_prefix, count_interval);
    check_positions!();
}
