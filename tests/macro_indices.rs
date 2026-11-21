use zeno_adp::algebras::Count;
use zeno_adp::{compiled, compiled_grammar, tabulate_cells, Chart, Operator, Rule};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Node(usize);

impl Operator for Node {
    fn arity(&self) -> usize {
        self.0
    }
}

mod caller_aliases {
    use super::*;

    #[allow(non_camel_case_types)]
    type usize = u8;

    compiled_grammar! {
        fn grammar(input: usize) -> Node {
            interval |tokens, start, end|;
            empty Empty => Ok(Some(Node(0)));
            pivot Key(split) => Ok((tokens[split] == 1).then_some(Node(2)));
        }
        with fn count: Count = Count;
    }

    #[test]
    fn token_type_uses_caller_alias_and_indices_use_core_usize() {
        // Length two exercises every pivot position and both possible weights.
        const MAX_LENGTH: ::core::primitive::usize = 2;
        for len in 0..=MAX_LENGTH {
            for word in 0..1 << len {
                let tokens: Vec<usize> = (0..len).map(|i| ((word >> i) & 1) as usize).collect();
                let mut cells = vec![vec![Rule::new(Node(0), [])]];
                if let Some(&first) = tokens.first() {
                    cells.push(vec![Rule::new(Node(0), [])]);
                    cells.push(if first == 1 {
                        vec![Rule::new(Node(2), [0, 1])]
                    } else {
                        vec![]
                    });
                }
                if let Some(&second) = tokens.get(1) {
                    cells.push(vec![Rule::new(Node(0), [])]);
                    cells.push(if second == 1 {
                        vec![Rule::new(Node(2), [1, 3])]
                    } else {
                        vec![]
                    });
                    let mut root = Vec::new();
                    if tokens[0] == 1 {
                        root.push(Rule::new(Node(2), [0, 4]));
                    }
                    if second == 1 {
                        root.push(Rule::new(Node(2), [2, 3]));
                    }
                    cells.push(root);
                }
                let root = cells.len() - 1;
                let reference = Chart::new(cells, root).unwrap();
                let bound = grammar(&tokens).unwrap();
                let table = count(&tokens).unwrap();
                assert_eq!(table, compiled::tabulate(&bound, &Count).unwrap());
                assert_eq!(table.root(), root);
                assert_eq!(
                    table
                        .cells()
                        .iter()
                        .map(|cell| cell.iter().copied().collect())
                        .collect::<Vec<Vec<_>>>(),
                    tabulate_cells(&reference, &Count).unwrap()
                );
            }
        }
    }
}
