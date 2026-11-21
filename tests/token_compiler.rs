use std::ops::Range;
use zeno_adp::algebras::{Additive, Cost, Count, Enumerate, ScoredOperator};
use zeno_adp::compiled::{
    self, Atom, Grammar, Production, TokenAtom, TokenGrammar, TokenMatched, TokenProduction,
};
use zeno_adp::{tabulate_cells, Cell, Chart, Operator, Rule};

#[derive(Eq, PartialEq)]
struct Token(String);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Term {
    site: &'static str,
    arity: usize,
    starts: Vec<usize>,
}

impl Operator for Term {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for Term {
    fn cost(&self) -> Cost {
        Cost::Finite(self.arity as i64)
    }
}

const BASE: usize = 0;
const ROOT: usize = 1;
const NAMES: [&str; 2] = ["base", "root"];
// Three single-track tokens allow repeated terminals; two on each of two
// tracks expose both split orientations while keeping enumeration small.
const SINGLE_MAX: usize = 3;
const DOUBLE_MAX: usize = 2;

type Spans<const N: usize> = [Range<usize>; N];
type Occurrence = (Cell, usize, String, Term, Vec<Cell>);
type Clause<A, const N: usize> = (usize, &'static str, Vec<usize>, [Vec<A>; N]);

fn term<const N: usize>(site: &'static str, arity: usize, spans: &Spans<N>) -> Term {
    Term {
        site,
        arity,
        starts: spans.iter().map(|span| span.start).collect(),
    }
}

fn specs<A, const N: usize>(
    empty: impl Fn() -> Vec<A>,
    literal: impl Fn() -> Vec<A>,
    predicate: impl Fn() -> Vec<A>,
    any: impl Fn() -> Vec<A>,
    child: impl Fn(usize) -> A,
) -> [Clause<A, N>; 6] {
    [
        (BASE, "empty", vec![], std::array::from_fn(|_| empty())),
        (BASE, "literal", vec![], std::array::from_fn(|_| literal())),
        (
            BASE,
            "predicate",
            vec![],
            std::array::from_fn(|_| predicate()),
        ),
        (BASE, "any", vec![], std::array::from_fn(|_| any())),
        (
            ROOT,
            "copy",
            vec![BASE],
            std::array::from_fn(|_| vec![child(0)]),
        ),
        (
            ROOT,
            "join",
            vec![BASE, BASE],
            std::array::from_fn(|track| vec![child(track), child(1 - track)]),
        ),
    ]
}

fn replay(source: &impl compiled::Program<Op = Term>) -> Vec<Occurrence> {
    let mut result = Vec::new();
    compiled::replay(source, |rank, ord, site, op, kids| {
        result.push((rank, ord, site.to_owned(), op, kids.to_vec()));
        Ok(())
    })
    .unwrap();
    result
}

fn words(max: usize) -> Vec<Vec<u8>> {
    (0..=max)
        .flat_map(|n| (0..1 << n).map(move |x| (0..n).map(|b| (x >> b) & 1).collect()))
        .collect()
}

fn spans(n: usize) -> Vec<Range<usize>> {
    (0..=n)
        .flat_map(|width| (0..=n - width).map(move |start| start..start + width))
        .collect()
}

fn check<const N: usize>(words: [&[u8]; N]) -> (usize, usize) {
    let expected_one = String::from("1");
    let definitions = specs::<_, N>(
        Vec::new,
        || vec![TokenAtom::Equals(Token(String::from("0")))],
        || {
            let target = expected_one.clone();
            vec![TokenAtom::Predicate(Box::new(move |token: &Token| {
                token.0 == target
            }))]
        },
        || vec![TokenAtom::Any],
        TokenAtom::Child,
    );
    let grammar = TokenGrammar::new(
        &NAMES,
        ROOT,
        definitions
            .into_iter()
            .map(|(parent, site, children, tracks)| {
                let arity = children.len();
                TokenProduction {
                    name: site.into(),
                    parent,
                    children,
                    tracks,
                    operator: Box::new(move |m: TokenMatched<'_, N, Token>| {
                        term(site, arity, m.parent)
                    }),
                }
            })
            .collect(),
    )
    .unwrap();
    let byte_grammar = Grammar::new(
        &NAMES,
        ROOT,
        specs::<_, N>(
            Vec::new,
            || vec![Atom::Byte(0)],
            || vec![Atom::Byte(1)],
            || vec![Atom::Any],
            Atom::Child,
        )
        .into_iter()
        .map(|(parent, site, children, tracks)| {
            let arity = children.len();
            Production {
                name: site.into(),
                parent,
                children,
                tracks,
                operator: Box::new(move |m| term(site, arity, m.parent)),
            }
        })
        .collect(),
    )
    .unwrap();
    let input = words.map(|word| {
        word.iter()
            .map(|b| Token(b.to_string()))
            .collect::<Vec<_>>()
    });
    let program = grammar
        .bind(std::array::from_fn(|track| input[track].as_slice()))
        .unwrap();
    let bytes = byte_grammar.bind(words).unwrap();
    assert_eq!(grammar.minimum_yields(BASE), Some([Some(0); N]));
    assert_eq!(grammar.minimum_yields(ROOT), Some([Some(0); N]));

    let mut coordinates = Vec::<Spans<N>>::new();
    for first in spans(words[0].len()) {
        if N == 1 {
            coordinates.push(std::array::from_fn(|_| first.clone()));
        } else {
            for second in spans(words[1].len()) {
                coordinates.push(std::array::from_fn(|track| {
                    if track == 0 {
                        first.clone()
                    } else {
                        second.clone()
                    }
                }));
            }
        }
    }
    let rank = |wanted: &Spans<N>, sym: usize| {
        NAMES.len() * coordinates.iter().position(|item| item == wanted).unwrap() + sym
    };
    let mut entries = Vec::new();
    let mut cells = Vec::new();
    for parent in &coordinates {
        for sym in [BASE, ROOT] {
            let cell = cells.len();
            assert_eq!(program.cell(cell), Some((sym, parent.clone())));
            assert_eq!(bytes.cell(cell), program.cell(cell));
            let mut rules = Vec::new();
            let mut emit = |site, children: &[Cell]| {
                let op = term(site, children.len(), parent);
                entries.push((
                    cell,
                    rules.len(),
                    site.to_owned(),
                    op.clone(),
                    children.to_vec(),
                ));
                rules.push(Rule::new(op, children));
            };
            if sym == BASE {
                if parent.iter().all(Range::is_empty) {
                    emit("empty", &[]);
                }
                if parent.iter().all(|span| span.len() == 1) {
                    for (byte, site) in [(0, "literal"), (1, "predicate")] {
                        if parent
                            .iter()
                            .zip(words)
                            .all(|(span, word)| word[span.start] == byte)
                        {
                            emit(site, &[]);
                        }
                    }
                    emit("any", &[]);
                }
            } else {
                emit("copy", &[rank(parent, BASE)]);
                for first in parent[0].start..=parent[0].end {
                    let mut join = |splits: [usize; N]| {
                        let left = std::array::from_fn(|t| {
                            if t == 0 {
                                parent[t].start..splits[t]
                            } else {
                                splits[t]..parent[t].end
                            }
                        });
                        let right = std::array::from_fn(|t| {
                            if t == 0 {
                                splits[t]..parent[t].end
                            } else {
                                parent[t].start..splits[t]
                            }
                        });
                        emit("join", &[rank(&left, BASE), rank(&right, BASE)]);
                    };
                    if N == 1 {
                        join([first; N]);
                    } else {
                        for second in parent[1].start..=parent[1].end {
                            join(std::array::from_fn(|t| if t == 0 { first } else { second }));
                        }
                    }
                }
            }
            cells.push(rules);
        }
    }
    assert_eq!(replay(&bytes), entries);
    assert_eq!(replay(&program), entries);
    assert_eq!(program.cell(cells.len()), None);
    let root = rank(&std::array::from_fn(|track| 0..words[track].len()), ROOT);
    let reference = Chart::new(cells, root).unwrap();
    let reconstructed = compiled::reference_chart(&program).unwrap();
    assert_eq!(reconstructed.root(), root);
    for (actual, wanted) in reconstructed.cells().iter().zip(reference.cells()) {
        assert!(actual
            .iter()
            .map(|r| (&r.operator, &r.children))
            .eq(wanted.iter().map(|r| (&r.operator, &r.children))));
    }
    let count = compiled::tabulate(&program, &Count).unwrap();
    let min = compiled::tabulate(&program, &Additive::default()).unwrap();
    for (actual, wanted) in count
        .cells()
        .iter()
        .zip(tabulate_cells(&reference, &Count).unwrap())
    {
        assert!(actual.iter().copied().eq(wanted));
    }
    for (actual, wanted) in min
        .cells()
        .iter()
        .zip(tabulate_cells(&reference, &Additive::default()).unwrap())
    {
        assert!(actual.iter().copied().eq(wanted));
    }
    assert_eq!(
        tabulate_cells(&reconstructed, &Enumerate),
        tabulate_cells(&reference, &Enumerate)
    );
    (reference.cells().len(), entries.len())
}

#[test]
fn typed_tracks_agree_at_every_rank() {
    let mut single = (0, 0);
    let mut double = (0, 0);
    for word in words(SINGLE_MAX) {
        let (cells, rules) = check([&word]);
        single.0 += cells;
        single.1 += rules;
    }
    let two = words(DOUBLE_MAX);
    for first in &two {
        for second in &two {
            let (cells, rules) = check([first, second]);
            double.0 += cells;
            double.1 += rules;
        }
    }
    println!("typed single: {} charts, {} cells, {} productions; typed double: {} charts, {} cells, {} productions",
        words(SINGLE_MAX).len(), single.0, single.1, two.len().pow(2), double.0, double.1);
}
