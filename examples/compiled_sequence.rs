use zeno_adp::algebras::{Cost, Count, ScoredOperator};
use zeno_adp::compiled::{self, Atom, Grammar, Production};
use zeno_adp::{Error, Operator};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Tile {
    End,
    Single,
    Pair,
}

impl Operator for Tile {
    fn arity(&self) -> usize {
        usize::from(*self != Self::End)
    }
}

impl ScoredOperator for Tile {
    fn cost(&self) -> Cost {
        Cost::Finite(i64::from(*self != Self::End))
    }
}

const ROW: usize = 0;

fn main() -> Result<(), Error> {
    let rule = |name: &str, tile: Tile, track: Vec<Atom>| Production {
        name: name.into(),
        parent: ROW,
        children: vec![ROW; tile.arity()],
        tracks: [track],
        operator: Box::new(move |_| tile),
    };
    let grammar = Grammar::new(
        &["Row"],
        ROW,
        vec![
            rule("end", Tile::End, vec![]),
            rule("single", Tile::Single, vec![Atom::Any, Atom::Child(0)]),
            rule(
                "pair",
                Tile::Pair,
                vec![Atom::Byte(b'a'), Atom::Byte(b'a'), Atom::Child(0)],
            ),
        ],
    )?;
    let program = grammar.bind([b"aaa"])?;
    let count = compiled::tabulate(&program, &Count)?;
    let best = compiled::best(&program)?;

    assert_eq!(count.answer(), Some(&3));
    assert_eq!(best.scores().answer(), Some(&Cost::Finite(2)));
    let ties = best.recover().co_minimal(Default::default())?;
    assert_eq!(ties.len(), 2);
    println!(
        "{} tilings; {} use two tiles",
        count.answer().unwrap(),
        ties.len()
    );
    Ok(())
}
