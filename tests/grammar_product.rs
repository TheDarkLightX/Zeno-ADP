use zeno_adp::algebras::{Additive, Count, Enumerate};
use zeno_adp::fast::{self, RuleSource};
use zeno_adp::grammars::{
    alignment, sequence_prefixes, Align, Prefix, PrefixProduct, ProductColumn,
};
use zeno_adp::{tabulate_cells, Chart, Error, Rule};

const MAX_LENGTH: usize = 3; // Complete small domain with repeated and tied paths.

fn words(max: usize) -> Vec<Vec<u8>> {
    (0..=max)
        .flat_map(|n| {
            (0..1usize << n).map(move |bits| (0..n).map(|i| ((bits >> i) & 1) as u8).collect())
        })
        .collect()
}

fn align_operator(column: &ProductColumn<Prefix<u8>, Prefix<u8>>) -> Align {
    use Prefix::{Start, Token};
    match *column {
        ProductColumn::Start(Start, Start) => Align::Start,
        ProductColumn::Both(Token(left), Token(right)) => Align::Diagonal { left, right },
        ProductColumn::Left(Token(left)) => Align::Left(left),
        ProductColumn::Right(Token(right)) => Align::Right(right),
        _ => panic!("invalid prefix column"),
    }
}

#[test]
fn sequence_product_agrees_with_two_track_alignment() {
    let words = words(MAX_LENGTH);
    let mut ranks = 0;
    for left in &words {
        for right in &words {
            let l = sequence_prefixes(left).unwrap();
            let r = sequence_prefixes(right).unwrap();
            let product = PrefixProduct::new(&l, &r).unwrap();
            let product_chart = fast::reference_chart(&product).unwrap();
            let mapped = Chart::new(
                product_chart
                    .cells()
                    .iter()
                    .map(|rules| {
                        rules
                            .iter()
                            .map(|rule| {
                                Rule::new(align_operator(&rule.operator), rule.children.clone())
                            })
                            .collect()
                    })
                    .collect(),
                product.root(),
            )
            .unwrap();
            let reference = alignment(left, right).unwrap();
            assert_eq!(mapped.root(), reference.root());
            for (a, b) in mapped.cells().iter().zip(reference.cells()) {
                assert!(a
                    .iter()
                    .map(|r| (&r.operator, &r.children))
                    .eq(b.iter().map(|r| (&r.operator, &r.children))));
            }
            let count = fast::tabulate(&product, &Count).unwrap();
            assert_eq!(
                count.cells().iter().flatten().copied().collect::<Vec<_>>(),
                tabulate_cells(&reference, &Count)
                    .unwrap()
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                tabulate_cells(&mapped, &Additive::default()).unwrap(),
                tabulate_cells(&reference, &Additive::default()).unwrap()
            );
            assert_eq!(
                tabulate_cells(&mapped, &Enumerate).unwrap(),
                tabulate_cells(&reference, &Enumerate).unwrap()
            );
            ranks += count.cells().len();
        }
    }
    println!("alignment product ranks={ranks}, disagreements=0");
    assert_eq!(ranks, 2401);
}

#[test]
fn product_retains_duplicate_leaves_gaps_and_nonfinal_roots() {
    use Prefix::{Start, Token};
    let left = Chart::new(
        vec![
            vec![Rule::new(Start, []), Rule::new(Start, [])],
            vec![Rule::new(Token('x'), [0])],
            vec![],
        ],
        1,
    )
    .unwrap();
    let right = Chart::new(
        vec![
            vec![Rule::new(Start, [])],
            vec![],
            vec![Rule::new(Token('y'), [0]), Rule::new(Token('z'), [1])],
        ],
        2,
    )
    .unwrap();
    let product = PrefixProduct::new(&left, &right).unwrap();
    let expected = [
        Some(2),
        None,
        Some(2),
        Some(2),
        None,
        Some(6),
        None,
        None,
        None,
    ];
    let chart = fast::reference_chart(&product).unwrap();
    use ProductColumn::{Both, Left, Right};
    let start = ProductColumn::Start(Prefix::Start, Prefix::Start);
    let x = Token('x');
    let y = Token('y');
    let z = Token('z');
    let emissions = [
        vec![(start.clone(), vec![]), (start, vec![])],
        vec![],
        vec![(Right(y.clone()), vec![0]), (Right(z.clone()), vec![1])],
        vec![(Left(x.clone()), vec![0])],
        vec![(Left(x.clone()), vec![1])],
        vec![
            (Both(x.clone(), y.clone()), vec![0]),
            (Both(x.clone(), z.clone()), vec![1]),
            (Left(x), vec![2]),
            (Right(y.clone()), vec![3]),
            (Right(z.clone()), vec![4]),
        ],
        vec![],
        vec![],
        vec![(Right(y), vec![6]), (Right(z), vec![7])],
    ];
    let grammar = Chart::new(
        emissions
            .map(|rules| {
                rules
                    .into_iter()
                    .map(|(op, children)| Rule::new(op, children))
                    .collect()
            })
            .into(),
        5,
    )
    .unwrap();
    assert_eq!(chart, grammar);
    assert_eq!(
        tabulate_cells(&chart, &Enumerate).unwrap(),
        tabulate_cells(&grammar, &Enumerate).unwrap()
    );
    let reference = tabulate_cells(&chart, &Count).unwrap();
    let streamed = fast::tabulate(&product, &Count).unwrap();
    assert_eq!(streamed.root(), 5);
    assert_eq!(streamed.cells(), &expected);
    assert_eq!(
        reference
            .iter()
            .map(|bag| bag.first().copied())
            .collect::<Vec<_>>(),
        expected
    );
    assert!(zeno_adp::audit(&chart, &Count)
        .unwrap()
        .first_failure
        .is_none());
    assert_eq!(
        product.rules_at(expected.len(), |_, _| unreachable!()),
        Err(Error::CellOutOfRange(expected.len()))
    );

    let binary = zeno_adp::grammars::nussinov(b"AU", 0).unwrap();
    assert!(
        matches!(PrefixProduct::new(&left, &binary), Err(Error::UnsupportedGrammar {name, ..})
        if name == "right product operand")
    );
}
