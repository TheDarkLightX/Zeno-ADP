use zeno_adp::algebras::Count;
use zeno_adp::compiled::{self, Atom, Grammar, Production, Program};
use zeno_adp::{compiled_grammar, tabulate_cells, Chart, Error, Operator, Rule};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Op(u8, usize);

impl Operator for Op {
    fn arity(&self) -> usize {
        self.1
    }
}

compiled_grammar! {
    fn triple(input: u8) -> Op {
        prefix_tracks 3 |tracks, ends|;
        empty Start => Ok(Some(Op(0, 0)));
        step Left [true, false, false] => Ok((tracks[0][ends[0] - 1] == 0).then_some(Op(1, 1)));
        step Right [false, false, true] => Ok(Some(Op(2, 1)));
        step Joint [true, true, true] => Ok(Some(Op(3, 1)));
    }
    with fn triple_count: Count = Count;
}

compiled_grammar! {
    fn quadruple(input: u8) -> Op {
        prefix_tracks 4 |tracks, ends|;
        empty Start => Ok(Some(Op(0, 0)));
        step Left [true, false, false, false] => Ok((tracks[0][ends[0] - 1] == 0).then_some(Op(1, 1)));
        step Right [false, false, false, true] => Ok(Some(Op(2, 1)));
        step Joint [true, true, true, true] => Ok(Some(Op(3, 1)));
    }
    with fn quadruple_count: Count = Count;
}

fn explicit<const N: usize>(
    inputs: [&[u8]; N],
    point: [usize; N],
    rank: impl Fn([usize; N]) -> usize,
) -> Vec<Rule<Op>> {
    if point == [0; N] {
        return vec![Rule::new(Op(0, 0), [])];
    }
    let mut rules = Vec::new();
    if point[0] != 0 && inputs[0][point[0] - 1] == 0 {
        let mut prior = point;
        prior[0] -= 1;
        rules.push(Rule::new(Op(1, 1), [rank(prior)]));
    }
    if point[N - 1] != 0 {
        let mut prior = point;
        prior[N - 1] -= 1;
        rules.push(Rule::new(Op(2, 1), [rank(prior)]));
    }
    if !point.contains(&0) {
        rules.push(Rule::new(Op(3, 1), [rank(point.map(|end| end - 1))]));
    }
    rules
}

fn general<const N: usize>() -> Grammar<Op, N> {
    let mut productions = vec![Production {
        name: "Start".into(),
        parent: 0,
        children: vec![],
        tracks: std::array::from_fn(|_| vec![]),
        operator: Box::new(|_| Op(0, 0)),
    }];
    for (id, name) in [(1, "Left"), (2, "Right"), (3, "Joint")] {
        productions.push(Production {
            name: name.into(),
            parent: 0,
            children: vec![0],
            tracks: std::array::from_fn(|axis| {
                let mut atoms = vec![Atom::Child(0)];
                if id == 3 || id == 2 && axis == N - 1 {
                    atoms.push(Atom::Any);
                } else if id == 1 && axis == 0 {
                    atoms.push(Atom::Byte(0));
                }
                atoms
            }),
            operator: Box::new(move |_| Op(id, 1)),
        });
    }
    Grammar::new(&["state"], 0, productions).unwrap()
}

fn grid<const N: usize>(
    max_len: usize,
    check: impl Fn([&[u8]; N], &Chart<Op>),
) -> (usize, usize, usize) {
    let words: Vec<_> = (0..=max_len)
        .flat_map(|width| {
            (0..1 << width).map(move |bits| {
                (0..width)
                    .map(|bit| ((bits >> bit) & 1) as u8)
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    let grammar = general::<N>();
    let mut prefix_cells = 0;
    let mut full_cells = 0;
    for word_index in 0..words.len().pow(N as u32) {
        let mut ordinal = word_index;
        let inputs = std::array::from_fn(|_| {
            let word = &words[ordinal % words.len()];
            ordinal /= words.len();
            word.as_slice()
        });
        let widths = inputs.map(|word| word.len() + 1);
        let count = widths.iter().product::<usize>();
        let rank = |ends: [usize; N]| {
            ends.into_iter()
                .zip(widths)
                .fold(0, |rank, (end, width)| rank * width + end)
        };
        let mut points = Vec::with_capacity(count);
        for mut cell in 0..count {
            let mut ends = [0; N];
            for axis in (0..N).rev() {
                ends[axis] = cell % widths[axis];
                cell /= widths[axis];
            }
            points.push(ends);
        }
        let chart = Chart::new(
            points
                .iter()
                .map(|&ends| explicit(inputs, ends, rank))
                .collect(),
            count - 1,
        )
        .unwrap();
        check(inputs, &chart);

        let all_spans = grammar.bind(inputs).unwrap();
        let full_chart = compiled::reference_chart(&all_spans).unwrap();
        let full_values = tabulate_cells(&full_chart, &Count).unwrap();
        let prefix_values = tabulate_cells(&chart, &Count).unwrap();
        let mut observed = 0;
        for (cell, answers) in full_values.iter().enumerate() {
            let (_, spans) = all_spans.cell(cell).unwrap();
            if spans.iter().all(|span| span.start == 0) {
                let point = spans.map(|span| span.end);
                assert_eq!(*answers, prefix_values[rank(point)]);
                observed += 1;
            }
        }
        assert_eq!(observed, count);
        prefix_cells += count;
        full_cells += full_values.len();
    }
    (words.len().pow(N as u32), prefix_cells, full_cells)
}

fn check(source: &impl Program<Op = Op>, chart: &Chart<Op>, paired: zeno_adp::fast::Table<u128>) {
    let expected = tabulate_cells(chart, &Count).unwrap();
    assert_eq!(paired, compiled::tabulate(source, &Count).unwrap());
    assert_eq!(paired.root(), chart.root());
    assert!(paired
        .cells()
        .iter()
        .zip(&expected)
        .all(|(one, bag)| one.iter().eq(bag)));
    assert_eq!(paired.cells().len(), expected.len());
    let mut emitted = vec![Vec::new(); chart.cells().len()];
    compiled::replay(source, |cell, ordinal, site, op, children| {
        assert_eq!(site, ["Start", "Left", "Right", "Joint"][op.0 as usize]);
        let reference = &chart.cells()[cell][ordinal];
        assert_eq!(op, reference.operator);
        assert_eq!(children, reference.children);
        emitted[cell].push(op);
        Ok(())
    })
    .unwrap();
    for (cell, ops) in emitted.into_iter().enumerate() {
        assert_eq!(ops.len(), chart.cells()[cell].len());
        let mut replay = Vec::new();
        source
            .rules_at(cell, |op, _| {
                replay.push(op);
                Ok(())
            })
            .unwrap();
        assert_eq!(replay, ops);
    }
    assert_eq!(
        source.rules_at(source.cell_count(), |_, _| panic!("invalid rank emitted")),
        Err(Error::CellOutOfRange(source.cell_count()))
    );
}

#[test]
fn three_and_four_tracks_match_separate_prefix_and_contiguous_charts() {
    // Width two exercises repeated steps, while four dimensions already
    // exercise the extra radix products with one token per track.
    const THREE_TRACK_MAX_LEN: usize = 2;
    const FOUR_TRACK_MAX_LEN: usize = 1;
    let triple_stats = grid(THREE_TRACK_MAX_LEN, |inputs, chart| {
        check(
            &triple(inputs).unwrap(),
            chart,
            triple_count(inputs).unwrap(),
        )
    });
    let quadruple_stats = grid(FOUR_TRACK_MAX_LEN, |inputs, chart| {
        check(
            &quadruple(inputs).unwrap(),
            chart,
            quadruple_count(inputs).unwrap(),
        )
    });
    assert_eq!(triple_stats, (343, 4_913, 29_791));
    assert_eq!(quadruple_stats, (81, 625, 2_401));
    println!("three tracks {triple_stats:?}; four tracks {quadruple_stats:?} (charts, prefix ranks, full interval ranks)");
}

#[test]
fn generated_track_refusals_are_named_and_preflighted() {
    compiled_grammar! {
        fn stalled(input: u8) -> Op {
            prefix_tracks 3 |tracks, ends|;
            step Stalled [false, false, false] => Ok(Some(Op(0, 1)));
        }
    }
    assert!(
        matches!(stalled([&[]; 3]), Err(Error::UnsupportedGrammar { name, .. }) if name == "Stalled")
    );

    compiled_grammar! {
        fn no_axes(input: u8) -> Op {
            prefix_tracks 0 |tracks, ends|;
            empty Empty => Ok(Some(Op(0, 0)));
        }
    }
    assert!(
        matches!(no_axes([]), Err(Error::UnsupportedGrammar { name, .. }) if name == "no_axes")
    );

    compiled_grammar! {
        fn bad_arity(input: u8) -> Op {
            prefix_tracks 3 |tracks, ends|;
            empty Empty => Ok(Some(Op(0, 1)));
        }
    }
    assert_eq!(
        compiled::tabulate(&bad_arity([&[]; 3]).unwrap(), &Count),
        Err(Error::Arity {
            cell: 0,
            expected: 1,
            actual: 0,
        })
    );

    compiled_grammar! {
        fn overflow(input: ()) -> Op {
            prefix_tracks 3 |tracks, ends|;
            empty Empty => Ok(Some(Op(0, 0)));
        }
    }
    let huge = vec![(); usize::MAX / 2];
    let short = [(); 1];
    for inputs in [
        [huge.as_slice(), &short, &[]],
        [&[], &short, huge.as_slice()],
    ] {
        assert!(matches!(overflow(inputs), Err(Error::Overflow)));
    }
}
