use zeno_adp::algebras::Count;
use zeno_adp::compiled;
use zeno_adp::fast::RuleSource;
use zeno_adp::{compiled_grammar, tabulate_cells, Error, Operator};

#[derive(Clone, Copy)]
struct Op(usize);

impl Operator for Op {
    fn arity(&self) -> usize {
        self.0
    }
}

compiled_grammar! {
    fn dependency_chain(input: u8) -> Op {
        prefix |tokens, start, end|;
        empty Base => Ok(Some(Op(0)));
        extend Step(prior) => Ok((prior + 1 == end && tokens[prior] == 1).then_some(Op(1)));
    }
}

#[test]
fn joint_requests_retain_exactly_the_live_or_requested_summaries() {
    // Through length four, absences can precede or follow a selected rank
    // and a live predecessor can contribute to two selected observations.
    const MAX_INPUT: usize = 4;
    let mut charts = 0;
    let mut observations = 0;
    for length in 0..=MAX_INPUT {
        for bits in 0..1 << length {
            let input: Vec<_> = (0..length).map(|axis| ((bits >> axis) & 1) as u8).collect();
            let bound = dependency_chain(&input).unwrap();
            let chart = compiled::reference_chart(&bound).unwrap();
            let expected = tabulate_cells(&chart, &Count).unwrap();
            for requested in 0..1 << bound.cell_count() {
                let mut ranks: Vec<_> = (0..bound.cell_count())
                    .rev()
                    .filter(|&rank| requested & (1 << rank) != 0)
                    .collect();
                // Duplicate requests share storage and return one entry per rank.
                if let Some(&first) = ranks.first() {
                    ranks.push(first);
                }
                let mut seen = Vec::new();
                let selected =
                    compiled::tabulate_selected(&bound, &Count, &ranks, |rank, count| {
                        seen.push((rank, count.copied()));
                    })
                    .unwrap();
                assert_eq!(
                    seen,
                    expected
                        .iter()
                        .enumerate()
                        .map(|(rank, bag)| (rank, bag.first().copied()))
                        .collect::<Vec<_>>()
                );
                assert_eq!(
                    selected.answers,
                    ranks
                        .iter()
                        .map(|&rank| (rank, expected[rank].first().copied()))
                        .collect()
                );
                let peak = (0..bound.cell_count())
                    .map(|end| {
                        (0..=end)
                            .filter(|&rank| {
                                !expected[rank].is_empty()
                                    && (ranks.contains(&rank)
                                        || chart.cells()[end + 1..]
                                            .iter()
                                            .flatten()
                                            .any(|rule| rule.children.contains(&rank)))
                            })
                            .count()
                    })
                    .max()
                    .unwrap();
                assert_eq!(selected.peak_retained, peak);
                charts += 1;
                observations += seen.len();
            }
        }
    }
    assert_eq!(charts, 682);
    let bound = dependency_chain(&[1, 1, 1]).unwrap();
    let peak = |ranks| {
        compiled::tabulate_selected(&bound, &Count, ranks, |_, _| {})
            .unwrap()
            .peak_retained
    };
    assert_eq!(
        (peak(&[0]), peak(&[1]), peak(&[3]), peak(&[0, 1, 3])),
        (2, 2, 1, 3)
    );
    assert_eq!(
        compiled::tabulate_selected(&bound, &Count, &[4], |_, _| {}),
        Err(Error::CellOutOfRange(4))
    );
    println!("joint retention: {charts} chart/selection pairs, {observations} all-cell observations; peaks 2/2/1 alone, 3 together");
}

impl zeno_adp::algebras::ScoredOperator for Op {
    fn cost(&self) -> zeno_adp::algebras::Cost {
        zeno_adp::algebras::Cost::Finite(self.0 as i64)
    }
}

#[test]
fn joint_projections_match_both_reference_algebras_and_peak_census() {
    use zeno_adp::algebras::{Additive, Minimum};

    // At length two a held output can overlap more than one future read.
    const MAX_INPUT: usize = 2;
    let (mut requests, mut observations) = (0, 0);
    for length in 0..=MAX_INPUT {
        for bits in 0..1 << length {
            let input: Vec<_> = (0..length).map(|axis| ((bits >> axis) & 1) as u8).collect();
            let source = dependency_chain(&input).unwrap();
            let chart = compiled::reference_chart(&source).unwrap();
            let count = tabulate_cells(&chart, &Count).unwrap();
            let minimum = tabulate_cells(&chart, &Minimum).unwrap();
            let ranks = |mask| {
                (0..source.cell_count())
                    .filter(|rank| mask & (1usize << rank) != 0)
                    .collect::<Vec<_>>()
            };
            for left_mask in 0..1 << source.cell_count() {
                for right_mask in 0..1 << source.cell_count() {
                    let left = ranks(left_mask);
                    let mut right = ranks(right_mask);
                    if let Some(&rank) = right.first() {
                        right.push(rank);
                    }
                    let mut seen = 0;
                    let selected = compiled::tabulate_joint(
                        &source,
                        (&Count, &left),
                        (&Additive::default(), &right),
                        |rank, actual_count, actual_minimum| {
                            assert_eq!(rank, seen);
                            assert!(actual_count.into_iter().eq(&count[rank]));
                            assert!(actual_minimum.into_iter().eq(&minimum[rank]));
                            seen += 1;
                        },
                    )
                    .unwrap();
                    assert_eq!(seen, chart.cells().len());
                    assert_eq!(
                        selected.left.answers,
                        left.iter()
                            .map(|&rank| (rank, count[rank].first().copied()))
                            .collect()
                    );
                    assert_eq!(
                        selected.right.answers,
                        right
                            .iter()
                            .map(|&rank| (rank, minimum[rank].first().copied()))
                            .collect()
                    );
                    let (mut left_peak, mut right_peak, mut peak) = (0, 0, 0);
                    for end in 0..chart.cells().len() {
                        let live = |rank| {
                            chart.cells()[end + 1..]
                                .iter()
                                .flatten()
                                .any(|rule| rule.children.contains(&rank))
                        };
                        let left_count = (0..=end)
                            .filter(|&rank| {
                                !count[rank].is_empty() && (left.contains(&rank) || live(rank))
                            })
                            .count();
                        let right_count = (0..=end)
                            .filter(|&rank| {
                                !minimum[rank].is_empty() && (right.contains(&rank) || live(rank))
                            })
                            .count();
                        left_peak = left_peak.max(left_count);
                        right_peak = right_peak.max(right_count);
                        peak = peak.max(left_count + right_count);
                    }
                    assert_eq!(
                        (
                            selected.left.peak_retained,
                            selected.right.peak_retained,
                            selected.peak_retained
                        ),
                        (left_peak, right_peak, peak)
                    );
                    requests += 1;
                    observations += seen;
                }
            }
        }
    }
    let source = dependency_chain(&[1, 1]).unwrap();
    let projected = compiled::tabulate_joint(
        &source,
        (&Count, &[0]),
        (&Additive::default(), &[2]),
        |_, _, _| {},
    )
    .unwrap();
    let full = compiled::tabulate_joint(
        &source,
        (&Count, &[0, 2]),
        (&Additive::default(), &[0, 2]),
        |_, _, _| {},
    )
    .unwrap();
    assert_eq!((projected.peak_retained, full.peak_retained), (3, 4));
    assert_eq!(
        compiled::tabulate_joint(
            &source,
            (&Count, &[0]),
            (&Additive::default(), &[3]),
            |_, _, _| {}
        ),
        Err(Error::CellOutOfRange(3))
    );
    assert_eq!((requests, observations), (292, 836));
    println!("joint folds: {requests} chart/request pairs, {observations} ranks per algebra, disjoint/full peak 3/4");
}

#[derive(Clone, Copy)]
struct Event(u8, usize);

impl Operator for Event {
    fn arity(&self) -> usize {
        self.1
    }
}

compiled_grammar! {
    fn event_chain(input: u8) -> Event {
        prefix |tokens, start, end|;
        empty Begin => Ok(Some(Event(0, 0)));
        extend First(prior) => {
            if tokens[end - 1] == u8::MAX {
                return Err(Error::InvalidSymbol(u8::MAX));
            }
            Ok((prior + 1 == end).then_some(Event(tokens[end - 1], 1)))
        };
        extend Second(prior) => Ok((prior + 1 == end).then_some(Event(0, 1)));
    }
}

#[derive(Debug, PartialEq, Eq)]
struct EventValue(u8);

struct Events {
    apply_error: Option<(u8, Error)>,
    merge_error: Option<Error>,
}

impl zeno_adp::fast::Fold<Event> for Events {
    type Value = EventValue;

    fn apply<'a>(
        &self,
        operator: &'a Event,
        _: impl Iterator<Item = &'a EventValue> + Clone,
    ) -> Result<EventValue, Error> {
        if let Some((_, error)) = self
            .apply_error
            .as_ref()
            .filter(|(tag, _)| *tag == operator.0)
        {
            return Err(error.clone());
        }
        Ok(EventValue(operator.0))
    }

    fn merge(&self, selected: &mut Option<EventValue>, next: EventValue) -> Result<(), Error> {
        if selected.is_some() {
            if let Some(error) = &self.merge_error {
                return Err(error.clone());
            }
        }
        selected.get_or_insert(next);
        Ok(())
    }
}

#[test]
fn joint_folds_keep_order_nonclone_values_and_source_error_priority() {
    let first = Events {
        apply_error: None,
        merge_error: None,
    };
    let fail_left = Events {
        apply_error: Some((2, Error::InvalidDimensions)),
        merge_error: Some(Error::AllocationFailed),
    };
    let fail_right = Events {
        apply_error: Some((1, Error::Overflow)),
        merge_error: None,
    };
    let source = event_chain(&[1, 2]).unwrap();
    let mut seen = Vec::new();
    let selected =
        compiled::tabulate_joint(&source, (&first, &[1]), (&Count, &[2]), |_, tag, count| {
            seen.push((tag.unwrap().0, *count.unwrap()))
        })
        .unwrap();
    assert_eq!(seen, [(0, 1), (1, 2), (2, 4)]);
    assert_eq!(selected.left.answers[&1], Some(EventValue(1)));
    assert_eq!(selected.right.answers[&2], Some(4));
    let run =
        |left, right| compiled::tabulate_joint(&source, (left, &[]), (right, &[]), |_, _, _| {});
    assert_eq!(run(&fail_left, &fail_right), Err(Error::AllocationFailed));
    assert_eq!(run(&first, &fail_right), Err(Error::Overflow));

    let later_failure = Events {
        apply_error: Some((2, Error::InvalidDimensions)),
        merge_error: None,
    };
    assert_eq!(run(&later_failure, &fail_right), Err(Error::Overflow));
    let bad_source = event_chain(&[1, 2, u8::MAX]).unwrap();
    assert_eq!(
        compiled::tabulate_joint(
            &bad_source,
            (&fail_left, &[]),
            (&fail_right, &[]),
            |_, _, _| {}
        ),
        Err(Error::InvalidSymbol(u8::MAX))
    );
}
