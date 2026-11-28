use zeno_adp::windows::{ClosestTo, Step, Stepped, UniqueMinimum};
use zeno_adp::{Chart, Error, Rule};

fn rule(step: Step, children: &[usize]) -> Rule<Stepped> {
    Rule::new(
        Stepped {
            step,
            arity: children.len(),
        },
        children.to_vec(),
    )
}

#[test]
fn checked_windows_refuse_hidden_literal_overflow() {
    let chart = Chart::new(
        vec![
            vec![rule(Step::add(0), &[]), rule(Step::add(u64::MAX), &[])],
            vec![rule(Step::add(1), &[0])],
        ],
        1,
    )
    .unwrap();
    assert!(matches!(
        UniqueMinimum::new(0).tabulate_cells(&chart),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        ClosestTo::new(0).tabulate_cells(&chart),
        Err(Error::Overflow)
    ));
}

#[test]
fn an_empty_sibling_makes_overflow_unattainable() {
    let chart = Chart::new(
        vec![
            vec![rule(Step::add(u64::MAX), &[])],
            vec![],
            vec![rule(Step::add(1), &[0, 1])],
        ],
        2,
    )
    .unwrap();
    let expected = vec![vec![u64::MAX], vec![], vec![]];
    assert_eq!(
        UniqueMinimum::new(0).tabulate_cells(&chart).unwrap(),
        expected
    );
    assert_eq!(ClosestTo::new(0).tabulate_cells(&chart).unwrap(), expected);
}

#[test]
fn a_productive_floor_must_fit_the_unique_window() {
    let chart = Chart::new(
        vec![
            vec![rule(Step::add(0), &[]), rule(Step::add(2), &[])],
            vec![rule(Step::floor(2), &[0])],
        ],
        1,
    )
    .unwrap();
    assert!(matches!(
        UniqueMinimum::new(1).tabulate_cells(&chart),
        Err(Error::FloorOutsideWindow {
            floor: 2,
            max_floor: 1
        })
    ));
    assert_eq!(
        UniqueMinimum::for_chart(&chart)
            .tabulate_cells(&chart)
            .unwrap(),
        [vec![0, 2], vec![2, 2]]
    );
    assert_eq!(
        ClosestTo::new(1).tabulate_cells(&chart).unwrap(),
        [vec![0], vec![2]]
    );
}

#[test]
fn a_disconnected_productive_cell_still_has_checked_arithmetic() {
    let chart = Chart::new(
        vec![
            vec![rule(Step::add(0), &[])],
            vec![rule(Step::add(u64::MAX), &[])],
            vec![rule(Step::add(1), &[1])],
        ],
        0,
    )
    .unwrap();
    assert!(matches!(
        UniqueMinimum::new(0).tabulate_cells(&chart),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        ClosestTo::new(0).tabulate_cells(&chart),
        Err(Error::Overflow)
    ));
}
