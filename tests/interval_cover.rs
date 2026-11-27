use num_bigint::BigUint;
use zeno_adp::fast::interval_cover::{
    solve, solve_chart, solve_range, CoverError, Interval, Optimum, Pin,
};

fn brute(n: usize, rows: &[Interval], pins: &[Pin]) -> Option<Optimum> {
    let mut best: Option<Optimum> = None;
    for bits in 0..(1_u64 << rows.len()) {
        let selected = |i| ((bits >> i) & 1_u64) == 1;
        if pins.iter().enumerate().any(|(i, pin)| {
            (*pin == Pin::Include && !selected(i)) || (*pin == Pin::Exclude && selected(i))
        }) {
            continue;
        }
        if !(0..n).all(|x| {
            rows.iter()
                .enumerate()
                .any(|(i, r)| selected(i) && r.start <= x && x < r.end)
        }) {
            continue;
        }
        let score = rows
            .iter()
            .enumerate()
            .filter(|(i, _)| selected(*i))
            .map(|(_, r)| u128::from(r.cost))
            .sum();
        match &mut best {
            Some(old) if old.cost == score => old.count += 1_u8,
            Some(old) if old.cost < score => {}
            _ => {
                best = Some(Optimum {
                    cost: score,
                    count: BigUint::from(1_u8),
                })
            }
        }
    }
    best
}

#[test]
fn random_pinned_and_unpinned_three_way() {
    let mut seed = 93_514_931_u64;
    let mut rand = |limit| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        (seed as usize) % limit
    };
    for i in 0..2400 {
        let n = 1 + rand(9);
        let rows: Vec<_> = (0..rand(12))
            .map(|_| {
                let start = rand(n);
                Interval {
                    start,
                    end: start + 1 + rand(n - start),
                    cost: rand(5) as u64,
                }
            })
            .collect();
        let pins: Vec<_> = if i % 2 == 0 {
            vec![]
        } else {
            rows.iter()
                .map(|_| match rand(6) {
                    0 => Pin::Include,
                    1 => Pin::Exclude,
                    _ => Pin::Either,
                })
                .collect()
        };
        let b = brute(n, &rows, &pins);
        assert_eq!(solve(n, &rows, &pins).unwrap(), b, "fast menu {i}");
        assert_eq!(solve_chart(n, &rows, &pins).unwrap(), b, "chart menu {i}");
        assert_eq!(solve_range(n, &rows, &pins).unwrap(), b, "range menu {i}");
    }
}

#[test]
fn extreme_cost_empty_and_invalid() {
    for f in [solve, solve_chart] {
        let r = |start, end, cost| Interval { start, end, cost };
        assert_eq!(
            f(0, &[], &[]).unwrap(),
            Some(Optimum {
                cost: 0,
                count: 1_u8.into()
            })
        );
        assert_eq!(f(1, &[], &[]).unwrap(), None);
        assert_eq!(
            f(2, &[r(0, 1, u64::MAX), r(1, 2, u64::MAX)], &[]).unwrap(),
            Some(Optimum {
                cost: 2 * u128::from(u64::MAX),
                count: 1_u8.into()
            })
        );
        assert!(matches!(
            f(2, &[r(1, 1, 0)], &[Pin::Exclude]),
            Err(CoverError::InvalidInterval { row: 0, .. })
        ));
        assert!(matches!(
            f(2, &[r(0, 2, 0)], &[Pin::Either, Pin::Either]),
            Err(CoverError::PinCount {
                expected: 1,
                actual: 2
            })
        ));
        assert_eq!(
            f(2, &[r(0, 2, 0), r(0, 1, 0), r(1, 2, 0)], &[]).unwrap(),
            Some(Optimum {
                cost: 0,
                count: 5_u8.into()
            })
        );
    }
}

#[test]
fn exact_50_000_points() {
    let n = 50_000;
    let rows: Vec<_> = (0..n)
        .flat_map(|p| {
            [Interval {
                start: p,
                end: p + 1,
                cost: 0,
            }; 3]
        })
        .collect();
    assert_eq!(
        solve(n, &rows, &[]).unwrap(),
        Some(Optimum {
            cost: 0,
            count: BigUint::from(7_u8).pow(n as u32),
        })
    );
}

#[test]
fn hybrid_promotes_with_nontrivial_counts_and_pins() {
    let points = 300;
    let mut rows: Vec<_> = (1..=points)
        .flat_map(|end| {
            [Interval {
                start: 0,
                end,
                cost: (end % 3) as u64,
            }; 2]
        })
        .collect();
    rows.push(Interval {
        start: 1,
        end: points - 1,
        cost: 7,
    });
    let mut pins = vec![Pin::Either; rows.len()];
    pins[0] = Pin::Exclude;
    *pins.last_mut().unwrap() = Pin::Include;
    let expected = solve_chart(points, &rows, &pins).unwrap();
    assert!(expected.is_some());
    assert_eq!(solve(points, &rows, &pins).unwrap(), expected);
    assert_eq!(solve_range(points, &rows, &pins).unwrap(), expected);
}
