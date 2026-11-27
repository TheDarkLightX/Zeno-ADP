use num_bigint::BigUint;
use std::{collections::BTreeMap, hint::black_box, time::Instant};
use zeno_adp::fast::{
    interval_choice::analyze,
    interval_cover::{solve, solve_range, Interval, Optimum, Pin},
};

fn fixture(n: usize, mixed: bool) -> Vec<Interval> {
    (0..n)
        .flat_map(|start| {
            let end = start + 1;
            if mixed {
                [
                    Interval {
                        start,
                        end,
                        cost: 2,
                    },
                    Interval {
                        start,
                        end: n.min(end + n / 8),
                        cost: 3,
                    },
                    Interval {
                        start,
                        end: n.min(end + n / 4),
                        cost: (start % 3) as u64,
                    },
                ]
            } else {
                [Interval {
                    start,
                    end,
                    cost: 0,
                }; 3]
            }
        })
        .collect()
}

// Same recurrence and score, but store only reachable boundaries and
// directly scan the affected portion. No generic chart construction.
fn rolled(n: usize, rows: &[Interval]) -> Option<Optimum> {
    let mut groups = vec![Vec::new(); n];
    for r in rows {
        groups[r.start].push(r);
    }
    let mut active = BTreeMap::from([(
        0,
        Optimum {
            cost: 0,
            count: BigUint::from(1u8),
        },
    )]);
    for (i, g) in groups.into_iter().enumerate() {
        for r in g {
            let mut pulled: Option<Optimum> = None;
            for state in active.range(..r.end).map(|(_, v)| v) {
                let c = state.cost + u128::from(r.cost);
                match pulled.as_mut() {
                    Some(p) if p.cost == c => p.count += &state.count,
                    Some(p) if p.cost < c => {}
                    _ => {
                        pulled = Some(Optimum {
                            cost: c,
                            count: state.count.clone(),
                        })
                    }
                }
            }
            if r.cost == 0 {
                for (_, v) in active.range_mut(r.end..) {
                    v.count <<= 1;
                }
            }
            if let Some(p) = pulled {
                active
                    .entry(r.end)
                    .and_modify(|q| {
                        if q.cost == p.cost {
                            q.count += &p.count;
                        } else if q.cost > p.cost {
                            *q = p.clone();
                        }
                    })
                    .or_insert(p);
            }
        }
        active.remove(&i);
    }
    active.remove(&n)
}

fn elapsed<R>(mut f: impl FnMut() -> R) -> f64 {
    let start = Instant::now();
    black_box(f());
    start.elapsed().as_secs_f64() * 1000.0
}
fn paired<R, S>(mut f: impl FnMut() -> R, mut g: impl FnMut() -> S, reps: usize) -> (f64, f64) {
    let (mut a, mut b) = (vec![], vec![]);
    for run in 0..reps {
        if run % 2 == 0 {
            a.push(elapsed(&mut f));
            b.push(elapsed(&mut g));
        } else {
            b.push(elapsed(&mut g));
            a.push(elapsed(&mut f));
        }
    }
    a.sort_by(f64::total_cmp);
    b.sort_by(f64::total_cmp);
    (a[reps / 2], b[reps / 2])
}

fn main() {
    println!("task,shape,points,rows,repetitions,baseline_ms,new_ms,ratio");
    for (mixed, name) in [(false, "independent-free"), (true, "overlap-mixed")] {
        for n in [512, 2048, 8192] {
            let r = fixture(n, mixed);
            assert_eq!(rolled(n, &r), solve(n, &r, &[]).unwrap());
            assert_eq!(solve_range(n, &r, &[]).unwrap(), solve(n, &r, &[]).unwrap());
            let (a, b) = paired(|| rolled(n, &r), || solve(n, &r, &[]).unwrap(), 9);
            println!("rolled,{name},{n},{},9,{a:.6},{b:.6},{:.2}", r.len(), a / b);
        }
        let n = 128;
        let r = fixture(n, mixed);
        let independent = || {
            let mut p = vec![Pin::Either; r.len()];
            let mut out = vec![];
            for i in 0..r.len() {
                p[i] = Pin::Exclude;
                let off = solve(n, &r, &p).unwrap();
                p[i] = Pin::Include;
                let on = solve(n, &r, &p).unwrap();
                p[i] = Pin::Either;
                out.push((off, on));
            }
            out
        };
        let tape = || analyze(n, &r, &[]).unwrap().unwrap();
        assert!(tape()
            .rows
            .iter()
            .zip(independent())
            .all(|(a, b)| (a.exclude.clone(), a.include.clone()) == b));
        let (a, b) = paired(independent, tape, 7);
        println!(
            "all-single-pins,{name},{n},{},7,{a:.6},{b:.6},{:.2}",
            r.len(),
            a / b
        );
    }
}
