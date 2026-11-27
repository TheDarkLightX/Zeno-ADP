use std::hint::black_box;
use std::time::{Duration, Instant};

use zeno_adp::fast::interval_cover::{
    solve, solve_chart, solve_range, CoverError, Interval, Optimum, Pin,
};

fn sample(shape: &str, n: usize) -> Vec<Interval> {
    (0..n)
        .flat_map(|start| {
            let end = start + 1;
            match shape {
                "independent-free" => {
                    [Interval {
                        start,
                        end,
                        cost: 0,
                    }; 3]
                }
                "overlap-mixed" => [
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
                        cost: (start as u64) % 3,
                    },
                ],
                _ => panic!("unknown fixture"),
            }
        })
        .collect()
}

type Solve = fn(usize, &[Interval], &[Pin]) -> Result<Option<Optimum>, CoverError>;

fn timed(f: Solve, n: usize, rows: &[Interval]) -> Duration {
    let t = Instant::now();
    black_box(f(black_box(n), black_box(rows), &[]).unwrap());
    t.elapsed()
}

fn main() {
    let (fast, name): (Solve, _) = match std::env::args().nth(1).as_deref() {
        None => (solve_range, "range"),
        Some("--default") => (solve, "default"),
        _ => panic!("expected --default or no argument"),
    };
    let raw = std::env::var_os("RAW_SAMPLES").is_some();
    if raw {
        eprintln!("shape,points,rep,first,chart_ns,{name}_ns");
    }
    println!(
        "shape,points,rows,repetitions,chart_median_ms,fast_median_ms,ratio,min_cost,count_bits"
    );
    for shape in ["independent-free", "overlap-mixed"] {
        for n in [16, 64, 128, 256, 512] {
            let rows = sample(shape, n);
            let score = fast(n, &rows, &[]).unwrap().unwrap();
            assert_eq!(Some(score.clone()), solve_chart(n, &rows, &[]).unwrap());
            let reps = if n <= 256 { 9 } else { 5 };
            let mut f = vec![];
            let mut c = vec![];
            for i in 0..reps {
                let (a, b);
                if i % 2 == 0 {
                    a = timed(fast, n, &rows);
                    b = timed(solve_chart, n, &rows);
                } else {
                    b = timed(solve_chart, n, &rows);
                    a = timed(fast, n, &rows);
                }
                if raw {
                    let first = if i % 2 == 0 { "fast" } else { "chart" };
                    eprintln!("{shape},{n},{i},{first},{},{}", b.as_nanos(), a.as_nanos());
                }
                f.push(a);
                c.push(b);
            }
            f.sort_unstable();
            c.sort_unstable();
            let a = f[reps / 2].as_secs_f64() * 1e3;
            let b = c[reps / 2].as_secs_f64() * 1e3;
            println!(
                "{shape},{n},{},{reps},{b:.6},{a:.6},{:.2},{},{}",
                rows.len(),
                b / a,
                score.cost,
                score.count.bits()
            );
        }
    }
}
