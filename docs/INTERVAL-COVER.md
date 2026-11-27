# Minimum-cost interval cover

Each row covers a nonempty half-open interval `[start, end)` within
`0..points` at a nonnegative `u64` price. Its index identifies it.
Equal rows at different indices are distinct choices. Adding a redundant
free row can therefore create another optimum.

`fast::interval_cover::solve(points, rows, pins)` returns the minimum
`u128` cost and an exact `BigUint` count. An empty pin slice leaves all
rows available. Otherwise, supply one `Pin::Include`, `Pin::Exclude` or
`Pin::Either` per row. An invalid interval, including an excluded one,
returns a typed error. `Ok(None)` means coverage is impossible. Zero
points and zero rows have one empty optimum at cost zero. [Example](FAST.md#cover-points-with-labelled-intervals)

## Choosing a frontier

The sweep groups rows by start. Its state is the exclusive end of the
covered prefix. Taking a row gathers states below its end into that end.
For states already reaching the end, an unrestricted free row doubles
the number of choices. A required row contributes its price once. After
the group, the sweep retires the edge that leaves the current point uncovered.

The default uses a sorted vector until its live-edge count exceeds
`43 * max(1, ceil(log2(points + 1)))` after a row. It then transfers
every live score to a lazy range tree. A vector may scan or move every
live entry. The tree visits a number of nodes proportional to its height
per operation. On a Ryzen Threadripper 1950X, the three mixed row densities
crossed at an estimated 31, 44 and 43 live edges per tree level. The
coefficient is their rounded median. The independent menus peaked at two
edges. The calibration CSV records forced sparse, forced range, rolled,
and the then-current 256-edge hybrid. [Crossover measurements](../verification/interval_cover/crossover.csv)

`solve_with_sparse_limit(points, rows, pins, limit)` sets an absolute
live-edge limit. Zero returns `CoverError::InvalidSparseLimit`.
`usize::MAX` keeps the vector throughout. `solve_range` starts with the
tree. Default and pure range take O((points + rows) log(points + 2))
arithmetic operations and O(points + rows) entries. A caller-specified
larger sparse limit allows longer scans. Exact count operations also
depend on the bit lengths. `solve_chart` materializes the same transitions
on the generic chart for small comparisons.

## Single-row choices

`fast::interval_choice::analyze` records a tape and runs one reverse pass.
Each row gets its own include and exclude optimum and count, even if
forcing it raises the price. The tape uses O((points + rows) log(points + 2))
entries, with additional storage for exact integers. `unanimous_rows()`
returns only the indices and decisions shared by all optimum sets.
A varying row has no published assignment. Joint interventions require
a new pinned context. An infeasible context returns `Ok(None)`.

## Evidence and replay

Lean checks the sweep geometry, indexed subset correspondence, local
cost/count laws and the full-count criterion for unanimity. These proofs
end at the mathematical model. Differential tests check the Rust sweep
and reverse computation against exhaustive enumeration and independently
pinned generic charts. The large count control checks the exact integer
7^50,000. [Proofs and Python checkers](../verification/interval_cover)

The two real menus represent source excerpts for reviewing error paths in
CPython 3.12.3's `tarfile.py` and `zipfile/__init__.py` (Ubuntu build
`3.12.3-1ubuntu0.17`). Each point is a distinct line starting an explicit
`raise`. Each candidate excerpt is a compound statement with a body,
from its first to last AST line, containing at least one such point.
It costs its physical line count plus one line identifying the excerpt.
The shipped numeric menus retain each source SHA-256. To regenerate one,
run `python3 examples/support/interval_cover/source_spans.py PATH`.
[Extractor and menus](../examples/support/interval_cover)

The benchmarks check complete costs and counts before timing release
solves, including table construction and destruction. Input generation
and source parsing are outside the timer. The chart baseline uses the
0.8 generic engine. The rolled baseline uses a specialized sparse sweep.

Nine paired samples per source on the Ryzen Threadripper 1950X (CPU 22,
Rust 1.97.1, 2026-11-27) gave these median-time ratios.

| Source | Sites | Excerpts | Minimum lines | Optimal sets | Chart / default | Rolled / default |
|---|---:|---:|---:|---:|---:|---:|
| tarfile | 96 | 174 | 529 | 1 | 270.75× | 1.29× |
| zipfile | 78 | 146 | 370 | 6 | 219.54× | 1.26× |

On the synthetic mixed-overlap menu at 8,192 points and three rows per
point, the paired rolled/default ratio was 3.82×. At 128 points, asking
all 768 pin questions by separate solves took 53.82× the reverse-pass
time on independent rows and 55.08× on mixed rows. All speed ratios apply
to the named workloads and host. The 50,000-point case is a correctness
check. [Timing tables](../verification/interval_cover/benchmarks)

```sh
cargo run --release --offline --locked --example interval_cover_cross_bench -- --real
cargo run --release --offline --locked --example interval_cover_cross_bench -- --grid
cargo run --release --offline --locked --example interval_cover_cross_bench
cargo run --release --offline --locked --example interval_cover_bench -- --default
cargo run --release --offline --locked --example interval_cover_bench
```

The final command times forced range against the chart. The `final-*.csv`
tables record the CPU 22 replay. Uppercase CSV filenames preserve earlier
synthetic measurements of the original range-only and 256-boundary
implementations. The initial range-only benchmark ran on an AMD EPYC 9V74.
