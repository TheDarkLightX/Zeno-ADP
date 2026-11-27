# Zeno-ADP

## Parenthesize three matrices

Suppose A is 10×30, B is 30×5, and C is 5×60. We want to parenthesize
`ABC` without changing the matrix order. The chart has one cell per
nonempty interval. Its root can put the last split after A or after B.

```text
M[i,i+1] ::= Matrix(i)
M[i,j]   ::= Multiply(M[i,k], M[k,j]) for i < k < j
```

Each `Multiply` also records its split and the local multiplication
cost. The root derives `A(BC)` and `(AB)C`. Zeno-ADP is a Rust library
for algebraic dynamic programming (ADP). The grammar generates those
trees, and an evaluation algebra defines what to compute from them.

| Algebra | Question | Root answer |
|---|---|---|
| `Minimum` | How many scalar multiplications does the cheapest tree take? | 4,500 |
| `Count` | How many derivations are there? | 2 |
| `Enumerate` | Which trees are there? | `A(BC)`, `(AB)C` |

```rust
use zeno_adp::algebras::{Cost, Count, Enumerate, Minimum};
use zeno_adp::grammars::{matrix_chain, MatrixChain};
use zeno_adp::tabulate;

fn main() -> Result<(), zeno_adp::Error> {
    let chart = matrix_chain(&[10, 30, 5, 60])?;
    assert_eq!(tabulate(&chart, &Minimum)?, [Cost::Finite(4_500)]);
    assert_eq!(tabulate(&chart, &Count)?, [2]);
    let trees = tabulate(&chart, &Enumerate)?;
    assert_eq!(trees.len(), 2);
    assert!(matches!(trees[0].operator, MatrixChain::Multiply { split: 1, .. }));
    assert!(matches!(trees[1].operator, MatrixChain::Multiply { split: 2, .. }));
    Ok(())
}
```

See the [cell-by-cell answers](docs/QUESTIONS.md#three-questions-one-chart)
and [the audit on this chart](docs/AUDIT.md#checking-bellmans-principle).

## Installation

Add the crate to your application's `Cargo.toml`.

```toml
[dependencies]
zeno-adp = "0.9.0"
```

Here, ≈DP (read “approximate DP”) means approximate dynamic programming,
and adaptive dynamic programming is written in full.

## Exact models

- Use `mdp::Model` for finite discounted Markov decision processes with
  signed rational rewards and a checked policy and value at every state.
- Use `cyclic::GroundChart` for Boolean existence and nonnegative integer
  min-plus over finite derivations, including grammars with cycles.
- Use `decomposition::Compiled` to solve binary factor problems with a
  supplied tree decomposition and recover an original assignment when feasible.
  The ladder example demonstrates this on a width-three decomposition.

- Use `common_optimum::common` to find the derivations of a chart that are
  optimal in several cost models at once: whether one exists, how many, and
  each one by rank.
- Use `robust_prefix::zero_regret` and `within_budget` to commit to the most
  useful first steps of a plan that keep an optimal, or budgeted, completion
  in every world.
- Use `state_discovery` to find the coarsest state of a reachable raw
  history model and align over it. The finite scorer check validates scores
  through its declared length.

These solvers return verified `Exact<T>` values for their declared models.
For a transferred certificate, replay it with `verify` on the intended
`mdp::Model`, `cyclic::GroundChart`, or `decomposition::Compiled`.
Use `Common::verify_for` and `WithinBudget::verify_for` to bind a replay
to the requested selection or budget, and `ZeroRegret::verify` for a
zero-regret certificate. Replay a quotient with `Quotient::verify` against
the raw model. Read `Solved::scorer_label` for the assurance an exhaustive check
gives the chart's answer against the scorer.

[Exact query guide](docs/EXACT.md) · [Ladder example](examples/separator_ladder.rs)

## Pick a grammar and an evaluation mode

Use built-in sequence grammars, declare byte tracks with
`compiled::Grammar`, or use `compiled::TokenGrammar` for `Eq` tokens
and predicate terminals. The current source supports generated prefix,
interval and multi-track prefix tables, forest edit and alignment, linear
multiple context-free grammars, and set partitions. `compiled::replay`
reports the cell rank, occurrence ordinal, clause name, constructor
payload and ordered child ranks. Use `compiled::tabulate_selected` for
several answers from one algebra. Use `compiled::tabulate_joint` for
two independent algebras with their own requested ranks.
Use `compiled::tabulate_with_budget` for a byte limit on table slots.
It chooses dense storage when it fits and tries packed runs otherwise.
Use `with_split_ends` to admit a union of child end ranges.

`compiled::tabulate_parallel` is experimental. The eight-CPU benchmark
used five runs per worker count. Speedups compare the median time to
the one-worker median. Answers agreed at every worker count.

| Workload | 2 workers | 4 workers | 8 workers |
|---|---:|---:|---:|
| Global alignment, 3,000 × 3,000 tokens | 0.23× | 0.32× | 0.40× |
| Nussinov, 700 bases | 1.46× | 2.12× | 2.53× |

[Compiler guide](docs/COMPILER.md) ·
[Streaming and recovery](docs/FAST.md) ·
[Forests, crossings and sets](docs/STRUCTURES.md)

Build an alignment grammar from two ranked prefix grammars with
`grammars::PrefixProduct`. For one minimum-cost unit alignment,
`fast::alignment_linear_space` recovers the first optimal path using a
single working row. [Products and recovery](docs/FAST.md)

For tree queries, pass `TreeMultiplicity::default()` for distinct ordered
constructor terms or `TreeMultiplicity::Derivations` for occurrences.
`queries::co_minimal` and `queries::k_lowest` score root trees exhaustively.
The `Recovery` methods with the same names use a finite additive minimum
table, as does `first_minimum_tree`. Both rank in ascending score order
and keep first derivation order for ties. `Count` counts occurrences.
`Classes` lists distinct keys. `Classified` applies a question per key
and may return several pairs per key.
[Ranking contracts](docs/QUESTIONS.md#ranking-trees)

`ParetoWitnesses` retains every non-dominated derivation in order for two
fixed additive costs with representable ordered sums. Filter by a resource
budget to recover an exact feasible minimum when one exists. `Provenance`
counts derivation label multisets. Substitute one fixed weight per label
in a lawful commutative semiring to reuse the polynomial.
[Question guide](docs/QUESTIONS.md)

Use bounded or arbitrary-precision nonnegative rationals for sum-product
and max-product tabulation and reference audits. On a fixed chart,
`Expectation` returns total mass and an unnormalized weighted feature sum
or partition derivative. At positive mass, `normalized()` returns the
expected feature or log-partition derivative. `ExactSampler` uses independent uniform `u64` words and draws on a positive partition.
Equal returned terms collect their derivation masses. Binary64 log
algebras support approximate evaluations. Use exact arithmetic for
equality audits. [Weighted questions](docs/QUESTIONS.md#partition-functions-and-sampling)

For finite-horizon expectimax, use a weighted rule per action and maximize
over actions to find the exact expected utility.
[Expectimax recipe](docs/COOKBOOK.md#finite-horizon-expectimax)

## Measured structural table timings

Median generated time divided by direct recurrence time, including
input binding and full-table allocation. Measurements used Rust 1.87.0
on one AMD Threadripper 1950X core, with six rotating samples per
implementation and size. Each timed table was compared cell by cell
with the reference chart before sampling.

| Workload | Input sizes | Generated/direct time |
|---|---|---|
| Forest edit minimum | 6, 12, 18 nodes per side | 1.121, 1.501, 1.275 |
| Forest alignment minimum | 6, 12, 18 nodes per side | 1.808, 1.939, 1.613 |
| Linear MCFG derivation count | 8, 16, 24 bytes | **2.247**, 1.669, 1.767 |
| Set partition count | 8, 12, 16 elements | 1.322, 1.589, 1.426 |
| Three-track prefix minimum | 8, 20, 40 tokens per track | 1.826, 1.587, 1.692 |
| Four-track prefix minimum | 4, 8, 12 tokens per track | 1.913, **2.012**, 1.650 |

The 8-byte MCFG case (2.247×) and four-track case with 8 tokens per
track (2.012×) exceeded the 2.0× time target. All 18 peak-memory
ratios were within 2.0×.

## Check a bounded input

`audit_bounded` evaluates the ranked reference chart. For a compiled
program, collect its emissions with `compiled::reference_chart`. Audit
a grammar product on the chart collected by `fast::reference_chart`.
Audit an algebra product with its paired chooser. A completed report exposes Bellman
failures in `bellman.first_failure` and duplicate identities in
`ambiguities`. A budget or evaluation error leaves the verdict incomplete.

For ranked charts with total operations, tabulation gives the same answers
as exhaustive evaluation when choice preserves the empty bag, commutes
with merging alternatives, and can be applied to children before their
parent without changing the chosen answers. This equality is proved for
the mathematical chart. In Rust, agreement also requires successful
operations on discarded branches and on every cell evaluated.

Rust's reference table is proved, by exhaustive check, to match that specification on
1,892 charts covering short folding, alignment, matrix-chain and knapsack
inputs and a four-cell fixture. The audit guide gives the exact domains
and five answers compared at each rank. [Audit guide](docs/AUDIT.md#verification-scope)

Run `cargo run --offline --locked --example matrix_chain` from the checkout.
Run `cargo run --offline --locked --example cookbook` for 24 recipes
with direct checks on raw inputs. [Cookbook](docs/COOKBOOK.md) · [Examples](examples/)

[API documentation](https://docs.rs/zeno-adp/0.9.0/zeno_adp/) · [MIT license](LICENSE)

See the changelog for upgrade notes from earlier versions. [Changelog](CHANGELOG.md)

## Lineage and acknowledgements

Zeno-ADP builds on algebraic dynamic programming as developed by Robert Giegerich and colleagues at Bielefeld
University, and on the Bellman's GAP language and compiler. Its design was inspired by Stefanie Schirmer's talk
["Dynamic programming at ease — with Grammars, Algebras, Products"](https://www.youtube.com/watch?v=anj_-Z2L4J0)
(Strange Loop, 2014). See the [lineage notes](docs/LINEAGE.md) for the papers and the BOB 2016 talk.
