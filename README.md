# Zeno-ADP

Zeno-ADP is a Rust library for algebraic dynamic programming (ADP). A grammar
builds candidate trees. Algebras ask questions about those trees, including
the minimum or maximum score, counts, Pareto fronts and distributions over
derivations. The query guide lists what each algebra counts and how to
check its answers. [Query guide](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/docs/QUESTIONS.md)

Here, ≈DP (read “approximate DP”) means approximate dynamic programming,
and adaptive dynamic programming is written in full.

## Installation

Add the crate to your application's `Cargo.toml`.

```toml
[dependencies]
zeno-adp = "0.7.0"
```

## Find the cheapest matrix parenthesization

The grammar supplies both parenthesizations for matrices A (10×30),
B (30×5) and C (5×60). Multiplying (AB)C takes 4,500 scalar
multiplications. A(BC) takes 27,000. The same grammar answers both
“what is the minimum cost?” and “how many choices are there?”

```rust
use zeno_adp::algebras::{Cost, Count};
use zeno_adp::compiled;
use zeno_adp::grammars::matrix_chain_source;

fn main() -> Result<(), zeno_adp::Error> {
    let source = matrix_chain_source(&[10, 30, 5, 60])?;
    let scores = compiled::best(&source)?;
    let optimum = scores.recover().first_minimum_tree()?;
    assert_eq!(optimum.map(|answer| answer.value), Some(Cost::Finite(4500)));

    let count = compiled::tabulate(&source, &Count)?;
    assert_eq!(count.answer(), Some(&2));
    Ok(())
}
```

## Exact models

- Use `mdp::Model` for finite discounted Markov decision processes with
  signed rational rewards and a checked policy and value at every state.
- Use `cyclic::GroundChart` for Boolean existence and nonnegative integer
  min-plus over finite derivations, including grammars with cycles.
- Use `decomposition::Compiled` to solve binary factor problems with a
  supplied tree decomposition and recover an original assignment when feasible.
  The ladder example demonstrates this on a width-three decomposition.

These three solvers return a verified `Exact<T>`. Existing ranked and
approximate APIs retain their return types. Bounded, Estimated and Unchecked
describe other assurance contracts. To transfer a certificate, extract it
with `into_inner()` and call `verify` on the intended model.

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
[Streaming and recovery](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/docs/FAST.md) ·
[Forests, crossings and sets](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/docs/STRUCTURES.md)

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
[Ranking contracts](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/docs/QUESTIONS.md#ranking-trees)

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

Rust's reference table was finite checked against that specification on
1,892 charts covering short folding, alignment, matrix-chain and knapsack
inputs and a four-cell fixture. The audit guide gives the exact domains
and five answers compared at each rank. [Audit guide](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/docs/AUDIT.md#verification-scope)

Run `cargo run --offline --locked --example matrix_chain` from the checkout.
Run `cargo run --offline --locked --example cookbook` for 24 recipes
with direct checks on raw inputs. [Cookbook](docs/COOKBOOK.md) · [Examples](examples/)

[API documentation](https://docs.rs/zeno-adp/0.7.0/zeno_adp/) · [MIT license](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/LICENSE)

See the changelog for upgrade notes from earlier versions. [Changelog](CHANGELOG.md) · [Release 0.7.0](https://github.com/TheDarkLightX/Zeno-ADP/releases/tag/v0.7.0)

## Acknowledgements

Zeno-ADP builds on algebraic dynamic programming as developed by Robert Giegerich and colleagues at Bielefeld
University, and on the Bellman's GAP language and compiler. Its design was inspired by Stefanie Schirmer's talk
["Dynamic programming at ease — with Grammars, Algebras, Products"](https://www.youtube.com/watch?v=anj_-Z2L4J0)
(Strange Loop, 2014).
