# Zeno-ADP

Zeno-ADP is a Rust library for algebraic dynamic programming. A grammar
builds candidate trees. Algebras ask questions about those trees, including
the minimum or maximum score, counts, Pareto fronts and distributions over
derivations. The query guide lists what each algebra counts and how to
check its answers. [Query guide](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/QUESTIONS.md)

## Installation

Add the crate to your application's `Cargo.toml`.

```toml
[dependencies]
zeno-adp = "0.1.0"
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

## Pick a grammar and an evaluation mode

Use built-in sequence grammars or declare one or two byte tracks with
`compiled::Grammar`. For forests, crossing dependencies and subsets, use
the structural grammars. `compiled::replay` reports the cell rank, occurrence
ordinal, clause name, constructor payload and ordered child ranks.
`compiled::tabulate_root` observes each cell as it finishes and keeps the
root and live summaries, with a last-use entry for each rank.
[Compiler guide](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/COMPILER.md) ·
[Streaming and recovery](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/FAST.md) ·
[Forests, crossings and sets](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/STRUCTURES.md)

For tree queries, pass `TreeMultiplicity::default()` for distinct ordered
constructor terms or `TreeMultiplicity::Derivations` for occurrences.
`queries::co_minimal` and `queries::k_lowest` score root trees exhaustively.
The `Recovery` methods with the same names use a finite additive minimum
table, as does `first_minimum_tree`. Both rank in ascending score order
and keep first derivation order for ties. `Count` counts occurrences.
`Classes` lists distinct keys. `Classified` applies a question per key
and may return several pairs per key.
[Ranking contracts](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/QUESTIONS.md#ranking-trees)

Exact weighted algebras use checked rational arithmetic. `ExactSampler`
uses independent uniform `u64` words and draws on a positive partition.
Equal returned terms collect their derivation masses. Binary64 log
algebras support approximate evaluations. Use exact arithmetic for
equality audits. [Weighted questions](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/QUESTIONS.md#partition-functions-and-sampling)

## Check a bounded input

`audit_bounded` evaluates the ranked reference chart. For a compiled
program, collect its emissions with `compiled::reference_chart`. Audit
a product with its paired chooser. A completed report exposes Bellman
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
and five answers compared at each rank. [Audit guide](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/docs/AUDIT.md#verification-scope)

Run `cargo run --offline --locked --example matrix_chain` from the checkout.
The other examples cover alignment, folding, knapsack, custom sequence and
streaming grammars, weighted derivations and structures. [Examples](https://github.com/TheDarkLightX/Zeno-ADP/tree/v0.1.0/examples)

[API documentation](https://docs.rs/zeno-adp/0.1.0/zeno_adp/) · [MIT license](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/LICENSE)

## Acknowledgements

Zeno-ADP builds on algebraic dynamic programming as developed by Robert Giegerich and colleagues at Bielefeld
University, and on the Bellman's GAP language and compiler. Its design was inspired by Stefanie Schirmer's talk
["Dynamic programming at ease — with Grammars, Algebras, Products"](https://www.youtube.com/watch?v=anj_-Z2L4J0)
(Strange Loop, 2014).
