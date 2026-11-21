# Zeno-ADP

Zeno-ADP is a Rust library for algebraic dynamic programming. A grammar
builds candidate trees. Algebras ask questions about those trees, including
the minimum or maximum score, counts, Pareto fronts and distributions over
derivations. The [query table](docs/QUESTIONS.md) gives each question's
arithmetic, answer identity and audit.

## Install from source

Place a Zeno-ADP checkout next to your application and add it to `Cargo.toml`.

```toml
[dependencies]
zeno-adp = { path = "../zeno-adp" }
```

## Find the cheapest matrix parenthesization

The grammar supplies both parenthesizations for three matrices of sizes
10×30, 30×5 and 5×60. The score counts scalar multiplications.

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
[Compiler guide](docs/COMPILER.md) · [Streaming and recovery](docs/FAST.md) ·
[Forests, crossings and sets](docs/STRUCTURES.md)

For tree queries, pass `TreeMultiplicity::default()` for distinct ordered
constructor terms or `TreeMultiplicity::Derivations` for occurrences.
`queries::co_minimal` and `queries::k_lowest` score root trees exhaustively.
The `Recovery` methods with the same names use a finite additive minimum
table, as does `first_minimum_tree`. Both rank in ascending score order
and keep first derivation order for ties. `Count` counts occurrences.
`Classes` lists distinct keys. `Classified` applies a question per key
and may return several pairs per key.
[Ranking contracts](docs/QUESTIONS.md#ranking-trees) · [Migration](CHANGELOG.md#tree-ranking)

Exact weighted algebras use checked rational arithmetic. `ExactSampler`
uses independent uniform `u64` words and draws on a positive partition.
Equal returned terms collect their derivation masses. Binary64 log
algebras support approximate evaluations. Use exact arithmetic for
equality audits. [Weighted questions](docs/QUESTIONS.md#partition-functions-and-sampling)

## Check a bounded input

`audit_bounded` evaluates the ranked reference chart. For a compiled
program, collect its emissions with `compiled::reference_chart`. Audit
a product with its paired chooser. A completed report exposes Bellman
failures in `bellman.first_failure` and duplicate identities in
`ambiguities`. A budget or evaluation error leaves the verdict incomplete.

Equality with exhaustive Rust evaluation needs representable intermediate
arithmetic, including on branches removed by early choice. A full table can
also encounter errors outside the root. Lean proves the mathematical
tabulation theorem and its stated instances. The executable bridge compares
five serialized answer bags per rank on 1,892 charts from five built-in
short domains and a ranked fixture. Enumeration uses recoded constructor
IDs. The lexicographic question adds a synthetic secondary cost and
uses only finite-weight rules.
[Audit guide](docs/AUDIT.md) · [Verification](verification/README.md)

Run `cargo run --offline --locked --example matrix_chain` from the checkout.
The other [examples](examples) cover alignment, folding, knapsack, custom
sequence and streaming grammars, weighted derivations and structures.

[MIT license](LICENSE)

## Acknowledgements

Zeno-ADP builds on algebraic dynamic programming as developed by Robert Giegerich and colleagues at Bielefeld
University, and on the Bellman's GAP language and compiler. Its design was inspired by Stefanie Schirmer's talk
["Dynamic programming at ease — with Grammars, Algebras, Products"](https://www.youtube.com/watch?v=anj_-Z2L4J0)
(Strange Loop, 2014).
