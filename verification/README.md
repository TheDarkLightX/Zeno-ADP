# Executable Bellman model

Run the proof and differential check with Lean 4.28.0, Rust 1.87.0 and
Python 3.10 or later. The checker uses Lean's standard library and Cargo's
offline mode. From the repository root, provide a directory for artifacts.

```sh
bash verification/verify.sh ../verification-output
```

`BellmanTabulation.tabulate_eq_exhaustive` relates the actual Lean table
lookup to exhaustive tree evaluation at every rank. Its local premises
follow from empty preservation, append merging and operator fusion by
`BellmanTabulation.atCell_of_laws`. Rules retain the order of their
alternatives and arguments. Repeated rules retain their occurrences.

`Instances.lean` applies these results to derivation count, ordered
enumeration, additive minimum, repaired minimum with ties, and finite
additive lexicographic minimum. Lexicographic selection requires that each
paired operator preserve the lexicographic order when its argument tuple
increases pointwise. Finite pairwise addition satisfies this condition.
The counterexamples in the same file show what can happen to the secondary
order when an operation collapses a strict primary comparison, and to tied
counts when an absorbing rule receives only optimal counts.

`BellmanProbability.lean` establishes the ranked sum-product theorem over
rationals and max-product over nonnegative rationals. It also checks the
local cancellation of the remaining suffix mass in exact sampling.
`BellmanFrontiers.lean` checks the Pareto merge and operator laws as front
set equalities and proves the integer additive operator preserves the
required order. The ranked Pareto theorem assumes that the chooser
uses a canonical representation of the front set. The ordered Δ theorem
covers constructors with a fixed additive weight plus the child scores. `DistinctIntersections.lean` checks the cancellation identity
per tree after grouping by its accepting alternatives.

`Structures.lean` checks size descent for promotion and gap splits, the
unmatched-node cost decomposition for a promoting cut, the tuple-yield
ranking equation, the equal-copy crossing language, and existence and
uniqueness of the pivot block of a pairwise disjoint cover. The Rust
structural grammar gates compare each chart cell against independent
projected forests, string slices and restricted-growth set partitions.

The exact model uses natural counts, integer weights, and optional infinite
scores. An empty cell has an empty answer bag. A cell with an infinite
answer has an inhabited bag. In the repaired product, every derivation ties
when the minimum is infinite, and the total count supplies that multiplicity.

The runner exports validated Rust reference charts and compares Rust and
Lean answer bags at every cell, including ordered tree encodings. The
comparison covers complete short domains for the five built-in grammars
and a ranked fixture with absence, duplicates, signed costs and absorption.
Enumeration compares ordered trees after replacing constructor payloads
with IDs. Lexicographic scores use a synthetic additive secondary cost
derived from those IDs. Both sides remove infinite-weight productions
for that question. The matrix score also runs through the separate
weighted interval model in `IntervalConvolution.lean`.

The comparator validates both reports against the five answer schemas
before comparing them. An inhabited count is one positive integer.
Enumeration takes recursive constructor terms. Minimum and minimum with
ties allow a null score for attainable infinity. The summary also checks
optimal and total multiplicities. The lexicographic answer is a finite
integer pair. Each non-enumeration bag holds at most one answer.
A separate reversal fixture must change enumeration order in at least one
cell, preserve every cell's enumeration multiset, and preserve all four
other questions at every cell. Corruption tests exercise those checks.
The bridge covers 1,892 Rust-emitted charts, 28,380 ranks and five answer
bags per rank. It begins after grammar emission and ends at serialized
table observations. The Rust grid for the
weighted, frontier and binary-grammar questions runs under
`cargo test --offline --locked --release`.

The same verification command checks both log algebras on a leaf-only
chart spanning powers of two, rounding midpoints, reciprocals, zero, unit
and seeded positive rational pairs. Each non-unit positive log must have
the correct sign and at most four binary64 epsilons of relative error
against a 120-digit decimal oracle. The result applies to the exercised
platform and the conversion alone. The [weighted questions guide](../docs/QUESTIONS.md#partition-functions-and-sampling)
gives the bound's arithmetic premises.

The proof concerns the Lean model. The Rust correspondence is finite
checked on the domains in `rust_bridge.rs`. Rust uses checked `i64` and
`u128` operations, so application of the exact laws requires representable
intermediate arithmetic. When claiming equality to exhaustive Rust
execution, the condition also covers derivations removed by early choice.
See the [audit guide](../docs/AUDIT.md) for bounded arithmetic and operator
checks on actual inputs.
