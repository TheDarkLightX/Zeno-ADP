# Changelog

## 0.3.0

- Compose nullary and unary prefix grammars with `grammars::PrefixProduct`.
- Keep exact rule-label provenance and project a table into commutative
  semiring questions.
- Return every ordered non-dominated witness for two finite additive
  objectives with `algebras::ParetoWitnesses`.
- Audit sum-product and max-product with arbitrary-precision
  nonnegative rationals.
- Recover the first minimum-cost unit alignment with
  `fast::alignment_linear_space`.
- Generate prefix or interval table schedules with `compiled_grammar!`.
  The generated program supports ordered replay and reference chart audits.
- Compile sequence grammars over any `Eq` token type, with equality and
  predicate terminals, through `compiled::TokenGrammar`.
- Evaluate exact expected additive features and directional derivatives
  with `probability::Expectation`, including signed components.
- Compare generated tables with the direct recurrences in the segmentation
  and optimal binary search tree examples.
- Drop deeply nested witness trees with an iterative traversal.
- Check the full two-track rank count before allocating offsets. Offset
  reservation failures return `Error::AllocationFailed`.

### Upgrading from 0.1.0

- `compiled::Matched<'_, 1>` remains the one-track byte type. Byte
  `Matched` literals infer `u8`, including empty slices and unsuffixed
  integer literals. Typed constructor callbacks use
  `compiled::TokenMatched<'_, TRACKS, T>`. The byte names `Grammar`,
  `Production` and `Sequence` use the same compiler as their token
  counterparts.
- To move fields out of a `Tree`, use `let (operator, children) =
  tree.into_parts();`. Field access and struct literals still work.
- To replace the operator of an owned tree, take its children with
  `let (_, children) = tree.into_parts();` and construct
  `Tree { operator: replacement, children }`.
- Call `drop(tree)` before mutating a value that the tree borrows. Its
  destructor keeps the borrow live through the end of the tree's scope
  unless the tree is consumed earlier. The root payload is dropped after
  the iterative child traversal. Payload destructors should keep cleanup
  independent of traversal order.
- Arbitrary-precision arithmetic uses `num-bigint` and `num-integer`.
  The crate archive excludes the historical design and literature notes.

## 0.1.0

This first release evaluates ranked tree grammars in Rust. Use the included
grammars for matrix chains, alignment, folding and knapsack, or define your
own. The same grammar can answer questions about scores, derivation counts,
Pareto fronts and weighted samples.

Recover a minimum-cost tree from a finite additive score table, or rank
root trees exhaustively with your own scorer. Both interfaces break score
ties in derivation order. A bounded audit checks an algebra on a chart
and reports duplicate terms separately.
[Ranking contracts](docs/QUESTIONS.md#ranking-trees)
