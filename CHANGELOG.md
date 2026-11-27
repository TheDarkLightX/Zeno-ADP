# Changelog

## 0.9.0 (unreleased)

- Find the minimum cost and exact number of labelled interval covers, including
  under required and excluded rows. The sparse frontier promotes to a range
  tree at a measured width, with an explicit caller override.
- Compute the optimum for every single include and exclude intervention in one
  reverse pass and report unanimous decisions. [Interval-cover guide](docs/INTERVAL-COVER.md)
- Evaluate one matrix-chain chart for minimum work, derivation count and
  parenthesizations in the [README example](README.md#parenthesize-three-matrices).

## 0.8.0

- Find derivations that are optimal in several additive cost models at once.
  `common_optimum::common` answers existence, the number of such derivations
  and each one by rank, with a certificate replayed cell by cell. Keep
  per-model optima, winner masks or an answer table for later questions.
  An answer table stores counts. `AnswerTable::get` looks up a retained
  count with no budget; `AnswerTable::answer` declines an unlisted selection
  with a generic collision when it fits the caller's construction budget.
- Commit to plan prefixes that keep an optimal completion in every world, or
  a completion within a regret budget per world, with `robust_prefix`.
  The caller's state limit counts pending and memoized budget DP states
  together, and live forward labels in a separate pass. `state_bound`
  gives an upper bound for each pass.
- Find the coarsest history state of a reachable raw model with
  `state_discovery` and build an explicit chart. Generic geometries count
  move derivations. An exhaustive check proves the scores through its length.
  A chart's scorer label is Exact when the check belongs to the same raw
  model and covers every candidate word length in the instance.
- Use `verify_for` to bind replay to the requested selection or regret
  budget. Common-optimum witness extraction and replay check the chart
  equations first. Feature-set generation and verification take caller
  limits, and malformed move symbols, features and refutations return errors.
- Certificate metadata names the question, family, checking method and shape.
  Checked solver returns carry `Exact<T>`. The chart answer records its
  separate `scorer_label`, and witness and refutation assurance comes from replay.
- Reproduce the retention figures of the guide with
  `cargo run --offline --locked --release --example retention`.
- `Chart` and `Rule` implement `PartialEq` and `Eq`.

### Upgrading from 0.7.0

- Existing APIs are unchanged. The new modules have their own error types.
  [Exact query guide](docs/EXACT.md)

## 0.7.0

- Solve finite discounted Markov decision processes over signed rational
  rewards and independently verify the returned policy and every state value.
- Give finite grounded cyclic grammars **Exact** Boolean and nonnegative
  min-plus answers with ranked derivation witnesses.
- Compile supplied tree decompositions for binary factor problems into ranked
  separator tables. Run the weighted independent-set ladder example to see
  an **Exact** optimum with a lifted original assignment.
  Its weight conversion covers the full `i64` range. Certificate replay
  checks factors and child messages directly in rank order.
- Algebraic dynamic programming (ADP) refers to grammar and algebra evaluation.
  Approximate dynamic programming is ≈DP. Adaptive dynamic programming is
  written in full.

### Upgrading from 0.6.0

- Set the dependency version to `0.7.0`. Existing ranked grammar and
  finite-horizon expectimax calls continue to use their existing APIs.
- The new modules use their own types and validation errors. Use
  `mdp::Rational` for signed model inputs. Use `cyclic::GroundChart` when
  productions can refer back to a cell, and `decomposition::Compiled` when
  given a tree decomposition for a binary factor model.
  [Exact query guide](docs/EXACT.md)

## 0.6.0

- The algebraic dynamic programming (ADP) cookbook has 24 recipes.
  The budgeted planning recipe finds an exact optimum from the Pareto front
  and compares it with the lower bound from a Lagrangian relaxation.
  The expectimax recipe computes maximum expected utility over a finite
  horizon with exact rational arithmetic.
- The README distinguishes ADP from approximate dynamic programming (≈DP)
  and adaptive dynamic programming.

### Upgrading from 0.5.0

- Set the dependency version to `0.6.0`. Use `ParetoWitnesses` for the
  budgeted recipe and `Chart`, `Algebra` and `BigRational` to model
  expectimax. Both recipes use the existing reference audit.
  [Cookbook](docs/COOKBOOK.md)

## 0.5.0

- Pack inhabited summaries by logical rank with `compiled::tabulate_compact`.
  Use `compiled::tabulate_with_budget` to select a layout under a caller
  limit on table slot bytes.
- Bound compiled sequence splits with per-track span caps and input-aware
  end intervals or interval unions. Each allowed end is visited once.
- Compute compiled inside and outside weights without retaining production
  rows. Query exact weighted rule occurrences and expected event visits.
- Run 22 cookbook recipes with direct checks on the raw inputs.
- Inspect chart growth with `grammar_growth` and print readable audit
  verdicts, Bellman counterexamples and ambiguity witnesses.

### Upgrading from 0.4.0

- Set the dependency version to `0.5.0`. Existing dense tables and grammar
  entry points still work. To set a slot budget, use
  `compiled::tabulate_with_budget` and read the result by logical rank.
- Exhaustive matches on `Error` can handle the new `TableBudgetExceeded`
  variant. If you surface audit errors, use their fields for structured
  information. The display text now describes the rank and failed law.
- If you add span limits or split guards to an existing grammar, check
  how the restricted candidates change counts and weights. Run the
  Bellman audit with `compiled::reference_chart`.
- Parallel filling remains experimental. The compiler guide lists
  timings and the `Sync` requirements for bound grammars.

## 0.4.0

- Generate ordered schedules for forest edit and alignment, proper linear
  MCFGs, and set partitions.
- Compile contiguous grammars over any positive number of tracks. Generate
  prefix schedules with clauses that advance a selected subset of tracks.
- Select several ranks with `compiled::tabulate_selected`. Evaluate two
  independent algebras on one schedule with `compiled::tabulate_joint`,
  retaining the ranks requested for each algebra.
- Fill independent ranks with experimental `compiled::tabulate_parallel`.
  Scoped workers are reused across waves. Global alignment tiles and
  interval-length schedules for Nussinov and generated intervals skip
  planning replay.
- Supply exact-size child iterators in every table mode. Validate
  arity and descending ranks at the multi-track emission boundary.
- Show the supported scope and fix in the diagnostic for `with fn` inside
  inherent and trait implementations.

### Upgrading from 0.3.0

- Change the dependency version to `0.4.0`. Existing byte and typed
  sequence grammar declarations use the same entry points.
- Custom `Fold` implementations keep their `Iterator + Clone` signature.
  Every evaluator now reports the exact remaining child count through
  `size_hint()`. Keep fold operations independent of evaluation order
  across cells.
- Use a positive track count. `Grammar<_, 0>` now reports that the
  grammar needs at least one input track.
- To evaluate an associated grammar, define it without `with fn` and
  call `compiled::tabulate(&Self::grammar(input)?, &algebra)` in the
  evaluation method. Module and function-local declarations can use
  the paired shorthand.
- Choose output ranks separately for each algebra with
  `compiled::tabulate_joint`. Pass the same rank to both projections
  when you need the pair of answers. Use a full table for random cell
  access or tree recovery.

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
