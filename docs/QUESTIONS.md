# Choose a question

The reference audit runs on a ranked chart. For a compiled program, first
collect its rules with `compiled::reference_chart`. In the table, **audit
the algebra** means run the bounded reference check and inspect
`bellman.first_failure`. Inspect `ambiguities` separately for duplicate
terms or class keys. An evaluation or budget error leaves the verdict
incomplete. See [Evaluating and auditing a grammar](AUDIT.md).

| Question | Entry points and arithmetic | Identity | Ranking or output order | Audit verdict to inspect |
|---|---|---|---|---|
| Lowest or highest additive score | `Additive`, `Minimum`, `queries::minimum`, `Maximum`. Checked `i64`. Attainable infinity is supported by `Minimum` or opt-in `Additive`. | One score per inhabited cell. | Ascending for minimum, descending for maximum. | Audit the chosen algebra. |
| Minimum and tie count | `MinimumCount` uses finite checked `i64` and `u128`. `MinimumWithMultiplicity` adds a total and can accept infinity by policy. | Derivation occurrences. | Ascending cost, count all ties. | Audit the paired summary. |
| Count all derivations | `Count`, `derivation_count`. Checked `u128`. | Derivation occurrences, including duplicates. | None. | Audit `Count`. Inspect injectivity if interpreting the count as distinct. |
| List or count terms | `Enumerate`, `queries::trees`, `queries::count`. Tree construction and optional term coalescing. | Pass `TreeMultiplicity::default()` for ordered constructor terms, or `Derivations` for occurrences. `Enumerate` retains occurrences. | First derivation order. | Audit `Enumerate` for occurrence bags. Inspect term injectivity separately. |
| Lowest-scoring trees | `queries::co_minimal` and `queries::k_lowest` score root trees exhaustively. `Recovery::co_minimal`, `Recovery::k_lowest` and `Recovery::first_minimum_tree` use a finite additive table. See [the ranking contracts](#ranking-trees). | Explicit term or occurrence identity. | Ascending score, then first derivation order. Use `exhaustive` to apply the scorer's own chooser to the root bag. | Exhaustive ranking requires successful scoring. Audit the relevant additive or score-tree algebra when relying on early choice. |
| Distinct class keys or a question per class | `Classes`, `Classified`. Classifier and inner question define operations and arithmetic. | Canonical class key, with ordered multiplicities supplied to each inner chooser. | Key order, then the inner chooser's order. | Audit the paired question with `audit_bounded_classified`. Inspect class collisions separately. |
| Lexicographic or Pareto selection | `Product::new` with `lexicographic_min` or `pareto_min`. Both use the components' arithmetic. | One lexicographic pair or unique nondominated score pairs. | Ascending lexicographic minimum or front sorted lexicographically. Both Pareto coordinates are minimized. | Audit the paired algebra and chooser. |
| Trees within Δ | `WithinDelta`, `queries::within_delta`. Checked finite `i64` costs, `u64` inclusive difference. | Ordered occurrences in the algebra. The query takes explicit term or occurrence identity. | First derivation order within the band above the minimum. | Audit `WithinDelta` on the ordered bags. |
| Derivation partition or best weight | `SumProduct`, `partition`, `MaxProduct`, `inside_outside`. Reduced rational, checked `u128`. | Occurrence mass. Outside sums contexts with one marked child position. | Sum for the partition, descending for the largest weight. | Audit the exact algebra. Compare outside separately against marked contexts. |
| Approximate log weights | `LogSumProduct`, `LogMaxProduct`, `log_inside_outside`. Binary64. | Occurrence mass in log space. | Log-sum-exp for totals, descending log weight for maxima. | Use exact algebras for equality audits. Compare log results with a domain-specific error allowance. |
| Sample a weighted tree | `ExactSampler`. Checked rational branch probabilities and independent uniform `u64` words. | Draw a derivation. Equal returned terms collect occurrence masses. | Sample, with no score ordering. | Audit `SumProduct` for inside mass. Check sampling separately against exact derivation probabilities. |
| Distinct binary count or intersection | `BinaryTreeGrammar::distinct_counts`. Checked `u128` acceptance buckets. | Ordered tree terms at an exact leaf count. | None. | Compare profiles to explicit term sets on reference charts. Audit their derivation algebra separately. |

Forest, tuple and set grammars use these questions. Their constructor
identities are described in [Forests, tuples and sets](STRUCTURES.md).

## Ranking trees

| | Exhaustive root ranking | Finite additive recovery |
|---|---|---|
| Entry points | `queries::co_minimal`, `queries::k_lowest` | `Recovery::first_minimum_tree`, `Recovery::co_minimal`, `Recovery::k_lowest`, obtained from `compiled::best` or `fast::BestTable` |
| Scoring | Evaluate each selected root tree using the scorer's constructor operations. Ranking supplies its own ascending choice. | Fill a checked finite additive minimum table over all ranks, then visit alternatives that can meet the requested score cutoff. |
| Identity and order | Natural ascending score order, then first derivation order. Choose structural terms or derivation occurrences with `TreeMultiplicity`. | Ascending `Cost::Finite` scores with the same tie and multiplicity rules. `first_minimum_tree` returns the first minimum occurrence. |
| Arithmetic | Every tree scored by the request must evaluate successfully. `k_lowest` with `k = 0` returns an empty list before scoring. | Checked sums run over the alternatives evaluated by tabulation and recovery. Agreement with exhaustive execution requires representable sums on discarded derivations too. |

A leaf choice of `0` or `i64::MAX` under a parent of cost `1` gives
`Error::Overflow` from both exhaustive ranking queries when requesting
the minimum. The recovery methods can return the tree of score `1`.

## Partition functions and sampling

Implement `probability::WeightedOperator` for a chart's operator. The
weight is a fixed nonnegative `Rational` for that constructor occurrence.
A derivation has the product of all its constructor weights. `SumProduct`
sums those weights and `MaxProduct` finds the largest. Both work with
`tabulate_cells`, `exhaustive` and the reference audit. An empty cell has
an empty answer bag, while a derivation of weight zero has an inhabited bag
with value zero. `probability::partition` returns zero in either case.

`inside_outside` returns all inside weights and the weight of root contexts
for each cell. A context is a derivation with one designated hole. The root
has outside weight one. Each parent rule contributes its outside weight,
its rule weight and the product of the other children's inside weights
to the outside value of each child position. Repeated child positions
contribute separately. Even a cell with no derivations can have a nonzero
outside value. For a positive partition, inside times outside divided by
the partition gives the expected number of occurrences of a cell. That
number can exceed one.

`ExactSampler::new` prepares conditional branch probabilities from the
inside table. `sample` chooses a rule proportional to its inside contribution
and independently descends into each child position. Supply a callback
returning independent uniform `u64` words. Rejection sampling gives an
unbiased ticket in the rational denominator. A zero partition returns
`None` without drawing words. `sample_from` and `rule_probabilities` expose
the corresponding question at any cell. Equal tree terms from distinct
derivations contribute their combined mass to that returned tree.

Rational arithmetic uses reduced fractions and checked `u128` operations.
An unrepresentable required intermediate yields `Error::Overflow`. The
algebra laws concern total arithmetic. An equality audit covers arithmetic
on derivations that early choice would discard. Exact samplers and outside
tables have additional rational operations, each subject to the same
representability condition.

`LogSumProduct`, `LogMaxProduct` and `log_inside_outside` evaluate the same
weights in binary64 log space. They use addition for products and stable
log-sum-exp for totals. They represent zero as negative infinity.
`LogWeight::ln()` preserves the log result for very small values.
`LogWeight::mass()` converts to linear space and can underflow or
overflow. For positive integers `n,d`, conversion takes `ln_1p(|n−d|/min(n,d))`
and applies the sign of `n−d`. The exact integer gap preserves the direction
before floating-point rounding. For binary64 round-to-nearest, let
`u = f64::EPSILON / 2`. The two integer conversions and one division
perturb a positive gap ratio by less than `4u` relatively. The arguments
remain in the normal exponent range, and the logarithmic sensitivity
`x / ((1+x) ln(1+x))` is at most one for `x > 0`. A one-ulp `ln_1p`
adds at most `2u` relative error at the rounded argument. Four binary64
epsilons bound the combined relative error under these premises. Unit
weights give log zero exactly. Rust does not specify a portable ulp bound
for its transcendental functions. Chart operations and linear-space
conversion add their own rounding.
Use the exact algebras for an equality-based Bellman audit. Log values were
finite checked on one four-cell chart with all four root choices and all
81 assignments of weights 0, 1/3 or 1 to four rule groups. For those 324
cases, the test allows an absolute log error of
`64 * f64::EPSILON * max(1, abs(ln(exact)))` for positive weights and
requires negative infinity for zero. [Weighted test](../tests/probability.rs)

Run `cargo run --offline --locked --example weighted_chart` for a weighted
chart with two repeated child positions.

## Pareto fronts and score bands

Use `Product::new(left, right, pareto_min)` to minimize two scores together.
The chooser returns unique non-dominated pairs sorted lexicographically.
Any discarded pair has a retained pair no larger in either coordinate.
When each constructor preserves the componentwise order in each child,
replacing the discarded child can only improve the parent or leave its
score equal. That also gives the merge law, since a local dominator
remains a candidate in the merged bag. Coordinatewise finite additive
costs satisfy this condition when the required sums are representable.
The result is a front of scores. Queries about the witnesses or multiplicity
behind a score need their own algebra and law.

`queries::within_delta` returns the finite additive score and tree for every
root answer at most Δ above the optimum, including the boundary. Choose
structural identity or derivation multiplicity with `TreeMultiplicity`.
The `WithinDelta` algebra returns the ordered occurrence bag at every
cell. A child more than Δ above its local optimum can be replaced by that
optimum, improving the parent by exactly the same difference. Merging
bands also preserves every globally eligible answer, since the global
optimum is no higher than any alternative's local optimum. This rule
applies to signed additive scores with representable intermediates.
A monotone transformation that shrinks score gaps can invalidate it.

For the mathematical ranked chart, ordered equality with exhaustive
evaluation is proved for a nonnegative Δ when each constructor score is
its fixed integer weight plus its child scores. For pairs of integers,
the Pareto theorem requires componentwise monotone constructors and a
chooser that preserves the empty bag and returns exactly the front in a
canonical order. Both equalities hold at every in-bounds rank.
[Score-band and Pareto theorems](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.1.0/verification/BellmanFrontiers.lean)

## Distinct binary trees by semantic intersection

Build a `distinct::BinaryTreeGrammar` from nonterminal rows of labeled leaf
productions and one fixed ordered binary constructor. Call
`distinct_counts(max_leaves)` once, then query `count(leaves, start)`
or `intersection(leaves, first, rest)`. Each query uses an exact leaf count.
Repeated productions and overlap through different nonterminals are
coalesced. The reference `chart(leaves, start)` exposes derivations of the
same grammar and can be used with the general tree and audit queries.

Every tree has one leaf label or one root split and ordered pair of
subtrees. For each pair of child acceptance profiles the recurrence
computes the exact set of parent nonterminals that accept the tree.
Counts in a bucket are disjoint. Within one split a tree accepted by
\(m\) alternatives contributes once, since the full signed sum of its
nonempty intersections is one for \(m > 0\). Grouping equal profiles
performs this cancellation without enumerating alternative subsets.
The number of profiles can be exponential in the number of nonterminals,
and intermediate counts must fit in `u128`. Both the profile table and its reference chart reserve their dense layouts fallibly. General charts remain
available through the canonical tree-counting query.
