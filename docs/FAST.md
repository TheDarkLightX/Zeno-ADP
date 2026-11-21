# Streaming evaluation and tree recovery

A ranked chart stores every production. A `fast::RuleSource` instead emits
one cell's ordered productions through a callback. Its cell IDs are dense,
zero-based ranks. Each child must precede its parent and the number of child
IDs must match the constructor's arity. The callback receives a borrowed
slice of child IDs. A grammar can emit directly from local arrays and loops.

The `*_source` functions in `grammars` provide this interface for the five
built-in grammars. Run `cargo run --offline --locked --example tile_row` for a
caller-defined grammar. Keep the source's layout, rules and payloads
deterministic while using a table.

## Ask a question

| API | Result |
|---|---|
| `fast::tabulate(&source, &Additive::default())` | Optional finite minimum at each cell. Call `cells()` on the returned table to read them all, or `answer()` for the root. |
| `fast::tabulate(&source, &Count)` | Derivation count at each inhabited cell. Absence is represented by `None`. |
| `fast::tabulate(&source, &MinimumWithMultiplicity::default())` | Minimum, number of optimal derivations and total derivation count. |
| `fast::tabulate(&source, &ScoreTrees)` | Minimum and ordered bag of co-optimal derivations at each inhabited cell. |
| `fast::BestTable::new(&source)` | Finite scores with methods for recovering the first optimum, all co-optimal trees or the k best trees from a selected cell. |
| `fast::reference_chart(&source)` | Explicit chart for any reference `Algebra`, exhaustive evaluation and the bounded audit. |

A custom `fast::Fold` supplies an operation over selected child summaries
and a merge operation over one alternative at a time. Match that reduction
to the corresponding reference algebra's batch choice. Each inhabited
cell has one summary. For example, the score × tree fold's summary contains
a score and an entire bag. A rule with an absent child contributes
nothing. Tabulation still visits cells the root cannot reach. The reference
engine supports general choice functions and bounded audits. [Audit guide](AUDIT.md)

Count uses checked `u128` arithmetic and preserves repeated productions.
Structural tree ranking uses constructor payloads and ordered children.
Choose `TreeMultiplicity::Derivations` for occurrence-sensitive results.
With `CostPolicy::AttainableInfinity`, `MinimumWithMultiplicity` uses the
total derivation count for ties when a rule's score is infinite.

## Recover trees in two phases

The first phase retains one score per cell. The second phase starts at
the requested cell and regenerates its alternatives. For the first optimum,
it follows the first rule attaining that cell's score. For all co-optima,
it follows every such rule and forms the ordered products of co-optimal
children. Repeated child cells share memoized recovery work within a query.

Ranking beyond the optimum needs further alternatives. The score table
bounds each rule by its best possible score. Recovery skips a later rule
when its bound cannot improve the current kth answer. It keeps at most
k ranked answers per visited cell and per intermediate ordered child
prefix. The stored order of a derivation is its rule ordinal followed by the
ordered derivation positions of its children. This order agrees with the
reference Cartesian enumeration even when child scores reorder its terms.

The eager score × tree product asks the same co-optimal question during
tabulation. It retains trees in all inhabited cells and can use more
memory than recovering trees from a single cell. Both paths can return
exponentially many co-optima. Ranked recovery can also need additional
competitive cells and generate up to k squared combinations at a child
join before truncation.

## Compose prefix grammars

`grammars::PrefixProduct::new` takes two ranked nullary/unary charts and
returns a `RuleSource`. Build a chart from ordinary tokens using
`grammars::sequence_prefixes`. Each product rank combines a pair of
operand ranks and equals `left_rank * right_cell_count + right_rank`.
Two nullary rules terminate together. A paired unary rule advances both
operands. A one-sided advance holds the other rank fixed. A product
derivation chooses an operand derivation on each side and an alignment
of their unary steps. One step on each side admits three alignments.

Paired rules come first in operand order, followed by left-only and
right-only rules. Constructor payloads on both sides and repeated
productions survive in `ProductColumn`. The root is the pair of operand
roots. Higher arities produce `Error::UnsupportedGrammar`. Use
`fast::reference_chart` to collect the product for an audit.

## Recover one global alignment in linear space

`fast::alignment_linear_space(left, right)` returns the unit-cost edit
distance and the first optimal alignment in reference derivation order.
`AlignmentPath::columns` visits columns from start to end.
`AlignmentPath::into_tree` materializes the same unary constructor term,
with one node per column plus the start node. Dropping a `Tree` walks its
children iteratively. `AlignmentPath` keeps its columns in flat storage.

The recurrence carries the selected predecessor's midpoint crossing
edge. Two recursive calls recover the subpaths on either side of that edge.
Ties follow diagonal, left, then right in backward traceback, including
when the implementation swaps the working axes. The workspace is one row
of length `min(left.len(), right.len()) + 1` and logarithmic recursion
depth. The returned path uses space proportional to the input lengths.
For input lengths `m` and `n`, running time is `O(mn + m + n + 1)`.
Use the rectangular reference chart for audits.

## Conditions for exact results

A finite, deterministic source and an additive finite score with all
ordered sums representable in `i64` are sufficient for these recovery
routes. For an arbitrary scoring algebra, propagating a single optimum
requires monotonicity and the appropriate Bellman choice law. Preserving
every tie or ranking with child truncation uses strict monotonicity in
each child score with the other children fixed. If one child score improves,
the result must improve. Finite addition has this property, including
when rule weights are negative. A worse child can tie after a step that
absorbs to infinity or clamps a score. An exhaustive reference query can
recover those ties.

Signed integer addition is checked in the original child order. Early
choice can hide overflow on a discarded derivation. Exactness claims
therefore require representability even for discarded scores, including
intermediate partial sums. Use a mathematical bound or a reference audit on
the finite input domain. A successfully filled score table alone establishes
that its evaluated additions fit.

For the product laws and strictness conditions, see Steffen and Giegerich,
[Versatile and declarative dynamic programming using pair algebras](https://doi.org/10.1186/1471-2105-6-224).
