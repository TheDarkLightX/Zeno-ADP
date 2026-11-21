# Compiled grammar schedules

Use a built-in grammar's `*_source` function or declare a reusable
`compiled::Grammar` and bind it to input. Both yield a `compiled::Program`.
The program fills tables by visiting ordered productions directly.
`compiled::replay` exposes the cell rank, occurrence ordinal, clause name,
operator payload and ordered child ranks of every emitted production. Apply
`compiled::reference_chart` to evaluate a general algebra or run an audit
on the same ordered emissions.

## Declaring a sequence grammar

See [compiled_sequence.rs](../examples/compiled_sequence.rs) for a complete
example. Supply the nonterminal names, root, and production clauses in
derivation order. Each clause names one parent and lists its children in
constructor order. Each input track is a sequence of `Atom::Byte`,
`Atom::Any`, and `Atom::Child` symbols. Every child occurs once per track.
The tracks may place those children in different orders. A deterministic
constructor callback receives the inputs and matched half-open spans and
returns an operator with the declared number of children.

The supported layouts use one or two contiguous byte-sequence tracks.
Child spans are matched in increasing split order, track zero first. Span
ranks increase by length and then start on each track. Equal-span edges
follow a derived order of nonterminals. A declaration that would require a
cycle among those edges returns `Error::UnsupportedGrammar` with the name of
a blocked declaration. Minimum yields, emptiness and productivity
eliminate impossible partitions. Yield analysis can revise a provisional
oversized width when a shorter child yield becomes known. After the minima
settle, compilation returns `Error::Overflow` if a productive clause's
minimum on any track exceeds `usize`, even if another clause accepts a
shorter input. Clauses with unproductive children have no yield. Moving
clauses of different parents past each other preserves acceptance and
keeps each parent's declared alternative order.

Every logical cell retains its rank for inspection. On two tracks the number of span pairs is
the product of the two interval counts, including zero-length intervals.

Ranked layouts outside the sequence declaration model can use
`fast::RuleSource` with `fast::tabulate`, or `fast::reference_chart` and the
reference engine. The five built-ins bring their own ranked schedules.
Knapsack includes capacity as an auxiliary index. The built-in sources,
bound sequence grammars and `Chart` return `Error::CellOutOfRange` from
`rules_at` before calling the visitor with a missing rank. Dense score,
chart and last-use tables reserve their rank-indexed storage before
traversal and return `Error::AllocationFailed` if that layout cannot be
reserved. Arithmetic overflow in calculating a rank count is
`Error::Overflow`. Binding a source computes its logical layout and
can succeed when a particular dense table cannot be reserved.

## Questions and backtracking

- `Additive` and `Maximum` compute minimum and maximum. `Maximum` uses finite
  additive scores with checked arithmetic.
- `Count` counts derivation occurrences. Distinct term and canonical-model
  questions use the corresponding reference queries.
- `MinimumWithMultiplicity` keeps the minimum score, its derivation count and
  the total derivation count. Select `CostPolicy::AttainableInfinity` when an
  operator can produce an attainable infinite score.
- `fast::ScoreTrees` carries the co-optimal derivation bag while filling the
  table. `compiled::best` fills a finite minimum table and recovers the first
  minimum with `first_minimum_tree`, every minimum with `co_minimal`, or
  the `k_lowest` trees in a second phase. Recovery supports
  structural identity and derivation occurrences.
- Questions with arbitrary bag choice use `zeno_adp::tabulate` on the
  reference chart. Compiled evaluation requires a `fast::Fold` and identifies
  an unsupported algebra type through that trait bound.

Co-optimal recovery and ranking require strict monotonicity in each child
score. Finite addition meets that condition when all intermediate sums fit
in `i64` in rule order, including the sums of derivations removed by early
choice. Use the reference audit to check bounded inputs. Equal-ranked trees
retain derivation order. [Audits](AUDIT.md) · [Streaming and recovery](FAST.md)

For a root-only global alignment minimum, `compiled::alignment_rolling`
keeps the live predecessor scores and passes each finished score to an
observer. Pass `|_, _| {}` to use only the root. Use the full minimum table when you need random cell access or tree recovery.

For other compiled grammars, `compiled::tabulate_root` runs a preliminary
replay to find each cell's last scheduled reader, then evaluates all cells
in rank order. It retains live summaries and the root. The observer receives
every completed cell, including absent cells. An algebra error may follow
observations of earlier cells, including an earlier root. The schedule is
validated before the first observation.

Choose this mode when large summaries can be released early and only the
root is needed after the scan. It uses one rank-indexed last-use entry per
logical cell and performs two production traversals. Full tabulation can
be faster, especially for small summaries. The alignment rolling schedule
has a fixed bound from the shape of the recurrence.

The sequence matcher reuses its child-span and rank buffers for a schedule
traversal. The largest matched constructor arity bounds the buffer
length, and each successful match sets every coordinate it exposes.
