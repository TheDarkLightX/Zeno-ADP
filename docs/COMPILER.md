# Compiled grammar schedules

Use a built-in grammar's `*_source` function or declare a reusable
`compiled::Grammar` and bind it to input. Both yield a `compiled::Program`.
The program fills tables by visiting ordered productions directly.
`compiled::replay` exposes the cell rank, occurrence ordinal, clause name,
operator payload and ordered child ranks of every emitted production. Use
`compiled::reference_chart` to collect those emissions into a chart, then
pass the chart to `zeno_adp::tabulate` or `zeno_adp::audit_bounded`.

## Generating a schedule

`compiled_grammar!` expands a declaration into a Rust function that binds
a concrete slice to a compiled program. The clause loops and their child
positions are fixed at compile time. An optional `with fn` pairs the
program with a streaming algebra and generates a second function that
returns its table by calling the generated grammar function. Use
`with fn` at module scope or inside a function. The compiler rejects
it in traits and implementations. For an associated grammar, omit
`with fn` and call `compiled::tabulate(&Self::grammar(input)?, &algebra)`
in the evaluation method.

```rust
use zeno_adp::{compiled_grammar, Operator};
use zeno_adp::algebras::Count;

#[derive(Clone)]
struct Segments(usize);

impl Operator for Segments {
    fn arity(&self) -> usize { self.0 }
}

compiled_grammar! {
    fn segments(input: char) -> Segments {
        prefix |input, start, end|;
        empty Empty => Ok(Some(Segments(0)));
        extend Segment(split) => Ok((input[split] != ' ').then_some(Segments(1)));
    }
    with fn segment_count: Count = Count;
}

assert_eq!(segment_count(&['a', 'b', 'c']).unwrap().answer(), Some(&4));
```

Each clause supplies a Rust callback expression of type
`Result<Option<Op>, Error>`. The names inside the expression resolve in
the declaration's scope, with the input, bounds and split bindings shown
in the layout and clause. Bounds and splits have type `usize`. The
argument name in the function signature is available as a slice in the
paired algebra expression. `Some` emits its constructor and `None` skips
the occurrence. Operators and guards must be deterministic because a
schedule can be replayed.
The constructor's `Operator::arity` must agree with the clause shape.

| Layout | Cells in rank order | Allowed clauses and children |
|---|---|---|
| `prefix` | `[0, end)` by ascending end, starting at zero | `empty` has no children and runs at the empty prefix. `extend(split)` tries `0 <= split < end` with child `[0, split)`. |
| `interval` | `[start, end)` by ascending end, then descending start | `empty` has no children and runs at every empty span. `pivot(k)` tries `start <= k < end` with children `[start, k)` and `[k+1, end)` in that order. |

Declare each clause under a unique name. The order of clauses and their
ascending splits determines occurrence order, including repetitions from
different clauses. The root is the full input. Each layout includes empty
cells and cells whose guards admit no candidate. An unsupported layout or
clause shape produces a compile-time diagnostic naming the layout or
clause. Declare at least one clause. A clause returning `Ok(None)` can
represent an empty language. Use a sequence grammar when you need
multiple nonterminals or tracks.

Use the bound program with `compiled::tabulate` to ask a second streaming
question. Use `compiled::reference_chart` to inspect the ordered derivations
or run any reference algebra and the bounded audit. The two worked
examples include direct recurrences for comparison. Chart replay collects
the expansion's own emissions. The direct and generated BST recurrences
share the same interval-weight helper. The tests check emitted payloads
using sums of the raw frequencies and check BST scores by enumerating
trees and charging each key at its depth. The segmentation tests
compute rule costs and enumerate cut sets from raw observations. The
natural-number rank lemmas establish child descent and the interval
offset traversal's child ranks.
[Change-point detection](../examples/segmentation.rs) ·
[Optimal binary search tree](../examples/optimal_bst.rs)

## Declaring a sequence grammar

See [compiled_sequence.rs](../examples/compiled_sequence.rs) for a complete
example. Supply the nonterminal names, root, and production clauses in
derivation order. Each clause names one parent and lists its children in
constructor order. Each input track is a sequence of `Atom::Byte`,
`Atom::Any`, and `Atom::Child` symbols. Every child occurs once per track.
The tracks may place those children in different orders. A deterministic
constructor callback receives the inputs and matched half-open spans and
returns an operator with the declared number of children. Byte callbacks
receive `Matched<'_, TRACKS>`. Typed callbacks receive
`TokenMatched<'_, TRACKS, T>`.

For any token type implementing `Eq`, use `TokenGrammar`,
`TokenProduction` and `TokenAtom`. `TokenAtom::Equals` matches a
literal token. `TokenAtom::Predicate` takes a boxed deterministic
function of `&T` and can capture its configuration. `TokenAtom::Any`
and `TokenAtom::Child` work as on byte tracks. Each terminal consumes
one token. Token spans use element offsets into the supplied slices.
Predicates affect emission. Yield analysis treats every terminal as
one token and computes a structural lower bound even for a predicate
that always rejects. Matching, arity and payloads must repeat across
traversals.

The supported layouts use one or two contiguous sequence tracks of a
single `Eq` token type, including predicate-only grammars.
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
reserved. Sequence binding checks the complete rank count before
allocating track offsets. Count overflow returns `Error::Overflow`.
An offset reservation failure returns `Error::AllocationFailed`.
Binding a source computes its logical layout and can succeed when a
particular dense table cannot be reserved.

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

Table-based recovery relies on finite addition being strictly increasing
in each child score. Agreement with exhaustive scoring requires all
intermediate sums to fit in `i64` in rule order, including sums on
derivations discarded by early choice. Exhaustive root ranking accepts
any scorer with ordered values. Both interfaces keep derivation order for
ties. [Audits](AUDIT.md) · [Streaming and recovery](FAST.md)

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
