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
concrete inputs to a compiled program. The prefix and interval clauses
fix their loops and child positions at compile time. An optional `with fn` pairs the
program with a streaming algebra and generates a second function that
returns its table by calling the generated grammar function. Use
`with fn` at module scope or inside a function. The compiler rejects
it in traits and implementations. Rustc reports
`const items in this context need a name` and identifies the expansion
of `__with_fn_requires_module_or_block__omit_with_fn_and_call_compiled_tabulate`
in its diagnostic. For an associated grammar, omit `with fn` and call
`compiled::tabulate(&Self::grammar(input)?, &algebra)` in the evaluation
method.

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
represent an empty language. Use a sequence grammar for multiple nonterminals or contiguous
intervals on several tracks.

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

## Other generated layouts

| Declaration in the function body | Inputs and cells | Productions |
|---|---|---|
| `forest edit;` | Two slices of `forests::Node<L>`, where `L: PartialEq`. Cells pair valid preorder spans. | Promotion and first-root matching. Counts describe scripts. Use `forests::edit_reference` for edit mapping counts and audits. |
| `forest alignment;` | The same paired forest spans. | Match first roots or align one root to a gap at a sibling boundary. |
| `set_partitions \|block\| => predicate;` | `u32` carrier size and one cell per subset mask. | Empty partition or a block containing the least member. The predicate is evaluated once per nonempty mask in increasing order. |
| `prefix_tracks N \|tracks, ends\|;` | `[&[T]; N]` for positive `N`, with one cell per prefix tuple. Rank is row-major with the last track fastest. | `empty` at the origin and `step Name [flags]` for a nonempty subset of tracks. Each true flag takes one token and the clause has one child. |
| `mcfg SYMBOLS; start START;` | One byte slice, with a reachable item per nonterminal and ordered tuple of component spans. | `production Name(matched): parent, children, patterns => operator;`. Each child component must appear exactly once. |

MCFG child lists and component patterns are typed Rust expressions.
Supply `Vec<Nonterminal>` and `Vec<Vec<mcfg::Atom>>`. The grammar validates
linearity and rank constraints when bound. The compiled matcher lowers
fixed-width terminals and variable positions before discovering reachable
items.

The corresponding function headers are `fn name(left, right: L)` for
forests, `fn name(elements: u32)` for partitions, and `fn name(input: T)
-> Op` for prefix tracks. An MCFG uses `fn name(input: u8) -> Op` and
accepts the same symbol, child and pattern definitions as `mcfg::Grammar`.
The macro's production body receives an `mcfg::Matched` and returns the
operator. The bound program's `item(rank)` recovers semantic coordinates.
Use `mcfg::compile(&grammar, input)` to reuse a previously checked schema.
The reachable schedule holds compact structural occurrences and calls
operator constructors during evaluation or replay.

```rust
use zeno_adp::{algebras::Count, compiled_grammar};

compiled_grammar! {
    fn partitions(elements: u32) {
        set_partitions |block| => block.count_ones() <= 2;
    }
    with fn count: Count = Count;
}

assert_eq!(count(3).unwrap().answer(), Some(&4));
```

Set and forest declarations stream the built-in ordered productions. A
prefix-track step takes Boolean flags in track order. Its callback receives
the track slices and the parent prefix ends. Return `Ok(None)` to suppress
that occurrence. An all-false step is refused by its site name during
binding. The prefix-track and full interval layouts both check their full
rank count before allocating table storage. Each layout grows as a product
of its per-track cell counts.

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

The sequence compiler accepts a positive number of contiguous tracks of
a single `Eq` token type, including predicate-only grammars.
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

Every logical cell retains its rank for inspection. The number of span tuples is
the product of the tracks’ interval counts, including zero-length intervals.

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

Use `compiled::tabulate_selected` for several outputs from one fold. It
retains the union of the requested ranks and their still-live summaries,
and returns the peak number of inhabited summaries stored after completing
a cell. Duplicate requests share one stored value. It still evaluates
every cell, preserving all observations and evaluation errors.

Use `compiled::tabulate_joint` for two independent folds. Pass one
`(&algebra, ranks)` pair per fold. Each returned projection keeps that
algebra's answers at its requested ranks. For example, request the minimum
at the root and the derivation count at a different rank. The two folds
share schedule validation and last reads. Each still applies its own
operations and choice in production order at every cell. The observer
sees both answers as each cell finishes. To keep the full pair at a rank,
request it on both sides. To keep every pair, request all ranks on both
sides. A retained absence is `None`.

The joint peak counts inhabited values present across both projections
after completing a cell. The rank-indexed last-use vector, request
metadata, and temporary operator values have separate storage. The
projection preserves independent queries on the same grammar. A
lexicographic choice or a count conditional on the optimum requires its
corresponding algebra.

All compiled table modes use the [`Fold` contract](FAST.md#ask-a-question).
Each application receives the exact ordered child sequence, including
repeats. A rule with an absent child skips application. The fold must
depend on the operator, child values and ordered contributions. Keep
constructors and folds independent of callback order across cells and
thread identity.

`compiled::tabulate_parallel` is experimental. Pass a nonzero worker
count and use shareable constructors and folds. The function returns
the original rank order and visits each cell's alternatives in source
order. With storage available and callbacks that return normally, source
errors take precedence, followed by the lowest failing evaluation rank.
An application error precedes a merge error in the same cell.

One worker uses `compiled::tabulate`. Larger teams reuse scoped workers
across waves. Global alignment fills rectangular tiles in anti-diagonal
waves. Nussinov and generated single-track intervals use length waves.
These layouts skip planning replay and replay in rank order on a returned
error. A callback panic can unwind first, even when an earlier rank
would return a source error. Worker panics resume with their original
payload when received. Panic order follows dispatch and can vary with the
layout and worker count.
Other programs replay to discover dependency levels before evaluation.
A wave with one task runs on the caller.

The scoped-worker scheduler was benchmarked on eight CPUs of an AMD
Threadripper 1950X. Each speedup divides the median one-worker time by
the median time at that worker count, using five runs per count.

| Workload | 2 workers | 4 workers | 8 workers |
|---|---:|---:|---:|
| Global alignment, 3,000 × 3,000 tokens | 0.22× | 0.32× | 0.37× |
| Nussinov, 700 bases | 1.28× | 1.99× | 2.33× |

The sequence matcher reuses its child-span and rank buffers for a schedule
traversal. The largest matched constructor arity bounds the buffer
length, and each successful match sets every coordinate it exposes.
