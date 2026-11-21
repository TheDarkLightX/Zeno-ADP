# Evaluating and auditing a grammar

Implement `Operator` on an enum of your constructors and payloads. Build
each production with `Rule::new` and collect the productions by cell.
Pass those cells and the root index to `Chart::new`, which checks each
constructor's arity and requires each child index to precede its parent.
A closure of type `Fn(&I) -> Result<Chart<O>, Error>` implements `Grammar<I>`
when `O` implements `Operator`.

Implement `Algebra::apply` to interpret one constructor and `Algebra::choose` to select or aggregate values. Both functions should be deterministic and free of side effects. On an empty candidate bag, return an empty bag. An empty cell means there are no candidate trees. An operator with zero children contributes one argument tuple. A rule with an empty child contributes zero argument tuples.

## Score and execution claims

`run` evaluates a grammar and input together. `exhaustive` evaluates each
root derivation in constructor argument order and calls the algebra's
chooser once at the root. A discarded derivation can overflow before
choice. `tabulate` and `tabulate_cells` evaluate all ranks, including ranks
unreachable from the root. A root query can therefore return an error in
an unreachable cell. Compiled and streaming tables also visit all ranks.
Streaming interleaves source validation and evaluation.

Early choice can give the mathematically correct score on its executed
paths even when exhaustive Rust evaluation returns an arithmetic error.
For example, adding one over child scores zero and `i64::MAX` yields early
minimum one. End-only evaluation must also add one to `i64::MAX`.
To claim equality of successful evaluations, require representable ordered
intermediates and successful choice on the full bags for the cells under
comparison. A reference audit checks both sides at all ranks for its input.

`queries::minimum` offers reference and scalar tabulation. It represents
absence as `None`. `Additive::default()` requires finite costs. `Minimum`
and `Additive::new(CostPolicy::AttainableInfinity)` both absorb a whole
rule to infinity if any operand is infinite. For an all-finite rule, each
ordered partial sum, starting from the operator cost, must fit in `i64`.

See the [query table](QUESTIONS.md) for arithmetic, identity, ranking and
audit choices.

For built-in grammars, functions such as `fast::matrix_chain` return a
minimum score table in reference chart order. Call `minimum()` for the
root or `cells()` for every rank. This path evaluates finite additive costs
without allocating a chart. Use a reference chart for an exhaustive audit.

`Product::new(left, right, choose)` interprets each constructor separately on the two components and sends the paired values to the supplied chooser. `lexicographic_min` is one such chooser. Audit the product with its own paired choice. Each lexicographic constructor must preserve lexicographic order in each paired argument for the usual Bellman justification. Separate component audits can both pass even when the product fails. `MinimumWithMultiplicity` reports additive minimum, optimal derivations and total derivations. `MinimumCount` returns only score and optimal derivation count and rejects infinity when evaluated. The total in `MinimumWithMultiplicity` allows an absorbing rule to recover every tied derivation when a cost becomes infinite. Its counts are occurrence counts. Use `co_minimal` with distinct identity when you need the distinct optimal trees on an ambiguous grammar.

## Distinct answers by canonical model

Implement `Classification` when you need to identify answers by a domain
representation such as dot-bracket strings or alignment columns. Each
constructor computes a canonical key from its payload and its children's
keys. `Classes::new(classifier)` lists distinct keys in their natural order.
The length of that list is the distinct-answer count.

Use `Classified::new(classifier, question)` to apply the question within each
class. With `Additive`, each nonempty class contributes its minimum score.
To rank classes by those minima, sort the returned pairs by score. The
product returns classes in key order and gives each class's choice
the ordered bag of values with derivation multiplicity. A class can yield
zero or several pairs. When child keys are regrouped into a common parent
class, their sorted order can change an order-sensitive choice. Audit the
product with ordered equality when order affects the answer. `Classified` with
`Count` therefore returns the number of derivations in each class.

Call `audit_bounded_classified` with the product and `product.classes()` to
check its Bellman behavior and the canonical model's injectivity over all
raw derivations in each cell. The injectivity check reports the first repeated
class by key order, its total occurrence count and two witness terms with
their derivation indices. When every class in the root has one derivation,
the derivation count equals the distinct-class count for that input.
Classification collisions and Bellman counterexamples can occur independently.
The [folding](../examples/fold_classes.rs) and
[local alignment](../examples/local_alignment.rs) examples show both uses.

## Checking Bellman's principle

Call `audit_bounded` on each input in the finite domain you want to check.

```rust
use zeno_adp::algebras::Additive;
use zeno_adp::grammars::matrix_chain;
use zeno_adp::{audit_bounded, AnswerOrder, AuditBudget};

fn main() -> Result<(), zeno_adp::Error> {
    let chart = matrix_chain(&[10, 30, 5, 60])?;
    let report = audit_bounded(
        &chart,
        &Additive::default(),
        AuditBudget { max_tree_nodes: 100 },
        AnswerOrder::Ordered,
    )?;
    assert_eq!(report.tree_nodes, 19);
    assert!(report.bellman.first_failure.is_none());
    assert!(report.ambiguities.is_empty());
    Ok(())
}
```

The audit independently builds and interprets every derivation in every cell. It checks the actual production arguments with and without child choice, checks merging the chart's alternatives with and without per-alternative choice, and compares each cell's exhaustive answer with reference tabulation. A mismatch includes the first failing law and cell, the rule index and constructor for an operation failure, the differing answers and the original term occurrences. Inspect the supplied chart at the named cell for any grouped merge failure. The ambiguity check separately reports a repeated constructor term with two derivation indices at each ambiguous cell. A grammar can be ambiguous even when every Bellman comparison passes.

Ordered comparisons are the default. Use `AnswerOrder::Unordered` only when your question and operations treat order as irrelevant. It compares bags with multiplicity. Both modes feed the algebra the same ordered inputs.

`Ok(report)` means the audit finished. `report.bellman.first_failure == None`
records Bellman agreement for the supplied chart, algebra, arithmetic,
choice and equality. Inspect `report.ambiguities` separately. Establish separately that your grammar generates the intended candidates. Test any representation or input change on its own scope. The size budget charges the number of constructor nodes across all raw derivations in all cells before expansion. It is a structural budget. Choose inputs and limits appropriate for the cost of your algebra, the available memory and the size of intermediate answers. `AuditBudgetExceeded` and `AuditEvaluation` signal an incomplete check.

## Verification scope

For a finite ranked chart with total operations, equality of the tabulated
answer and exhaustive choice is proved at every in-bounds rank if the
Bellman laws hold there. Three sufficient conditions are that choice
preserves the empty bag, choosing each of two bags before merging them
preserves the final choice, and choosing each child's bag before applying
a constructor preserves the final choice over its results.
[Tabulation theorem and premises](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.4.0/verification/BellmanTabulation.lean)

The Rust reference table was finite checked against the mathematical table
after grammar emission on the following domains. Length bounds include
both endpoints.

| Chart | Inputs | Charts |
|---|---|---:|
| Nussinov folding | Every A/U sequence of length 0–6, minimum loop length 0 | 127 |
| Global alignment | Every ordered pair of A/C sequences, each of length 0–4 | 961 |
| Local alignment | Every ordered pair of A/C sequences, each of length 0–3 | 225 |
| Matrix chain | Every list of 2–6 dimensions, each 2 or 3 | 124 |
| Knapsack | Every list of 0–4 items with (weight, value) equal to (1, 1) or (2, 3), at each capacity 0–4 | 155 |
| Four-cell fixture | Two leaf slots independently absent or cost −1, 0, 1 or ∞. A third leaf is absent or costs 0 or ∞. The binary and ternary rules independently cost 0 or ∞. | 300 |

Across those 1,892 charts and 28,380 ranks, the five answers compared were
derivation count, ordered enumeration, minimum, minimum with optimal and
total counts, and lexicographic minimum. Enumeration replaced distinct
constructor payloads with IDs. Lexicographic minimum used a secondary
additive cost derived from the ID and omitted infinite-weight rules.
For a new grammar or algebra, run the bounded audit on its own inputs.
[Verification sources](https://github.com/TheDarkLightX/Zeno-ADP/tree/v0.4.0/verification)
