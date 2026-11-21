# Evaluating and auditing a grammar

Implement `Operator` on an enum of your constructors and payloads. Compile each input into a `Chart` using `Rule::new`. Cells have ranks equal to their indices and each child index must be earlier than its parent. `Chart::new` checks this rule and constructor arity. A closure returning a chart implements `Grammar`.

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

For built-in grammars, `fast` returns a finite additive minimum and a table of
cell scores in the same order as the reference chart. This path evaluates
without allocating a chart. Use the chart for tree queries, other algebras
and audits.

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

let chart = matrix_chain(&[10, 30, 5, 60])?;
const DEMO_BUDGET: usize = 100; // This two-bracketing chart needs 19 nodes.
let report = audit_bounded(
    &chart,
    &Additive::default(),
    AuditBudget { max_tree_nodes: DEMO_BUDGET },
    AnswerOrder::Ordered,
)?;
if let Some(failure) = report.bellman.first_failure {
    eprintln!("Bellman counterexample: {failure:?}");
}
for ambiguity in report.ambiguities {
    eprintln!("Duplicate term: {ambiguity:?}");
}
# Ok::<(), zeno_adp::Error>(())
```

The audit independently builds and interprets every derivation in every cell. It checks the actual production arguments with and without child choice, checks merging the chart's alternatives with and without per-alternative choice, and compares each cell's exhaustive answer with reference tabulation. A mismatch includes the first failing law and cell, the rule index and constructor for an operation failure, the differing answers and the original term occurrences. Inspect the supplied chart at the named cell for any grouped merge failure. The ambiguity check separately reports a repeated constructor term with two derivation indices at each ambiguous cell. A grammar can be ambiguous even when every Bellman comparison passes.

Ordered comparisons are the default. Use `AnswerOrder::Unordered` only when your question and operations treat order as irrelevant. It compares bags with multiplicity. Both modes feed the algebra the same ordered inputs.

`Ok(report)` means the audit finished. `report.bellman.first_failure == None`
records Bellman agreement for the supplied chart, algebra, arithmetic,
choice and equality. Inspect `report.ambiguities` separately. Establish separately that your grammar generates the intended candidates. Test any representation or input change on its own scope. The size budget charges the number of constructor nodes across all raw derivations in all cells before expansion. It is a structural budget. Choose inputs and limits appropriate for the cost of your algebra, the available memory and the size of intermediate answers. `AuditBudgetExceeded` and `AuditEvaluation` signal an incomplete check.

The [executable Bellman model](../verification/README.md) formalizes the
laws for exact arithmetic and compares the corresponding answers with the
Rust reference on complete short domains. Use the reference audit for
bounded inputs with custom operators, products or arithmetic conditions.
