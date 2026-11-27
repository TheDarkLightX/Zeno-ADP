# Exact queries

Zeno-ADP uses algebraic dynamic programming (ADP) to evaluate tree grammars.
Here, ≈DP means approximate dynamic programming. Adaptive dynamic programming
is written in full.

**Exact** means the returned optimum or value has been checked against the
declared model. **Bounded** requires a checked feasible witness and a
deterministic optimality gap for the original problem. **Estimated** requires
a named method and an error and failure probability. **Unchecked** carries
no guarantee. `mdp::Model::solve`, `cyclic::GroundChart::solve` and
`decomposition::Compiled::solve` return checked `Exact<T>` results or an
error. Other ranked and approximate APIs retain their return types.

Read the wrapper label with `label()` and borrow the result with `as_ref()`.
For certificates with a replay method, use `into_inner()` to extract one for
storage or transfer. Keep the intended model separately and preserve its state
and action indices, cell-local production order, or ordered bag and edge
inputs. The replay methods below specify which inputs and questions they check.

`Common`, `ZeroRegret`, `WithinBudget` and `Quotient` also expose an associated
`LABEL` constant for their checked results. `ObserverCheck::label_for` gives the
assurance for a length against the scorer it checked. `Solved::scorer_label`
records the label against that scorer for the entire chart instance. The
`Exact<Solved>` wrapper refers to the chart's declared model. Raw collision,
feature-set, refutation and witness values get their assurance from replay with
their original inputs. `Strict` preserves every optimum within the declared
family, with the order and multiplicity required by the certificate's shape.

## Discounted Markov decision processes

`mdp::Model` has finite states, nonempty finite action sets, signed rational
immediate rewards, normalized rational transition rows and a rational
discount in `[0, 1)`. The objective maximizes the expected infinite sum of
discounted rewards. The policy selects one action per state. Zero
probabilities and repeated successor entries are accepted.

`solve` evaluates each policy by exact elimination and switches only to
strictly improving actions. `verify` checks the certificate against the supplied
model, including states outside the reach of any particular start. For every
state `s` and action `a`, it computes
`Q(s,a) = reward(s,a) + discount × Σ probability(t|s,a) × value(t)`.
It requires `Q(s,a) ≤ value(s)` for all actions and equality for the selected
action. For two value vectors, the change in each `Q` is bounded by the
discount times the largest coordinate change because probabilities sum to one.
This gives uniqueness of the Bellman value. The selected policy attains it.
A modified certificate can pass if it still certifies an optimum, for example
when it switches between tied optimal actions.

```rust
use zeno_adp::mdp::{Action, Model, Rational};

fn main() -> Result<(), zeno_adp::mdp::Error> {
    let half = Rational::new(1.into(), 2.into()).unwrap();
    let model = |reward: i64| Model::new(half.clone(), vec![vec![Action {
        reward: reward.into(),
        transitions: vec![(0, 1.into())],
    }]]);
    let answer = model(3)?.solve()?;
    assert_eq!(answer.label(), "Exact");
    let certificate = answer.into_inner();
    assert_eq!(certificate.policy, [0]);
    assert_eq!(certificate.values, [6.into()]);
    model(3)?.verify(&certificate)?;
    assert!(model(4)?.verify(&certificate).is_err());
    Ok(())
}
```

The solver stores a dense linear system and uses arbitrary-precision signed
rational arithmetic. The verifier scans the sparse transition rows. Average
reward, undiscounted reachability and stochastic shortest path, partial
observability and constrained policies require other models. For a finite
horizon with actions outside expectations, use the ranked
[expectimax recipe](COOKBOOK.md#finite-horizon-expectimax).

Policy iteration follows Howard. Ye analyzes its fixed-discount complexity.
Storm describes exact rational policy iteration. For certificates in related
undiscounted models, see Chatterjee et al. For mechanized MDP algorithms,
see Schäffeler and Abdulaziz.
[Howard](https://books.google.com/books/about/Dynamic_programming_and_Markov_processes.html?id=fXJEAAAAIAAJ) ·
[Ye](https://doi.org/10.1287/moor.1110.0516) ·
[Storm](https://doi.org/10.1007/S10009-021-00633-Z) ·
[Fixed-point certificates](https://doi.org/10.1007/978-3-031-90653-4_7) ·
[Verified MDP algorithms](https://doi.org/10.1609/aaai.v37i12.26759)

## Cyclic grammars

`cyclic::GroundChart` takes finite ground productions with arbitrary valid
cell dependencies. Ask for `boolean` to determine whether a finite
derivation exists, or `nonnegative-min-plus` for its minimum total weight.
Min-plus takes arbitrary-precision nonnegative integer production weights.
Boolean existence admits every rule regardless of its weight. `None` in the
certificate means there is no finite derivation. Parsing a question name
outside the two supported choices returns `UnsupportedCarrier` with that name.

```rust
use zeno_adp::cyclic::{GroundChart, Production, Question, Solution};

fn main() -> Result<(), zeno_adp::cyclic::Error> {
    let chart = GroundChart::new(vec![vec![
        Production::new(0u32.into(), vec![0]),
        Production::new(3u32.into(), vec![]),
    ]], 0)?;
    let answer = chart.solve(Question::NonnegativeMinPlus)?;
    let Solution::MinPlus(evidence) = answer.as_ref() else { unreachable!() };
    assert_eq!(evidence.values, [Some(3u32.into())]);
    assert_eq!(evidence.witnesses[0].unwrap().rule, 1);
    chart.verify(answer.as_ref())
}
```

In the semiring order the answer is the least fixed point from bottom,
aggregating all finite derivations. The evaluator puts ready productions
in an agenda and uses nonnegative weights to settle minimum costs. The
checker re-evaluates every grounded equation. At each inhabited cell it
also checks a production that attains the reported value and whose
children have smaller witness ranks. The rank condition excludes
self-supporting zero-cost cycles. A production keeps the order and
multiplicity of child occurrences, including two uses of the same cell.
Counting, sum-product, signed min-plus, user-defined closures and all-optimal
recovery need separate semantics and evidence.

The bottom semantics and the bound of at most `n` changing rounds for
`n` cells follow the 0-stable case of Abo Khamis et al. Zhao et al. discuss
grounded evaluation, including a Dijkstra-like route for ordered absorptive
semirings. Lehmann and Kozen give related closure results for matrix or
Kleene algebra settings.
[Convergence over semirings](https://doi.org/10.1145/3643027) ·
[Grounding-based evaluation](https://doi.org/10.1145/3651591) ·
[Algebraic transitive closure](https://doi.org/10.1016/0304-3975(77)90056-1) ·
[Kleene algebra](https://doi.org/10.1006/inco.1994.1037)

## Supplied tree decompositions

`decomposition::Compiled` minimizes signed additive unary and binary factors
over Boolean variables. A factor entry may forbid a local assignment. Supply
the bags, tree edges, root and the factor indices owned by each bag. Compilation
checks that every variable appears, the bags containing a variable form a
connected subtree, and each factor is owned by exactly one bag covering its
scope. Pair factors require two distinct variable IDs. Distinct factors may
have the same scope.

Each bag has a rank per local assignment and a message rank per assignment
to its separator with its parent. The message takes the minimum of bag rows
extending that separator. A separator mask assigns bits from least to most
significant in ascending order of shared variable IDs. A bag mask starts
with its separator bits and then assigns its other variable IDs in ascending
order. A bag row charges its owned factors and reads one indexed message
from each child in the child's separator order. Agreement on the separator makes joint
assignments consistent under running intersection. Empty separators
combine independent parts. `solve` uses the ranked fold and lifts one
global assignment when feasible. `verify` checks the submitted rows directly
from the bags and factors, using earlier checked rows for child sums and
separator minima. It uses the original factors to check witness feasibility
and score. The fold and the explicit ranked chart share the bag-to-rule
compiler. Use that chart for the Bellman audit.
An infeasible instance has an empty root value and no lifted assignment.
The module accepts supplied trees and optimizes a single additive objective.

Run the weighted independent-set example with
`cargo run --offline --locked --example separator_ladder`.
On the 2 × 64 ladder the supplied width-three path uses 1,008 bag-assignment
rows before local pruning. The whole binary assignment space has size
2^128. The example returns maximum weight 160. For work on solving and
finding tree decompositions, see Arnborg, Lagergren and Seese, and Bodlaender.
[Tree-decomposable graphs](https://www.sciencedirect.com/science/article/pii/019667749190006K) ·
[Treewidth recognition](https://doi.org/10.1137/S0097539793251219)

## Common optima across cost models

`common_optimum::common` takes a ranked `Chart` whose operators carry one
finite `i64` cost per model, through the `CostVector` trait or the plain
`Costed` operator. For any nonempty `ModelSet` it answers whether some
derivation of the root is optimal in every selected model, how many
derivations are, and which one has a given rank. Counts are derivation
occurrences and use `BigUint`. Costs are summed as `BigInt`.

At each cell the query keeps the rules whose cost plus their children's
optima equals the cell optimum in every selected model. With finite
additive costs, a derivation is optimal in a model exactly when every node
uses such a rule, so the restricted chart holds exactly the common optima.
The `Common` certificate records each cell's optimum per selected model
and its count of common optima. `verify` replays every cell equation for the
selection recorded in the certificate, and `verify_for` also checks that it is
the selection you asked about.
`witness(&chart, rank)` returns the common optimum of that rank in the
order of `enumerate`: rules in cell order, then child ranks with the first
child most significant. Both `witness` and `verify_witness` first validate the
shape and replay all recorded Bellman and count equations on the supplied
chart. `verify_witness` then re-parses the derivation, rescores it in every
selected model and recomputes its rank. Use `verify_for` to bind the certificate
to a caller-selected set of models.

```rust
use num_bigint::BigUint;
use zeno_adp::common_optimum::{common, Costed, ModelSet};
use zeno_adp::Chart;

fn main() -> Result<(), zeno_adp::common_optimum::Error> {
    let chart = Chart::new(vec![vec![
        Costed::rule([0, 0, 1], []),
        Costed::rule([0, 1, 0], []),
        Costed::rule([1, 0, 0], []),
    ]], 0).unwrap();
    // Each pair of models shares one optimum.
    let pair = common(&chart, 3, &ModelSet::new([0, 1], 3)?)?;
    assert_eq!(pair.as_ref().count(), &BigUint::from(1u32));
    // No rule is optimal in all three.
    let all = common(&chart, 3, &ModelSet::all(3)?)?;
    assert_eq!(all.label(), "Exact");
    assert!(!all.as_ref().exists());
    Ok(())
}
```

A model's minimum and tie count do not determine common optima. Charts
with rule costs `(0, 0), (1, 1)` and `(0, 1), (1, 0)` both report minimum
zero and one tie per model, yet have one and zero common optima.

### Keeping answers for later questions

Three summaries can answer later common-optimum questions about the same
chart. `Optima` keeps every cell optimum per model. `WinnerMasks` keeps one
bit per rule and model and needs only the chart's child lists to count.
`AnswerTable` keeps the root counts for a declared family of selections and
every singleton. `count_common_rescan` keeps nothing and recomputes.

| Kept | Payload | Counted work for one later question |
|---|---|---|
| Nothing | none | Evaluate each rule in each selected model, then count |
| `Optima` | Signed-magnitude values and inhabitation bits | Scan the rules of each cell reached through common winners |
| `WinnerMasks` | Rules × models bits | Visit only the common winning rules of the cells reached |
| `AnswerTable` | Each count's bit length | One lookup, after building every declared selection |

On 200 seeded random charts of 80 cells and 12 models, the masks used 1.89
times the unsigned payload of `Optima` (479,700 against 254,129 bits).
`Optima::unsigned_bits` applies to inhabited nonnegative tables. For general
tables, `Optima::storage_bits` uses one inhabitation bit per entry and
signed-magnitude for inhabited values. An entry containing `-1` takes
three bits. Over one random
pair query per chart, the masks visited 3,478 rules in total and `Optima`
scanned 3,966. Recomputing from nothing took 83,428 rule evaluations and
visits, and building a table of every pair and singleton took 277,420 rule
visits. The reported evaluation and counting work excludes validation passes.
In particular, `Optima::count_common` validates every rule's cost width, and
`WinnerMasks::count_common` checks the chart's shape. Both methods require the
same chart used to compute the summary, including rule order and costs. No mask
query visited more rules than the corresponding `Optima` scan. Run
`cargo run --offline --locked --release --example retention` to reproduce
these figures.

An answer table declines any unlisted selection. `AnswerTable::get` returns a
retained count, or `None`, and needs no budget. For an unlisted query,
`AnswerTable::answer` uses the caller's `CollisionBudget` to attempt a generic
collision. If it fits, `Error::NotRetained` carries two one-cell charts that
agree on the retained keys and differ on the new count. `Collision::verify`
compares those two charts. The pair refutes a uniform decoder from the retained
keys, regardless of the original table's counts. With `k` selected models
and `m` declared models in the collision, construction emits
`2 × (2^k + 1)` rules and initializes `m` costs per rule. A fresh model
extends the declared width of the generic pair. Both rule and cost-entry
limits apply before allocation. Masks without costs cannot answer a question about a later
cost change. Rule costs `0, 1` and `0, 2` have the same winner mask, but
lowering the second rule by one gives two ties in the first chart and one
in the second.

For one cell with `R ≥ 2` rules and an arbitrary nonempty tie set, a later
model whose only winner is rule `i` asks whether `i` is in the tie set. A
summary that answers every such question takes a different value on each
of the `2^R - 1` tie sets, so it needs at least `R` bits. A mask has `R`
bits. When the tie count `c` is already known, the bound is
`ceil(log2(C(R, c)))` bits. `WinnerMasks::conditional_bits` reports that
total, which was 0.32 times the mask payload on the charts above (153,400
bits). The bound
does not cover a fixed list of later questions, rescanning the costs, or
compressed codes across cells.

## Robust plan prefixes

`robust_prefix` takes a plan chart whose rules are steps to one child or
finishes, with a cost per world and a nonnegative credit for useful work.
Worlds share the same rules. A prefix is a rule sequence from the root,
possibly empty. In each world, `V(x)` is the least cost of finishing from
`x`. A rule's slack is its cost plus `V` of its child minus `V` of its cell.
Committing to a prefix and then finishing optimally costs the world's
optimum plus the sum of the prefix's slacks in that world.

`zero_regret` returns the prefix of greatest total credit whose rules have
zero slack in every world, the number of prefixes of that credit, the first
in prefix order (stopping before continuing, then rule order), and an
optimal completion in each world. It also reports whether a whole plan is
optimal in every world, with the first such plan as a witness.
`within_budget` returns the greatest prefix credit within the per-world budgets,
its tie count, the first maximizing prefix, its regret vector and one
completion per world. Whole-plan existence is answered by `zero_regret`.
`within_budget` tracks the remaining budget of each world separately. One shared budget is wrong. With a budget of 2 per
world, two steps with slacks `(3, 0)` and `(0, 3)` cost each world 3, yet a
shared budget charged by the smaller slack accepts them. Charged by the
larger slack, a shared budget of 2 refuses steps with slacks `(2, 0)` and
`(0, 2)`, which fit both worlds. Checking each step alone is also wrong: two
steps of slack 2 fit a budget of 2 one at a time, but together use 4.

```rust
use num_bigint::BigUint;
use zeno_adp::robust_prefix::{state_bound, within_budget, zero_regret, Step};
use zeno_adp::Chart;

fn main() -> Result<(), zeno_adp::robust_prefix::Error> {
    let chart = Chart::new(vec![
        vec![Step::finish([2, 2], 4), Step::finish([0, 0], 1)],
        vec![Step::to([2, 2], 4, 0), Step::finish([0, 0], 1)],
    ], 1).unwrap();
    assert_eq!(zero_regret(&chart, 2)?.as_ref().best_credit(1), 1);
    let budget = [BigUint::from(2u32), BigUint::from(2u32)];
    let limit = usize::try_from(state_bound(&chart, &budget)).unwrap();
    assert_eq!(within_budget(&chart, 2, &budget, limit)?.as_ref().best, 5);
    let budget = [BigUint::from(4u32), BigUint::from(4u32)];
    let limit = usize::try_from(state_bound(&chart, &budget)).unwrap();
    assert_eq!(within_budget(&chart, 2, &budget, limit)?.as_ref().best, 8);
    Ok(())
}
```

`verify` replays each world's cell equations, the credit and count
equations over zero-slack rules, the prefix and each completion. The
budgeted certificate's greatest credit is recomputed by a separate forward
search over per-world slack vectors, and its count and first prefix by the
budget program. A certificate answers the budget recorded inside it; use
`verify_for` to check that it is the budget you asked about.

Zero regret takes a number of big-integer arithmetic operations linear in
rules times worlds. An adversary argument, not a machine-checked proof, shows
that any exact method must read every cost of every world in the worst case.
The budgeted question contains 0/1 knapsack, with one world and a chain of
take-or-skip steps, so it is NP-hard. Its dynamic program visits at most one
state per cell and remaining budget vector, and `state_bound` gives that
number: the cells times the product of `budget[w] + 1`. The caller's
`max_states` bounds pending frames plus memoized states in each budget DP
pass, with one slot per distinct state. In the separate forward pass it
bounds all live slack labels, including those at the cell being processed.
Passes use separate state stores. A zero limit or an admission beyond the
limit returns `Error::StateLimit`.

## Explicit history state

`state_discovery` finds the coarsest quotient of a reachable raw model for
operation words. A scorer gives each word a score. Declare an
`Observer` of histories that is assumed sufficient: `Observer::last_symbols`
keeps the last `k` operations, and `Feature::library` builds the product of
feature automata such as "the last operation" or "the parity of mismatches".
`RawModel::read` asks the scorer for the empty word, the shortest word
reaching each observer state, and each one-symbol extension. With `n`
reachable states and `s` symbols, it asks `n × s + 1` distinct words. The
same count is an information lower bound in the additive parameter model
with an independent, unbounded base and one independent, unbounded gain per
reachable state and symbol. Each query supplies one linear equation in those
parameters.

`RawModel::check(&mut scorer, length)` compares the model with the supplied
scorer on every word up to that length. On success it asks the scorer once
per word, including the empty word and the read's cached words within that
length. A disagreement with a cached answer returns `Error::ScorerDisagrees`.
The check validates scores through the declared length. The coarsest-state
claim refers to the reachable raw model.
A successful check makes `1 + s + … + s^length` calls in addition to the read's
`n × s + 1` calls. Of those calls, `n × s + 1` recheck the read's words when all
of them are within the checked length.

If the observer is too coarse, the check returns a `Violation` naming two
words that reach one observer state and a symbol whose score change differs
after them. For a last-k observer, a scorer whose changes depend on its last
`k'` operations and not only on its last `k` is refused by a check of length
`k' + 1`. Other observers can pass a short check and fail a longer one. A
black-box scorer that agrees on every checked word can differ on a longer
one.

Only a check makes an `ObserverCheck`, and it remembers the raw model it
ran on. `StateChart::solve` takes the `Exact<ObserverCheck>` and labels the
answer **Exact** against the checked scorer only when the check ran on the
raw model the chart was built from and every candidate word of the instance
is within the checked length; otherwise the label is **Unchecked**. Against
the declared observer the answer is always **Exact**. `Violation::replay`
and `Refusal::replay` check symbols or states against the model.
`Violation::replay` also checks that both probed extensions fit the recorded
length.

`RawModel::quotient` merges observer states that agree on every future score
change, by partition refinement, and returns an `Exact<Quotient>`; only such a
verified class table has a `chart`. An edited `Quotient` is charted again after
`Quotient::checked(&raw)` verifies it. The `Quotient` certificate lists each
state's class, each class's score change and successor class per symbol,
and probe words whose score changes tell every two classes apart.
`Quotient::verify` replays both conditions against the raw table. Together
they make the quotient the coarsest partition that keeps every score.
`RawModel::merging` admits or refuses proposed merges one at a time: a merge
is admitted with every merge it forces, or refused with a probe word.
`minimum_feature_sets` returns the smallest feature sets whose values can
serve as chart state, with a collision for every smaller set, and
`FeatureSets::verify` replays the collisions, checks their coverage
by subset counts, and streams candidates of the stated size. Set
`FeatureSetBudget` for generation to limit the number of subset tests and
the peak logical slots retained for findings. Pass `max_candidates` to
verification to cap collision replays and streamed subset tests together.
Each subset test can scan the raw states and their symbol transitions.

The `chart` method of a verified quotient builds a chart over
`(geometry cell, class)` pairs for a `Geometry` such as `Alignment`.
`StateChart::solve` returns the best score, the number of optimal move
derivations, and the word of the first one. When each word determines its
move derivation, as in `Alignment`, this is also a word count. A geometry's
reachable pairs must form a finite acyclic chart with stable, in-alphabet
moves. Maximizing refuses an `i64::MIN` base or gain used by a rule. On every pair of binary strings
of length at most four, a scorer whose gains depend on the last two
operations needed 7 of its 21 history states. Its chart had 40,473 cells
against 71,753 for the 21-state chart, summed over those pairs
(`tests/state_discovery.rs` reproduces both counts). Affine gap scoring reduces to the
three states of Gotoh's algorithm at every declared horizon from one to
three.

```rust
use zeno_adp::state_discovery::{Alignment, Observer, RawModel, Sense, Symbol};

fn main() -> Result<(), zeno_adp::state_discovery::Error> {
    // Affine gaps: open -3, extend -1; match 2, mismatch -1.
    let affine = |word: &[Symbol]| -> i64 {
        word.iter().enumerate().map(|(n, &op)| match op {
            Alignment::MATCH => 2,
            Alignment::MISMATCH => -1,
            _ if n > 0 && word[n - 1] == op => -1,
            _ => -3,
        }).sum()
    };
    let mut scorer = |w: &[Symbol]| affine(w);
    let mut raw = RawModel::read(Observer::last_symbols(Alignment::SYMBOLS, 2)?, &mut scorer)?;
    let check = raw.check(&mut scorer, 6)?;
    let quotient = raw.quotient()?;
    assert_eq!(quotient.as_ref().classes(), 3);
    let chart = quotient.chart(&Alignment { x: b"GAT", y: b"GT" }, Sense::Maximize)?;
    let best = chart.solve(Some(&check))?.into_inner();
    assert_eq!(best.score, 1);
    Ok(())
}
```

Moore's partition refinement and the Myhill–Nerode theorem give the
coarsest congruence. Hopcroft and Karp's union-find closure decides merges.
Gotoh gives the three-state affine gap recurrence.

## Verification scope

The Rust differential checks are finite. Common optima were compared
with enumeration of every derivation on 286 of 300 random five-cell chart
draws. The test's 5,000-derivation cap skipped 14 charts. It checked 4,290
selections of four models in total, including every ranked common witness. Robust
prefixes were compared with enumeration of every plan on 400 random plan
trees and layered graphs, for zero regret and a random budget per world,
and knapsack reductions with brute force. History quotients were compared
with enumeration of every alignment on all pairs of binary strings of
length at most four. The 128 generated discounted runs
cover 126 distinct models with 1–6 states against all stationary deterministic
policies in each model. The 128 generated cyclic runs cover 96 distinct
weighted charts and 89 Boolean structures with 1–4 cells against all
derivations through the cell-count height. The 32 generated short ladder
runs cover 19 distinct weight grids against raw subset enumeration.
A 64-column ladder is checked against a raw column recurrence and the
ranked reference. The boundary tests compare every cell on 91 grids of zero,
one or two columns using the minimum, zero and maximum `i64` weights.
Debug and release runs use the same grids. The separator permutation grid
checks every rank on 768 combinations of factor permissions and roots.

Lean checks that a class table satisfying the closure conditions keeps
every word's score, that a closed and separated table is the coarsest such
table, that a check up to length `L` fixes every score up to `L`, that a
too-short horizon fails by the true horizon plus one, and that no finite
check certifies a horizon. It checks that restricting each cell to the
rules that attain the optimum in every selected model keeps exactly the
derivations optimal in all of them, in order and with multiplicity, and
the tie-set storage bound. It checks that prefix regret is the sum of
slacks. Lean also checks mathematical models of cyclic bounds and ranked attainment,
discounted policy prefixes and uniqueness under a contraction premise,
local assignment gluing, and uniqueness of ranks checked against equations
over earlier ranks. The Rust results are proved, by exhaustive check, to match the policy,
tree and assignment oracles above. The Rust–Lean bridge covers earlier ranked
charts.
[Lean declarations](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.8.0/verification/ExactProfiles.lean) ·
[Quotient model](../verification/MetaQuotient.lean) ·
[Common-optimum model](../verification/MetaCommon.lean) ·
[Robust-prefix model](../verification/MetaRobust.lean)
