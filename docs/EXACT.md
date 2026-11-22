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

Read the label with `label()` and borrow the certificate with `as_ref()`.
Use `into_inner()` to extract the raw certificate for storage or transfer.
Keep the intended model separately and reconstruct it at the destination.
Then pass the received certificate to that model's `verify(&certificate)`.
Preserve state and action indices, cell-local production order, or the
ordered bag and edge inputs, as applicable. Successful replay establishes
the result for the model supplied to `verify`.

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

## Verification scope

The Rust differential checks are finite. The 128 generated discounted runs
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

Lean checks mathematical models of cyclic bounds and ranked attainment,
discounted policy prefixes and uniqueness under a contraction premise,
local assignment gluing, and uniqueness of ranks checked against equations
over earlier ranks. The Rust results were finite checked against the policy,
tree and assignment oracles above. The Rust–Lean bridge covers earlier ranked
charts.
[Lean declarations](https://github.com/TheDarkLightX/Zeno-ADP/blob/v0.7.0/verification/ExactProfiles.lean)
