# Cookbook

Run the examples together with `cargo run --example cookbook`. Each
recipe compares a grammar and its answer algebra with a direct calculation
on the input. The checks use short inputs so they can also inspect
individual candidates. In the output, a *fast value comparison* compares
one compiled or specialized table value with the reference evaluator at
the same rank, including empty cells. Run the same assertions with
`cargo test --example cookbook`.

The direct calculations read the raw inputs. Some checks share model
constants, exact rational arithmetic, or the library's rank-to-coordinate
mapping. The tables describe which checks use independent recurrences
or enumeration, and which compare two library evaluators.

## Intervals

| Recipe | Model and independent check |
|---|---|
| [Arithmetic parenthesization](../examples/cookbook/intervals.rs) | Declare typed operand and operator tokens. A constructor combines the four pairs of child extrema for addition, subtraction or multiplication. Enumerate splits directly over the raw operands to check extrema, count and term values. |
| [Minimum matrix-chain work](../examples/cookbook/intervals.rs) | Give each split a scalar multiplication cost from the three dimensions it joins. Recompute interval minima and price the recovered tree using the original dimensions. |
| [Matrix work and memory](../examples/cookbook/intervals.rs) | Keep a Pareto set of scalar work and peak live elements. Input matrices are loaded when used, and a multiply allocates its output before releasing both inputs. Simulate both evaluation orders for every tree. Keeping just the lowest local peak can lose the cheapest solution at the final peak. |
| [Optimal search tree](../examples/cookbook/intervals.rs) | Try each key as a root. Successful lookup costs weight each key by its depth, with depth one at the root. Check every interval from the original frequencies and check the witness's in-order key sequence. |
| [Equal wings around a center](../examples/cookbook/intervals.rs) | Require at least one pair of adjacent reversed flanks around a nonempty center. The center may contain any text. Check the grammar's outer-to-inner expansion by starting at every center and expanding outward. |

## Alignment

| Recipe | Model and independent check |
|---|---|
| [Global alignment](../examples/cookbook/alignment.rs) | Ask for the minimum, its derivation count and the first few derivations in increasing cost. Check all prefix scores and ties by rectangular recurrence, then check ranked witnesses by enumerating column paths. |
| [Local alignment with starts](../examples/cookbook/alignment.rs) | A start has input coordinates. Charge a matching column −2 and every other column 1. There is one empty root candidate. Check endpoint costs with a reset-to-zero table and verify positional paths by enumerating substring pairs. |
| [Affine gap runs](../examples/cookbook/alignment.rs) | Remember whether the last column was diagonal, a left gap or a right gap. A new run costs 3 and each extension costs 1. A switch between gap directions opens a new run. Score raw column paths by grouping maximal gap runs. |
| [Semiglobal infix match](../examples/cookbook/alignment.rs) | Leave both target flanks free. Bind one affine core to each target interval, including the empty intervals, and retain the best interval coordinates. Check the complete ordered interval row by enumerating raw substrings separately and scoring their column paths. The empty pattern against `a` has score zero and locations `(0,0)` and `(1,1)`. |
| [Three-way alignment](../examples/cookbook/alignment.rs) | The prefix macro declares each nonempty subset of advancing tracks. The column cost is the sum over pairs, with zero for a pair of gaps. Compare score and count with a three-dimensional prefix recurrence. |
| [Edit trade-offs](../examples/cookbook/alignment.rs) | Keep nondominated vectors of substitutions, insertions and deletions with a derivation count per vector. Translation by the same column increment preserves strict dominance. Check the three-coordinate counts with a raw path histogram. Count substitutions and gap columns directly to check the two-objective front. A single mismatch gives `(0,2)` and `(1,0)`. |

## Weighted sequence models

| Recipe | Model and independent check |
|---|---|
| [Hidden dice](../examples/cookbook/weighted.rs) | One rank per observation position and final die state. Sum-product measures likelihood, max-product tracks the best path weight, and inside–outside weights give state visits. Check exact fractions with direct forward and backward recurrences and path enumeration over explicit face lists and a transition matrix. The likelihood of `aa` is `9/32`. Sampling tickets check the branch boundary after one roll. |
| [Weighted span parsing](../examples/cookbook/weighted.rs) | Two weighted terminal productions compete in each recognized span. Binary splits and an acyclic start alias complete a parse. Compare compiled inside–outside with the reference, then enumerate raw splits to check summed weights, maximum weights and marked-span masses. |

## Forests

| Recipe | Model and independent check |
|---|---|
| [Ordered forest alignment](../examples/cookbook/forests.rs) | Align the roots or align one root to a gap and split the other forest at a sibling boundary. Recurse on the raw child and sibling lists for the minimum. Compare counts between library evaluators and project the recovered superforest onto both original forests. |
| [Promoting tree edit mappings](../examples/cookbook/forests.rs) | Deleting a root promotes its children. Check the cut grammar against retained subsets in preorder, preserving ancestry and order. Check shortest scripts separately by branching over next operations. Two opposite deletion orders can give the same mapping. |

## Graphs

| Recipe | Model and independent check |
|---|---|
| [Hamiltonian paths and edge mass](../examples/cookbook/routes.rs) | Rank states by visited set and endpoint. Use exact inside–outside to sum masses for directed edges and endpoints. The direct subset recurrence extends paths forward, and directed permutations check root cost and masses. A zero partition gives no distribution. |
| [Anchored tours](../examples/cookbook/routes.rs) | Start at vertex zero and require a closing edge. A singleton costs zero and uses no edge. Compare the full subset table and enumerate permutations returning to the anchor. |

## Discontinuous languages

| Recipe | Model and independent check |
|---|---|
| [Repeated halves](../examples/cookbook/languages.rs) | An MCFG constructor grows two equal spans at once. Concatenate them at the root. Check against direct slice equality and decode the recovered witness. Accept empty input through a separate nullary case. |
| [Cross-serial runs](../examples/cookbook/languages.rs) | Interleave two span pairs to recognize `a^m b^n c^m d^n`. Give absent runs their own alternatives. Scan the four raw runs independently and recover their lengths from the term. |

## Pairing structures

| Recipe | Model and independent check |
|---|---|
| [Noncrossing paired-count folding](../examples/cookbook/structures.rs) | On short A/U strings, minimize negative pair count at a chosen loop minimum. Compare a rightmost-position recurrence and enumerate noncrossing pair sets to check their identities and counts. |
| [Folds by shape](../examples/cookbook/structures.rs) | Remove unpaired positions from dot-bracket notation and evaluate score, count and exact weight within each remaining shape. A separate audit shows the multiplicity of a redundant production. The weights are illustrative. |
| [Two crossing pairs](../examples/cookbook/structures.rs) | Build two pairs with ordered endpoints `i < j < k < l`, paired as `(i,k)` and `(j,l)`. Each endpoint must match its partner. Use an explicit ranked chart and test it by enumerating four-element subsets. Other positions stay unpaired. |
