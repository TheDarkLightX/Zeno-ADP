# Changelog

## 0.1.0

This first release evaluates ranked tree grammars in Rust. Use the included
grammars for matrix chains, alignment, folding and knapsack, or define your
own. The same grammar can answer questions about scores, derivation counts,
Pareto fronts and weighted samples.

Recover a minimum-cost tree from a finite additive score table, or rank
root trees exhaustively with your own scorer. Both interfaces break score
ties in derivation order. A bounded audit checks an algebra on a chart
and reports duplicate terms separately.
[Ranking contracts](docs/QUESTIONS.md#ranking-trees)
