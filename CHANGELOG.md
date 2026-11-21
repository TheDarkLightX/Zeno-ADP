# Changelog

## Unreleased

### Tree ranking

| Earlier name | Replacement | Execution |
|---|---|---|
| `queries::co_optimal` | `queries::co_minimal` | Exhaustive root scoring |
| `queries::k_best` | `queries::k_lowest` | Exhaustive root scoring |
| `Recovery::optimal_tree` | `Recovery::first_minimum_tree` | Finite additive recovery |
| `Recovery::co_optimal` | `Recovery::co_minimal` | Finite additive recovery |
| `Recovery::k_best` | `Recovery::k_lowest` | Finite additive recovery |

Update the names at call sites. Both interfaces rank in ascending score
order and use first derivation order for ties.
[Ranking contracts](docs/QUESTIONS.md#ranking-trees)

### Sequence grammar compiler

Yield analysis settles the minimum of each nonterminal before checking
whether a productive clause's minimum exceeds `usize`. Interleaving
clauses for different parents preserves acceptance and ordered emissions.
[Compiler guide](docs/COMPILER.md#declaring-a-sequence-grammar)
