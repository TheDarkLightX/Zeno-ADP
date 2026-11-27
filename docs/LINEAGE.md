# Algebraic dynamic programming lineage

The [three-matrix example](../README.md#parenthesize-three-matrices) uses
one tree grammar with separate algebras for cost, count and enumeration.
The sources below develop that formulation, its implementations and how
to explain it.

- Robert Giegerich, Carsten Meyer and Peter Steffen. “A discipline of dynamic
  programming over sequence data.” *Science of Computer Programming*
  51(3), 215–263 (2004). The ADP formulation defines candidate trees by a
  grammar and evaluates them with an algebra and a choice function.
  [Journal article](https://doi.org/10.1016/j.scico.2003.12.005)
- Georg Sauthoff, Mathias Möhl, Stefan Janssen and Robert Giegerich.
  “Bellman's GAP—a language and compiler for dynamic programming in
  sequence analysis.” *Bioinformatics* 29(5), 551–560 (2013). Bellman's
  GAP provides a language and compiler for tree grammars, evaluation
  algebras and their products.
  [Journal article](https://doi.org/10.1093/bioinformatics/btt022)
- Christian Höner zu Siederdissen, Sonja J. Prohaska and Peter F. Stadler.
  “Algebraic Dynamic Programming over general data structures.”
  *BMC Bioinformatics* 16 (Suppl 19), S2 (2015). The paper generalizes
  decompositions beyond string intervals and constructs outside recursions.
  [Journal article](https://doi.org/10.1186/1471-2105-16-S19-S2)
- Christian Höner zu Siederdissen. “Sneaking around concatMap: efficient
  combinators for dynamic programming.” *ICFP ’12*, 215–226 (2012).
  ADPfusion uses stream fusion for dynamic programming combinators in
  Haskell. [Paper](https://doi.org/10.1145/2364527.2364559) ·
  [ADPfusion source](https://github.com/choener/ADPfusion)
- Stefanie Schirmer. “Dynamic Programming — with grammars, algebras,
  products.” BOB 2016. The talk builds the grammar before asking
  different questions of its trees and explains when early choice is valid.
  [Talk slides](https://bobkonf.de/2016/slides/schirmer.pdf)
