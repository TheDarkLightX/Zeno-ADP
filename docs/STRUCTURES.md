# Forests, tuples and sets

Each of these constructors returns a ranked chart for the same reference
engine. Use `tabulate_cells` to observe every scheduled subproblem and
`audit_bounded` to check an algebra on a concrete chart. Run
`cargo run --offline --locked --example structures` for three examples.

## Ordered trees and forests

Represent a tree with `forests::Node::new(label, children)`. A slice of
nodes is a forest in sibling order. Labels need `PartialEq` for the
built-in unit score. `Comparison::spans` assigns each cell a pair of
half-open preorder intervals. Each forest interval contains complete
subtrees rooted at the nodes exposed in that interval. Empty intervals
keep their coordinates.

- `forests::edit` gives the ordered tree edit recurrence. Removing a root
  promotes its children. A matched pair splits the question into its child
  forests and remaining siblings. `Minimum` charges one per unmatched
  node or label mismatch.
- `forests::edit_reference` enumerates ordered promoting cuts. A cut retains
  a frontier of disjoint complete subtrees. The grammar pays for nodes
  outside the retained subtrees, pairs frontier roots in order, then
  compares their children. Each partial edit mapping has one such
  decomposition by its topmost matched nodes. Use `Count` on this chart
  to count mappings. `Count` on the first-root recurrence counts its
  derivations, including different deletion orders.
- `forests::alignment` generates common superforests. Every alignment root
  comes from both inputs or from one input paired with a gap. Removing gaps
  and promoting children projects the alignment back to the inputs. When
  a root is paired with a gap, it can enclose a prefix of the other forest.
  `Minimum` charges one per gap or label mismatch. `Count` counts the
  resulting alignments.

Edit and alignment optimize different candidate sets. For example, the
forests `[z(a,b),c]` and `[a,z(b,c)]` have edit cost 2 and alignment cost
4. The two unmatched `z` roots cover overlapping groups of matched leaves.

All three constructors materialize chart productions. Edit has at most
three rules per cell. Alignment uses root boundaries for gap splits. The
cut reference can enumerate exponentially many frontier pairs. For a
forest of isolated leaves, every subset is a frontier.

## Multiple context-free grammars

Declare each symbol with its number of yield components, also called its
fan-out. A `mcfg::Production` gives one pattern per parent component. Each
pattern contains literal bytes, wildcard bytes or variables that select an
ordered child's component. Every child component appears once across the
patterns. The callback receives the input and the matched coordinates and
constructs the operator. Encode relevant coordinates or clause identity in
the operator when they are part of a term's meaning.

For two children `A` and `B` with two components each, the single start
pattern `A₀ B₀ A₁ B₁` interleaves their components. A chart cell for `A`
sees both of its spans. The component order in a tuple follows its
declaration, independent of physical order in the input.

`Grammar::instantiate` binds the start to the whole input and constructs
the span tuples needed by its production matches. `Instance::items` maps
ranks back to symbols and spans. Occurrences follow production declaration
order and then increasing split positions in pattern order. Counting sums
derivations. Structural tree queries also consider constructor equality.

This grammar class has one nonempty start component and positive-length
child components. Empty input yields an absent root. A cycle of
terminal-free unary productions is refused because all its edges can
keep the same total length. Other edges consume a terminal or leave a
positive yield to another child. Tuple counts and split work can grow
quickly with fan-out.

## Partitions over a finite set

`sets::partitions(elements, allowed_block)` gives one cell per subset of
the carrier `0..elements`. Ranks are membership bit masks, with the full
mask as the root. Each production takes an allowed block containing the
least remaining member, then asks for a partition of the remainder. Every
unordered partition has exactly one block containing that member, so this
order counts each partition once. The empty set has one empty partition.

Use `Count` for the number of partitions. Supply an `Algebra<PartitionOp>`
if you want to score or classify each block. With all blocks allowed,
the total number of nonempty-set productions across the full table is
`(3^elements - 1) / 2`. The chart uses machine-word masks and
exponential storage.
