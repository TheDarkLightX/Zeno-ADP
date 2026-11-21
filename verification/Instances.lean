import BellmanAlgebras
import BellmanLexicographic
import IntervalConvolution

open BellmanTabulation BellmanAlgebras

namespace ZenoADPVerification

theorem count_eq_exhaustive (chart : Chart O) {bound i : Nat} (h : i < bound) :
    lookup (tabulate chart countApply countChoose bound) i =
      countChoose ((unfoldTrees chart i).map (foldTree countApply)) :=
  tabulate_eq_exhaustive chart countApply countChoose bound (fun r _ => count_atCell chart r) i h

theorem enumeration_eq_exhaustive (chart : Chart O) {bound i : Nat} (h : i < bound) :
    lookup (tabulate chart Tree.node id bound) i = unfoldTrees chart i := by
  have fold_id (t : Tree O) : foldTree Tree.node t = t :=
    foldTree.induct (fun t => foldTree Tree.node t = t)
      (fun ts => foldChildren Tree.node ts = ts)
      (fun op ts ih => by
        change foldTree Tree.node (.node op ts) = .node op ts
        rw [foldTree, ih])
      rfl
      (fun child rest hChild hRest => by
        change foldChildren Tree.node (child :: rest) = child :: rest
        rw [foldChildren, hChild, hRest]) t
  rw [tabulate_eq_exhaustive chart Tree.node id bound (fun r _ => enumerate_atCell chart r) i h]
  change (unfoldTrees chart i).map (foldTree Tree.node) = unfoldTrees chart i
  calc
    _ = (unfoldTrees chart i).map id := List.map_congr_left (fun t _ => fold_id t)
    _ = _ := List.map_id _

theorem ties_eq_exhaustive (chart : Chart O) (weight : O → Option Int)
    {bound i : Nat} (h : i < bound) :
    lookup (tabulate chart (tiesApply weight) tiesChoose bound) i =
      tiesChoose ((unfoldTrees chart i).map (foldTree (tiesApply weight))) :=
  tabulate_eq_exhaustive chart (tiesApply weight) tiesChoose bound
    (fun r _ => ties_atCell chart weight r) i h

theorem minimum_eq_exhaustive (chart : Chart O) (weight : O → Option Int)
    {bound i : Nat} (h : i < bound) :
    lookup (tabulate chart (minimumApply weight) minimumChoose bound) i =
      minimumChoose ((unfoldTrees chart i).map (foldTree (minimumApply weight))) :=
  tabulate_eq_exhaustive chart (minimumApply weight) minimumChoose bound
    (fun r _ => minimum_atCell chart weight r) i h

theorem lex_eq_exhaustive (chart : Chart O) (weight : O → BellmanLexicographic.Score)
    {bound i : Nat} (h : i < bound) :
    lookup (tabulate chart (BellmanLexicographic.apply weight) BellmanLexicographic.choose bound) i =
      BellmanLexicographic.choose
        ((unfoldTrees chart i).map (foldTree (BellmanLexicographic.apply weight))) :=
  tabulate_eq_exhaustive chart (BellmanLexicographic.apply weight) BellmanLexicographic.choose bound
    (fun r _ => BellmanLexicographic.additive_atCell chart weight r) i h

private def collapsePrimary (args : List BellmanLexicographic.Score) : BellmanLexicographic.Score :=
  ⟨0, (args.map BellmanLexicographic.Score.secondary).sum⟩

theorem lex_collapsed_primary_counterexample :
    let bags : List (List BellmanLexicographic.Score) := [[⟨0, 1⟩, ⟨1, 0⟩]]
    let choose := BellmanLexicographic.choose (A := BellmanLexicographic.Score)
    choose ((tuples bags).map collapsePrimary) = [⟨0, 0⟩] ∧
    choose ((tuples (bags.map choose)).map collapsePrimary) = [⟨0, 1⟩] := by decide

private def oldChoose (xs : List (Option Int × Nat)) : List (Option Int × Nat) :=
  let encode : Option Int × Nat → Summary
    | (some c, n) => .finite c n n
    | (none, n) => .infinity n
  let decode : Summary → Option Int × Nat
    | .finite c n _ => (some c, n)
    | .infinity n => (none, n)
  (tiesChoose (xs.map encode)).map decode

private def oldAbsorb (args : List (Option Int × Nat)) : Option Int × Nat :=
  (none, args.foldl (fun n arg => n * arg.2) 1)

theorem unrepaired_ties_counterexample :
    let bags : List (List (Option Int × Nat)) := [[(some 0, 1), (some 1, 1)]]
    oldChoose ((tuples bags).map oldAbsorb) = [(none, 2)] ∧
    oldChoose ((tuples (bags.map oldChoose)).map oldAbsorb) = [(none, 1)] := by decide

#print axioms count_eq_exhaustive
#print axioms enumeration_eq_exhaustive
#print axioms ties_eq_exhaustive
#print axioms minimum_eq_exhaustive
#print axioms lex_eq_exhaustive
#print axioms lex_collapsed_primary_counterexample
#print axioms unrepaired_ties_counterexample
#print axioms BellmanLexicographic.selective_atCell

end ZenoADPVerification
