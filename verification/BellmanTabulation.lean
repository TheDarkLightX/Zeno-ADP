import Lean

namespace BellmanTabulation

universe u v

/-- Each field of a constructor tuple ranges independently, in list order. -/
def tuples {A : Type v} : List (List A) → List (List A)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (tuples rest).map (x :: ·)

theorem tuples_map {A : Type u} {B : Type v} (f : A → B) (bags : List (List A)) :
    (tuples bags).map (List.map f) = tuples (bags.map (List.map f)) := by
  induction bags with
  | nil => rfl
  | cons head tail ih =>
    simp [tuples, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, ← ih]

abbrev Rule (O : Type u) (rank : Nat) := O × List (Fin rank)
abbrev Chart (O : Type u) := (rank : Nat) → List (Rule O rank)

inductive Tree (O : Type u) where
  | node (operator : O) (children : List (Tree O))

mutual
  def foldTree (apply : O → List V → V) : Tree O → V
    | .node op children => apply op (foldChildren apply children)

  def foldChildren (apply : O → List V → V) : List (Tree O) → List V
    | [] => []
    | child :: rest => foldTree apply child :: foldChildren apply rest
end

theorem foldChildren_eq_map (apply : O → List V → V) (children : List (Tree O)) :
    foldChildren apply children = children.map (foldTree apply) := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp [foldChildren, ih]

/-- Enumerate the finite ordered bag of constructor derivations, including duplicates. -/
def unfoldTrees (chart : Chart O) (n : Nat) : List (Tree O) :=
  (chart n).flatMap fun rule =>
    (tuples (rule.2.map fun child => unfoldTrees chart child.val)).map (Tree.node rule.1)
termination_by n
decreasing_by exact child.isLt

def ruleValues (apply : O → List V → V) (get : Fin n → List V) (rule : Rule O n) : List V :=
  (tuples (rule.2.map get)).map (apply rule.1)

/-- Evaluate the same equations over full value bags, without intermediate choice. -/
def rawValues (chart : Chart O) (apply : O → List V → V) (n : Nat) : List V :=
  ((chart n).map fun rule =>
    ruleValues apply (fun child => rawValues chart apply child.val) rule).flatten
termination_by n
decreasing_by exact child.isLt

theorem raw_eq_unfold_fold (chart : Chart O) (apply : O → List V → V) (n : Nat) :
    rawValues chart apply n = (unfoldTrees chart n).map (foldTree apply) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [rawValues, unfoldTrees, List.map_flatMap, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro rule _
    simp only [ruleValues, List.map_map, Function.comp_def, foldTree, foldChildren_eq_map]
    let trees := rule.2.map (fun child => unfoldTrees chart child.val)
    change _ = (tuples trees).map (apply rule.1 ∘ List.map (foldTree apply))
    rw [← List.map_map, tuples_map]
    simp only [trees, List.map_map, Function.comp_def]
    congr 2
    apply List.map_congr_left
    intro child _
    exact ih child.val child.isLt

def lookup (table : List (List V)) (rank : Nat) : List V :=
  table[rank]?.getD []

/-- Store every cell once, in ascending rank. -/
def tabulate (chart : Chart O) (apply : O → List V → V) (choose : List V → List V) :
    Nat → List (List V)
  | 0 => []
  | n + 1 =>
    let previous := tabulate chart apply choose n
    let values := (chart n).map (ruleValues apply fun child => lookup previous child.val)
    previous ++ [choose values.flatten]

@[simp] theorem tabulate_length (chart : Chart O) (apply : O → List V → V)
    (choose : List V → List V) (n : Nat) :
    (tabulate chart apply choose n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tabulate, ih]

/-- The obligations only mention bags reached at this rank.
The merge law is used on the raw alternative bags and on their early-input variants. -/
structure AtCell (chart : Chart O) (apply : O → List V → V) (choose : List V → List V)
    (n : Nat) : Prop where
  operator : ∀ r ∈ chart n,
    choose (ruleValues apply (fun child => rawValues chart apply child.val) r) =
      choose (ruleValues apply (fun child => choose (rawValues chart apply child.val)) r)
  merge : ∀ (reduceChildren : Bool),
    let bags := (chart n).map (ruleValues apply fun child =>
      if reduceChildren then choose (rawValues chart apply child.val)
      else rawValues chart apply child.val)
    choose bags.flatten = choose (bags.map choose).flatten

theorem tabulate_eq_raw_choice (chart : Chart O) (apply : O → List V → V)
    (choose : List V → List V) (bound : Nat)
    (bellman : ∀ n < bound, AtCell chart apply choose n)
    (i : Nat) (inBounds : i < bound) :
    lookup (tabulate chart apply choose bound) i = choose (rawValues chart apply i) := by
  induction bound generalizing i with
  | zero => omega
  | succ n ih =>
    have earlier := ih (fun j less => bellman j (Nat.lt_succ_of_lt less))
    rcases Nat.lt_or_ge i n with old | lastOrLater
    · have inPrefix : i < (tabulate chart apply choose n).length := by simpa using old
      simpa only [tabulate, lookup, List.getElem?_append_left inPrefix] using earlier i old
    · have last : i = n := by omega
      subst i
      have atRank := bellman n (Nat.lt_succ_self n)
      have leftLength : (tabulate chart apply choose n).length ≤ n := by simp
      have childValues : (fun (child : Fin n) =>
          lookup (tabulate chart apply choose n) child.val) =
          (fun child => choose (rawValues chart apply child.val)) := by
        funext child
        exact earlier child.val child.isLt
      simp only [tabulate, lookup, List.getElem?_append_right leftLength, tabulate_length,
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      change choose ((chart n).map
        (ruleValues apply (fun child => lookup (tabulate chart apply choose n) child.val))).flatten =
        choose (rawValues chart apply n)
      rw [childValues, rawValues]
      have rawMerge := atRank.merge false
      have earlyMerge := atRank.merge true
      simp only [Bool.false_eq_true, ↓reduceIte] at rawMerge
      simp only [↓reduceIte] at earlyMerge
      rw [earlyMerge, rawMerge, List.map_map, List.map_map]
      apply congrArg (fun bags : List (List V) => choose bags.flatten)
      apply List.map_congr_left
      intro rule member
      exact (atRank.operator rule member).symm

/-- Actual table lookup agrees, at every in-bounds cell, with one choice after tree evaluation. -/
theorem tabulate_eq_exhaustive (chart : Chart O) (apply : O → List V → V)
    (choose : List V → List V) (bound : Nat)
    (bellman : ∀ n < bound, AtCell chart apply choose n)
    (i : Nat) (inBounds : i < bound) :
    lookup (tabulate chart apply choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree apply)) := by
  rw [tabulate_eq_raw_choice chart apply choose bound bellman i inBounds, raw_eq_unfold_fold]

/-- A familiar universal pairwise merge law supplies the finite ordered merge obligation.
This generalizes the append calculation in the integer-minimum starter. -/
theorem choice_flatten (choose : List V → List V) (empty : choose [] = [])
    (merge : ∀ xs ys, choose (xs ++ ys) = choose (choose xs ++ choose ys))
    (bags : List (List V)) :
    choose bags.flatten = choose (bags.map choose).flatten := by
  have idem (xs : List V) : choose xs = choose (choose xs) := by
    simpa only [empty, List.append_nil] using merge xs []
  induction bags with
  | nil => rfl
  | cons bag rest ih =>
    simp only [List.flatten_cons, List.map_cons]
    calc
      choose (bag ++ rest.flatten) =
          choose (choose bag ++ choose rest.flatten) := merge _ _
      _ = choose (choose bag ++ choose (rest.map choose).flatten) := by rw [ih]
      _ = choose (choose bag ++ (rest.map choose).flatten) := by
        conv => rhs; rw [merge, ← idem bag]

/-- Shape-independent laws are sufficient, but the table theorem needs only AtCell. -/
theorem atCell_of_laws (chart : Chart O) (apply : O → List V → V)
    (choose : List V → List V) (empty : choose [] = [])
    (merge : ∀ xs ys, choose (xs ++ ys) = choose (choose xs ++ choose ys))
    (operator : ∀ op bags, choose ((tuples bags).map (apply op)) =
      choose ((tuples (bags.map choose)).map (apply op)))
    (n : Nat) : AtCell chart apply choose n := by
  constructor
  · intro rule _
    simpa only [ruleValues, List.map_map, Function.comp_def] using
      operator rule.1 (rule.2.map (fun child => rawValues chart apply child.val))
  · intro reduceChildren
    exact choice_flatten choose empty merge _

#print axioms raw_eq_unfold_fold
#print axioms tabulate_eq_exhaustive
#print axioms atCell_of_laws

end BellmanTabulation
