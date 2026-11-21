import BellmanBag
import IntervalConvolution

namespace BellmanAlgebras

open BellmanTabulation

def countOps : BellmanBag.Operations Nat where
  merge := Nat.add
  combine := Nat.mul
  merge_assoc := Nat.add_assoc
  combine_merge_left := Nat.add_mul
  combine_merge_right := Nat.mul_add

def countApply (_ : O) (children : List Nat) : Nat :=
  children.foldl Nat.mul 1

def countChoose := BellmanBag.choose countOps

theorem count_atCell (chart : Chart O) (rank : Nat) :
    AtCell chart countApply countChoose rank := by
  have applyEq : (fun (_ : O) => BellmanBag.apply countOps 1 1) = countApply := by
    funext _ children
    exact BellmanBag.apply_eq_foldl countOps 1 Nat.mul_assoc Nat.mul_one 1 children
  rw [← applyEq]
  exact BellmanBag.atCell countOps chart 1 (fun _ => 1) rank

theorem enumerate_atCell (chart : Chart O) (rank : Nat) :
    AtCell chart Tree.node id rank :=
  atCell_of_laws chart Tree.node id rfl (fun _ _ => rfl) (by simp) rank

def minimumOps : BellmanBag.Operations (Option Int) :=
  let exact := IntervalConvolution.minPlusSemiring
  ⟨exact.add, exact.mul, exact.addAssoc, exact.rightDistrib, exact.leftDistrib⟩

def minimumApply (cost : O → Option Int) (op : O) (children : List (Option Int)) : Option Int :=
  children.foldl minimumOps.combine (cost op)

def minimumChoose := BellmanBag.choose minimumOps

theorem minimum_atCell (chart : Chart O) (cost : O → Option Int) (rank : Nat) :
    AtCell chart (minimumApply cost) minimumChoose rank := by
  let exact := IntervalConvolution.minPlusSemiring
  have applyEq : (fun op => BellmanBag.apply minimumOps exact.one (cost op)) =
      minimumApply cost := by
    funext op children
    exact BellmanBag.apply_eq_foldl minimumOps exact.one exact.mulAssoc
      exact.mulOne (cost op) children
  rw [← applyEq]
  exact BellmanBag.atCell minimumOps chart exact.one cost rank

/-- The infinite case is normalized: every represented occurrence ties.
Absence is represented by an empty bag, outside of this type. -/
inductive Summary where
  | finite (cost : Int) (optimal total : Nat)
  | infinity (total : Nat)
  deriving DecidableEq, Repr

namespace Summary

def total : Summary → Nat
  | .finite _ _ total | .infinity total => total

def merge : Summary → Summary → Summary
  | .infinity a, .infinity b => .infinity (a + b)
  | .finite cost opt a, .infinity b => .finite cost opt (a + b)
  | .infinity a, .finite cost opt b => .finite cost opt (a + b)
  | .finite a u c, .finite b v d =>
    if a < b then .finite a u (c + d)
    else if b < a then .finite b v (c + d)
    else .finite a (u + v) (c + d)

def combine : Summary → Summary → Summary
  | .finite a u c, .finite b v d => .finite (a + b) (u * v) (c * d)
  | a, b => .infinity (a.total * b.total)

theorem merge_total (x y : Summary) : (merge x y).total = x.total + y.total := by
  cases x <;> cases y
  case finite.finite a _ _ b _ _ =>
    by_cases ab : a < b <;> by_cases ba : b < a <;> simp [merge, total, ab, ba]
  all_goals rfl

theorem merge_assoc (x y z : Summary) : merge (merge x y) z = merge x (merge y z) := by
  cases x <;> cases y <;> cases z
  case finite.finite.finite a _ _ b _ _ c _ _ =>
    rcases Int.lt_trichotomy a b with ab | ab | ab <;>
    rcases Int.lt_trichotomy b c with bc | bc | bc <;>
    rcases Int.lt_trichotomy a c with ac | ac | ac <;>
      first | omega | simp (disch := omega) [merge, Nat.add_assoc, if_neg, *]
  case finite.finite.infinity a _ _ b _ _ _ =>
    by_cases ab : a < b <;> by_cases ba : b < a <;> simp [merge, ab, ba, Nat.add_assoc]
  case finite.infinity.finite a _ _ _ b _ _ =>
    by_cases ab : a < b <;> by_cases ba : b < a <;> simp [merge, ab, ba, Nat.add_assoc]
  case infinity.finite.finite _ a _ _ b _ _ =>
    by_cases ab : a < b <;> by_cases ba : b < a <;> simp [merge, ab, ba, Nat.add_assoc]
  all_goals simp [merge, Nat.add_assoc]

theorem combine_comm (x y : Summary) : combine x y = combine y x := by
  cases x <;> cases y <;> simp [combine, Int.add_comm, Nat.mul_comm]

theorem combine_assoc (x y z : Summary) :
    combine (combine x y) z = combine x (combine y z) := by
  cases x <;> cases y <;> cases z <;> simp [combine, total, Int.add_assoc, Nat.mul_assoc]

private theorem combine_infinity (x : Summary) (total : Nat) :
    combine x (.infinity total) = .infinity (x.total * total) := by
  cases x <;> rfl

theorem combine_merge_left (x y z : Summary) :
    combine (merge x y) z = merge (combine x z) (combine y z) := by
  cases z with
  | infinity t =>
    rw [combine_infinity, merge_total, combine_infinity, combine_infinity, Nat.add_mul]
    rfl
  | finite z w t =>
    cases x <;> cases y
    case finite.finite a _ _ b _ _ =>
      by_cases ab : a < b <;> by_cases ba : b < a <;>
        simp (disch := omega) [merge, combine, ab, ba, Nat.add_mul]
    all_goals simp [combine, merge, total, Nat.add_mul]

theorem combine_merge_right (x y z : Summary) :
    combine x (merge y z) = merge (combine x y) (combine x z) := by
  rw [combine_comm x, combine_merge_left, combine_comm y x, combine_comm z x]

def operations : BellmanBag.Operations Summary :=
  ⟨merge, combine, merge_assoc, combine_merge_left, combine_merge_right⟩

def unit : Summary := .finite 0 1 1

theorem combine_unit (x : Summary) : combine x unit = x := by
  cases x <;> simp [combine, unit, total]

def weight : Option Int → Summary
  | some x => .finite x 1 1
  | none => .infinity 1

end Summary

def tiesApply (cost : O → Option Int) (op : O) (children : List Summary) : Summary :=
  children.foldl Summary.combine (Summary.weight (cost op))

def tiesChoose := BellmanBag.choose Summary.operations

theorem ties_atCell (chart : Chart O) (cost : O → Option Int) (rank : Nat) :
    AtCell chart (tiesApply cost) tiesChoose rank := by
  have applyEq :
      (fun op => BellmanBag.apply Summary.operations Summary.unit (Summary.weight (cost op))) =
        tiesApply cost := by
    funext op children
    exact BellmanBag.apply_eq_foldl Summary.operations Summary.unit Summary.combine_assoc
      Summary.combine_unit (Summary.weight (cost op)) children
  rw [← applyEq]
  exact BellmanBag.atCell Summary.operations chart Summary.unit (Summary.weight ∘ cost) rank

end BellmanAlgebras
