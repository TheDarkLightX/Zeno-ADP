import BellmanBag
import Init.Data.Rat.Lemmas

namespace BellmanExpectation

open BellmanTabulation

abbrev Dual := Rat × Rat

def unit : Dual := (1, 0)

def add (x y : Dual) : Dual := (x.1 + y.1, x.2 + y.2)

def mul (x y : Dual) : Dual :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

theorem add_assoc (x y z : Dual) : add (add x y) z = add x (add y z) := by
  simp [add, Rat.add_assoc]

theorem mul_assoc (x y z : Dual) : mul (mul x y) z = mul x (mul y z) := by
  simp only [mul, Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Prod.mk.injEq, true_and]
  exact (Rat.add_assoc _ _ _).symm

theorem mul_unit (x : Dual) : mul x unit = x := by
  cases x
  simp [mul, unit, Rat.zero_add]

theorem add_mul (x y z : Dual) : mul (add x y) z = add (mul x z) (mul y z) := by
  simp only [mul, add, Rat.add_mul, Prod.mk.injEq, true_and]
  simp only [Rat.add_assoc]
  rw [Rat.add_left_comm (y.1 * z.2) (x.2 * z.1)]

theorem mul_add (x y z : Dual) : mul x (add y z) = add (mul x y) (mul x z) := by
  simp only [mul, add, Rat.mul_add, Prod.mk.injEq, true_and]
  simp only [Rat.add_assoc]
  rw [Rat.add_left_comm (x.1 * z.2) (x.2 * y.1)]

def ops : BellmanBag.Operations Dual where
  merge := add
  combine := mul
  merge_assoc := add_assoc
  combine_merge_left := add_mul
  combine_merge_right := mul_add

theorem expectation_atCell (chart : Chart O) (weight : O → Dual) (rank : Nat) :
    AtCell chart (fun op args => args.foldl mul (weight op))
      (BellmanBag.choose ops) rank := by
  have h := BellmanBag.atCell ops chart unit weight rank
  have align : (fun op => BellmanBag.apply ops unit (weight op)) =
      (fun op args => args.foldl mul (weight op)) := by
    funext op args
    exact BellmanBag.apply_eq_foldl ops unit mul_assoc mul_unit (weight op) args
  rwa [align] at h

theorem expectation_eq_exhaustive (chart : Chart O) (weight : O → Dual) (bound i : Nat)
    (inBounds : i < bound) :
    let apply := fun (op : O) (args : List Dual) => args.foldl mul (weight op)
    let choose := BellmanBag.choose ops
    lookup (tabulate chart apply choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree apply)) :=
  tabulate_eq_exhaustive chart _ _ bound (fun n _ => expectation_atCell chart weight n) i inBounds

#print axioms BellmanExpectation.expectation_atCell
#print axioms BellmanExpectation.expectation_eq_exhaustive

end BellmanExpectation
