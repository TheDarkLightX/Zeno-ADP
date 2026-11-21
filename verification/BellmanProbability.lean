import BellmanBag
import Init.Data.Rat.Lemmas

namespace BellmanProbability

open BellmanTabulation

def sumOps : BellmanBag.Operations Rat where
  merge := (· + ·)
  combine := (· * ·)
  merge_assoc := Rat.add_assoc
  combine_merge_left := Rat.add_mul
  combine_merge_right := Rat.mul_add

theorem sum_atCell (chart : Chart O) (weight : O → Rat) (rank : Nat) :
    AtCell chart (fun op args => args.foldl (· * ·) (weight op))
      (BellmanBag.choose sumOps) rank := by
  have h := BellmanBag.atCell sumOps chart 1 weight rank
  have align : (fun op => BellmanBag.apply sumOps 1 (weight op)) =
      (fun op args => args.foldl (· * ·) (weight op)) := by
    funext op args
    exact BellmanBag.apply_eq_foldl sumOps 1 Rat.mul_assoc Rat.mul_one (weight op) args
  rwa [align] at h

theorem sum_eq_exhaustive (chart : Chart O) (weight : O → Rat) (bound i : Nat)
    (inBounds : i < bound) :
    let apply := fun (op : O) (args : List Rat) => args.foldl (· * ·) (weight op)
    let choose := BellmanBag.choose sumOps
    lookup (tabulate chart apply choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree apply)) :=
  tabulate_eq_exhaustive chart _ _ bound (fun n _ => sum_atCell chart weight n) i inBounds

abbrev Nonnegative := { x : Rat // 0 ≤ x }

def one : Nonnegative := ⟨1, by decide⟩
def mul (x y : Nonnegative) : Nonnegative := ⟨x.val * y.val, Rat.mul_nonneg x.property y.property⟩
def sup (x y : Nonnegative) : Nonnegative := if x.val ≤ y.val then y else x

private theorem left_le_sup (x y : Nonnegative) : x.val ≤ (sup x y).val := by
  unfold sup
  split
  · assumption
  · exact Rat.le_refl

private theorem right_le_sup (x y : Nonnegative) : y.val ≤ (sup x y).val := by
  unfold sup
  split
  · exact Rat.le_refl
  · exact (Rat.le_total.resolve_left ‹¬x.val ≤ y.val›)

private theorem sup_le {x y z : Nonnegative} (hx : x.val ≤ z.val) (hy : y.val ≤ z.val) :
    (sup x y).val ≤ z.val := by
  unfold sup
  split <;> assumption

private theorem sup_assoc (x y z : Nonnegative) : sup (sup x y) z = sup x (sup y z) := by
  apply Subtype.ext
  exact Rat.le_antisymm
    (sup_le (sup_le (left_le_sup x _) (Rat.le_trans (left_le_sup y z) (right_le_sup x _)))
      (Rat.le_trans (right_le_sup y z) (right_le_sup x _)))
    (sup_le (Rat.le_trans (left_le_sup x y) (left_le_sup _ z))
      (sup_le (Rat.le_trans (right_le_sup x y) (left_le_sup _ z)) (right_le_sup _ z)))

private theorem mul_sup_left (x y z : Nonnegative) : mul (sup x y) z = sup (mul x z) (mul y z) := by
  by_cases h : x.val ≤ y.val
  · have hm := Rat.mul_le_mul_of_nonneg_right h z.property
    simp only [sup, if_pos h, if_pos (show (mul x z).val ≤ (mul y z).val from hm)]
  · have hm : (mul y z).val ≤ (mul x z).val :=
      Rat.mul_le_mul_of_nonneg_right (Rat.le_total.resolve_left h) z.property
    rw [sup, if_neg h, sup]
    split
    · apply Subtype.ext
      exact Rat.le_antisymm (by assumption) hm
    · rfl

private theorem mul_comm (x y : Nonnegative) : mul x y = mul y x :=
  Subtype.ext (Rat.mul_comm _ _)

def maxOps : BellmanBag.Operations Nonnegative where
  merge := sup
  combine := mul
  merge_assoc := sup_assoc
  combine_merge_left := mul_sup_left
  combine_merge_right := by
    intro x y z
    rw [mul_comm x (sup y z), mul_sup_left, mul_comm y x, mul_comm z x]

theorem max_atCell (chart : Chart O) (weight : O → Nonnegative) (rank : Nat) :
    AtCell chart (fun op args => args.foldl mul (weight op))
      (BellmanBag.choose maxOps) rank := by
  have h := BellmanBag.atCell maxOps chart one weight rank
  have align : (fun op => BellmanBag.apply maxOps one (weight op)) =
      (fun op args => args.foldl mul (weight op)) := by
    funext op args
    exact BellmanBag.apply_eq_foldl maxOps one
      (fun a b c => Subtype.ext (Rat.mul_assoc a.val b.val c.val))
      (fun a => Subtype.ext (Rat.mul_one a.val)) (weight op) args
  rwa [align] at h

theorem max_eq_exhaustive (chart : Chart O) (weight : O → Nonnegative) (bound i : Nat)
    (inBounds : i < bound) :
    let apply := fun (op : O) (args : List Nonnegative) => args.foldl mul (weight op)
    let choose := BellmanBag.choose maxOps
    lookup (tabulate chart apply choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree apply)) :=
  tabulate_eq_exhaustive chart _ _ bound (fun n _ => max_atCell chart weight n) i inBounds

/-- At a sampling step the event of reaching the current suffix has mass
`suffix / total`. Multiplying by the conditional choice cancels the suffix. -/
theorem sample_suffix_cancels (branch suffix total : Rat) (nonzero : suffix ≠ 0) :
    (suffix / total) * (branch / suffix) = branch / total := by
  calc
    _ = (branch / suffix) * (suffix * total⁻¹) := Rat.mul_comm _ _
    _ = ((branch / suffix) * suffix) * total⁻¹ := (Rat.mul_assoc _ _ _).symm
    _ = branch / total := by rw [Rat.div_mul_cancel nonzero]; rfl

#print axioms BellmanProbability.sum_eq_exhaustive
#print axioms BellmanProbability.max_eq_exhaustive
#print axioms BellmanProbability.sample_suffix_cancels

end BellmanProbability
