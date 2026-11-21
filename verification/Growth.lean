import Lean

namespace Growth

abbrev Summary := Nat × Nat

def summary (sizes : List Nat) : Summary := (sizes.length, sizes.sum)

def combine (left right : Summary) : Summary :=
  (left.1 * right.1, left.2 * right.1 + left.1 * right.2)

def join (left right : List Nat) : List Nat :=
  left.flatMap fun size => right.map (size + ·)

private theorem sum_shift (shift : Nat) (sizes : List Nat) :
    (sizes.map (shift + ·)).sum = shift * sizes.length + sizes.sum := by
  induction sizes with
  | nil => simp
  | cons head tail ih =>
    simp [ih, Nat.mul_succ]
    omega

/-- Cartesian product preserves both multiplicity and total size via the
    count/size summary, including empty bags and repeated sizes. -/
theorem cartesian_summary (left right : List Nat) :
    summary (join left right) = combine (summary left) (summary right) := by
  induction left with
  | nil => simp [summary, join, combine]
  | cons size rest ih =>
    simp only [summary, join, combine, Prod.mk.injEq] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
      List.sum_append_nat, List.sum_cons, sum_shift]
    rw [ih.1, ih.2]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

def treeSizes (seed : List Nat) (children : List (List Nat)) : List Nat :=
  children.foldl join seed

private theorem summary_fold (seed : List Nat) (children : List (List Nat)) :
    summary (treeSizes seed children) = (children.map summary).foldl combine (summary seed) := by
  induction children generalizing seed with
  | nil => rfl
  | cons child rest ih =>
    simpa only [treeSizes, List.map_cons, List.foldl_cons, cartesian_summary] using ih (join seed child)

/-- Start with the constructor's own node and combine the ordered child
    slots. The list contains one size per argument tuple. -/
theorem rule_summary (children : List (List Nat)) :
    summary (treeSizes [1] children) = (children.map summary).foldl combine (1, 1) :=
  summary_fold [1] children

#print axioms cartesian_summary
#print axioms rule_summary

end Growth
