import Lean

namespace DistinctIntersections

/-- Signs of all subsets of the accepting alternatives, including the
empty subset. Here the sign is positive for an even number of members. -/
def signs : Nat → List Int
  | 0 => [1]
  | n + 1 => let previous := signs n; previous ++ previous.map (- ·)

private theorem sum_neg (xs : List Int) : (xs.map (- ·)).sum = -xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_append (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [ih, Int.add_assoc]

theorem signs_cancel (n : Nat) : (signs (n + 1)).sum = 0 := by
  simp [signs, sum_append, sum_neg]
  omega

/-- The empty term contributes one. Removing it and reversing the signs
gives exactly one contribution per tree accepted by at least one alternative. -/
theorem inclusion_exclusion_per_tree (accepting : Nat) :
    1 - (signs accepting).sum = if accepting = 0 then 0 else 1 := by
  cases accepting with
  | zero => decide
  | succ n => simp [signs_cancel]

end DistinctIntersections

#print axioms DistinctIntersections.signs_cancel
#print axioms DistinctIntersections.inclusion_exclusion_per_tree
