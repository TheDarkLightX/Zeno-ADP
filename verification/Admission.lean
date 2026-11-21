import Lean

namespace Admission

/-- Under ascending starts and adjacency or overlap, coalescing preserves membership
    after intersection with a structural window. -/
theorem clipped_coalesced_pair (a b c d lo hi x : Nat)
    (ordered : a ≤ c) (right : c ≤ d) (touches : c ≤ b + 1) :
    (max lo a ≤ x ∧ x ≤ min hi (max b d)) ↔
    ((lo ≤ x ∧ x ≤ hi) ∧ ((a ≤ x ∧ x ≤ b) ∨ (c ≤ x ∧ x ≤ d))) := by
  omega

/-- Two separated source ranges stay strictly ordered whenever both admit an end. -/
theorem clipped_separate_order (a b c d lo hi x y : Nat)
    (separated : b < c)
    (left : max lo a ≤ x ∧ x ≤ min hi b)
    (right : max lo c ≤ y ∧ y ≤ min hi d) : x < y := by
  omega

inductive Layout where
  | dense
  | packed
  | refuse

def chooseLayout (denseBytes packedBytes budget : Nat) : Layout :=
  if denseBytes ≤ budget then .dense
  else if packedBytes ≤ budget then .packed
  else .refuse

theorem dense_iff (denseBytes packedBytes budget : Nat) :
    chooseLayout denseBytes packedBytes budget = .dense ↔ denseBytes ≤ budget := by
  by_cases hd : denseBytes ≤ budget
  · simp [chooseLayout, hd]
  · by_cases hp : packedBytes ≤ budget <;> simp [chooseLayout, hd, hp]

theorem packed_iff (denseBytes packedBytes budget : Nat) :
    chooseLayout denseBytes packedBytes budget = .packed ↔
    budget < denseBytes ∧ packedBytes ≤ budget := by
  by_cases hd : denseBytes ≤ budget
  · simp [chooseLayout, hd, Nat.not_lt.mpr hd]
  · simp [chooseLayout, hd, Nat.lt_of_not_ge hd]

theorem refusal_iff (denseBytes packedBytes budget : Nat) :
    chooseLayout denseBytes packedBytes budget = .refuse ↔
    budget < denseBytes ∧ budget < packedBytes := by
  by_cases hd : denseBytes ≤ budget
  · simp [chooseLayout, hd, Nat.not_lt.mpr hd]
  · by_cases hp : packedBytes ≤ budget
    · simp [chooseLayout, hd, hp, Nat.not_lt.mpr hp]
    · simp [chooseLayout, hd, hp, Nat.lt_of_not_ge hd, Nat.lt_of_not_ge hp]

#print axioms clipped_coalesced_pair
#print axioms clipped_separate_order
#print axioms dense_iff
#print axioms packed_iff
#print axioms refusal_iff

end Admission
