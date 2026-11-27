import Lean

namespace ChoiceContract

/-- Count the exact two slices of a list of equally optimal assignments. -/
def noCount (row : α → Bool) (xs : List α) :=
  (xs.filter fun x => !(row x)).length

def yesCount (row : α → Bool) (xs : List α) :=
  (xs.filter row).length

theorem counts_partition (row : α → Bool) (xs : List α) :
    noCount row xs + yesCount row xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : row x <;> simp [noCount, yesCount, h] at * <;> omega

theorem exclude_sound (row : α → Bool) (xs : List α)
    (h : noCount row xs = xs.length) : ∀ x ∈ xs, row x = false := by
  have n := counts_partition row xs
  have nz : yesCount row xs = 0 := by omega
  intro x hx
  cases he : row x
  · rfl
  · have hm : x ∈ xs.filter row := List.mem_filter.mpr ⟨hx, he⟩
    have e : xs.filter row = [] := List.length_eq_zero_iff.mp nz
    simp [e] at hm

theorem include_sound (row : α → Bool) (xs : List α)
    (h : yesCount row xs = xs.length) : ∀ x ∈ xs, row x = true := by
  intro x hx
  have h' : noCount (fun y => !(row y)) xs = xs.length := by
    simpa [yesCount, noCount] using h
  simpa using exclude_sound (fun y => !(row y)) xs h' x hx

end ChoiceContract

#print axioms ChoiceContract.counts_partition
#print axioms ChoiceContract.exclude_sound
#print axioms ChoiceContract.include_sound
