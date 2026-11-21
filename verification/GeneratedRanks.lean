import Lean

namespace GeneratedRanks

/-- Triangular row offset, formed without machine-width arithmetic. -/
def row : Nat → Nat
  | 0 => 0
  | n + 1 => row n + (n + 1)

/-- End-major layout with start decreasing inside each row. -/
def rank (start stop : Nat) : Nat := row stop + (stop - start)

private theorem row_mono (a b : Nat) (h : a ≤ b) : row a ≤ row b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    simp [this]
  | succ b ih =>
    by_cases h' : a ≤ b
    · have := ih h'
      simp only [row]
      omega
    · have : a = b + 1 := by omega
      simp [this]

def prefixRank (stop : Nat) : Nat := stop

theorem prefix_child (split stop : Nat) (inside : split < stop) :
    prefixRank split < prefixRank stop := inside

theorem pivot_left (start pivot stop : Nat) (inside : pivot < stop) :
    rank start pivot < rank start stop := by
  have hr := row_mono (pivot + 1) stop (by omega)
  simp only [row] at hr
  unfold rank
  omega

theorem pivot_right (start pivot stop : Nat) (inside : start ≤ pivot) (ltStop : pivot < stop) :
    rank (pivot + 1) stop < rank start stop := by
  unfold rank
  omega

/-- The offset slice starts at the first pivot. The right rank decrements
    from the parent's rank once per pivot, including the current pivot. -/
theorem pivot_children_from_offsets (start stop index : Nat) (inside : start + index < stop) :
    (row (start + index) + index, rank start stop - (index + 1)) =
      (rank start (start + index), rank (start + index + 1) stop) := by
  unfold rank
  congr 1 <;> omega

#print axioms GeneratedRanks.pivot_children_from_offsets
#print axioms GeneratedRanks.pivot_left
#print axioms GeneratedRanks.pivot_right

end GeneratedRanks
