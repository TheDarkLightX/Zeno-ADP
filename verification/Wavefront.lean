import Lean

namespace Wavefront

def tileWave (edge row column : Nat) : Nat := row / edge + column / edge

/-- For a north, west or northwest predecessor, the tile is already
published, or both coordinates are in the same tile. -/
theorem prefix_child_wave_or_same_tile (edge row column north west : Nat)
    (rowLe : north ≤ row) (columnLe : west ≤ column) :
    tileWave edge north west < tileWave edge row column ∨
      (north / edge = row / edge ∧ west / edge = column / edge) := by
  have nr := Nat.div_le_div_right (c := edge) rowLe
  have wc := Nat.div_le_div_right (c := edge) columnLe
  unfold tileWave
  omega

/-- Inside a tile, a strict coordinate predecessor occurs first in
row-major order when both columns fit the stride. -/
theorem prefix_child_rank (stride row column north west : Nat)
    (westBound : west < stride) (rowLe : north ≤ row)
    (changed : north < row ∨ west < column) :
    north * stride + west < row * stride + column := by
  rcases Nat.lt_or_ge north row with h | h
  · have step := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at step
    omega
  · have same : north = row := by omega
    subst north
    omega

/-- Both generated pivot children precede their parent in length order. -/
theorem interval_pivot_children (start pivot stop : Nat)
    (left : start ≤ pivot) (right : pivot < stop) :
    pivot - start < stop - start ∧ stop - (pivot + 1) < stop - start := by
  omega

/-- Removing the leftmost base shortens every nonempty span. -/
theorem unpaired_child (start stop : Nat) (nonempty : start < stop) :
    stop - (start + 1) < stop - start := by
  omega

/-- Both children of a Nussinov pair use shorter spans. -/
theorem pair_children (start partner stop : Nat)
    (left : start < partner) (right : partner < stop) :
    partner - (start + 1) < stop - start ∧
      stop - (partner + 1) < stop - start := by
  omega

#print axioms prefix_child_wave_or_same_tile
#print axioms prefix_child_rank
#print axioms interval_pivot_children
#print axioms unpaired_child
#print axioms pair_children

end Wavefront
