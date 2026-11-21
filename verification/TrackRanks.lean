import Lean

namespace TrackRanks

structure Axis where
  width : Nat
  digit : Nat
  step : Nat

def volume : List Axis → Nat
  | [] => 1
  | axis :: rest => axis.width * volume rest

def rank : List Axis → Nat
  | [] => 0
  | axis :: rest => axis.digit * volume rest + rank rest

def lag : List Axis → Nat
  | [] => 0
  | axis :: rest => axis.step * volume rest + lag rest

def move (axes : List Axis) : List Axis :=
  axes.map fun axis => { axis with digit := axis.digit - axis.step }

private theorem volume_move (axes : List Axis) : volume (move axes) = volume axes := by
  induction axes with
  | nil => rfl
  | cons axis rest ih => simp [move, volume, ← ih, List.map_cons]

theorem rank_eq_child_add_lag (axes : List Axis)
    (enabled : ∀ axis ∈ axes, axis.step ≤ axis.digit) :
    rank axes = rank (move axes) + lag axes := by
  induction axes with
  | nil => rfl
  | cons axis rest ih =>
    have stepFits := enabled axis (by simp)
    have restFits : ∀ next ∈ rest, next.step ≤ next.digit :=
      fun next mem => enabled next (List.mem_cons_of_mem _ mem)
    have localDigit :
        axis.digit * volume rest =
          (axis.digit - axis.step) * volume rest + axis.step * volume rest := by
      rw [← Nat.add_mul, Nat.sub_add_cancel stepFits]
    change axis.digit * volume rest + rank rest =
      (axis.digit - axis.step) * volume (move rest) + rank (move rest) +
        (axis.step * volume rest + lag rest)
    rw [volume_move, localDigit, ih restFits]
    omega

theorem predecessor_rank (axes : List Axis)
    (enabled : ∀ axis ∈ axes, axis.step ≤ axis.digit) :
    rank (move axes) = rank axes - lag axes := by
  rw [rank_eq_child_add_lag axes enabled, Nat.add_sub_cancel]

theorem predecessor_descends (axes : List Axis)
    (enabled : ∀ axis ∈ axes, axis.step ≤ axis.digit)
    (advances : 0 < lag axes) :
    rank (move axes) < rank axes := by
  rw [predecessor_rank axes enabled]
  have bounded := rank_eq_child_add_lag axes enabled
  omega

#print axioms rank_eq_child_add_lag
#print axioms predecessor_rank
#print axioms predecessor_descends

end TrackRanks
