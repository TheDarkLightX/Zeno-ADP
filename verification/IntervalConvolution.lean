import Lean

namespace IntervalConvolution

/-- Semiring laws with ordered multiplication. -/
class Semiring (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  addAssoc : ∀ x y z, add (add x y) z = add x (add y z)
  addComm : ∀ x y, add x y = add y x
  zeroAdd : ∀ x, add zero x = x
  addZero : ∀ x, add x zero = x
  mulAssoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  oneMul : ∀ x, mul one x = x
  mulOne : ∀ x, mul x one = x
  zeroMul : ∀ x, mul zero x = zero
  mulZero : ∀ x, mul x zero = zero
  leftDistrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  rightDistrib : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)

open Semiring

def total {R : Type u} [Semiring R] : List R → R
  | [] => zero
  | head :: tail => add head (total tail)

theorem total_append [Semiring R] (xs ys : List R) :
    total (xs ++ ys) = add (total xs) (total ys) := by
  induction xs with
  | nil => simp [total, zeroAdd]
  | cons x xs ih => simp [total, ih, addAssoc]

theorem total_flatMap [Semiring R] (xs : List A) (f : A → List R) :
    total (xs.flatMap f) = total (xs.map fun x => total (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, total_append, ih]

theorem total_mul_left [Semiring R] (xs : List A) (f : A → R) (w : R) :
    total (xs.map fun x => mul w (f x)) = mul w (total (xs.map f)) := by
  induction xs with
  | nil => simp [total, mulZero]
  | cons x xs ih => simp [total, leftDistrib, ih]

theorem total_mul_right [Semiring R] (xs : List A) (f : A → R) (w : R) :
    total (xs.map fun x => mul (f x) w) = mul (total (xs.map f)) w := by
  induction xs with
  | nil => simp [total, zeroMul]
  | cons x xs ih => simp [total, rightDistrib, ih]

theorem total_pairs [Semiring R] (xs : List A) (ys : List B) (f : A → R) (g : B → R)
    (w : R) :
    total (xs.flatMap fun x => ys.map fun y => mul w (mul (f x) (g y))) =
      mul w (mul (total (xs.map f)) (total (ys.map g))) := by
  calc
    _ = total (xs.map fun x => mul w (mul (f x) (total (ys.map g)))) := by
      rw [total_flatMap]
      apply congrArg total
      apply List.map_congr_left
      intro x _
      rw [total_mul_left, total_mul_left]
    _ = _ := by rw [total_mul_left, total_mul_right]

/-- A tree on [i, i+n+1). The index n is width minus one. Each fork has a
    uniquely specified strict interior split; its children tile the interval. -/
inductive SplitTree : Nat → Nat → Type where
  | leaf (i : Nat) : SplitTree i 0
  | fork {i n : Nat} (split : Fin (n + 1))
      (left : SplitTree i split.val)
      (right : SplitTree (i + split.val + 1) (n - split.val)) : SplitTree i (n + 1)

def allTrees (i : Nat) (n : Nat) : List (SplitTree i n) :=
  match n with
  | 0 => [.leaf i]
  | n + 1 => (List.finRange (n + 1)).flatMap fun split =>
    (allTrees i split.val).flatMap fun left =>
      (allTrees (i + split.val + 1) (n - split.val)).map (SplitTree.fork split left)
termination_by n
decreasing_by
  all_goals have := split.isLt; omega

theorem mem_allTrees (tree : SplitTree i n) : tree ∈ allTrees i n := by
  induction tree with
  | leaf i => rw [allTrees]; exact List.mem_cons_self
  | fork split left right leftMem rightMem =>
    rw [allTrees]
    exact List.mem_flatMap_of_mem (List.mem_finRange split)
      (List.mem_flatMap_of_mem leftMem (List.mem_map_of_mem rightMem))

private theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    refine ⟨?_, List.pairwise_map.mpr (ih.imp fun ne eq => ne (Fin.succ_inj.mp eq))⟩
    simp
    intro x eq
    exact Nat.noConfusion (congrArg Fin.val eq)

private def rootSplit : SplitTree i (n + 1) → Fin (n + 1)
  | .fork split _ _ => split

private theorem fork_same_split {s : Fin (n + 1)} {a c : SplitTree i s.val}
    {b d : SplitTree (i + s.val + 1) (n - s.val)}
    (eq : SplitTree.fork s a b = SplitTree.fork s c d) : a = c ∧ b = d := by
  injection eq
  exact ⟨by assumption, by assumption⟩

theorem allTrees_nodup (i n : Nat) : (allTrees i n).Nodup := by
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    cases n with
    | zero => rw [allTrees]; simp
    | succ n =>
      rw [allTrees]
      apply List.pairwise_flatMap.mpr
      constructor
      · intro split _
        apply List.pairwise_flatMap.mpr
        constructor
        · intro left _
          apply List.pairwise_map.mpr
          exact (ih (n - split.val) (by omega) _).imp
            (fun ne eq => ne (fork_same_split eq).2)
        · apply (ih split.val split.isLt i).imp
          intro left₁ left₂ ne t₁ mem₁ t₂ mem₂ eq
          obtain ⟨right₁, _, rfl⟩ := List.mem_map.mp mem₁
          obtain ⟨right₂, _, rfl⟩ := List.mem_map.mp mem₂
          exact ne (fork_same_split eq).1
      · apply (nodup_finRange _).imp
        intro split₁ split₂ ne t₁ mem₁ t₂ mem₂ eq
        obtain ⟨left₁, _, leftMem₁⟩ := List.mem_flatMap.mp mem₁
        obtain ⟨left₂, _, leftMem₂⟩ := List.mem_flatMap.mp mem₂
        obtain ⟨right₁, _, rfl⟩ := List.mem_map.mp leftMem₁
        obtain ⟨right₂, _, rfl⟩ := List.mem_map.mp leftMem₂
        exact ne (congrArg rootSplit eq)

def weight [Semiring R] (atom : Nat → R) (forkWeight : Nat → Nat → Nat → R) :
    SplitTree i n → R
  | .leaf i => atom i
  | @SplitTree.fork i n split left right =>
    mul (forkWeight i (i + split.val + 1) (i + n + 2))
      (mul (weight atom forkWeight left) (weight atom forkWeight right))

/-- Strict, weighted interval convolution on positive-width intervals. -/
def weightedConvolution [Semiring R] (forkWeight : Nat → Nat → Nat → R)
    (f g : Nat → Nat → R) (i : Nat) : Nat → R
  | 0 => zero
  | n + 1 => total ((List.finRange (n + 1)).map fun split =>
      mul (forkWeight i (i + split.val + 1) (i + n + 2))
        (mul (f i split.val) (g (i + split.val + 1) (n - split.val))))

def strictConvolution [Semiring R] (f g : Nat → Nat → R) : Nat → Nat → R :=
  weightedConvolution (fun _ _ _ => one) f g

/-- Width-one atoms, then the binary convolution recurrence at every larger width. -/
def intervalDP [Semiring R] (atom : Nat → R) (forkWeight : Nat → Nat → Nat → R)
    (i n : Nat) : R :=
  match n with
  | 0 => atom i
  | n + 1 => total ((List.finRange (n + 1)).map fun split =>
    mul (forkWeight i (i + split.val + 1) (i + n + 2))
      (mul (intervalDP atom forkWeight i split.val)
           (intervalDP atom forkWeight (i + split.val + 1) (n - split.val))))
termination_by n
decreasing_by
  all_goals have := split.isLt; omega

theorem intervalDP_step [Semiring R] (atom : Nat → R) (forkWeight : Nat → Nat → Nat → R)
    (i n : Nat) :
    intervalDP atom forkWeight i (n + 1) =
      weightedConvolution forkWeight (intervalDP atom forkWeight) (intervalDP atom forkWeight)
        i (n + 1) := by
  rw [intervalDP, weightedConvolution]

theorem intervalDP_strict_step [Semiring R] (atom : Nat → R) (i n : Nat) :
    let dp := intervalDP atom (fun _ _ _ => one)
    dp i (n + 1) = strictConvolution dp dp i (n + 1) := by
  exact intervalDP_step atom _ i n

theorem intervalDP_eq_tree_sum [Semiring R] (atom : Nat → R)
    (forkWeight : Nat → Nat → Nat → R) (i n : Nat) :
    intervalDP atom forkWeight i n = total ((allTrees i n).map (weight atom forkWeight)) := by
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    cases n with
    | zero => rw [intervalDP, allTrees]; simp [weight, total, addZero]
    | succ n =>
      rw [intervalDP, allTrees, List.map_flatMap, total_flatMap]
      apply congrArg total
      apply List.map_congr_left
      intro split _
      rw [ih split.val split.isLt, ih (n - split.val) (by omega)]
      simp only [List.map_flatMap, List.map_map, Function.comp_def, weight]
      exact (total_pairs _ _ _ _ _).symm

/-- Ordinary incidence convolution on the chain, including both endpoints.
Here d is the distance j-i, including distance zero. -/
def incidenceConvolution [Semiring R] (f g : Nat → Nat → R) (i d : Nat) : R :=
  total ((List.finRange (d + 1)).map fun k => mul (f i k.val) (g (i + k.val) (d - k.val)))

def extendZeroDiagonal [Semiring R] (f : Nat → Nat → R) (i : Nat) : Nat → R
  | 0 => zero
  | n + 1 => f i n

theorem incidence_zero_diagonal_eq_strict [Semiring R]
    (f g : Nat → Nat → R) (i n : Nat) :
    incidenceConvolution (extendZeroDiagonal f) (extendZeroDiagonal g) i (n + 2) =
      strictConvolution f g i (n + 1) := by
  unfold incidenceConvolution strictConvolution
  rw [List.finRange_succ, List.finRange_succ_last]
  simp only [List.map_cons, List.map_append, List.map_map, List.map_nil, Function.comp_def,
    Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  rw [total, total_append]
  simp only [extendZeroDiagonal, zeroMul, zeroAdd, Nat.sub_self, mulZero, total, addZero,
    weightedConvolution, oneMul]
  apply congrArg total
  apply List.map_congr_left
  intro split _
  have rightLength : n + 2 - (split.val + 1) = (n - split.val) + 1 := by
    have := split.isLt
    omega
  rw [rightLength]
  simp only [Nat.add_assoc]

def natSemiring : Semiring Nat where
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  addAssoc := Nat.add_assoc
  addComm := Nat.add_comm
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero
  mulAssoc := Nat.mul_assoc
  oneMul := Nat.one_mul
  mulOne := Nat.mul_one
  zeroMul := Nat.zero_mul
  mulZero := Nat.mul_zero
  leftDistrib := Nat.mul_add
  rightDistrib := Nat.add_mul

def unitEdges (_ : Nat) (distance : Nat) : Nat := if distance = 1 then 1 else 0

/-- Three unit edges give one three-step path, but there are two split trees. -/
theorem incidence_power_ne_split_trees :
    letI := natSemiring
    incidenceConvolution (incidenceConvolution unitEdges unitEdges) unitEdges 0 3
      ≠ intervalDP (fun _ => 1) (fun _ _ _ => 1) 0 2 := by
  letI := natSemiring
  have dp : intervalDP (fun _ => (1 : Nat)) (fun _ _ _ => 1) 0 2 = 2 := by
    simp [intervalDP, List.finRange_succ, total, Fin.succ]
    rfl
  change incidenceConvolution (incidenceConvolution unitEdges unitEdges) unitEdges 0 3 ≠ _
  rw [dp]
  decide

/-- Interpret `none` as positive infinity. -/
def minPlusMin : Option Int → Option Int → Option Int
  | none, y => y
  | x, none => x
  | some x, some y => some (min x y)

def minPlusAdd : Option Int → Option Int → Option Int
  | some x, some y => some (x + y)
  | _, _ => none

def minPlusSemiring : Semiring (Option Int) where
  zero := none
  one := some 0
  add := minPlusMin
  mul := minPlusAdd
  addAssoc := by intro x y z; cases x <;> cases y <;> cases z <;> simp [minPlusMin, Int.min_assoc]
  addComm := by intro x y; cases x <;> cases y <;> simp [minPlusMin, Int.min_comm]
  zeroAdd := by intro x; rfl
  addZero := by intro x; cases x <;> rfl
  mulAssoc := by intro x y z; cases x <;> cases y <;> cases z <;> simp [minPlusAdd, Int.add_assoc]
  oneMul := by intro x; cases x <;> simp [minPlusAdd]
  mulOne := by intro x; cases x <;> simp [minPlusAdd]
  zeroMul := by intro x; rfl
  mulZero := by intro x; cases x <;> rfl
  leftDistrib := by intro x y z; cases x <;> cases y <;> cases z <;> simp [minPlusMin, minPlusAdd]
  rightDistrib := by intro x y z; cases x <;> cases y <;> cases z <;> simp [minPlusMin, minPlusAdd]

private theorem total_minPlus (xs : List (Option Int)) :
    @total _ minPlusSemiring xs = xs.foldr minPlusMin none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change minPlusMin x (@total _ minPlusSemiring xs) = minPlusMin x (xs.foldr minPlusMin none)
    rw [ih]

theorem intervalDP_eq_min_tree_weight (atom : Nat → Option Int)
    (forkWeight : Nat → Nat → Nat → Option Int) (i n : Nat) :
    letI := minPlusSemiring
    intervalDP atom forkWeight i n =
      ((allTrees i n).map (weight atom forkWeight)).foldr minPlusMin none := by
  letI := minPlusSemiring
  rw [intervalDP_eq_tree_sum]
  exact total_minPlus _

#print axioms mem_allTrees
#print axioms allTrees_nodup
#print axioms intervalDP_step
#print axioms intervalDP_strict_step
#print axioms intervalDP_eq_tree_sum
#print axioms incidence_zero_diagonal_eq_strict
#print axioms incidence_power_ne_split_trees
#print axioms intervalDP_eq_min_tree_weight

end IntervalConvolution
