import BellmanBag
import BellmanFrontiers

namespace ProductProvenance

open BellmanTabulation

/-- One strictly decreasing component suffices for row-major descent. -/
theorem pair_rank_descends (width i j a b : Nat)
    (inRow : b < width) (left : a ≤ i)
    (strict : a < i ∨ b < j) :
    a * width + b < i * width + j := by
  rcases strict with h | h
  · have step := Nat.mul_le_mul_right width (show a + 1 ≤ i by omega)
    rw [Nat.add_mul, Nat.one_mul] at step
    omega
  · have step := Nat.mul_le_mul_right width left
    omega

def strictlyBelow (a b : BellmanFrontiers.Score) : Prop :=
  BellmanFrontiers.Below a b ∧ ¬ BellmanFrontiers.Below b a

def translate (offset score : BellmanFrontiers.Score) : BellmanFrontiers.Score :=
  (offset.1 + score.1, offset.2 + score.2)

/-- Strict dominance is preserved and reflected when replacing one child. -/
theorem translate_strictlyBelow (offset a b : BellmanFrontiers.Score) :
    strictlyBelow (translate offset a) (translate offset b) ↔ strictlyBelow a b := by
  simp [strictlyBelow, BellmanFrontiers.Below, translate, Int.add_le_add_iff_left]

section
variable {A B O : Type} {source : BellmanBag.Operations A} {target : BellmanBag.Operations B}

structure Projection (source : BellmanBag.Operations A) (target : BellmanBag.Operations B) where
  map : A → B
  mapMerge : ∀ x y, map (source.merge x y) = target.merge (map x) (map y)
  mapCombine : ∀ x y, map (source.combine x y) = target.combine (map x) (map y)

variable (p : Projection source target)

private theorem project_product (unit : A) (xs : List A) :
    p.map (xs.foldr source.combine unit) =
      (xs.map p.map).foldr target.combine (p.map unit) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [p.mapCombine, ih]

private theorem project_apply (unit weight : A) (xs : List A) :
    p.map (BellmanBag.apply source unit weight xs) =
      BellmanBag.apply target (p.map unit) (p.map weight) (xs.map p.map) := by
  simp [BellmanBag.apply, p.mapCombine, project_product]

private theorem project_merge (a b : Option A) :
    (BellmanBag.merge source a b).map p.map =
      BellmanBag.merge target (a.map p.map) (b.map p.map) := by
  cases a <;> cases b <;> simp [BellmanBag.merge, p.mapMerge]

private theorem project_reduce (xs : List (Option A)) :
    (BellmanBag.reduce source xs).map p.map =
      BellmanBag.reduce target (xs.map (Option.map p.map)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (BellmanBag.merge source x (BellmanBag.reduce source xs)).map p.map =
      BellmanBag.merge target (x.map p.map) (BellmanBag.reduce target (xs.map (Option.map p.map)))
    rw [project_merge, ih]

theorem project_choice (xs : List A) :
    (BellmanBag.choose source xs).map p.map = BellmanBag.choose target (xs.map p.map) := by
  have h : (BellmanBag.summary source xs).map p.map =
      BellmanBag.summary target (xs.map p.map) := by
    simpa [BellmanBag.summary, List.map_map, Function.comp_def] using
      project_reduce p (xs.map some)
  rw [BellmanBag.choose, BellmanBag.choose, ← h]
  cases BellmanBag.summary source xs <;> rfl

mutual
  theorem project_tree (unit : A) (weight : O → A) (tree : Tree O) :
      p.map (foldTree (fun op => BellmanBag.apply source unit (weight op)) tree) =
        foldTree (fun op => BellmanBag.apply target (p.map unit) (p.map (weight op))) tree := by
    cases tree with
    | node op children =>
      simp only [foldTree, project_apply, project_children unit weight children]
  theorem project_children (unit : A) (weight : O → A) (children : List (Tree O)) :
      (foldChildren (fun op => BellmanBag.apply source unit (weight op)) children).map p.map =
        foldChildren (fun op => BellmanBag.apply target (p.map unit) (p.map (weight op))) children := by
    cases children with
    | nil => rfl
    | cons tree trees =>
      simp only [foldChildren, List.map_cons, project_tree unit weight tree,
        project_children unit weight trees]
end

/-- Projecting the stored summary gives direct tabulation under mapped weights.
The ordered empty or singleton bag also preserves inhabitation. -/
theorem project_table (chart : Chart O) (unit : A) (weight : O → A)
    (bound rank : Nat) (inBounds : rank < bound) :
    ((lookup (tabulate chart (fun op => BellmanBag.apply source unit (weight op))
      (BellmanBag.choose source) bound) rank)).map p.map =
      lookup (tabulate chart (fun op =>
        BellmanBag.apply target (p.map unit) (p.map (weight op)))
        (BellmanBag.choose target) bound) rank := by
  rw [tabulate_eq_exhaustive _ _ _ _ (fun n _ => BellmanBag.atCell source chart unit weight n)
    _ inBounds, project_choice]
  rw [tabulate_eq_exhaustive chart
    (fun op => BellmanBag.apply target (p.map unit) (p.map (weight op)))
    _ bound (fun n _ => BellmanBag.atCell target chart (p.map unit) (p.map ∘ weight) n)
    rank inBounds]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro tree _
  exact project_tree p unit weight tree

end

#print axioms pair_rank_descends
#print axioms translate_strictlyBelow
#print axioms project_choice
#print axioms project_tree
#print axioms project_children
#print axioms project_table

end ProductProvenance
