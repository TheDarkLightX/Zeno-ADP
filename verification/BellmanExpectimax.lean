import BellmanFrontiers
import Init.Data.Rat.Lemmas

namespace BellmanExpectimax

open BellmanTabulation
open BellmanFrontiers (Covers Pointwise cover_append cover_product)

local instance : Std.IsLinearOrder Rat where
  le_refl _ := Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total

local instance : Std.LawfulOrderMax Rat where
  max_eq_or a b := by
    rw [Rat.max_def]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  max_le_iff a b c := by
    rw [Rat.max_def]
    split
    · rename_i ab
      exact ⟨fun bc => ⟨Rat.le_trans ab bc, bc⟩, And.right⟩
    · rename_i nab
      have ba := Rat.le_total.resolve_left nab
      exact ⟨fun ac => ⟨ac, Rat.le_trans ba ac⟩, And.left⟩

def choose (xs : List Rat) : List Rat := xs.max?.toList

private abbrev Greater (a b : Rat) : Prop := b ≤ a

private theorem choose_covers (xs : List Rat) : Covers xs (choose xs) Greater := by
  intro a ha
  cases h : xs.max? with
  | none => simp [List.max?_eq_none_iff.mp h] at ha
  | some b =>
    exact ⟨b, by simp [choose, h], (List.max?_eq_some_iff.mp h).2 a ha⟩

private theorem choose_subset (xs : List Rat) : Covers (choose xs) xs Greater := by
  intro a ha
  cases h : xs.max? with
  | none => simp [choose, h] at ha
  | some b =>
    simp [choose, h] at ha
    subst a
    exact ⟨b, List.max?_mem h, Rat.le_refl⟩

private theorem choose_congr {xs ys : List Rat}
    (there : Covers xs ys Greater) (back : Covers ys xs Greater) : choose xs = choose ys := by
  apply congrArg Option.toList
  cases hx : xs.max? <;> cases hy : ys.max?
  · rfl
  · obtain ⟨x, hxmem, _⟩ := back _ (List.max?_mem hy)
    simp [List.max?_eq_none_iff.mp hx] at hxmem
  · obtain ⟨y, hymem, _⟩ := there _ (List.max?_mem hx)
    simp [List.max?_eq_none_iff.mp hy] at hymem
  · obtain ⟨y, hymem, ay⟩ := there _ (List.max?_mem hx)
    obtain ⟨x, hxmem, bx⟩ := back _ (List.max?_mem hy)
    exact congrArg some (Rat.le_antisymm
      (Rat.le_trans ay ((List.max?_eq_some_iff.mp hy).2 y hymem))
      (Rat.le_trans bx ((List.max?_eq_some_iff.mp hx).2 x hxmem)))

theorem choose_append (xs ys : List Rat) :
    choose (xs ++ ys) = choose (choose xs ++ choose ys) :=
  choose_congr (cover_append (choose_covers xs) (choose_covers ys))
    (cover_append (choose_subset xs) (choose_subset ys))

abbrev Weight := { w : Rat // 0 ≤ w }

def weighted : List Weight → List Rat → Rat
  | w :: ws, x :: xs => w.val * x + weighted ws xs
  | _, _ => 0

theorem weighted_monotone (weights : List Weight) {xs ys : List Rat}
    (le : Pointwise (fun upper lower => lower ≤ upper) ys xs) :
    weighted weights xs ≤ weighted weights ys := by
  induction xs generalizing ys weights with
  | nil =>
    cases ys with
    | nil => exact Rat.le_refl
    | cons => cases le
  | cons x xs ih =>
    cases ys with
    | nil => cases le
    | cons y ys =>
      cases weights with
      | nil => exact Rat.le_refl
      | cons w ws =>
        exact Rat.le_trans
          (Rat.add_le_add_right.mpr (Rat.mul_le_mul_of_nonneg_left le.1 w.property))
          (Rat.add_le_add_left.mpr (ih ws le.2))

def apply (bias : O → Rat) (weight : O → List Weight) (op : O) (args : List Rat) : Rat :=
  bias op + weighted (weight op) args

theorem choose_operator (bias : O → Rat) (weight : O → List Weight) (op : O)
    (bags : List (List Rat)) :
    choose ((tuples bags).map (apply bias weight op)) =
      choose ((tuples (bags.map choose)).map (apply bias weight op)) := by
  have aligned (xs : List (List Rat)) :
      Pointwise (fun a b => Covers a b Greater) xs (xs.map choose) ∧
        Pointwise (fun a b => Covers a b Greater) (xs.map choose) xs := by
    induction xs with
    | nil => exact ⟨trivial, trivial⟩
    | cons x xs ih => exact ⟨⟨choose_covers x, ih.1⟩, ⟨choose_subset x, ih.2⟩⟩
  have transfer {xs ys : List (List Rat)}
      (cover : Covers xs ys (Pointwise Greater)) :
      Covers (xs.map (apply bias weight op)) (ys.map (apply bias weight op)) Greater := by
    intro value member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨b, hb, dominates⟩ := cover a ha
    exact ⟨_, List.mem_map_of_mem hb,
      Rat.add_le_add_left.mpr (weighted_monotone _ dominates)⟩
  exact choose_congr
    (transfer (cover_product Greater _ _ (aligned bags).1))
    (transfer (cover_product Greater _ _ (aligned bags).2))

/-- A nullary rule can carry a terminal utility in its bias. A decision rule
uses one weight of one. A chance rule has a nonnegative weight for each
outcome. Normalization is needed for probability semantics. -/
theorem tabulate_eq_policy_max (chart : Chart O) (bias : O → Rat)
    (weight : O → List Weight) (bound i : Nat) (hi : i < bound) :
    lookup (tabulate chart (apply bias weight) choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree (apply bias weight))) :=
  tabulate_eq_exhaustive chart _ _ bound (fun n _ =>
    atCell_of_laws chart _ _ rfl choose_append (choose_operator bias weight) n) i hi

#print axioms BellmanExpectimax.choose_append
#print axioms BellmanExpectimax.weighted_monotone
#print axioms BellmanExpectimax.choose_operator
#print axioms BellmanExpectimax.tabulate_eq_policy_max

end BellmanExpectimax
