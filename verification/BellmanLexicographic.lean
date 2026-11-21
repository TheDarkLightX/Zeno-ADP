import BellmanBag

namespace BellmanLexicographic

open BellmanTabulation Std

section Selective

variable [LE A] [Min A] [IsLinearOrder A] [LawfulOrderMin A]

def choose (xs : List A) : List A := xs.min?.toList

/-- Each left argument is no greater than its corresponding right argument. -/
inductive Below [LE A] : List A → List A → Prop
  | nil : Below [] []
  | cons : x ≤ y → Below xs ys → Below (x :: xs) (y :: ys)

private theorem replaceBag (xs ys : List A) :
    (xs ++ ys).min? = (choose xs ++ ys).min? := by
  cases h : (xs ++ ys).min? with
  | none =>
    have empty := List.min?_eq_none_iff.mp h
    simp_all [choose]
  | some m =>
    obtain ⟨member, least⟩ := List.min?_eq_some_iff.mp h
    apply Eq.symm
    apply List.min?_eq_some_iff.mpr
    have inside : ∀ a ∈ choose xs, a ∈ xs := by
      intro a ha
      exact List.min?_mem (Option.mem_toList.mp ha)
    exact ⟨by
      rcases List.mem_append.mp member with hx | hy
      · apply List.mem_append_left
        apply Option.mem_toList.mpr
        exact List.min?_eq_some_iff.mpr ⟨hx, fun b hb => least b (List.mem_append_left _ hb)⟩
      · exact List.mem_append_right _ hy,
      fun b hb => least b (by
        rcases List.mem_append.mp hb with hx | hy
        · exact List.mem_append_left _ (inside b hx)
        · exact List.mem_append_right _ hy)⟩

private theorem appendSwap (xs ys : List A) : (xs ++ ys).min? = (ys ++ xs).min? := by
  cases h : (xs ++ ys).min? with
  | none => have e := List.min?_eq_none_iff.mp h; simp_all
  | some m =>
    apply Eq.symm
    simpa only [List.min?_eq_some_iff, List.mem_append, or_comm] using h

theorem choose_append (xs ys : List A) : choose (xs ++ ys) = choose (choose xs ++ choose ys) := by
  apply congrArg Option.toList
  rw [replaceBag xs ys, appendSwap (choose xs) ys, replaceBag ys (choose xs), appendSwap]

private theorem tuple_minimum (bags : List (List A)) :
    (tuples bags = [] ∧ tuples (bags.map choose) = []) ∨
      ∃ best, tuples (bags.map choose) = [best] ∧ best ∈ tuples bags ∧
        ∀ args ∈ tuples bags, Below best args := by
  induction bags with
  | nil => exact Or.inr ⟨[], rfl, by simp [tuples], by simp [tuples, Below.nil]⟩
  | cons xs bags ih =>
    cases h : xs.min? with
    | none =>
      have e := List.min?_eq_none_iff.mp h
      exact Or.inl (by simp [e, tuples, choose])
    | some x =>
      rcases ih with ⟨empty, earlyEmpty⟩ | ⟨tail, early, memTail, below⟩
      · exact Or.inl (by simp [tuples, empty, earlyEmpty])
      · have ⟨memX, leastX⟩ := List.min?_eq_some_iff.mp h
        refine Or.inr ⟨x :: tail, by simp [tuples, choose, h, early], ?_, ?_⟩
        · exact List.mem_flatMap.mpr ⟨x, memX, List.mem_map.mpr ⟨tail, memTail, rfl⟩⟩
        · intro args member
          obtain ⟨y, memY, hargs⟩ := List.mem_flatMap.mp member
          obtain ⟨ys, memYs, rfl⟩ := List.mem_map.mp hargs
          exact .cons (leastX y memY) (below ys memYs)

theorem choose_operator (apply : List A → A)
    (monotone : ∀ {xs ys}, Below xs ys → apply xs ≤ apply ys)
    (bags : List (List A)) :
    choose ((tuples bags).map apply) = choose ((tuples (bags.map choose)).map apply) := by
  rcases tuple_minimum bags with ⟨empty, earlyEmpty⟩ | ⟨best, early, member, least⟩
  · simp [empty, earlyEmpty]
  · have minimum : ((tuples bags).map apply).min? = some (apply best) := by
      apply List.min?_eq_some_iff.mpr
      refine ⟨List.mem_map_of_mem member, ?_⟩
      intro value hv
      obtain ⟨args, hargs, rfl⟩ := List.mem_map.mp hv
      exact monotone (least args hargs)
    simp [choose, early, minimum]

/-- A selective lexicographic minimum applies this theorem with its pair order.
The condition concerns the paired operator in that order. -/
theorem selective_atCell (chart : Chart O) (apply : O → List A → A)
    (monotone : ∀ op {xs ys}, Below xs ys → apply op xs ≤ apply op ys)
    (rank : Nat) :
    AtCell chart apply choose rank :=
  atCell_of_laws chart apply choose rfl choose_append
    (fun op => choose_operator (apply op) (monotone op)) rank

end Selective

structure Score where
  primary : Int
  secondary : Int
  deriving DecidableEq, Repr

instance : LE Score := ⟨fun x y =>
  x.primary < y.primary ∨ (x.primary = y.primary ∧ x.secondary ≤ y.secondary)⟩

instance (x y : Score) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ < _ ∨ (_ = _ ∧ _ ≤ (_ : Int))))

instance : IsLinearOrder Score where
  le_refl x := Or.inr ⟨rfl, Int.le_refl x.secondary⟩
  le_trans x y z a b := by
    change _ < _ ∨ (_ = _ ∧ _ ≤ _) at a b ⊢
    rcases a with a | ⟨a, a'⟩ <;> rcases b with b | ⟨b, b'⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨a.trans b, Int.le_trans a' b'⟩
  le_antisymm x y a b := by
    change _ < _ ∨ (_ = _ ∧ _ ≤ _) at a b
    rcases a with a | ⟨a, a'⟩ <;> rcases b with b | ⟨b, b'⟩
    · omega
    · omega
    · omega
    · cases x; cases y; simp_all; omega
  le_total x y := by
    change (_ < _ ∨ (_ = _ ∧ _ ≤ _)) ∨ (_ < _ ∨ (_ = _ ∧ _ ≤ _))
    rcases Int.lt_trichotomy x.primary y.primary with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases Int.le_total x.secondary y.secondary with s | s
      · exact Or.inl (Or.inr ⟨h, s⟩)
      · exact Or.inr (Or.inr ⟨h.symm, s⟩)
    · exact Or.inr (Or.inl h)

instance : Min Score := ⟨fun x y => if x ≤ y then x else y⟩

instance : LawfulOrderMin Score :=
  LawfulOrderMin.of_le_min_iff
    (by
      intro x a b
      change x ≤ (if a ≤ b then a else b) ↔ _
      by_cases h : a ≤ b
      · rw [if_pos h]
        exact ⟨fun l => ⟨l, le_trans l h⟩, And.left⟩
      · rw [if_neg h]
        have total : a ≤ b ∨ b ≤ a := Std.le_total
        have ba : b ≤ a := total.resolve_left h
        exact ⟨fun l => ⟨le_trans l ba, l⟩, And.right⟩)
    (by
      intro a b
      change (if a ≤ b then a else b) = a ∨ (if a ≤ b then a else b) = b
      by_cases h : a ≤ b <;> simp [h])

def add (x y : Score) : Score := ⟨x.primary + y.primary, x.secondary + y.secondary⟩

def zero : Score := ⟨0, 0⟩

private theorem add_monotone {x y z w : Score} (a : x ≤ y) (b : z ≤ w) :
    add x z ≤ add y w := by
  change _ < _ ∨ (_ = _ ∧ _ ≤ _) at a b
  change _ < _ ∨ (_ = _ ∧ _ ≤ _)
  simp only [add]
  rcases a with a | ⟨a, a'⟩ <;> rcases b with b | ⟨b, b'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; constructor <;> omega

def apply (weight : O → Score) (op : O) (xs : List Score) : Score :=
  xs.foldl add (weight op)

private theorem fold_monotone {xs ys : List Score} (h : Below xs ys)
    {x y : Score} (base : x ≤ y) : xs.foldl add x ≤ ys.foldl add y := by
  induction h generalizing x y with
  | nil => exact base
  | cons head _ ih => exact ih (add_monotone base head)

theorem additive_atCell (chart : Chart O) (weight : O → Score) (rank : Nat) :
    AtCell chart (apply weight) choose rank :=
  selective_atCell chart (apply weight) (fun _ {_ _} h => fold_monotone h (le_refl _)) rank

end BellmanLexicographic
