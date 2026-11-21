import BellmanTabulation

namespace BellmanBag

open BellmanTabulation

/-- An inhabited summary can have a zero value. The outer option means that
there are no derivations, independently of the summary's value. -/
structure Operations (A : Type) where
  merge : A → A → A
  combine : A → A → A
  merge_assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z)
  combine_merge_left : ∀ x y z, combine (merge x y) z = merge (combine x z) (combine y z)
  combine_merge_right : ∀ x y z, combine x (merge y z) = merge (combine x y) (combine x z)

variable (ops : Operations A)

def merge : Option A → Option A → Option A
  | none, y => y
  | x, none => x
  | some x, some y => some (ops.merge x y)

def combine : Option A → Option A → Option A
  | some x, some y => some (ops.combine x y)
  | _, _ => none

private theorem merge_assoc (x y z : Option A) :
    merge ops (merge ops x y) z = merge ops x (merge ops y z) := by
  cases x <;> cases y <;> cases z <;> simp [merge, ops.merge_assoc]

private theorem combine_merge_left (x y z : Option A) :
    combine ops (merge ops x y) z = merge ops (combine ops x z) (combine ops y z) := by
  cases x <;> cases y <;> cases z <;> simp [merge, combine, ops.combine_merge_left]

private theorem combine_merge_right (x y z : Option A) :
    combine ops x (merge ops y z) = merge ops (combine ops x y) (combine ops x z) := by
  cases x <;> cases y <;> cases z <;> simp [merge, combine, ops.combine_merge_right]

def reduce (xs : List (Option A)) : Option A := xs.foldr (merge ops) none

def summary (xs : List A) : Option A := reduce ops (xs.map some)

def choose (xs : List A) : List A := (summary ops xs).toList

private theorem reduce_append (xs ys : List (Option A)) :
    reduce ops (xs ++ ys) = merge ops (reduce ops xs) (reduce ops ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, reduce, List.foldr_cons] at ih ⊢
    rw [ih, merge_assoc]

private theorem summary_toList (x : Option A) :
    summary ops x.toList = x := by
  cases x <;> rfl

theorem choose_append (xs ys : List A) :
    choose ops (xs ++ ys) = choose ops (choose ops xs ++ choose ops ys) := by
  simp only [choose, summary, List.map_append, reduce_append]
  change (merge ops (summary ops xs) (summary ops ys)).toList =
    (merge ops (summary ops (summary ops xs).toList)
      (summary ops (summary ops ys).toList)).toList
  rw [summary_toList, summary_toList]

private theorem reduce_flatMap (xs : List B) (f : B → List (Option A)) :
    reduce ops (xs.flatMap f) = reduce ops (xs.map (reduce ops ∘ f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, reduce_append, ih]
    rfl

private theorem reduce_combine_left (xs : List (Option A)) (y : Option A) :
    reduce ops (xs.map (combine ops · y)) = combine ops (reduce ops xs) y := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change merge ops (combine ops x y) (reduce ops (xs.map (combine ops · y))) =
      combine ops (merge ops x (reduce ops xs)) y
    rw [ih, combine_merge_left]

private theorem reduce_combine_right (x : Option A) (ys : List (Option A)) :
    reduce ops (ys.map (combine ops x)) = combine ops x (reduce ops ys) := by
  induction ys with
  | nil => cases x <;> rfl
  | cons y ys ih =>
    change merge ops (combine ops x y) (reduce ops (ys.map (combine ops x))) =
      combine ops x (merge ops y (reduce ops ys))
    rw [ih, combine_merge_right]

/-- The neutral constructor suffix is specified by the algebra. -/
def apply (unit weight : A) (children : List A) : A :=
  ops.combine weight (children.foldr ops.combine unit)

theorem apply_eq_foldl (unit : A)
    (assoc : ∀ x y z, ops.combine (ops.combine x y) z = ops.combine x (ops.combine y z))
    (rightUnit : ∀ x, ops.combine x unit = x) (weight : A) (children : List A) :
    apply ops unit weight children = children.foldl ops.combine weight := by
  induction children generalizing weight with
  | nil => exact rightUnit weight
  | cons head rest ih =>
    rw [List.foldl_cons, ← ih]
    exact (assoc weight head (rest.foldr ops.combine unit)).symm

private theorem summary_tuples (unit : A) (bags : List (List A)) :
    summary ops ((tuples bags).map (fun args => args.foldr ops.combine unit)) =
      (bags.map (summary ops)).foldr (combine ops) (some unit) := by
  induction bags with
  | nil => rfl
  | cons bag bags ih =>
    let suffixes := (tuples bags).map (fun args => args.foldr ops.combine unit)
    calc
      _ = reduce ops (bag.flatMap
          (fun x => (suffixes.map some).map (combine ops (some x)))) := by
        simp [summary, tuples, suffixes, List.map_flatMap, List.map_map, Function.comp_def, combine]
      _ = reduce ops ((bag.map some).map (fun x => combine ops x (summary ops suffixes))) := by
        rw [reduce_flatMap]
        simp only [List.map_map, Function.comp_def]
        apply congrArg (reduce ops)
        apply List.map_congr_left
        intro x _
        simpa only [List.map_map, Function.comp_def, summary] using
          reduce_combine_right ops (some x) (suffixes.map some)
      _ = combine ops (summary ops bag) (summary ops suffixes) := reduce_combine_left ops _ _
      _ = _ := by rw [ih]; rfl

private theorem summary_apply (unit weight : A) (bags : List (List A)) :
    summary ops ((tuples bags).map (apply ops unit weight)) =
      combine ops (some weight) ((bags.map (summary ops)).foldr (combine ops) (some unit)) := by
  rw [← summary_tuples ops unit bags]
  change reduce ops (((tuples bags).map (apply ops unit weight)).map some) = _
  rw [show ((tuples bags).map (apply ops unit weight)).map some =
      (((tuples bags).map (fun args => args.foldr ops.combine unit)).map some).map
        (combine ops (some weight)) by simp [List.map_map, Function.comp_def, apply, combine]]
  exact reduce_combine_right ops _ _

theorem choose_operator (unit weight : A) (bags : List (List A)) :
    choose ops ((tuples bags).map (apply ops unit weight)) =
      choose ops ((tuples (bags.map (choose ops))).map (apply ops unit weight)) := by
  simp only [choose, summary_apply, List.map_map, Function.comp_def, summary_toList]

theorem atCell (chart : Chart O) (unit : A) (weight : O → A) (rank : Nat) :
    AtCell chart (fun op => apply ops unit (weight op)) (choose ops) rank :=
  atCell_of_laws chart (fun op => apply ops unit (weight op)) (choose ops) rfl
    (choose_append ops) (fun op => choose_operator ops unit (weight op)) rank

end BellmanBag
