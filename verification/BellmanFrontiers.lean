import BellmanTabulation

namespace BellmanFrontiers

open BellmanTabulation

abbrev Score := Int × Int

def Below (x y : Score) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2

theorem below_refl (a : Score) : Below a a := ⟨Int.le_refl _, Int.le_refl _⟩

theorem below_trans {a b c : Score} (ab : Below a b) (bc : Below b c) : Below a c :=
  ⟨Int.le_trans ab.1 bc.1, Int.le_trans ab.2 bc.2⟩

theorem below_antisymm {a b : Score} (ab : Below a b) (ba : Below b a) : a = b :=
  Prod.ext (Int.le_antisymm ab.1 ba.1) (Int.le_antisymm ab.2 ba.2)

def OnFront (xs : List Score) (a : Score) : Prop :=
  a ∈ xs ∧ ∀ b ∈ xs, Below b a → Below a b

def Covers (xs ys : List A) (relation : A → A → Prop) : Prop :=
  ∀ a ∈ xs, ∃ b ∈ ys, relation b a

theorem front_covers (xs : List Score) :
    ∀ a ∈ xs, ∃ b, OnFront xs b ∧ Below b a := by
  induction xs with
  | nil => simp
  | cons head rest ih =>
    intro a member
    rcases List.mem_cons.mp member with rfl | inRest
    · by_cases dominated : ∃ b ∈ rest, Below b a ∧ ¬Below a b
      · obtain ⟨b, inTail, ba, nab⟩ := dominated
        obtain ⟨c, ⟨cMem, cMin⟩, cb⟩ := ih b inTail
        refine ⟨c, ⟨List.mem_cons_of_mem a cMem, ?_⟩, below_trans cb ba⟩
        intro d dMem dc
        rcases List.mem_cons.mp dMem with rfl | dTail
        · exact False.elim (nab (below_trans dc cb))
        · exact cMin d dTail dc
      · refine ⟨a, ⟨List.mem_cons_self, ?_⟩, below_refl a⟩
        intro b bMem ba
        rcases List.mem_cons.mp bMem with rfl | bTail
        · exact below_refl b
        · apply Classical.byContradiction
          intro nab
          exact dominated ⟨b, bTail, ba, nab⟩
    · obtain ⟨b, ⟨bMem, bMin⟩, ba⟩ := ih a inRest
      by_cases dominates : Below head b ∧ ¬Below b head
      · refine ⟨head, ⟨List.mem_cons_self, ?_⟩, below_trans dominates.1 ba⟩
        intro c cMem cHead
        rcases List.mem_cons.mp cMem with rfl | cTail
        · exact below_refl c
        · exact False.elim (dominates.2 (below_trans
            (bMin c cTail (below_trans cHead dominates.1)) cHead))
      · refine ⟨b, ⟨List.mem_cons_of_mem head bMem, ?_⟩, ba⟩
        intro c cMem cb
        rcases List.mem_cons.mp cMem with rfl | cTail
        · apply Classical.byContradiction
          intro nbc
          exact dominates ⟨cb, nbc⟩
        · exact bMin c cTail cb

private theorem front_transfer {xs ys : List Score} {a : Score}
    (there : Covers xs ys Below) (back : Covers ys xs Below) :
    OnFront xs a → OnFront ys a := by
  rintro ⟨mem, minimal⟩
  obtain ⟨b, bMem, ba⟩ := there a mem
  obtain ⟨c, cMem, cb⟩ := back b bMem
  have ab := below_trans (minimal c cMem (below_trans cb ba)) cb
  refine ⟨below_antisymm ba ab ▸ bMem, ?_⟩
  intro d dMem da
  obtain ⟨e, eMem, ed⟩ := back d dMem
  exact below_trans (minimal e eMem (below_trans ed da)) ed

theorem front_congr {xs ys : List Score}
    (there : Covers xs ys Below) (back : Covers ys xs Below) (a : Score) :
    OnFront xs a ↔ OnFront ys a :=
  ⟨front_transfer there back, front_transfer back there⟩

private theorem front_bag_covers {xs ys : List Score}
    (selection : ∀ a, a ∈ ys ↔ OnFront xs a) : Covers xs ys Below := by
  intro a ha
  obtain ⟨b, front, ba⟩ := front_covers xs a ha
  exact ⟨b, (selection b).mpr front, ba⟩

private theorem bag_front_covers {xs ys : List Score}
    (selection : ∀ a, a ∈ ys ↔ OnFront xs a) : Covers ys xs Below :=
  fun a ha => ⟨a, ((selection a).mp ha).1, below_refl a⟩

private theorem cover_append {w x y z : List A} {rel : A → A → Prop}
    (first : Covers w y rel) (second : Covers x z rel) :
    Covers (w ++ x) (y ++ z) rel := by
  intro a ha
  rcases List.mem_append.mp ha with left | right
  · obtain ⟨b, hb, ba⟩ := first a left
    exact ⟨b, List.mem_append_left _ hb, ba⟩
  · obtain ⟨b, hb, ba⟩ := second a right
    exact ⟨b, List.mem_append_right _ hb, ba⟩

/-- Filtering both groups before merging leaves exactly the same front scores. -/
theorem pareto_merge {xs ys xf yf : List Score}
    (left : ∀ a, a ∈ xf ↔ OnFront xs a) (right : ∀ a, a ∈ yf ↔ OnFront ys a)
    (a : Score) : OnFront (xs ++ ys) a ↔ OnFront (xf ++ yf) a :=
  front_congr (cover_append (front_bag_covers left) (front_bag_covers right))
    (cover_append (bag_front_covers left) (bag_front_covers right)) a

def Pointwise (p : A → A → Prop) : List A → List A → Prop
  | [], [] => True
  | a :: as, b :: bs => p a b ∧ Pointwise p as bs
  | _, _ => False

private theorem cover_product (rel : A → A → Prop)
    (xs ys : List (List A))
    (covered : Pointwise (fun x y => Covers x y rel) xs ys) :
    Covers (tuples xs) (tuples ys) (Pointwise rel) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      intro a aMem
      rw [tuples] at aMem
      cases List.mem_singleton.mp aMem
      exact ⟨[], List.mem_singleton_self _, trivial⟩
    | cons => cases covered
  | cons x xs ih =>
    cases ys with
    | nil => cases covered
    | cons y ys =>
      intro a aMem
      obtain ⟨h, hMem, hArg⟩ := List.mem_flatMap.mp aMem
      obtain ⟨t, tMem, rfl⟩ := List.mem_map.mp hArg
      obtain ⟨h', hh, hr⟩ := covered.1 h hMem
      obtain ⟨t', th, tr⟩ := ih _ covered.2 t tMem
      exact ⟨h' :: t', List.mem_flatMap_of_mem hh (List.mem_map_of_mem th), ⟨hr, tr⟩⟩

private theorem cover_apply {xs ys : List (List Score)} (op : List Score → Score)
    (monotone : ∀ {x y}, Pointwise Below x y → Below (op x) (op y))
    (covered : Pointwise (fun x y => Covers x y Below) xs ys) :
    Covers ((tuples xs).map op) ((tuples ys).map op) Below := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, yx⟩ := cover_product Below xs ys covered x hx
  exact ⟨op y, List.mem_map_of_mem hy, monotone yx⟩

private theorem covers_selected (choose : List Score → List Score)
    (selection : ∀ xs a, a ∈ choose xs ↔ OnFront xs a) (bags : List (List Score)) :
    Pointwise (fun x y => Covers x y Below) bags (bags.map choose) ∧
    Pointwise (fun x y => Covers x y Below) (bags.map choose) bags := by
  induction bags with
  | nil => exact ⟨trivial, trivial⟩
  | cons xs bags ih => exact ⟨⟨front_bag_covers (selection xs), ih.1⟩,
      ⟨bag_front_covers (selection xs), ih.2⟩⟩

/-- Moving front selection into the children preserves the front set when the
constructor is monotone in the pointwise componentwise order. -/
theorem pareto_operator (choose : List Score → List Score)
    (selection : ∀ xs a, a ∈ choose xs ↔ OnFront xs a)
    (op : List Score → Score) (monotone : ∀ {x y}, Pointwise Below x y → Below (op x) (op y))
    (bags : List (List Score)) (a : Score) :
    OnFront ((tuples bags).map op) a ↔ OnFront ((tuples (bags.map choose)).map op) a :=
  front_congr (cover_apply op monotone (covers_selected choose selection bags).1)
    (cover_apply op monotone (covers_selected choose selection bags).2) a

theorem additive_monotone {xs ys : List Score} (pointwise : Pointwise Below xs ys)
    (weight : Score) :
    Below (weight.1 + (xs.map Prod.fst).sum, weight.2 + (xs.map Prod.snd).sum)
      (weight.1 + (ys.map Prod.fst).sum, weight.2 + (ys.map Prod.snd).sum) := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | exact below_refl _ | cases pointwise
  | cons x xs ih =>
    cases ys with
    | nil => cases pointwise
    | cons y ys =>
      have h := ih pointwise.2
      have hx := pointwise.1.1
      have hy := pointwise.1.2
      have lx := h.1
      have ly := h.2
      constructor <;> simp only [List.map_cons, List.sum_cons] at * <;> omega

/-- The other arguments are fixed. Even with signed contributions, a
replacement improving a child's score by more than Δ rejects the original
parent candidate. -/
theorem delta_additive_replacement (before after context delta : Int)
    (outside : delta < before - after) :
    delta < (context + before) - (context + after) := by omega

/-- A candidate within the global band passes the band test of any subbag. -/
theorem delta_merge_no_loss (value delta : Int) (all subbag : List Int)
    (subset : ∀ score ∈ subbag, score ∈ all)
    (near : ∀ score ∈ all, value - score ≤ delta) :
    ∀ score ∈ subbag, value - score ≤ delta :=
  fun score h => near score (subset score h)

/-- If each discarded score has a replacement no larger, checking against
the retained scores gives precisely the original threshold test. -/
theorem delta_threshold_unchanged (value delta : Int) (all kept : List Int)
    (subset : ∀ score ∈ kept, score ∈ all)
    (cover : Covers all kept (· ≤ ·)) :
    (∀ score ∈ all, value - score ≤ delta) ↔ (∀ score ∈ kept, value - score ≤ delta) := by
  constructor
  · exact delta_merge_no_loss value delta all kept subset
  · intro h score member
    obtain ⟨k, hk, le⟩ := cover score member
    have := h k hk
    omega

def BandTest (cost : A → Int) (delta : Int) (xs : List A) (a : A) : Bool :=
  xs.all fun b => decide (cost a - cost b ≤ delta)

def band (cost : A → Int) (delta : Int) (xs : List A) : List A :=
  xs.filter (BandTest cost delta xs)

private theorem band_test_iff (cost : A → Int) (delta : Int) (xs : List A) (a : A) :
    BandTest cost delta xs a = true ↔ ∀ b ∈ xs, cost a - cost b ≤ delta := by
  simp [BandTest, List.all_eq_true]

private theorem min_mem (cost : A → Int) (x : A) (xs : List A) :
    ∃ b ∈ x :: xs, ∀ c ∈ x :: xs, cost b ≤ cost c := by
  induction xs generalizing x with
  | nil => exact ⟨x, List.mem_cons_self, fun c hc => List.mem_singleton.mp hc ▸ Int.le_refl _⟩
  | cons y ys ih =>
    obtain ⟨b, hb, min⟩ := ih y
    by_cases bx : cost b ≤ cost x
    · refine ⟨b, List.mem_cons_of_mem x hb, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact bx
      · exact min c hc
    · refine ⟨x, List.mem_cons_self, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Int.le_refl _
      · have := min c hc
        omega

private theorem band_covers (cost : A → Int) (delta : Int) (nonnegative : 0 ≤ delta) (xs : List A) :
    Covers xs (band cost delta xs) (fun a b => cost a ≤ cost b) := by
  cases xs with
  | nil => simp [Covers]
  | cons x xs =>
    intro a ha
    obtain ⟨b, hb, minimum⟩ := min_mem cost x xs
    refine ⟨b, List.mem_filter.mpr ⟨hb, (band_test_iff _ _ _ _).mpr ?_⟩, minimum a ha⟩
    intro c hc
    have := minimum c hc
    omega

private theorem band_test_reduce (cost : A → Int) (delta : Int) {xs ys : List A}
    (subset : ∀ a ∈ ys, a ∈ xs) (cover : Covers xs ys (fun a b => cost a ≤ cost b)) (a : A) :
    BandTest cost delta xs a = BandTest cost delta ys a := by
  apply Bool.eq_iff_iff.mpr
  rw [band_test_iff, band_test_iff]
  constructor
  · exact fun h b hb => h b (subset b hb)
  · intro h b hb
    obtain ⟨c, hc, cb⟩ := cover b hb
    have := h c hc
    omega

private theorem band_before_global (cost : A → Int) (delta : Int) (localBag globalBag : List A)
    (subset : ∀ a ∈ localBag, a ∈ globalBag) :
    (band cost delta localBag).filter (BandTest cost delta globalBag) =
      localBag.filter (BandTest cost delta globalBag) := by
  unfold band
  rw [List.filter_filter]
  apply List.filter_congr
  intro a _
  cases h : BandTest cost delta globalBag a
  · simp
  · have localPass : BandTest cost delta localBag a = true :=
      (band_test_iff _ _ _ _).mpr fun b hb => (band_test_iff _ _ _ _).mp h b (subset b hb)
    simp [localPass]

/-- Early per-alternative band selection preserves the exact ordered bag
of final answers, including repeats. -/
theorem delta_merge_ordered (cost : A → Int) (delta : Int) (nonnegative : 0 ≤ delta)
    (xs ys : List A) :
    band cost delta (xs ++ ys) = band cost delta (band cost delta xs ++ band cost delta ys) := by
  let early := band cost delta xs ++ band cost delta ys
  have cover : Covers (xs ++ ys) early (fun a b => cost a ≤ cost b) :=
    cover_append (band_covers cost delta nonnegative xs) (band_covers cost delta nonnegative ys)
  have subset : ∀ a ∈ early, a ∈ xs ++ ys := by
    intro a h
    rcases List.mem_append.mp h with left | right
    · exact List.mem_append_left _ (List.mem_filter.mp left).1
    · exact List.mem_append_right _ (List.mem_filter.mp right).1
  have filters : early.filter (BandTest cost delta (xs ++ ys)) =
      (xs ++ ys).filter (BandTest cost delta (xs ++ ys)) := by
    dsimp only [early]
    rw [List.filter_append, List.filter_append]
    rw [band_before_global cost delta xs (xs ++ ys) (fun a ha => List.mem_append_left ys ha)]
    rw [band_before_global cost delta ys (xs ++ ys) (fun a ha => List.mem_append_right xs ha)]
  change (xs ++ ys).filter (BandTest cost delta (xs ++ ys)) =
    early.filter (BandTest cost delta early)
  rw [← filters]
  apply List.filter_congr
  intro a _
  exact band_test_reduce cost delta subset cover a

def TupleBand (cost : A → Int) (delta : Int) : List (List A) → List A → Bool
  | [], [] => true
  | bag :: bags, x :: xs => BandTest cost delta bag x && TupleBand cost delta bags xs
  | _, _ => false

private theorem filter_product_cons (choices : List A) (tails : List (List A))
    (headTest : A → Bool) (tailTest resultTest : List A → Bool)
    (testCons : ∀ x xs, resultTest (x :: xs) = (headTest x && tailTest xs)) :
    (choices.filter headTest).flatMap (fun x => (tails.filter tailTest).map (x :: ·)) =
      (choices.flatMap (fun x => tails.map (x :: ·))).filter resultTest := by
  induction choices with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append, List.filter_map, Function.comp_def, testCons]
    cases h : headTest x <;> simp [h, ih]

private theorem tuple_band_ordered (cost : A → Int) (delta : Int) (bags : List (List A)) :
    tuples (bags.map (band cost delta)) = (tuples bags).filter (TupleBand cost delta bags) := by
  induction bags with
  | nil => rfl
  | cons bag bags ih =>
    simp only [List.map_cons, tuples, ih, band]
    exact filter_product_cons bag (tuples bags) (BandTest cost delta bag)
      (TupleBand cost delta bags) (TupleBand cost delta (bag :: bags)) (fun _ _ => rfl)

def totalCost (cost : A → Int) (args : List A) : Int := (args.map cost).sum

private theorem total_cost_monotone (cost : A → Int) {xs ys : List A}
    (pointwise : Pointwise (fun x y => cost x ≤ cost y) xs ys) :
    totalCost cost xs ≤ totalCost cost ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact Int.le_refl _
    | cons => cases pointwise
  | cons x xs ih =>
    cases ys with
    | nil => cases pointwise
    | cons y ys =>
      have tail := ih pointwise.2
      have head := pointwise.1
      simp only [totalCost, List.map_cons, List.sum_cons] at tail ⊢
      omega

private theorem global_passes_tuple_band (cost : A → Int) (delta : Int) (bags : List (List A))
    (args : List A) (member : args ∈ tuples bags)
    (near : ∀ other ∈ tuples bags, totalCost cost args - totalCost cost other ≤ delta) :
    TupleBand cost delta bags args = true := by
  induction bags generalizing args with
  | nil =>
    rw [tuples] at member
    cases List.mem_singleton.mp member
    rfl
  | cons bag bags ih =>
    obtain ⟨x, xMem, xArgs⟩ := List.mem_flatMap.mp member
    obtain ⟨xs, xsMem, rfl⟩ := List.mem_map.mp xArgs
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply (band_test_iff cost delta bag x).mpr
      intro b bMem
      have candidate : b :: xs ∈ tuples (bag :: bags) :=
        List.mem_flatMap_of_mem bMem (List.mem_map_of_mem xsMem)
      have h := near (b :: xs) candidate
      simp only [totalCost, List.map_cons, List.sum_cons] at h
      omega
    · apply ih xs xsMem
      intro ys ysMem
      have candidate : x :: ys ∈ tuples (bag :: bags) :=
        List.mem_flatMap_of_mem xMem (List.mem_map_of_mem ysMem)
      have h := near (x :: ys) candidate
      simp only [totalCost, List.map_cons, List.sum_cons] at h ⊢
      omega

/-- With a fixed constructor weight and additive child cost, early band
selection preserves the exact ordered bag, even when equal values occur. -/
theorem delta_operator_ordered (childCost : A → Int) (outputCost : B → Int)
    (delta : Int) (nonnegative : 0 ≤ delta) (op : List A → B) (weight : Int)
    (additive : ∀ args, outputCost (op args) = weight + totalCost childCost args)
    (bags : List (List A)) :
    band outputCost delta ((tuples bags).map op) =
      band outputCost delta ((tuples (bags.map (band childCost delta))).map op) := by
  let raw := (tuples bags).map op
  let earlyTuples := tuples (bags.map (band childCost delta))
  let early := earlyTuples.map op
  have selected :
      Pointwise (fun x y => Covers x y (fun a b => childCost a ≤ childCost b))
        bags (bags.map (band childCost delta)) := by
    induction bags with
    | nil => trivial
    | cons bag bags ih => exact ⟨band_covers childCost delta nonnegative bag, ih⟩
  have cover : Covers raw early (fun a b => outputCost a ≤ outputCost b) := by
    intro a ha
    obtain ⟨args, argMem, rfl⟩ := List.mem_map.mp ha
    obtain ⟨better, bMem, betterScore⟩ := cover_product _ _ _ selected args argMem
    refine ⟨op better, List.mem_map_of_mem bMem, ?_⟩
    change outputCost (op better) ≤ outputCost (op args)
    rw [additive, additive]
    have := total_cost_monotone childCost betterScore
    omega
  have earlyFilter : earlyTuples = (tuples bags).filter (TupleBand childCost delta bags) :=
    tuple_band_ordered childCost delta bags
  have subset : ∀ a ∈ early, a ∈ raw := by
    intro a ha
    obtain ⟨args, argsMem, rfl⟩ := List.mem_map.mp ha
    rw [earlyFilter] at argsMem
    exact List.mem_map_of_mem (List.mem_filter.mp argsMem).1
  have filters : early.filter (BandTest outputCost delta raw) =
      raw.filter (BandTest outputCost delta raw) := by
    dsimp only [early]
    rw [earlyFilter]
    dsimp only [raw]
    simp only [List.filter_map, List.filter_filter, Function.comp_def]
    apply congrArg (List.map op)
    apply List.filter_congr
    intro args argsMem
    cases h : BandTest outputCost delta ((tuples bags).map op) (op args)
    · simp
    · have near := (band_test_iff _ _ _ _).mp h
      have pass := global_passes_tuple_band childCost delta bags args argsMem (by
        intro other otherMem
        have compare := near (op other) (List.mem_map_of_mem otherMem)
        rw [additive, additive] at compare
        omega)
      simp [pass]
  change raw.filter (BandTest outputCost delta raw) = early.filter (BandTest outputCost delta early)
  rw [← filters]
  apply List.filter_congr
  intro a _
  exact band_test_reduce outputCost delta subset cover a

theorem delta_eq_exhaustive (chart : Chart O) (apply : O → List A → A) (cost : A → Int)
    (weight : O → Int) (delta : Int) (nonnegative : 0 ≤ delta)
    (additive : ∀ op args, cost (apply op args) = weight op + totalCost cost args)
    (bound i : Nat) (inBounds : i < bound) :
    lookup (tabulate chart apply (band cost delta) bound) i =
      band cost delta ((unfoldTrees chart i).map (foldTree apply)) :=
  tabulate_eq_exhaustive chart apply (band cost delta) bound
    (fun n _ => atCell_of_laws chart apply (band cost delta) rfl
      (delta_merge_ordered cost delta nonnegative)
      (fun op bags => delta_operator_ordered cost cost delta nonnegative
        (apply op) (weight op) (additive op) bags) n) i inBounds

/-- The front-set laws imply ordered table equality for any deterministic
representation that depends only on front membership. -/
theorem pareto_eq_exhaustive (chart : Chart O) (apply : O → List Score → Score)
    (choose : List Score → List Score) (empty : choose [] = [])
    (selection : ∀ xs a, a ∈ choose xs ↔ OnFront xs a)
    (canonical : ∀ xs ys, (∀ a, a ∈ choose xs ↔ a ∈ choose ys) → choose xs = choose ys)
    (monotone : ∀ op {x y}, Pointwise Below x y → Below (apply op x) (apply op y))
    (bound i : Nat) (inBounds : i < bound) :
    lookup (tabulate chart apply choose bound) i =
      choose ((unfoldTrees chart i).map (foldTree apply)) := by
  have merge (xs ys : List Score) :
      choose (xs ++ ys) = choose (choose xs ++ choose ys) := by
    apply canonical
    intro a
    rw [selection, selection, pareto_merge (selection xs) (selection ys)]
  have operator (op : O) (bags : List (List Score)) :
      choose ((tuples bags).map (apply op)) =
        choose ((tuples (bags.map choose)).map (apply op)) := by
    apply canonical
    intro a
    rw [selection, selection, pareto_operator choose selection (apply op) (monotone op)]
  exact tabulate_eq_exhaustive chart apply choose bound
    (fun n _ => atCell_of_laws chart apply choose empty merge operator n) i inBounds

theorem contraction_counterexample :
    (1 : Int) < 2 - 0 ∧ 2 / 2 - 0 / 2 ≤ 1 := by decide

theorem order_reversal_counterexample :
    Below (0, 0) (2, 0) ∧ ¬Below (-(0 : Int), 0) (-(2 : Int), 0) := by
  simp [Below]

end BellmanFrontiers

#print axioms BellmanFrontiers.front_covers
#print axioms BellmanFrontiers.pareto_merge
#print axioms BellmanFrontiers.pareto_operator
#print axioms BellmanFrontiers.additive_monotone
#print axioms BellmanFrontiers.delta_additive_replacement
#print axioms BellmanFrontiers.delta_merge_no_loss
#print axioms BellmanFrontiers.delta_threshold_unchanged
#print axioms BellmanFrontiers.delta_merge_ordered
#print axioms BellmanFrontiers.delta_operator_ordered
#print axioms BellmanFrontiers.delta_eq_exhaustive
#print axioms BellmanFrontiers.pareto_eq_exhaustive
#print axioms BellmanFrontiers.contraction_counterexample
#print axioms BellmanFrontiers.order_reversal_counterexample
