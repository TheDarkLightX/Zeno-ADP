import Lean
import Init.Data.Rat.Lemmas

namespace CyclicCertificate

abbrev Chart (Cell : Type) := Cell → List (Nat × List Cell)

/-- A finite derivation. Its child list records every occurrence and its cost. -/
inductive Derives (chart : Chart Cell) : Cell → Nat → Prop where
  | node {cell weight} {args : List (Cell × Nat)}
      (rule : (weight, args.map Prod.fst) ∈ chart cell)
      (children : ∀ p ∈ args, Derives chart p.1 p.2) :
      Derives chart cell (weight + (args.map Prod.snd).sum)

def ChildScores (values : Cell → Option Nat) (args : List (Cell × Nat)) : Prop :=
  ∀ p ∈ args, values p.1 = some p.2

def ProductionBounds (chart : Chart Cell) (values : Cell → Option Nat) : Prop :=
  ∀ {cell weight args}, (weight, args.map Prod.fst) ∈ chart cell →
    ChildScores values args →
    ∃ v, values cell = some v ∧ v ≤ weight + (args.map Prod.snd).sum

def RankedSupport (chart : Chart Cell) (values : Cell → Option Nat)
    (rank : Cell → Nat) : Prop :=
  ∀ cell cost, values cell = some cost →
    ∃ (weight : Nat) (args : List (Cell × Nat)),
      (weight, args.map Prod.fst) ∈ chart cell ∧ ChildScores values args ∧
      (∀ p ∈ args, rank p.1 < rank cell) ∧ weight + (args.map Prod.snd).sum = cost

private theorem collectBounds (values : Cell → Option Nat) (args : List (Cell × Nat))
    (each : ∀ p ∈ args, ∃ v, values p.1 = some v ∧ v ≤ p.2) :
    ∃ bounded : List (Cell × Nat), bounded.map Prod.fst = args.map Prod.fst ∧
      ChildScores values bounded ∧ (bounded.map Prod.snd).sum ≤ (args.map Prod.snd).sum := by
  induction args with
  | nil => exact ⟨[], rfl, by simp [ChildScores], Nat.le_refl _⟩
  | cons first rest ih =>
    obtain ⟨v, score, le⟩ := each first (by simp)
    obtain ⟨bounded, cells, childScores, total⟩ := ih (fun p hp => each p (by simp [hp]))
    refine ⟨(first.1, v) :: bounded, by simp [cells], ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with eq | tail
      · subst p
        exact score
      · exact childScores p tail
    · simpa using Nat.add_le_add le total

theorem bounds_every_derivation {chart : Chart Cell} {values : Cell → Option Nat}
    (bounds : ProductionBounds chart values) {cell cost} (tree : Derives chart cell cost) :
    ∃ v, values cell = some v ∧ v ≤ cost := by
  induction tree with
  | @node cell weight args rule _ ih =>
    obtain ⟨bounded, cells, childScores, total⟩ := collectBounds values args ih
    have member : (weight, bounded.map Prod.fst) ∈ chart cell := by rwa [cells]
    obtain ⟨v, hv, le⟩ := bounds member childScores
    exact ⟨v, hv, Nat.le_trans le (Nat.add_le_add_left total weight)⟩

theorem ranked_support_attains {chart : Chart Cell} {values : Cell → Option Nat}
    {rank : Cell → Nat} (support : RankedSupport chart values rank) {cell cost}
    (score : values cell = some cost) : Derives chart cell cost := by
  have build : ∀ n c v, rank c = n → values c = some v → Derives chart c v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro c v hr hv
      obtain ⟨weight, args, rule, childScores, descent, total⟩ := support c v hv
      rw [← total]
      apply Derives.node rule
      intro p hp
      have earlier : rank p.1 < n := hr ▸ descent p hp
      exact ih _ earlier p.1 p.2 rfl (childScores p hp)
  exact build _ cell cost rfl score

theorem checked_characterizes {chart : Chart Cell} {values : Cell → Option Nat}
    {rank : Cell → Nat} (bounds : ProductionBounds chart values)
    (support : RankedSupport chart values rank) (cell : Cell) :
    match values cell with
    | none => ∀ value, ¬Derives chart cell value
    | some v => Derives chart cell v ∧ ∀ value, Derives chart cell value → v ≤ value := by
  cases h : values cell with
  | none =>
    intro value tree
    obtain ⟨score, hs, _⟩ := bounds_every_derivation bounds tree
    simp [h] at hs
  | some v =>
    refine ⟨ranked_support_attains support h, ?_⟩
    intro value tree
    obtain ⟨score, hs, le⟩ := bounds_every_derivation bounds tree
    have eq : score = v := Option.some.inj (hs.symm.trans h)
    simpa [eq] using le

end CyclicCertificate

namespace DiscountedCertificate

abbrev Step (State Action : Type) := (State → Rat) → State → Action → Rat

def Valid (q : Step State Action) (v : State → Rat) (policy : State → Action) : Prop :=
  (∀ s, q v s (policy s) = v s) ∧ ∀ s a, q v s a ≤ v s

def rolled (q : Step State Action) (v : State → Rat) :
    List (State → Action) → State → Rat
  | [] => v
  | policy :: rest => fun s => q (rolled q v rest) s (policy s)

theorem every_policy_prefix_bounded (q : Step State Action) (v : State → Rat)
    (policy : State → Action) (cert : Valid q v policy)
    (monotone : ∀ x y, (∀ s, x s ≤ y s) → ∀ s a, q x s a ≤ q y s a)
    (actions : List (State → Action)) (s : State) :
    rolled q v actions s ≤ v s := by
  induction actions generalizing s with
  | nil => exact Rat.le_refl
  | cons next rest ih => exact Rat.le_trans (monotone _ _ ih s (next s)) (cert.2 s (next s))

theorem selected_prefix_attains (q : Step State Action) (v : State → Rat)
    (policy : State → Action) (cert : Valid q v policy) (steps : Nat) :
    rolled q v (List.replicate steps policy) = v := by
  induction steps with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, rolled, ih]
    exact funext cert.1

theorem contractive_fixed_point_unique (step : V → V) (dist : V → V → Rat)
    (γ : Rat) (discount : γ < 1)
    (separates : ∀ x y, x ≠ y → 0 < dist x y)
    (contracts : ∀ x y, dist (step x) (step y) ≤ γ * dist x y)
    {x y : V} (hx : step x = x) (hy : step y = y) : x = y := by
  apply Classical.byContradiction
  intro h
  have bound := contracts x y
  rw [hx, hy] at bound
  have smaller := Rat.mul_lt_mul_of_pos_right discount (separates x y h)
  rw [Rat.one_mul] at smaller
  exact (Rat.not_lt.mpr bound) smaller

end DiscountedCertificate

namespace SeparatorCertificate

def Agrees (scope : Var → Prop) (a b : Var → Value) : Prop :=
  ∀ x, scope x → a x = b x

theorem glue_iff {left right : Var → Prop} [DecidablePred left]
    {a b : Var → Value} :
    (∃ joined, Agrees left joined a ∧ Agrees right joined b) ↔
      ∀ x, left x → right x → a x = b x := by
  constructor
  · intro ⟨joined, hl, hr⟩ x xl xr
    exact (hl x xl).symm.trans (hr x xr)
  · intro overlap
    refine ⟨(fun x => if left x then a x else b x), ?_, ?_⟩
    · intro x xl
      simp [xl]
    · intro x xr
      by_cases xl : left x
      · simp [xl, overlap x xl xr]
      · simp [xl]

theorem glue_attains_sum {left right : Var → Prop} [DecidablePred left]
    {a b : Var → Value} (overlap : ∀ x, left x → right x → a x = b x)
    (leftCost rightCost : (Var → Value) → Int)
    (localLeft : ∀ x y, Agrees left x y → leftCost x = leftCost y)
    (localRight : ∀ x y, Agrees right x y → rightCost x = rightCost y) :
    ∃ joined, Agrees left joined a ∧ Agrees right joined b ∧
      leftCost joined + rightCost joined = leftCost a + rightCost b := by
  obtain ⟨joined, hl, hr⟩ := glue_iff.mpr overlap
  exact ⟨joined, hl, hr, by rw [localLeft _ _ hl, localRight _ _ hr]⟩

/-- A row equation can read only earlier ranks. Two tables satisfying all the
equations on the requested prefix agree there, including absent rows. -/
theorem ranked_equations_unique (step : (n : Nat) → (Fin n → Value) → Value)
    (bound : Nat) {left right : Nat → Value}
    (validLeft : ∀ n < bound, left n = step n (fun k => left k.val))
    (validRight : ∀ n < bound, right n = step n (fun k => right k.val))
    (n : Nat) (inBounds : n < bound) : left n = right n := by
  induction n using Nat.strongRecOn with
  | ind n earlier =>
    rw [validLeft n inBounds, validRight n inBounds]
    apply congrArg (step n)
    funext k
    exact earlier k.val k.isLt (Nat.lt_trans k.isLt inBounds)

end SeparatorCertificate

#print axioms CyclicCertificate.bounds_every_derivation
#print axioms CyclicCertificate.ranked_support_attains
#print axioms CyclicCertificate.checked_characterizes
#print axioms DiscountedCertificate.every_policy_prefix_bounded
#print axioms DiscountedCertificate.selected_prefix_attains
#print axioms DiscountedCertificate.contractive_fixed_point_unique
#print axioms SeparatorCertificate.glue_iff
#print axioms SeparatorCertificate.glue_attains_sum
#print axioms SeparatorCertificate.ranked_equations_unique
