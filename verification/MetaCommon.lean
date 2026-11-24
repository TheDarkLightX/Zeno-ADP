/-
Common optima across additive cost models: the restriction theorem behind
`common_optimum`, stated over the ranked chart model of `BellmanTabulation`.

Each model `m` gives every operator a cost `w m op`. A derivation's cost in `m`
is the sum over its nodes. `V m n` are recorded cell values that satisfy every
cell equation, as `Optima::verify` and `Common::verify` check. Keeping at each
cell only the rules whose value equals the cell value in every selected model
gives a chart whose ordered derivation bag is exactly the full chart's bag
filtered to the derivations optimal in every selected model. Counts, existence
and ranked witnesses are read from that bag.
-/
import BellmanTabulation

open BellmanTabulation

namespace MetaCommon

universe u v

variable {O : Type u}

/-- The additive cost of a derivation in one model. -/
def cost (w : O → Int) (t : Tree O) : Int :=
  foldTree (fun op cs => w op + cs.sum) t

theorem cost_node (w : O → Int) (op : O) (ts : List (Tree O)) :
    cost w (.node op ts) = w op + (ts.map (cost w)).sum := by
  rw [cost, foldTree, foldChildren_eq_map]
  rfl

/-- Two lists related position by position. -/
inductive Forall2 {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Forall2 R as bs →
      Forall2 R (a :: as) (b :: bs)

theorem Forall2.imp {α : Type u} {β : Type v} {R S : α → β → Prop}
    (h : ∀ {a b}, R a b → S a b) : ∀ {as : List α} {bs : List β}, Forall2 R as bs → Forall2 S as bs
  | _, _, .nil => .nil
  | _, _, .cons hab rest => .cons (h hab) (Forall2.imp h rest)

@[simp] theorem forall2_nil_nil {α : Type u} {β : Type v} (R : α → β → Prop) :
    Forall2 R ([] : List α) ([] : List β) ↔ True :=
  ⟨fun _ => trivial, fun _ => .nil⟩

@[simp] theorem forall2_nil_cons {α : Type u} {β : Type v} (R : α → β → Prop) (b : β) (bs : List β) :
    Forall2 R ([] : List α) (b :: bs) ↔ False :=
  ⟨fun h => (nomatch h), False.elim⟩

@[simp] theorem forall2_cons_nil {α : Type u} {β : Type v} (R : α → β → Prop) (a : α) (as : List α) :
    Forall2 R (a :: as) ([] : List β) ↔ False :=
  ⟨fun h => (nomatch h), False.elim⟩

theorem sum_le_of_forall2 : ∀ {as bs : List Int}, Forall2 (· ≤ ·) as bs → as.sum ≤ bs.sum
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
    have := sum_le_of_forall2 rest
    simp only [List.sum_cons]
    omega

theorem sum_eq_of_forall2 : ∀ {as bs : List Int}, Forall2 (· = ·) as bs → as.sum = bs.sum
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
    have := sum_eq_of_forall2 rest
    simp only [List.sum_cons]
    omega

theorem flatMap_congr {A B : Type u} {f g : A → List B} :
    ∀ {l : List A}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, flatMap_congr (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem nodup_map_on {A B : Type} (f : A → B) :
    ∀ {l : List A}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: rest, inj, nd => by
    rw [List.nodup_cons] at nd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_on f (fun x hx y hy => inj x (List.mem_cons_of_mem a hx) y
      (List.mem_cons_of_mem a hy)) nd.2⟩
    intro hmem
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hmem
    have := inj b (List.mem_cons_of_mem a hb) a List.mem_cons_self e
    exact nd.1 (this ▸ hb)

@[simp] theorem forall2_cons {α : Type u} {β : Type v} (R : α → β → Prop) (a : α) (as : List α)
    (b : β) (bs : List β) : Forall2 R (a :: as) (b :: bs) ↔ R a b ∧ Forall2 R as bs :=
  ⟨fun h => by cases h with | cons hab rest => exact ⟨hab, rest⟩, fun ⟨hab, rest⟩ => .cons hab rest⟩

/-- The least of the inhabited values. -/
def minOpt : List (Option Int) → Option Int
  | [] => none
  | none :: rest => minOpt rest
  | some a :: rest =>
    match minOpt rest with
    | none => some a
    | some b => some (min a b)

theorem minOpt_le {l : List (Option Int)} {a : Int} (h : some a ∈ l) :
    ∃ b, minOpt l = some b ∧ b ≤ a := by
  induction l with
  | nil => cases h
  | cons x rest ih =>
    rcases List.mem_cons.mp h with e | h'
    · subst e
      simp only [minOpt]
      cases minOpt rest with
      | none => exact ⟨a, rfl, Int.le_refl a⟩
      | some b => exact ⟨min a b, rfl, Int.min_le_left a b⟩
    · obtain ⟨b, hb, hle⟩ := ih h'
      cases x with
      | none => exact ⟨b, by simp [minOpt, hb], hle⟩
      | some c =>
        refine ⟨min c b, by simp [minOpt, hb], ?_⟩
        exact Int.le_trans (Int.min_le_right c b) hle

/-- The sum of a list of values, if every one is inhabited. -/
def sumOpt : List (Option Int) → Option Int
  | [] => some 0
  | none :: _ => none
  | some a :: rest => (sumOpt rest).map (a + ·)

/-- A rule's value in one model: its cost plus its children's values. -/
def ruleVal (V : Nat → Option Int) (w : O → Int) {n : Nat} (r : Rule O n) : Option Int :=
  (sumOpt (r.2.map fun c => V c.val)).map (w r.1 + ·)

/-- The cell equations of one model. -/
def CellEquations (chart : Chart O) (w : O → Int) (V : Nat → Option Int) : Prop :=
  ∀ n, V n = minOpt ((chart n).map (ruleVal V w))

/-- Every member of a tuple comes from its bag. -/
theorem mem_tuples {A : Type u} : ∀ {bags : List (List A)} {xs : List A},
    xs ∈ tuples bags → Forall2 (fun x b => x ∈ b) xs bags
  | [], xs, h => by
    simp [tuples] at h
    subst h
    exact Forall2.nil
  | b :: rest, xs, h => by
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    exact Forall2.cons hx (mem_tuples hys)

/-- Children values bound children costs from below, and sum accordingly. -/
theorem sum_bound (w : O → Int) (V : Nat → Option Int) :
    ∀ {cs : List Nat} {xs : List (Tree O)},
      Forall2 (fun x c => ∃ v, V c = some v ∧ v ≤ cost w x) xs cs →
      ∃ s, sumOpt (cs.map V) = some s ∧ s ≤ (xs.map (cost w)).sum
  | [], [], _ => ⟨0, rfl, by simp⟩
  | c :: cs, x :: xs, Forall2.cons ⟨v, hv, hle⟩ rest => by
    obtain ⟨s, hs, hsle⟩ := sum_bound w V rest
    refine ⟨v + s, ?_, ?_⟩
    · simp [sumOpt, hv, hs]
    · simp only [List.map_cons, List.sum_cons]
      omega

/-- Every derivation of a cell costs at least the recorded value, which is inhabited. -/
theorem lower_bound (chart : Chart O) (w : O → Int) (V : Nat → Option Int)
    (eqs : CellEquations chart w V) :
    ∀ n, ∀ t ∈ unfoldTrees chart n, ∃ v, V n = some v ∧ v ≤ cost w t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht
    rw [unfoldTrees] at ht
    simp only [List.mem_flatMap, List.mem_map] at ht
    obtain ⟨r, hr, xs, hxs, rfl⟩ := ht
    have members := mem_tuples hxs
    -- Each child tree is bounded by its cell value.
    have bounds : Forall2 (fun x c => ∃ v, V c = some v ∧ v ≤ cost w x)
        xs (r.2.map Fin.val) := by
      have : ∀ {cs : List (Fin n)} {xs : List (Tree O)},
          Forall2 (fun x b => x ∈ b) xs (cs.map fun c => unfoldTrees chart c.val) →
          Forall2 (fun x c => ∃ v, V c = some v ∧ v ≤ cost w x) xs (cs.map Fin.val) := by
        intro cs
        induction cs with
        | nil => intro xs h; cases h; exact Forall2.nil
        | cons c cs ihc =>
          intro xs h
          cases h with
          | cons hx hrest => exact Forall2.cons (ih c.val c.isLt _ hx) (ihc hrest)
      exact this members
    obtain ⟨s, hs, hsle⟩ := sum_bound w V bounds
    have hval : ruleVal V w r = some (w r.1 + s) := by
      have : (r.2.map fun c => V c.val) = (r.2.map Fin.val).map V := by simp
      unfold ruleVal
      rw [this, hs]
      rfl
    have hmem : some (w r.1 + s) ∈ (chart n).map (ruleVal V w) :=
      List.mem_map.mpr ⟨r, hr, hval⟩
    obtain ⟨b, hb, hble⟩ := minOpt_le hmem
    refine ⟨b, by rw [eqs n]; exact hb, ?_⟩
    rw [cost_node]
    omega

theorem minOpt_attained : ∀ {l : List (Option Int)} {b : Int}, minOpt l = some b → some b ∈ l
  | [], _, h => by simp [minOpt] at h
  | none :: rest, b, h => by
    simp only [minOpt] at h
    exact List.mem_cons_of_mem _ (minOpt_attained h)
  | some a :: rest, b, h => by
    simp only [minOpt] at h
    cases hr : minOpt rest with
    | none =>
      rw [hr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | some c =>
      rw [hr] at h
      simp only [Option.some.injEq] at h
      by_cases hac : a ≤ c
      · rw [Int.min_eq_left hac] at h
        subst h
        exact List.mem_cons_self
      · rw [Int.min_eq_right (by omega)] at h
        subst h
        exact List.mem_cons_of_mem _ (minOpt_attained hr)

theorem sumOpt_some : ∀ {l : List (Option Int)} {s : Int}, sumOpt l = some s →
    ∃ vs : List Int, l = vs.map some ∧ vs.sum = s
  | [], s, h => by
    simp only [sumOpt, Option.some.injEq] at h
    exact ⟨[], rfl, by simp [h]⟩
  | none :: _, _, h => by simp [sumOpt] at h
  | some a :: rest, s, h => by
    simp only [sumOpt] at h
    cases hr : sumOpt rest with
    | none => rw [hr] at h; simp at h
    | some t =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨vs, hvs, hsum⟩ := sumOpt_some hr
      exact ⟨a :: vs, by simp [hvs], by simp [hsum]; omega⟩

theorem mem_tuples_of_forall2 {A : Type u} : ∀ {bags : List (List A)} {xs : List A},
    Forall2 (fun x b => x ∈ b) xs bags → xs ∈ tuples bags
  | [], [], _ => by simp [tuples]
  | b :: rest, x :: xs, .cons hx hrest => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    exact ⟨x, hx, xs, mem_tuples_of_forall2 hrest, rfl⟩

/-- Every inhabited recorded value is the cost of some derivation of its cell. -/
theorem attained (chart : Chart O) (w : O → Int) (V : Nat → Option Int)
    (eqs : CellEquations chart w V) :
    ∀ n v, V n = some v → ∃ t ∈ unfoldTrees chart n, cost w t = v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv
    rw [eqs n] at hv
    obtain ⟨r, hr, hrv⟩ := List.mem_map.mp (minOpt_attained hv)
    unfold ruleVal at hrv
    cases hs : sumOpt (r.2.map fun c => V c.val) with
    | none => rw [hs] at hrv; simp at hrv
    | some s =>
      rw [hs] at hrv
      simp only [Option.map_some, Option.some.injEq] at hrv
      obtain ⟨vs, hvs, hsum⟩ := sumOpt_some hs
      -- Choose an attaining derivation for each child.
      have choose : ∀ {cs : List (Fin n)} {vs : List Int},
          cs.map (fun c => V c.val) = vs.map some →
          ∃ xs : List (Tree O), Forall2 (fun x b => x ∈ b) xs (cs.map fun c => unfoldTrees chart c.val) ∧
            xs.map (cost w) = vs := by
        intro cs
        induction cs with
        | nil => intro vs h; cases vs with
          | nil => exact ⟨[], .nil, rfl⟩
          | cons _ _ => simp at h
        | cons c cs ihc =>
          intro vs h
          cases vs with
          | nil => simp at h
          | cons v vs =>
            simp only [List.map_cons, List.cons.injEq] at h
            obtain ⟨t, ht, hct⟩ := ih c.val c.isLt v h.1
            obtain ⟨xs, hxs, hcs⟩ := ihc h.2
            exact ⟨t :: xs, .cons ht hxs, by simp [hct, hcs]⟩
      obtain ⟨xs, hxs, hcost⟩ := choose hvs
      refine ⟨.node r.1 xs, ?_, ?_⟩
      · rw [unfoldTrees]
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨r, hr, xs, mem_tuples_of_forall2 hxs, rfl⟩
      · rw [cost_node, hcost, hsum, hrv]

/-- With the cell equations, a derivation's cost equals the recorded value
exactly when no derivation of the same cell costs less. -/
theorem value_iff_optimal (chart : Chart O) (w : O → Int) (V : Nat → Option Int)
    (eqs : CellEquations chart w V) {n : Nat} {t : Tree O} (ht : t ∈ unfoldTrees chart n) :
    some (cost w t) = V n ↔ ∀ t' ∈ unfoldTrees chart n, cost w t ≤ cost w t' := by
  obtain ⟨v, hv, hle⟩ := lower_bound chart w V eqs n t ht
  rw [hv]
  constructor
  · intro e t' ht'
    obtain ⟨v', hv', hle'⟩ := lower_bound chart w V eqs n t' ht'
    rw [hv] at hv'
    simp only [Option.some.injEq] at e hv'
    omega
  · intro all
    obtain ⟨t', ht', hc⟩ := attained chart w V eqs n v hv
    have := all t' ht'
    simp only [Option.some.injEq]
    omega

/-- Equal sums of pointwise-bounded lists force pointwise equality. -/
theorem eq_of_sum_eq : ∀ {vs cs : List Int},
    Forall2 (· ≤ ·) vs cs → vs.sum = cs.sum → Forall2 (· = ·) vs cs
  | [], [], _, _ => Forall2.nil
  | v :: vs, c :: cs, Forall2.cons hle rest, hsum => by
    simp only [List.sum_cons] at hsum
    have tail_le : vs.sum ≤ cs.sum := by
      clear hsum
      induction rest with
      | nil => simp
      | cons h _ ih => simp only [List.sum_cons]; omega
    exact Forall2.cons (by omega) (eq_of_sum_eq rest (by omega))

/-- A child predicate checked position by position. -/
def allAt {A : Type u} (P : Nat → A → Bool) : List Nat → List A → Bool
  | [], [] => true
  | c :: cs, x :: xs => P c x && allAt P cs xs
  | _, _ => false

theorem flatMap_if_filter {A B : Type u} (l : List A) (p : A → Bool) (g : A → List B) :
    l.flatMap (fun x => if p x then g x else []) = (l.filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    by_cases h : p x <;> simp [List.flatMap_cons, h, ih]

/-- Filtering tuples position by position equals the tuples of filtered bags. -/
theorem filter_tuples {A : Type u} (B : Nat → List A) (P : Nat → A → Bool) :
    ∀ cs : List Nat, (tuples (cs.map B)).filter (allAt P cs) =
      tuples (cs.map fun c => (B c).filter (P c))
  | [] => by simp [tuples, allAt]
  | c :: cs => by
    simp only [List.map_cons, tuples, List.filter_flatMap, List.filter_map]
    have step : ∀ x, ((tuples (cs.map B)).filter (allAt P (c :: cs) ∘ (x :: ·))) =
        if P c x then (tuples (cs.map B)).filter (allAt P cs) else [] := by
      intro x
      by_cases h : P c x
      · simp only [h, if_true]
        apply List.filter_congr
        intro ys _
        simp [allAt, h]
      · simp only [h]
        apply List.filter_eq_nil_iff.mpr
        intro ys _
        simp [allAt, h]
    have : (fun x => ((tuples (cs.map B)).filter (allAt P (c :: cs) ∘ (x :: ·))).map (x :: ·)) =
        fun x => if P c x then ((tuples (cs.map B)).filter (allAt P cs)).map (x :: ·) else [] := by
      funext x
      rw [step x]
      split <;> rfl
    rw [this, flatMap_if_filter, filter_tuples B P cs]

/-- The models in `S` and their costs and recorded values. -/
structure Models (O : Type u) where
  S : List Nat
  w : Nat → O → Int
  V : Nat → Nat → Option Int

/-- A derivation of cell `n` is optimal in every selected model. -/
def optimalAt (M : Models O) (n : Nat) (t : Tree O) : Bool :=
  M.S.all fun m => decide (some (cost (M.w m) t) = M.V m n)

/-- A rule attains the cell value in every selected model. -/
def wins (M : Models O) {n : Nat} (r : Rule O n) : Bool :=
  M.S.all fun m => decide (ruleVal (M.V m) (M.w m) r = M.V m n)

/-- The chart that keeps only the common winning rules. -/
def restrict (chart : Chart O) (M : Models O) : Chart O :=
  fun n => (chart n).filter (wins M)

/-- One model, one node: the node is optimal exactly when its rule attains the
cell value and every child is optimal at its cell. -/
theorem node_optimal_iff (chart : Chart O) (w : O → Int) (V : Nat → Option Int)
    (eqs : CellEquations chart w V) {n : Nat} {r : Rule O n} (hr : r ∈ chart n)
    {xs : List (Tree O)}
    (members : Forall2 (fun x c => x ∈ unfoldTrees chart c) xs (r.2.map Fin.val)) :
    some (cost w (.node r.1 xs)) = V n ↔
      ruleVal V w r = V n ∧
        Forall2 (fun x c => some (cost w x) = V c) xs (r.2.map Fin.val) := by
  have bounds : Forall2 (fun x c => ∃ v, V c = some v ∧ v ≤ cost w x) xs (r.2.map Fin.val) :=
    members.imp fun {x c} hx => lower_bound chart w V eqs c x hx
  -- Name the child values.
  have values : ∀ {cs : List Nat} {xs : List (Tree O)},
      Forall2 (fun x c => ∃ v, V c = some v ∧ v ≤ cost w x) xs cs →
      ∃ vs : List Int, cs.map V = vs.map some ∧ Forall2 (· ≤ ·) vs (xs.map (cost w)) := by
    intro cs
    induction cs with
    | nil => intro xs h; cases h; exact ⟨[], rfl, Forall2.nil⟩
    | cons c cs ih =>
      intro xs h
      cases h with
      | cons hx hrest =>
        obtain ⟨v, hv, hle⟩ := hx
        obtain ⟨vs, hvs, hles⟩ := ih hrest
        exact ⟨v :: vs, by simp [hv, hvs], Forall2.cons hle hles⟩
  obtain ⟨vs, hvs, hles⟩ := values bounds
  have sum_some : ∀ vs : List Int, sumOpt (vs.map some) = some vs.sum := by
    intro vs
    induction vs with
    | nil => rfl
    | cons v vs ih => simp [sumOpt, ih]
  have hval : ruleVal V w r = some (w r.1 + vs.sum) := by
    have : (r.2.map fun c => V c.val) = (r.2.map Fin.val).map V := by simp
    simp only [ruleVal, this, hvs, sum_some]
    rfl
  have hmem : some (w r.1 + vs.sum) ∈ (chart n).map (ruleVal V w) :=
    List.mem_map.mpr ⟨r, hr, hval⟩
  obtain ⟨b, hb, hble⟩ := minOpt_le hmem
  have hVn : V n = some b := by rw [eqs n]; exact hb
  have sum_le : vs.sum ≤ (xs.map (cost w)).sum := sum_le_of_forall2 hles
  -- Pointwise statements over the named values.
  have child_eq : ∀ {cs : List Nat} {xs : List (Tree O)} {vs : List Int},
      cs.map V = vs.map some →
      (Forall2 (fun x c => some (cost w x) = V c) xs cs ↔
        Forall2 (· = ·) vs (xs.map (cost w))) := by
    intro cs
    induction cs with
    | nil =>
      intro xs vs h
      cases vs with
      | nil => cases xs <;> simp
      | cons _ _ => simp at h
    | cons c cs ih =>
      intro xs vs h
      cases vs with
      | nil => simp at h
      | cons v vs =>
        simp only [List.map_cons, List.cons.injEq] at h
        cases xs with
        | nil => simp
        | cons x xs =>
          simp only [forall2_cons, List.map_cons, h.1, ih h.2]
          constructor
          · rintro ⟨e, rest⟩; exact ⟨by simpa using e.symm, rest⟩
          · rintro ⟨e, rest⟩; exact ⟨by simp [e], rest⟩
  rw [cost_node, hVn, hval, child_eq hvs]
  constructor
  · intro e
    have e' : w r.1 + (xs.map (cost w)).sum = b := by simpa using e
    have eqsum : vs.sum = (xs.map (cost w)).sum := by omega
    refine ⟨by simp; omega, eq_of_sum_eq hles eqsum⟩
  · rintro ⟨e, pointwise⟩
    have e' : w r.1 + vs.sum = b := by simpa using e
    have : vs.sum = (xs.map (cost w)).sum := sum_eq_of_forall2 pointwise
    simp; omega

/-- The restriction theorem. If the recorded values satisfy every cell equation
of every selected model, the restricted chart's ordered derivations at any cell
are exactly the full chart's derivations that are optimal in every selected model,
in the same order and with the same multiplicities. -/
theorem restrict_unfold (chart : Chart O) (M : Models O)
    (eqs : ∀ m ∈ M.S, CellEquations chart (M.w m) (M.V m)) :
    ∀ n, unfoldTrees (restrict chart M) n = (unfoldTrees chart n).filter (optimalAt M n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [unfoldTrees, unfoldTrees, List.filter_flatMap, restrict, ← flatMap_if_filter]
    apply flatMap_congr
    intro r hr
    -- Children of the restricted chart are the filtered children.
    have children : (r.2.map fun c => unfoldTrees (restrict chart M) c.val) =
        (r.2.map Fin.val).map fun c => (unfoldTrees chart c).filter (optimalAt M c) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c _
      exact ih c.val c.isLt
    rw [children, List.filter_map]
    have chartChildren : (r.2.map fun c => unfoldTrees chart c.val) =
        (r.2.map Fin.val).map fun c => unfoldTrees chart c := by simp
    rw [chartChildren]
    -- Each tuple's node is optimal iff its rule wins and each child is optimal.
    have pointwise : ∀ xs ∈ tuples ((r.2.map Fin.val).map fun c => unfoldTrees chart c),
        (optimalAt M n ∘ Tree.node r.1) xs = (wins M r && allAt (optimalAt M) (r.2.map Fin.val) xs) := by
      intro xs hxs
      have raw := mem_tuples hxs
      have members : Forall2 (fun x c => x ∈ unfoldTrees chart c) xs (r.2.map Fin.val) := by
        have : ∀ {cs : List Nat} {xs : List (Tree O)},
            Forall2 (fun x b => x ∈ b) xs (cs.map fun c => unfoldTrees chart c) →
            Forall2 (fun x c => x ∈ unfoldTrees chart c) xs cs := by
          intro cs
          induction cs with
          | nil => intro xs h; cases h; exact Forall2.nil
          | cons c cs ihc => intro xs h; cases h with
            | cons hx hrest => exact Forall2.cons hx (ihc hrest)
        exact this raw
      have allAt_iff : ∀ {cs : List Nat} {xs : List (Tree O)},
          Forall2 (fun x c => x ∈ unfoldTrees chart c) xs cs →
          (allAt (optimalAt M) cs xs = true ↔
            ∀ m ∈ M.S, Forall2 (fun x c => some (cost (M.w m) x) = M.V m c) xs cs) := by
        intro cs
        induction cs with
        | nil => intro xs h; cases h; simp [allAt]
        | cons c cs ihc =>
          intro xs h
          cases h with
          | cons hx hrest =>
            simp only [allAt, Bool.and_eq_true, ihc hrest, optimalAt, List.all_eq_true,
              decide_eq_true_eq, forall2_cons]
            constructor
            · rintro ⟨h1, h2⟩ m hm; exact ⟨h1 m hm, h2 m hm⟩
            · intro h; exact ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp, optimalAt, wins, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq, allAt_iff members]
      constructor
      · intro h
        exact ⟨fun m hm => ((node_optimal_iff chart (M.w m) (M.V m) (eqs m hm) hr members).mp (h m hm)).1,
          fun m hm => ((node_optimal_iff chart (M.w m) (M.V m) (eqs m hm) hr members).mp (h m hm)).2⟩
      · rintro ⟨h1, h2⟩ m hm
        exact (node_optimal_iff chart (M.w m) (M.V m) (eqs m hm) hr members).mpr ⟨h1 m hm, h2 m hm⟩
    rw [List.filter_congr pointwise]
    by_cases hw : wins M r
    · simp only [hw, Bool.true_and, if_true]
      rw [filter_tuples]
    · simp only [hw, Bool.false_and]
      simp

/-- The restriction theorem with optimality spelled out: the restricted chart's
derivations are the derivations that no derivation of the same cell beats in any
selected model. -/
theorem restrict_unfold_optimal (chart : Chart O) (M : Models O)
    (eqs : ∀ m ∈ M.S, CellEquations chart (M.w m) (M.V m)) (n : Nat) :
    unfoldTrees (restrict chart M) n = (unfoldTrees chart n).filter fun t =>
      decide (∀ m ∈ M.S, ∀ t' ∈ unfoldTrees chart n, cost (M.w m) t ≤ cost (M.w m) t') := by
  rw [restrict_unfold chart M eqs n]
  apply List.filter_congr
  intro t ht
  apply Bool.eq_iff_iff.mpr
  simp only [optimalAt, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h m hm
    exact (value_iff_optimal chart (M.w m) (M.V m) (eqs m hm) ht).mp (h m hm)
  · intro h m hm
    exact (value_iff_optimal chart (M.w m) (M.V m) (eqs m hm) ht).mpr (h m hm)

/-- Counts, existence and ranked witnesses: the number of common optima is the
length of the restricted bag, and the common optimum of rank `k` is its `k`-th entry. -/
theorem count_and_rank (chart : Chart O) (M : Models O)
    (eqs : ∀ m ∈ M.S, CellEquations chart (M.w m) (M.V m)) (n k : Nat) :
    (unfoldTrees (restrict chart M) n).length = ((unfoldTrees chart n).filter (optimalAt M n)).length ∧
    (unfoldTrees (restrict chart M) n)[k]? = ((unfoldTrees chart n).filter (optimalAt M n))[k]? := by
  rw [restrict_unfold chart M eqs n]
  exact ⟨rfl, rfl⟩

/-
The retention lower bound. A tie set over `R` rules is a nonempty mask below
`2^R`. A later question with a fresh model whose only winner is rule `i` asks
whether rule `i` is in the tie set. If a retained summary answers every such
question, it takes a different value on each tie set.
-/

theorem summary_injective (R : Nat) (summary : Nat → Nat) (decode : Nat → Nat → Bool)
    (answers : ∀ T, 0 < T → T < 2 ^ R → ∀ i, i < R → decode (summary T) i = T.testBit i)
    {T U : Nat} (hT0 : 0 < T) (hT : T < 2 ^ R) (hU0 : 0 < U) (hU : U < 2 ^ R)
    (same : summary T = summary U) : T = U := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < R
  · rw [← answers T hT0 hT i hi, ← answers U hU0 hU i hi, same]
  · have hle : R ≤ i := Nat.le_of_not_lt hi
    have bT : T.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) hle))
    have bU : U.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hU (Nat.pow_le_pow_right (by decide) hle))
    rw [bT, bU]

/-- A list without repeats of numbers below `m` has at most `m` entries. -/
theorem nodup_length_le : ∀ (m : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < m) → l.length ≤ m
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self)) (Nat.not_lt_zero x)
  | m + 1, l, nd, h => by
    by_cases hm : m ∈ l
    · have nd' := nd.erase m
      have below : ∀ x ∈ l.erase m, x < m := by
        intro x hx
        rw [nd.mem_erase_iff] at hx
        have := h x hx.2
        omega
      have := nodup_length_le m (l.erase m) nd' below
      rw [List.length_erase_of_mem hm] at this
      omega
    · have below : ∀ x ∈ l, x < m := by
        intro x hx
        have := h x hx
        have : x ≠ m := fun e => hm (e ▸ hx)
        omega
      have := nodup_length_le m l nd below
      omega

/-- A summary that answers every fresh singleton question needs at least
`2^R - 1` distinct values on the nonempty tie sets. With `b` bits (`2^b` values)
that forces `2^R - 1 ≤ 2^b`, so `b ≥ R` when `R ≥ 2`. -/
theorem tie_set_lower_bound (R b : Nat) (hR : 2 ≤ R) (summary : Nat → Nat) (decode : Nat → Nat → Bool)
    (answers : ∀ T, 0 < T → T < 2 ^ R → ∀ i, i < R → decode (summary T) i = T.testBit i)
    (fits : ∀ T, 0 < T → T < 2 ^ R → summary T < 2 ^ b) : R ≤ b := by
  have hpos : 0 < 2 ^ R := Nat.two_pow_pos R
  let sets := List.range' 1 (2 ^ R - 1)
  have mem_sets : ∀ T ∈ sets, 0 < T ∧ T < 2 ^ R := by
    intro T hT
    simp only [sets, List.mem_range'] at hT
    omega
  have nd : (sets.map summary).Nodup := by
    apply nodup_map_on
    · intro T hT U hU same
      exact summary_injective R summary decode answers (mem_sets T hT).1 (mem_sets T hT).2
        (mem_sets U hU).1 (mem_sets U hU).2 same
    · exact List.nodup_range'
  have bound := nodup_length_le (2 ^ b) (sets.map summary) nd (by
    intro x hx
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
    exact fits T (mem_sets T hT).1 (mem_sets T hT).2)
  simp only [List.length_map, sets, List.length_range'] at bound
  apply Classical.byContradiction
  intro hlt
  have hb : b + 1 ≤ R := by omega
  have : 2 ^ (b + 1) ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hb
  have hb2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hR2 : 4 ≤ 2 ^ R := by
    have : 2 ^ 2 ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hR
    simpa using this
  omega

end MetaCommon
