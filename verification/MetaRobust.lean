/-
Robust prefixes: the telescoping argument behind `robust_prefix`.

A prefix is a start node and a list of steps, each a cost and the node it
reaches. `V` is a world's least finishing cost. The Bellman inequality says no
step lowers `cost + V(next)` below `V(here)`.
-/
namespace MetaRobust

variable {N : Type}

/-- The cost of a prefix's steps. -/
def pathCost : List (Int × N) → Int
  | [] => 0
  | (c, _) :: rest => c + pathCost rest

/-- The node a prefix ends at. -/
def endOf : N → List (Int × N) → N
  | x, [] => x
  | _, (_, y) :: rest => endOf y rest

/-- The sum of the steps' slacks `c + V(y) - V(x)`. -/
def slackSum (V : N → Int) : N → List (Int × N) → Int
  | _, [] => 0
  | x, (c, y) :: rest => (c + V y - V x) + slackSum V y rest

/-- Every step of the prefix has zero slack. -/
def allTight (V : N → Int) : N → List (Int × N) → Prop
  | _, [] => True
  | x, (c, y) :: rest => c + V y - V x = 0 ∧ allTight V y rest

/-- Every step satisfies the Bellman inequality. -/
def Bellman (V : N → Int) : N → List (Int × N) → Prop
  | _, [] => True
  | x, (c, y) :: rest => V x ≤ c + V y ∧ Bellman V y rest

/-- Regret of committing to the prefix and then finishing optimally: its cost,
plus the best finish from its end, minus the best finish from the start. -/
def regret (V : N → Int) (x : N) (steps : List (Int × N)) : Int :=
  pathCost steps + V (endOf x steps) - V x

/-- Telescoping: the regret is the sum of the step slacks. -/
theorem regret_eq_slackSum (V : N → Int) (x : N) (steps : List (Int × N)) :
    regret V x steps = slackSum V x steps := by
  induction steps generalizing x with
  | nil => simp [regret, pathCost, endOf, slackSum]
  | cons step rest ih =>
    obtain ⟨c, y⟩ := step
    have := ih y
    simp only [regret, pathCost, endOf, slackSum] at this ⊢
    omega

theorem slackSum_nonneg (V : N → Int) (x : N) (steps : List (Int × N))
    (h : Bellman V x steps) : 0 ≤ slackSum V x steps := by
  induction steps generalizing x with
  | nil => simp [slackSum]
  | cons step rest ih =>
    obtain ⟨c, y⟩ := step
    simp only [Bellman] at h
    have := ih y h.2
    simp only [slackSum]
    omega

/-- Zero regret holds exactly when every step of the prefix has zero slack. -/
theorem zero_regret_iff_tight (V : N → Int) (x : N) (steps : List (Int × N))
    (h : Bellman V x steps) : regret V x steps = 0 ↔ allTight V x steps := by
  rw [regret_eq_slackSum]
  induction steps generalizing x with
  | nil => simp [slackSum, allTight]
  | cons step rest ih =>
    obtain ⟨c, y⟩ := step
    simp only [Bellman] at h
    have rest_nonneg := slackSum_nonneg V y rest h.2
    simp only [slackSum, allTight]
    constructor
    · intro zero
      have tight : c + V y - V x = 0 := by omega
      exact ⟨tight, (ih y h.2).mp (by omega)⟩
    · rintro ⟨tight, rest_tight⟩
      have := (ih y h.2).mpr rest_tight
      omega

/-- A world's budget holds exactly when that world's slacks sum to at most the budget. -/
theorem within_budget_iff (V : N → Int) (x : N) (steps : List (Int × N)) (budget : Int) :
    regret V x steps ≤ budget ↔ slackSum V x steps ≤ budget := by
  rw [regret_eq_slackSum]

/-- One budget shared by two worlds is not the per-world condition. Two steps
with slacks (3, 0) and (0, 3) each fit a budget of 2 in their tight world, a
shared budget charged by the smaller slack is never spent, yet each world's
regret is 3. -/
example :
    let slacks : List (Int × Int) := [(3, 0), (0, 3)]
    (slacks.map fun s => min s.1 s.2).sum ≤ 2 ∧
    ¬ ((slacks.map Prod.fst).sum ≤ 2 ∧ (slacks.map Prod.snd).sum ≤ 2) := by
  decide

/-- Charging the larger slack to one shared budget of 2 refuses two steps with
slacks (2, 0) and (0, 2), whose per-world regrets (2, 2) fit. -/
example :
    let slacks : List (Int × Int) := [(2, 0), (0, 2)]
    ¬ (slacks.map fun s => max s.1 s.2).sum ≤ 2 ∧
    ((slacks.map Prod.fst).sum ≤ 2 ∧ (slacks.map Prod.snd).sum ≤ 2) := by
  decide

end MetaRobust
