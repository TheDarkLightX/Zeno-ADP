import Lean

namespace CoverCount
abbrev Answer := Option (Nat × Nat)

def choose : Answer → Answer → Answer
  | none, b => b
  | a, none => a
  | some (c,n), some (d,m) =>
      if c < d then some (c,n) else if d < c then some (d,m)
      else some (c,n+m)

def shift (w : Nat) : Answer → Answer := Option.map (fun (c,n) => (c+w,n))
def double : Answer → Answer := Option.map (fun (c,n) => (c,n+n))

theorem shift_choose (w : Nat) (a b : Answer) :
    shift w (choose a b) = choose (shift w a) (shift w b) := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      rcases a with ⟨c,n⟩
      rcases b with ⟨d,m⟩
      by_cases h : c < d <;> by_cases g : d < c <;> simp [choose, shift, h, g]

theorem double_choose (a b : Answer) :
    double (choose a b) = choose (double a) (double b) := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      rcases a with ⟨c,n⟩
      rcases b with ⟨d,m⟩
      by_cases h : c < d
      · simp [choose, double, h]
      · by_cases g : d < c
        · simp [choose, double, h, g]
        · simp [choose, double, h, g]; omega

theorem unchanged_frontier (w : Nat) (a : Answer) :
    choose a (shift w a) = if w = 0 then double a else a := by
  cases a with
  | none => by_cases h : w = 0 <;> simp [choose, shift, double, h]
  | some a =>
    rcases a with ⟨c,n⟩
    by_cases h : w = 0
    · simp [choose, shift, double, h]
    · have h' : c < c+w := by omega
      simp [choose, shift, h, h']

end CoverCount

#print axioms CoverCount.shift_choose
#print axioms CoverCount.double_choose
#print axioms CoverCount.unchanged_frontier
