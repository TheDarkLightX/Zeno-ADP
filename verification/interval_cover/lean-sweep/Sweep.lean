import Lean

namespace CoverSweep

/-- An ordered include/skip row. The right endpoint is exclusive. -/
structure Row where
  left : Nat
  right : Nat
  take : Bool

def Row.valid (n : Nat) (r : Row) : Prop := r.left < r.right ∧ r.right ≤ n

def Row.covers (r : Row) (x : Nat) : Prop :=
  r.take = true ∧ r.left ≤ x ∧ x < r.right

def Row.advance (r : Row) (edge : Nat) : Nat :=
  if r.take then max edge r.right else edge

/-- The list is sorted by left endpoint; tie order is unrestricted. -/
def startsOrdered : List Row → Prop
  | [] => True
  | r :: rs => (∀ s ∈ rs, r.left ≤ s.left) ∧ startsOrdered rs

/-- Points below edge are already covered. Only these and selected rows
    of the continuation contribute to the cover question. -/
def completes (n edge : Nat) (rs : List Row) : Prop :=
  ∀ x < n, x < edge ∨ ∃ r ∈ rs, r.covers x

/-- Gap checks before successive start positions, then final edge check.
    This handles empty starts without materializing them. -/
def accepts (n : Nat) : List Row → Nat → Prop
  | [], edge => n ≤ edge
  | r :: rs, edge => r.left ≤ edge ∧ accepts n rs (r.advance edge)

theorem advance_point (r : Row) (edge x : Nat) (h : r.left ≤ edge) :
    x < r.advance edge ↔ x < edge ∨ r.covers x := by
  cases ht : r.take
  · simp [Row.advance, Row.covers, ht]
  · simp only [Row.advance, Row.covers, ht, true_and, if_true]
    omega

theorem prestart_gap (n edge : Nat) (r : Row) (rs : List Row)
    (valid : r.valid n) (ord : startsOrdered (r :: rs))
    (ok : completes n edge (r :: rs)) :
    r.left ≤ edge := by
  by_cases h : r.left ≤ edge
  · exact h
  · have hn : edge < n := by
      unfold Row.valid at valid
      omega
    rcases ok edge hn with hh | ⟨s, hm, hs⟩
    · omega
    · have hr : r.left ≤ s.left := by
        rcases List.mem_cons.mp hm with he | hm
        · subst s
          exact Nat.le_refl _
        · exact ord.1 s hm
      unfold Row.covers at hs
      omega

theorem absorb_start (n edge : Nat) (r : Row) (rs : List Row)
    (h : r.left ≤ edge) :
    completes n edge (r :: rs) ↔ completes n (r.advance edge) rs := by
  constructor
  · intro hc x hx
    rcases hc x hx with he | ⟨s, hm, hs⟩
    · exact Or.inl ((advance_point r edge x h).2 (Or.inl he))
    · rcases List.mem_cons.mp hm with he | hm
      · subst s
        exact Or.inl ((advance_point r edge x h).2 (Or.inr hs))
      · exact Or.inr ⟨s, hm, hs⟩
  · intro hc x hx
    rcases hc x hx with he | ⟨s, hm, hs⟩
    · rcases (advance_point r edge x h).1 he with hl | hl
      · exact Or.inl hl
      · exact Or.inr ⟨r, List.mem_cons_self, hl⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem r hm, hs⟩

theorem accepts_iff_completes (n edge : Nat) (rs : List Row)
    (valid : ∀ r ∈ rs, r.valid n) (ord : startsOrdered rs) :
    accepts n rs edge ↔ completes n edge rs := by
  induction rs generalizing edge with
  | nil =>
    constructor
    · intro h x hx
      exact Or.inl (Nat.lt_of_lt_of_le hx h)
    · intro h
      change n ≤ edge
      by_cases he : n ≤ edge
      · exact he
      · have hn : edge < n := by omega
        simpa using h edge hn
  | cons r rs ih =>
    have hv : ∀ s ∈ rs, s.valid n := fun s hs => valid s (List.mem_cons_of_mem r hs)
    constructor
    · rintro ⟨h, ha⟩
      exact (absorb_start n edge r rs h).2 ((ih _ hv ord.2).1 ha)
    · intro h
      have hg := prestart_gap n edge r rs (valid r List.mem_cons_self) ord h
      exact ⟨hg, (ih _ hv ord.2).2 ((absorb_start n edge r rs hg).1 h)⟩

/-- Equal frontier states accept precisely the same continuations,
    for a fixed block position and valid sorted continuation. -/
theorem same_edge_same_observation (n e₁ e₂ : Nat) (rows : List Row)
    (valid : ∀ r ∈ rows, r.valid n) (ord : startsOrdered rows)
    (h : e₁ = e₂) :
    accepts n rows e₁ ↔ completes n e₂ rows := by
  subst e₂
  exact accepts_iff_completes n e₁ rows valid ord

/-- A selected set of positions is represented by its characteristic
    predicate; a finite vector of decisions is represented by indexed Bool.
    Position IDs, rather than interval equality, preserve duplicate rows. -/
def selection {m : Nat} (bits : Fin m → Bool) : Fin m → Prop :=
  fun i => bits i = true

noncomputable def decisions {m : Nat} (set : Fin m → Prop) : Fin m → Bool :=
  fun i => @decide (set i) (Classical.propDecidable _)

theorem selection_decisions {m : Nat} (set : Fin m → Prop) :
    selection (decisions set) = set := by
  classical
  funext i
  exact propext decide_eq_true_iff

theorem decisions_selection {m : Nat} (bits : Fin m → Bool) :
    decisions (selection bits) = bits := by
  classical
  funext i
  have he := congrFun (selection_decisions (selection bits)) i
  have he' : (decisions (selection bits) i = true) = (bits i = true) := he
  cases hb : bits i <;> cases hd : decisions (selection bits) i <;> simp_all


/-- A representation matching the Rust/Python sweep: for a start block,
    update the edge for each take, then retire that position. -/
def advanceBlock (edge : Nat) (rs : List Row) : Nat :=
  rs.foldl (fun e r => r.advance e) edge

theorem edge_monotone (r : Row) (edge : Nat) : edge ≤ r.advance edge := by
  cases h : r.take <;> simp [Row.advance, h, Nat.le_max_left]

theorem absorb_block (n i edge : Nat) (rs tail : List Row)
    (rowsAt : ∀ r ∈ rs, r.left = i) (h : i ≤ edge) :
    completes n edge (rs ++ tail) ↔ completes n (advanceBlock edge rs) tail := by
  induction rs generalizing edge with
  | nil => rfl
  | cons r rs ih =>
    have hr : r.left ≤ edge := by rw [rowsAt r List.mem_cons_self]; exact h
    have hnext := Nat.le_trans h (edge_monotone r edge)
    have hrest : ∀ s ∈ rs, s.left = i := fun s hs => rowsAt s (List.mem_cons_of_mem r hs)
    exact (absorb_start n edge r (rs ++ tail) hr).trans (ih _ hrest hnext)

def startsAt (i : Nat) : List (List Row) → Prop
  | [] => True
  | rs :: groups => (∀ r ∈ rs, r.left = i) ∧ startsAt (i+1) groups

theorem future_starts (i : Nat) (groups : List (List Row))
    (hg : startsAt i groups) (r : Row) (hm : r ∈ groups.flatten) :
    i ≤ r.left := by
  induction groups generalizing i with
  | nil => simp at hm
  | cons rs groups ih =>
    rw [List.flatten_cons, List.mem_append] at hm
    rcases hm with hr | hr
    · exact Nat.le_of_eq (hg.1 r hr).symm
    · have h := ih (i+1) hg.2 hr
      omega

/-- At each processed point, only states covering that point survive.
    For an empty block list this uses the terminal right-edge check. -/
def blockedSweep (n i : Nat) : List (List Row) → Nat → Prop
  | [], edge => n ≤ edge
  | rs :: groups, edge =>
      let next := advanceBlock edge rs
      i < next ∧ blockedSweep n (i+1) groups next

theorem block_sweep_iff (n i edge : Nat) (groups : List (List Row))
    (starts : startsAt i groups) (remaining : i + groups.length ≤ n)
    (h : i ≤ edge) :
    blockedSweep n i groups edge ↔ completes n edge groups.flatten := by
  induction groups generalizing i edge with
  | nil =>
    exact accepts_iff_completes n edge [] (by simp) trivial
  | cons rs groups ih =>
    rw [List.flatten_cons, absorb_block n i edge rs groups.flatten starts.1 h]
    have hrem : i+1 + groups.length ≤ n := by simp only [List.length_cons] at remaining; omega
    have hi : i < n := by omega
    constructor
    · rintro ⟨hgate, ht⟩
      exact (ih _ _ starts.2 hrem hgate).1 ht
    · intro hc
      have hgate : i < advanceBlock edge rs := by
        rcases hc i hi with hh | ⟨r, hm, hr⟩
        · exact hh
        · have hf := future_starts (i+1) groups starts.2 r hm
          unfold Row.covers at hr
          omega
      exact ⟨hgate, (ih _ _ starts.2 hrem hgate).2 hc⟩

/-- Complete sweep started at zero accepts precisely covers of [0,n). -/
theorem from_zero (n : Nat) (groups : List (List Row))
    (starts : startsAt 0 groups) (h : groups.length ≤ n) :
    blockedSweep n 0 groups 0 ↔
      ∀ x < n, ∃ r ∈ groups.flatten, r.covers x := by
  simpa [completes] using block_sweep_iff n 0 0 groups starts (by simpa) (Nat.le_refl 0)


/-- A route menu without its decisions. Index identity distinguishes rows,
    including multiple occurrences of exactly the same interval. -/
def materialize {m : Nat} (menu : Fin m → Nat × Nat) (bits : Fin m → Bool) :
    List Row :=
  List.ofFn (fun i => ⟨(menu i).1, (menu i).2, bits i⟩)

theorem materialized_coverage {m : Nat} (menu : Fin m → Nat × Nat)
    (bits : Fin m → Bool) (x : Nat) :
    (∃ r ∈ materialize menu bits, r.covers x) ↔
    (∃ i : Fin m, selection bits i ∧ (menu i).1 ≤ x ∧ x < (menu i).2) := by
  simp only [materialize, selection, List.mem_ofFn]
  constructor
  · rintro ⟨r, ⟨i, rfl⟩, hr⟩
    exact ⟨i, hr⟩
  · rintro ⟨i, h⟩
    exact ⟨_, ⟨i, rfl⟩, h⟩

/-- Joining the block theorem with the position-indexed decision semantics. -/
theorem selected_set_sweep {m : Nat} (n : Nat) (menu : Fin m → Nat × Nat)
    (set : Fin m → Prop) (groups : List (List Row))
    (order : startsAt 0 groups) (count : groups.length ≤ n)
    (encoding : groups.flatten = materialize menu (decisions set)) :
    blockedSweep n 0 groups 0 ↔
      ∀ x < n, ∃ i : Fin m, set i ∧ (menu i).1 ≤ x ∧ x < (menu i).2 := by
  rw [from_zero n groups order count, encoding]
  simp only [materialized_coverage, selection_decisions]

/-- Lower bound across *all* future valid interval menus, not optimally
    compressed states for any one menu. Two unequal legal edges can be
    distinguished by an empty continuation or one interval. -/
theorem edge_distinguishable (n i small large : Nat)
    (lower : i ≤ small) (different : small < large) (upper : large ≤ n) :
    ∃ future : List Row,
      (∀ r ∈ future, r.valid n ∧ i ≤ r.left) ∧ startsOrdered future ∧
      accepts n future large ∧ ¬ accepts n future small := by
  by_cases h : large = n
  · refine ⟨[], by simp, trivial, ?_, ?_⟩
    · change n ≤ large; omega
    · intro hbad
      change n ≤ small at hbad
      omega
  · have hln : large < n := by omega
    let r : Row := ⟨large, n, true⟩
    refine ⟨[r], ?_, ?_, ?_, ?_⟩
    · intro s hm
      have he : s = r := by simpa using hm
      subst s
      exact ⟨⟨hln, Nat.le_refl n⟩, by change i ≤ large; omega⟩
    · exact ⟨by simp, trivial⟩
    · exact ⟨Nat.le_refl large, by change n ≤ r.advance large; simp [r, Row.advance, Nat.le_max_right]⟩
    · intro hbad
      have hg : large ≤ small := hbad.1
      omega

end CoverSweep

#print axioms CoverSweep.advance_point
#print axioms CoverSweep.prestart_gap
#print axioms CoverSweep.absorb_start
#print axioms CoverSweep.accepts_iff_completes
#print axioms CoverSweep.same_edge_same_observation
#print axioms CoverSweep.selection_decisions
#print axioms CoverSweep.decisions_selection
#print axioms CoverSweep.edge_monotone
#print axioms CoverSweep.absorb_block
#print axioms CoverSweep.future_starts
#print axioms CoverSweep.block_sweep_iff
#print axioms CoverSweep.from_zero
#print axioms CoverSweep.materialized_coverage
#print axioms CoverSweep.selected_set_sweep
#print axioms CoverSweep.edge_distinguishable
