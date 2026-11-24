/-
Chart-state discovery: the statements behind `state_discovery`.

A Mealy machine has a successor and a score change for each state and symbol.
The checker's closure obligations say that a class table reproduces the score
change and successor class of every state. The separation obligation says that
probe words tell every two classes apart.
-/
namespace MetaQuotient

structure Machine (S A : Type) where
  next : S → A → S
  gain : S → A → Int

/-- The score change of a word read from a state. -/
def Machine.run {S A : Type} (m : Machine S A) : S → List A → Int
  | _, [] => 0
  | s, a :: w => m.gain s a + m.run (m.next s a) w

/-- The closure obligations replayed by `Quotient::verify`. -/
def Closed {S C A : Type} (m : Machine S A) (q : Machine C A) (f : S → C) : Prop :=
  ∀ s a, q.gain (f s) a = m.gain s a ∧ q.next (f s) a = f (m.next s a)

/-- The separation obligation replayed by `Quotient::verify`. -/
def Separated {S C A : Type} (m : Machine S A) (f : S → C) (probes : List (List A)) : Prop :=
  ∀ s t, f s ≠ f t → ∃ z ∈ probes, m.run s z ≠ m.run t z

/-- A closed class table gives every word the score change of the raw machine. -/
theorem quotient_run {S C A : Type} (m : Machine S A) (q : Machine C A) (f : S → C)
    (h : Closed m q f) : ∀ w s, q.run (f s) w = m.run s w := by
  intro w
  induction w with
  | nil => intro s; rfl
  | cons a w ih =>
    intro s
    simp only [Machine.run, (h s a).1, (h s a).2, ih]

/-- States in one class of a closed table agree on every future score change. -/
theorem same_class_same_run {S C A : Type} {m : Machine S A} {q : Machine C A} {f : S → C}
    (h : Closed m q f) {s t : S} (e : f s = f t) (w : List A) : m.run s w = m.run t w := by
  rw [← quotient_run m q f h, ← quotient_run m q f h, e]

/-- A closed and separated table is the Nerode equivalence of the raw machine. -/
theorem class_iff_equivalent {S C A : Type} {m : Machine S A} {q : Machine C A} {f : S → C}
    {probes : List (List A)} (hc : Closed m q f) (hs : Separated m f probes) (s t : S) :
    f s = f t ↔ ∀ w, m.run s w = m.run t w := by
  constructor
  · intro e w
    exact same_class_same_run hc e w
  · intro all
    apply Classical.byContradiction
    intro ne
    obtain ⟨z, _, differs⟩ := hs s t ne
    exact differs (all z)

/-- Every closed table refines a closed and separated one, so the latter is the
coarsest congruence: no closed table merges more states. -/
theorem coarsest {S C D A : Type} {m : Machine S A} {q : Machine C A} {f : S → C}
    {probes : List (List A)} (hc : Closed m q f) (hs : Separated m f probes)
    {q' : Machine D A} {g : S → D} (hg : Closed m q' g) (s t : S) (e : g s = g t) :
    f s = f t :=
  (class_iff_equivalent hc hs s t).mpr (same_class_same_run hg e)

/-- The state an observer reaches after a word. -/
def stateAfter {S A : Type} (m : Machine S A) (start : S) (w : List A) : S :=
  w.foldl m.next start

theorem stateAfter_append {S A : Type} (m : Machine S A) (start : S) (p : List A) (a : A) :
    stateAfter m start (p ++ [a]) = m.next (stateAfter m start p) a := by
  simp [stateAfter, List.foldl_append]

theorem run_append {S A : Type} (m : Machine S A) (start : S) (p : List A) (a : A) :
    m.run start (p ++ [a]) = m.run start p + m.gain (stateAfter m start p) a := by
  induction p generalizing start with
  | nil => simp [Machine.run, stateAfter]
  | cons b p ih =>
    simp only [List.cons_append, Machine.run, ih]
    simp only [stateAfter, List.foldl_cons]
    omega

/-- The observer check of `RawModel::check`: if every word of length at most `L`
changes the scorer's score as the declared model says, the model's score equals the
scorer's score on every word of length at most `L`. -/
theorem check_fixes_scores {S A : Type} (m : Machine S A) (start : S) (score : List A → Int)
    (L : Nat)
    (check : ∀ p a, p.length + 1 ≤ L → score (p ++ [a]) - score p = m.gain (stateAfter m start p) a) :
    ∀ w : List A, w.length ≤ L → score w = score [] + m.run start w := by
  -- Read the word after any checked prefix, one symbol at a time.
  have extend : ∀ (s p : List A), (p ++ s).length ≤ L →
      score (p ++ s) = score p + m.run (stateAfter m start p) s := by
    intro s
    induction s with
    | nil => intro p _; simp [Machine.run]
    | cons a s ih =>
      intro p hlen
      have hlen' : ((p ++ [a]) ++ s).length ≤ L := by simpa using hlen
      have step := check p a (by simp at hlen; omega)
      have rest := ih (p ++ [a]) hlen'
      rw [stateAfter_append] at rest
      simp only [List.append_assoc, List.singleton_append] at rest
      rw [rest, Machine.run]
      omega
  intro w hw
  have := extend w [] (by simpa using hw)
  simpa [stateAfter] using this

/-- The last `k` symbols of a word, or the whole word while it is shorter. -/
def lastN {A : Type} (k : Nat) (l : List A) : List A := l.drop (l.length - k)

theorem lastN_length {A : Type} (k : Nat) (l : List A) : (lastN k l).length ≤ k := by
  simp [lastN, List.length_drop]
  omega

theorem lastN_lastN {A : Type} {k k' : Nat} (h : k ≤ k') (l : List A) :
    lastN k (lastN k' l) = lastN k l := by
  simp only [lastN, List.drop_drop, List.length_drop]
  congr 1
  omega

/-- The score change of a symbol after a word. -/
def gainAfter {A : Type} (score : List A → Int) (p : List A) (a : A) : Int :=
  score (p ++ [a]) - score p

/-- A scorer whose score changes depend only on the last `k` symbols. -/
def Local {A : Type} (k : Nat) (score : List A → Int) : Prop :=
  ∀ p a, gainAfter score p a = gainAfter score (lastN k p) a

/-- A declared horizon `k` that is too short for a scorer of horizon `k'` (with
`k ≤ k'`) fails at a history of length at most `k'`. So a check of every word up
to length `k' + 1` refuses it. -/
theorem violation_by_true_horizon {A : Type} {k k' : Nat} (hk : k ≤ k') (score : List A → Int)
    (true_horizon : Local k' score) (p : List A) (a : A)
    (fails : gainAfter score p a ≠ gainAfter score (lastN k p) a) :
    ∃ p', p'.length ≤ k' ∧ gainAfter score p' a ≠ gainAfter score (lastN k p') a := by
  refine ⟨lastN k' p, lastN_length k' p, ?_⟩
  have e1 : gainAfter score (lastN k' p) a = gainAfter score p a := by
    rw [true_horizon p a, true_horizon (lastN k' p) a, lastN_lastN (Nat.le_refl k')]
  rw [e1, lastN_lastN hk]
  exact fails

/-- No finite check certifies the horizon of a black-box scorer: for any finite
set of words and any `k`-local scorer there is a scorer that agrees on every one
of those words and is not `k`-local. -/
theorem no_finite_horizon_check {A : Type} (k : Nat) (checked : List (List A))
    (score : List A → Int) (local_k : Local k score) (a : A) :
    ∃ other : List A → Int,
      (∀ w ∈ checked, other w = score w) ∧ ¬ Local k other := by
  let T := k + (checked.map List.length).sum + 1
  let other := fun w : List A => score w + if T < w.length then 1 else 0
  refine ⟨other, ?_, ?_⟩
  · intro w hw
    have hle : w.length ≤ (checked.map List.length).sum := by
      clear local_k
      induction checked with
      | nil => cases hw
      | cons head rest ih =>
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hw with h | h
        · subst h; omega
        · have := ih h; omega
    have : ¬ T < w.length := by omega
    simp [other, this]
  · intro hother
    let p := List.replicate T a
    have hp : p.length = T := List.length_replicate
    have hshort : (lastN k p).length ≤ k := lastN_length k p
    have e := hother p a
    have l1 := local_k p a
    simp only [gainAfter, other, List.length_append, List.length_singleton, hp] at e l1
    have c1 : T < T + 1 := by omega
    have c2 : ¬ T < T := by omega
    have c3 : ¬ T < (lastN k p).length + 1 := by omega
    have c4 : ¬ T < (lastN k p).length := by omega
    simp only [c1, c2, c3, c4, if_true, if_false] at e
    omega

end MetaQuotient
