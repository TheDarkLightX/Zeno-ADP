import Lean

namespace JointRetention

def lastRead (rank : Nat) (reads : List Nat) : Nat :=
  reads.foldr max rank

def keep (rank now : Nat) (reads : List Nat) (present requested : Prop) : Prop :=
  present ∧ (requested ∨ now < lastRead rank reads)

theorem before_lastRead (rank now : Nat) (reads : List Nat) :
    now < lastRead rank reads ↔ now < rank ∨ ∃ later ∈ reads, now < later := by
  induction reads with
  | nil => simp [lastRead]
  | cons read reads ih =>
    change now < max read (lastRead rank reads) ↔
      now < rank ∨ ∃ later ∈ read :: reads, now < later
    have ltMax : now < max read (lastRead rank reads) ↔
        now < read ∨ now < lastRead rank reads := by omega
    rw [ltMax, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (earlier | earlier | ⟨later, member, future⟩)
      · exact Or.inr ⟨read, Or.inl rfl, earlier⟩
      · exact Or.inl earlier
      · exact Or.inr ⟨later, Or.inr member, future⟩
    · rintro (earlier | ⟨later, h | member, future⟩)
      · exact Or.inr (Or.inl earlier)
      · exact Or.inl (h ▸ future)
      · exact Or.inr (Or.inr ⟨later, member, future⟩)

theorem keep_iff_future_read_or_request (rank now : Nat) (reads : List Nat)
    (finished : rank ≤ now) (present requested : Prop) :
    keep rank now reads present requested ↔
      present ∧ (requested ∨ ∃ later ∈ reads, now < later) := by
  simp [keep, before_lastRead, Nat.not_lt_of_ge finished]

#print axioms before_lastRead
#print axioms keep_iff_future_read_or_request

end JointRetention
