import Lean

namespace CompiledQueries

def packFrom (rank : Nat) : List (Option α) → List (Nat × α)
  | [] => []
  | none :: tail => packFrom (rank + 1) tail
  | some value :: tail => (rank, value) :: packFrom (rank + 1) tail

def packedLookup (rank : Nat) (entries : List (Nat × α)) : Option α :=
  (entries.find? fun entry => entry.1 == rank).map Prod.snd

/-- Removing absent slots preserves all logical lookups, including trailing holes. -/
theorem packed_lookup (slots : List (Option α)) (base offset : Nat) :
    packedLookup (base + offset) (packFrom base slots) = slots[offset]?.join := by
  induction slots generalizing base offset with
  | nil => simp [packFrom, packedLookup]
  | cons slot tail ih =>
    cases slot with
    | none =>
      cases offset with
      | zero =>
        have below : ∀ (rest : List (Option α)) (first : Nat), base < first →
            packedLookup base (packFrom first rest) = none := by
          intro rest
          induction rest with
          | nil => simp [packFrom, packedLookup]
          | cons item rest step =>
            intro first h
            cases item with
            | none => exact step (first + 1) (by omega)
            | some value =>
              have ne : first ≠ base := by omega
              simpa [packFrom, packedLookup, ne] using step (first + 1) (by omega)
        exact below tail (base + 1) (by omega)
      | succ offset =>
        simpa [packFrom, Nat.add_assoc, Nat.add_comm 1 offset] using ih (base + 1) offset
    | some value =>
      cases offset with
      | zero => simp [packFrom, packedLookup]
      | succ offset =>
        have ne : base ≠ base + (offset + 1) := by omega
        simpa [packFrom, packedLookup, ne, Nat.add_assoc, Nat.add_comm 1 offset]
          using ih (base + 1) offset

/-- Inclusive clipping agrees with post-filtering on any ordered candidate list. -/
theorem clipped_splits (splits : List Nat) (a b c d : Nat) :
    splits.filter (fun x => decide (max a c ≤ x ∧ x ≤ min b d)) =
      (splits.filter (fun x => decide (a ≤ x ∧ x ≤ b))).filter
        (fun x => decide (c ≤ x ∧ x ≤ d)) := by
  rw [List.filter_filter]
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

def totalMass : List (Nat × Nat) → Nat
  | [] => 1
  | (weight, _) :: rest => weight * totalMass rest

def totalVisits (slots : List (Nat × Nat)) : Nat :=
  (slots.map Prod.snd).sum

def markedMass : List (Nat × Nat) → Nat
  | [] => 0
  | (weight, visits) :: rest =>
    weight * visits * totalMass rest + weight * markedMass rest

/-- Sum contributions with one marked child slot, counting repeated slots. -/
theorem marked_mass (slots : List (Nat × Nat)) :
    markedMass slots = totalMass slots * totalVisits slots := by
  induction slots with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨weight, visits⟩
    simp [markedMass, totalMass, totalVisits, ih, Nat.mul_add, Nat.mul_assoc,
      Nat.mul_comm]
    ac_rfl

theorem repeated_slots : markedMass [(1, 1), (1, 1)] = 2 := by decide

#print axioms packed_lookup
#print axioms clipped_splits
#print axioms marked_mass
#print axioms repeated_slots

end CompiledQueries
