import Std

namespace Structures

/-- Consuming an exposed forest root by promotion removes one node. -/
theorem promotion_descends (remaining other : Nat) :
    remaining + other < (remaining + 1) + other := by
  omega

/-- A gap may capture a prefix of the opposite forest. It still consumes
one root on its own side, and both recursive subproblems are smaller. -/
theorem alignment_gap_descends (inside siblings prefixSize suffixSize : Nat) :
    inside + prefixSize < inside + siblings + 1 + (prefixSize + suffixSize) ∧
    siblings + suffixSize < inside + siblings + 1 + (prefixSize + suffixSize) := by
  omega

/-- Unit unmatched-node cost decomposes into the promoting-cut cost outside
the retained subtrees and the unmatched-node cost inside. Paired roots cancel. -/
theorem promoting_cut_cost
    (outsideLeft outsideRight insideLeft insideRight roots insideMatches : Nat)
    (leftBound : insideMatches ≤ insideLeft) (rightBound : insideMatches ≤ insideRight) :
    (outsideLeft + roots + insideLeft) + (outsideRight + roots + insideRight) -
        2 * (roots + insideMatches) =
      outsideLeft + outsideRight + (insideLeft + insideRight - 2 * insideMatches) := by
  omega

/-- A linear nonerasing tuple production partitions its parent yield into
one child, other children, and fresh terminals. A positive remaining yield
gives strict descent. Otherwise the distinguished child has equal size. -/
theorem tuple_yield_rank (own other terminals : Nat) :
    (0 < other + terminals → own < own + other + terminals) ∧
    (other + terminals = 0 → own = own + other + terminals) := by
  omega

inductive CopyPair {A : Type} : List A → List A → Prop where
  | byte (a : A) : CopyPair [a] [a]
  | step (a : A) : CopyPair x y → CopyPair (a :: x) (a :: y)

theorem copy_pair_iff {A : Type} (x y : List A) :
    CopyPair x y ↔ x = y ∧ x ≠ [] := by
  constructor
  · intro hx
    induction hx with
    | byte a => simp
    | step a _ ih => simp [ih.1]
  · rintro ⟨rfl, hn⟩
    induction x with
    | nil => contradiction
    | cons a rest ih =>
      cases rest with
      | nil => exact CopyPair.byte a
      | cons b rest => exact CopyPair.step a (ih (by simp))

/-- Characterization of the crossing fixture's start language. -/
theorem crossing_yield_iff {A : Type} (word : List A) :
    (∃ u v u' v', CopyPair u u' ∧ CopyPair v v' ∧ word = u ++ v ++ u' ++ v') ↔
    (∃ u v : List A, u ≠ [] ∧ v ≠ [] ∧ word = u ++ v ++ u ++ v) := by
  constructor
  · rintro ⟨u, v, u', v', hu, hv, hword⟩
    have ⟨ueq, une⟩ := (copy_pair_iff u u').mp hu
    have ⟨veq, vne⟩ := (copy_pair_iff v v').mp hv
    exact ⟨u, v, une, vne, by simpa [← ueq, ← veq] using hword⟩
  · rintro ⟨u, v, hu, hv, hword⟩
    exact ⟨u, v, u, v, (copy_pair_iff u u).mpr ⟨rfl, hu⟩,
      (copy_pair_iff v v).mpr ⟨rfl, hv⟩, hword⟩

/-- Pairwise disjoint blocks covering the pivot have exactly one occurrence
of the block containing it. -/
theorem unique_pivot_block {A : Type} [DecidableEq A] (pivot : A) (blocks : List (List A))
    (disjoint : blocks.Pairwise fun a b => ∀ x, x ∈ a → x ∉ b)
    (covered : ∃ b ∈ blocks, pivot ∈ b) :
    ∃ b, blocks.filter (fun b => decide (pivot ∈ b)) = [b] := by
  induction blocks with
  | nil => simp at covered
  | cons head rest ih =>
    obtain ⟨separate, restDisjoint⟩ := List.pairwise_cons.mp disjoint
    by_cases here : pivot ∈ head
    · have onlyHead : rest.filter (fun b => decide (pivot ∈ b)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simp [separate b hb pivot here]
      exact ⟨head, by simp [here, onlyHead]⟩
    · have restCovered : ∃ b ∈ rest, pivot ∈ b := by
        rcases covered with ⟨b, hb, inBlock⟩
        rcases List.mem_cons.mp hb with eq | inRest
        · subst b
          exact False.elim (here inBlock)
        · exact ⟨b, inRest, inBlock⟩
      obtain ⟨b, found⟩ := ih restDisjoint restCovered
      exact ⟨b, by simp [here, found]⟩

theorem partition_remainder_descends (block remainder : Nat) (positive : 0 < block) :
    remainder < block + remainder := by
  omega

end Structures
