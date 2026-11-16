/- E040 | Set extensionality | 3 min | Set, ext, membership, subset, mathlib
GOAL
  Prove set equalities by `ext` and subset facts by chasing an element.

REFERENCE
  example (A B : Set ℕ) : A ∪ B = B ∪ A := by ext x; simp only [Set.mem_union]; exact Or.comm
    -- `ext x` turns `S = T` into `x ∈ S ↔ x ∈ T`
  #check Set.mem_inter_iff   -- x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b   (also Set.mem_union)
  example (A B : Set ℕ) : A ∩ B ⊆ A := fun x hx => hx.1   -- `S ⊆ T` is `∀ x, x ∈ S → x ∈ T`
  example (A B : Set ℕ) : A ∩ B ⊆ A := by intro x hx; exact hx.1
  #check Set.mem_setOf_eq    -- (x ∈ {y | p y}) = p x
BANNED: Set.inter_comm, Set.subset_union_left, Set.inter_subset_inter_left
-/
import Mathlib

-- BEGIN SPEC
theorem inter_comm_set (A B : Set ℕ) : A ∩ B = B ∩ A :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem subset_union_set (A B : Set ℕ) : A ⊆ A ∪ B :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem inter_mono (A B C : Set ℕ) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem set_builder : {n : ℕ | n < 3} = {0, 1, 2} :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Equalities of sets: `ext x`. Subsets: `intro x hx` (or `rintro x ⟨ha, hc⟩`).
H2. After `ext`, rewrite membership into logic with `simp only [Set.mem_inter_iff]` etc.
H3. `set_builder`: `ext n; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; omega`.
-/
