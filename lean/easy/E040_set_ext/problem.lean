/- E040 | Set extensionality | 3 min | Set, ext, membership, subset, mathlib
GOAL
  Prove set equalities by `ext` and subset facts by chasing an element.

BANNED: Set.inter_comm, Set.subset_union_left, Set.inter_subset_inter_left

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · inter_comm_set
  1. Set equation → membership `↔` for one element `x`:                       R1
  2. Turn both memberships in `∩` into `∧`:                                   R2
  3. Split the `↔` into its two directions:                                   R3
  4. In each direction (same shape, so `<;>`): split the `∧` premise,
     then rebuild the conjunction in the other order:                        R4 → R5
-/
-- BEGIN SPEC
theorem inter_comm_set (A B : Set ℕ) : A ∩ B = B ∩ A :=
-- END SPEC
  sorry

/- SKELETON · subset_union_set
  1. `⊆` is a `∀`: take `x` and `hx : x ∈ A`:                                 R6
  2. `x ∈ A ∪ B` is by definition an `∨`: prove its left side
     (optionally rewrite it first with R7):                                  R8
  (Steps 1–2 also fit in one `fun` term, since `⊆` unfolds.)
-/
-- BEGIN SPEC
theorem subset_union_set (A B : Set ℕ) : A ⊆ A ∪ B :=
-- END SPEC
  sorry

/- SKELETON · inter_mono
  1. Take `x` and split `x ∈ A ∩ C` in the pattern:                           R9
  2. Move `x ∈ A` to `x ∈ B` with `h`:                                        R10
  3. Pair the two memberships into `x ∈ B ∩ C`:                               R11 (with R10 inside)
-/
-- BEGIN SPEC
theorem inter_mono (A B C : Set ℕ) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
-- END SPEC
  sorry

/- SKELETON · set_builder
  1. Set equation → membership `↔` for one `n`:                               R1
  2. Rewrite both memberships into arithmetic in one `simp only`:
       left side `{n | n < 3}`, right side `{0, 1, 2}`                       R12, R13, R14
  3. A linear statement about one natural number remains:                     R15
-/
-- BEGIN SPEC
theorem set_builder : {n : ℕ | n < 3} = {0, 1, 2} :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Equalities of sets: `ext x` (R1), then the goal is about membership. Subsets: `⊆` is a `∀`, so
    `intro x hx` (R6), or `rintro x ⟨ha, hc⟩` when the left side is an intersection (R9).
H2. Membership unfolds to logic: `∩` is `∧`, `∪` is `∨`, `{n | p n}` is `p n`, `{0, 1, 2}` is a chain of `=`
    joined by `∨`. Rewrite with the lemmas R2, R12–R14 under `simp only`, or use the unfolded form directly
    (`Or.inl`, `⟨_, _⟩`, `h ha`). `inter_comm_set`: after R1, R2, `constructor` and swap the `∧` both ways.
H3. `inter_comm_set`: after `ext x; simp only [Set.mem_inter_iff]; constructor`, each direction is
    `rintro ⟨h1, h2⟩` and then the swapped pair (`<;>` runs it on both).
    `subset_union_set`: the element `hx : x ∈ A` goes into `Or.inl`.
    `inter_mono`: after `rintro x ⟨ha, hc⟩`, the key term is `h ha : x ∈ B`; pair it with `hc`.
    `set_builder`: `ext n; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; omega`.
-/
