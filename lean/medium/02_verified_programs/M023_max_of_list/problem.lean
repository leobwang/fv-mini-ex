/- M023 | Max of a non-empty list | 10-15 min | non-empty list, max, induction generalizing [R05]
GOAL
  Implement `maxList x xs`, the maximum of the non-empty list `x :: xs`, and prove it is an
  upper bound that occurs in the list.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M023

/- SKELETON · maxList
  1. Recurse on the list, carrying the maximum so far in the first argument:   R1
       `[]`      → nothing left: the answer is the accumulator `x`
       `y :: ys` → recurse on `ys` with the new accumulator `max x y`         R2
-/
-- BEGIN SPEC
def maxList (x : Int) (xs : List Int) : Int :=
-- END SPEC
  sorry

/- SKELETON · maxList_ge
  1. Induct on `xs` generalizing `x` (the recursive call is at `max x z`,
     and `ih` must apply there):                                              R3
  2. In both cases first introduce `y` and `hy : y ∈ …`:                       R4
  3. `nil`: `hy : y ∈ [x]` → `y = x`; then unfold `maxList` and close:        R5 → R6
  4. `cons z zs ih`: unfold one step; goal `y ≤ maxList (max x z) zs`:        R7
       BEFORE splitting `hy`, the IH at the head of `max x z :: zs`:
         hmax : max x z ≤ maxList (max x z) zs                                R8 (uses R9)
       `hy` → `y = x ∨ y = z ∨ y ∈ zs`; split it, substituting:               R10 → R11
         `y = x`, `y = z`: arithmetic with `max` and `hmax`                   R12
         `y ∈ zs`: the IH at `max x z` and `y`, membership in the tail        R8 (uses R13)
-/
-- BEGIN SPEC
theorem maxList_ge (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, y ≤ maxList x xs :=
-- END SPEC
  sorry

/- SKELETON · maxList_mem
  1. Induct on `xs` generalizing `x`:                                         R3
  2. `nil`: unfold `maxList` and close:                                       R6
  3. `cons z zs ih`: unfold one step; goal `maxList (max x z) zs ∈ x :: z :: zs`:   R7
       the IH at the new accumulator: `h : maxList (max x z) zs ∈ max x z :: zs`  R8
       `∈ _ :: _` → `= ∨ ∈` in `h` and in the goal:                          R10
       close: `max x z` is `x` or `z` (not something `omega` can use here)    R14
-/
-- BEGIN SPEC
theorem maxList_mem (x : Int) (xs : List Int) : maxList x xs ∈ x :: xs :=
-- END SPEC
  sorry

end M023

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Carry the maximum so far as the first argument: `maxList (max x y) ys` (R1, R2). Both proofs
    induct on `xs`, and the recursive call is at `max x z`, not at `x`: the IH must hold for every `x`.
H2. `induction xs generalizing x` (R3); in `cons`, `simp only [maxList]` (R7) and use `ih (max x z)` (R8).
    `maxList_ge`: get `hmax : max x z ≤ maxList (max x z) zs` from the IH at the head of the list, then
    `simp only [List.mem_cons] at hy` and split it into `y = x`, `y = z`, `y ∈ zs` (R10, R11).
    `maxList_mem`: rewrite both the IH and the goal with `List.mem_cons`, and finish with `grind` (R14).
H3. `maxList_ge`, `cons`: `have hmax := ih (max x z) (max x z) List.mem_cons_self`, then
    `rcases hy with rfl | rfl | hy`; `omega` closes the first two; the third is
    `exact ih (max x z) y (List.mem_cons_of_mem _ hy)`.
    `maxList_mem`, `cons`: `have h := ih (max x z); simp only [List.mem_cons] at h ⊢; grind`
    (`omega` cannot use facts like `m ∈ zs`; `grind` mixes them with arithmetic).
-/
