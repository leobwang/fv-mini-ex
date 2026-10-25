/- M21 | Max of a non-empty list | 10-15 min | non-empty list, max, induction generalizing [R05]
GOAL
  Implement `maxList x xs`, the maximum of the non-empty list `x :: xs`, and prove it is an
  upper bound that occurs in the list.

REFERENCE
  -- Non-emptiness is built into the signature: the list is `x :: xs`.
  example (a b : Int) : a ≤ max a b ∧ b ≤ max a b := by omega        -- omega knows max
  example (a b : Int) : max a b = a ∨ max a b = b := by omega
  #check List.mem_cons   -- a ∈ b :: l ↔ a = b ∨ a ∈ l
  example (y : Int) (ys : List Int) (h : y ∈ ys) : y ∈ 0 :: ys := List.mem_cons_of_mem 0 h
-/

namespace M21

-- BEGIN SPEC
def maxList (x : Int) (xs : List Int) : Int :=
-- END SPEC
  match xs with
  | [] => x
  | y :: ys => maxList (max x y) ys

-- BEGIN SPEC
theorem maxList_ge (x : Int) (xs : List Int) : ∀ y ∈ x :: xs, y ≤ maxList x xs :=
-- END SPEC
  by
    induction xs generalizing x with
    | nil => intro y hy; simp at hy; simp [maxList, hy]
    | cons z zs ih =>
      intro y hy
      simp only [maxList]
      have hmax := ih (max x z) (max x z) (List.mem_cons_self)
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · omega
      · omega
      · exact ih (max x z) y (List.mem_cons_of_mem _ hy)

-- BEGIN SPEC
theorem maxList_mem (x : Int) (xs : List Int) : maxList x xs ∈ x :: xs :=
-- END SPEC
  by
    induction xs generalizing x with
    | nil => simp [maxList]
    | cons z zs ih =>
      simp only [maxList]
      have h := ih (max x z)
      simp only [List.mem_cons] at h ⊢
      grind

end M21

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Carry the maximum so far as the first argument: `maxList (max x y) ys`.
H2. Induct on `xs` generalising `x`; the IH is about `maxList (max x z) zs`.
H3. `maxList_mem`: `have h := ih (max x z); simp only [List.mem_cons] at h ⊢; grind` (omega cannot use facts like `m ∈ zs`; grind mixes them with arithmetic).
-/
