/- M021 | Partition is a permutation | 10-15 min | List.Perm, List.filter, pairs
GOAL
  `partition p xs` splits a list in one pass. Show it equals the two filters, and that
  gluing the parts back together is a permutation of the input.

REFERENCE
  #check List.filter_cons   -- filter p (x :: xs) = if p x = true then x :: filter p xs else filter p xs
  #check List.perm_middle   -- (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))
  example (b : Bool) : b = true ∨ b = false := by cases b <;> simp
  example (p : Nat → Bool) (x : Nat) : True := by cases h : p x <;> trivial   -- name the case fact
  example (a b : List Nat) : (a, b).1 = a := rfl
BANNED: List.filter_append_perm
-/

namespace M021

-- BEGIN SPEC
def partition (p : Nat → Bool) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let r := partition p xs
    if p x then (x :: r.1, r.2) else (r.1, x :: r.2)
-- END SPEC

-- BEGIN SPEC
theorem partition_eq (p : Nat → Bool) (xs : List Nat) :
    partition p xs = (xs.filter p, xs.filter (fun x => !p x)) :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases h : p x <;> simp [partition, ih, List.filter_cons, h]

-- BEGIN SPEC
theorem partition_perm (p : Nat → Bool) (xs : List Nat) :
    ((partition p xs).1 ++ (partition p xs).2).Perm xs :=
-- END SPEC
  by
    rw [partition_eq]
    induction xs with
    | nil => exact .refl _
    | cons x xs ih =>
      cases h : p x
      · simp only [List.filter_cons, h] at ih ⊢
        simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
        exact List.perm_middle.trans (ih.cons x)
      · simp only [List.filter_cons, h] at ih ⊢
        simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false, List.cons_append]
        exact ih.cons x

end M021

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove `partition_eq` first, then the permutation is about the two filters.
H2. Induct on `xs` and split on `p x` with `cases h : p x`; simplify with `List.filter_cons` and `h`.
H3. When `p x = false`, the goal is `filter p xs ++ x :: filter (!p ·) xs ~ x :: xs`: `exact List.perm_middle.trans (ih.cons x)`.
-/
