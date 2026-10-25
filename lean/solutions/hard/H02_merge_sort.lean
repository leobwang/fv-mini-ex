/- H02 | Merge sort | 1-1.5 h | well-founded recursion, fun_induction, List.Perm, List.Pairwise [R20]
GOAL
  Prove merge sort returns a sorted permutation of its input. `msort` splits the list in half
  with `take`/`drop` and recurses by well-founded recursion on the length.

REFERENCE
  #check List.take_append_drop   -- (n : Nat) (l : List α) : List.take n l ++ List.drop n l = l
  #check List.Perm.append        -- l₁ ~ l₂ → l₃ ~ l₄ → l₁ ++ l₃ ~ l₂ ++ l₄
  #check List.perm_middle        -- (l₁ ++ a :: l₂) ~ (a :: (l₁ ++ l₂))
  #check List.Perm.mem_iff       -- l₁ ~ l₂ → (a ∈ l₁ ↔ a ∈ l₂)
  #check List.Pairwise.cons      -- (∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)
  #check List.rel_of_pairwise_cons   -- Pairwise R (a :: l) → a' ∈ l → R a a'
  -- fun_induction msort xs : a base case (length < 2) and a recursive case with IHs for both halves.
  -- In the recursive case, `let` names (`half`) appear as local definitions; `simp only [half]` or `show`.
-/

namespace H02

-- BEGIN SPEC
abbrev Sorted (xs : List Nat) : Prop := xs.Pairwise (· ≤ ·)

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

def msort (xs : List Nat) : List Nat :=
  if h : xs.length < 2 then xs
  else
    let half := xs.length / 2
    merge (msort (xs.take half)) (msort (xs.drop half))
termination_by xs.length
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem merge_perm (xs ys : List Nat) : (merge xs ys).Perm (xs ++ ys) := by
  fun_induction merge xs ys with
  | case1 ys => exact .refl _
  | case2 x xs => simp
  | case3 x xs y ys h ih => exact ih.cons x
  | case4 x xs y ys h ih => exact (ih.cons y).trans List.perm_middle.symm

-- MILESTONE (optional: change or delete)
theorem merge_sorted (xs ys : List Nat) (hx : Sorted xs) (hy : Sorted ys) : Sorted (merge xs ys) := by
  fun_induction merge xs ys with
  | case1 ys => exact hy
  | case2 x xs => exact hx
  | case3 x xs y ys hxy ih =>
    refine List.Pairwise.cons ?_ (ih hx.of_cons hy)
    intro z hz
    rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact List.rel_of_pairwise_cons hx hz
    · exact hxy
    · exact Nat.le_trans hxy (List.rel_of_pairwise_cons hy hz)
  | case4 x xs y ys hxy ih =>
    refine List.Pairwise.cons ?_ (ih hx hy.of_cons)
    intro z hz
    rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz
    rcases hz with (rfl | hz) | hz
    · omega
    · have := List.rel_of_pairwise_cons hx hz
      omega
    · exact List.rel_of_pairwise_cons hy hz

-- BEGIN SPEC
theorem msort_perm (xs : List Nat) : (msort xs).Perm xs :=
-- END SPEC
  by
    fun_induction msort xs with
    | case1 xs h => exact .refl _
    | case2 xs h half ih1 ih2 =>
      refine (merge_perm _ _).trans ?_
      have := (ih1.append ih2)
      rw [List.take_append_drop] at this
      exact this

-- BEGIN SPEC
theorem msort_sorted (xs : List Nat) : Sorted (msort xs) :=
-- END SPEC
  by
    fun_induction msort xs with
    | case1 xs h =>
      match xs, h with
      | [], _ => exact .nil
      | [x], _ => exact List.pairwise_singleton _ x
    | case2 xs h half ih1 ih2 => exact merge_sorted _ _ ih1 ih2

end H02

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything about `msort` reduces to `merge_perm` and `merge_sorted` plus the IHs from `fun_induction msort xs`.
H2. Perm: `merge (msort take) (msort drop) ~ msort take ++ msort drop ~ take ++ drop = xs`. Sorted base case: a list of length < 2 is `[]` or `[x]`.
H3. `refine (merge_perm _ _).trans ?_; have := ih1.append ih2; rw [List.take_append_drop] at this; exact this`. Base case: `match xs, h with | [], _ => exact .nil | [x], _ => exact List.pairwise_singleton _ x`.
-/
