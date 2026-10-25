/- M28 | Merge sorted lists | 20 min | lexicographic termination, List.Perm, List.Pairwise [R15]
GOAL
  Implement `merge` of two sorted lists. Prove the result is a permutation of `xs ++ ys` and is
  sorted whenever both inputs are.

REFERENCE
  -- `match xs, ys with | [], ys => .. | x :: xs, [] => .. | x :: xs, y :: ys => ..`
  -- Lean finds the termination order itself (one list shrinks while the other stays).
  #check List.perm_middle      -- (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))
  #check List.Perm.mem_iff     -- l₁.Perm l₂ → (a ∈ l₁ ↔ a ∈ l₂)
  #check List.Pairwise.cons    -- (∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)
  #check List.rel_of_pairwise_cons   -- Pairwise R (a :: l) → a' ∈ l → R a a'
  -- fun_induction merge xs ys : one case per match arm / if branch, with IHs.
-/

namespace M28

-- BEGIN SPEC
def merge (xs ys : List Nat) : List Nat :=
-- END SPEC
  match xs, ys with
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

-- BEGIN SPEC
theorem merge_perm (xs ys : List Nat) : (merge xs ys).Perm (xs ++ ys) :=
-- END SPEC
  by
    fun_induction merge xs ys with
    | case1 ys => exact .refl _
    | case2 x xs => simp
    | case3 x xs y ys h ih => exact ih.cons x
    | case4 x xs y ys h ih => exact (ih.cons y).trans List.perm_middle.symm

-- BEGIN SPEC
theorem merge_sorted (xs ys : List Nat) (hx : xs.Pairwise (· ≤ ·)) (hy : ys.Pairwise (· ≤ ·)) :
    (merge xs ys).Pairwise (· ≤ ·) :=
-- END SPEC
  by
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

end M28

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove `merge_perm` first: sortedness needs to know which elements end up behind the head.
H2. In the sortedness proof, the new head is ≤ every element of the merged tail; get the tail's elements from `merge_perm` with `.mem_iff`.
H3. Perm when `y` goes first: `(ih.cons y).trans List.perm_middle.symm`. Sorted: `refine List.Pairwise.cons ?_ (ih ..)`, then `rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz`.
-/
