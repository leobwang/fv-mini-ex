/- M031 | Dedup a sorted list | 15 min | List.Pairwise, strict order, fun_induction [R16]
GOAL
  Implement `dedup`, which removes adjacent duplicates. Prove it keeps the same elements, and that
  on a sorted input the output is strictly increasing.

REFERENCE
  -- Pairwise (· < ·): strictly increasing.   Pairwise (· ≤ ·): sorted.
  #check List.Pairwise.cons          -- (∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)
  #check List.rel_of_pairwise_cons   -- Pairwise R (a :: l) → a' ∈ l → R a a'
  #check List.Pairwise.of_cons       -- Pairwise R (a :: l) → Pairwise R l
  example (x y : Nat) (h1 : x ≤ y) (h2 : x ≠ y) : x < y := by omega
  -- fun_induction on a def with `if x = y` substitutes `y := x` in that case automatically.
-/

namespace M031

-- BEGIN SPEC
def dedup (xs : List Nat) : List Nat :=
-- END SPEC
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedup (y :: rest) else x :: dedup (y :: rest)

-- BEGIN SPEC
theorem dedup_mem (xs : List Nat) (z : Nat) : z ∈ dedup xs ↔ z ∈ xs :=
-- END SPEC
  by
    fun_induction dedup xs with
    | case1 => simp
    | case2 x => simp
    | case3 x rest ih => simp_all
    | case4 x y rest h ih => simp_all

-- BEGIN SPEC
theorem dedup_strict (xs : List Nat) (h : xs.Pairwise (· ≤ ·)) : (dedup xs).Pairwise (· < ·) :=
-- END SPEC
  by
    fun_induction dedup xs with
    | case1 => simp
    | case2 x => simp
    | case3 x rest ih => exact ih h.of_cons
    | case4 x y rest hxy ih =>
      refine List.Pairwise.cons ?_ (ih h.of_cons)
      intro z hz
      rw [dedup_mem] at hz
      have h1 : x ≤ y := List.rel_of_pairwise_cons h List.mem_cons_self
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · have h2 : y ≤ z := List.rel_of_pairwise_cons h.of_cons hz
        omega

end M031

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare the first two elements; drop the first if they are equal.
H2. Prove `dedup_mem` first and use it in `dedup_strict` to locate elements of the recursive result.
H3. Case `x ≠ y`: `refine List.Pairwise.cons ?_ (ih h.of_cons)`; then `z ∈ y :: rest` gives `x ≤ y ≤ z` with `x ≠ y`, so `x < z` by omega.
-/
