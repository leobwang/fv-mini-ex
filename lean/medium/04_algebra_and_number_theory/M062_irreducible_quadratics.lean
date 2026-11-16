/- M062 | Irreducible quadratics | 10-15 min | Polynomial, Irreducible, IsRoot, compute_degree, mathlib
GOAL
  Show `X² + 1` and `X² + X + 1` are irreducible over ℚ (over a field, a polynomial of degree 2 or 3
  is irreducible iff it has no root), and that `X² + 1` is not irreducible over ℂ (it has the root `i`).
  `ℚ[X]` is the type of polynomials in `X` with rational coefficients (`open Polynomial`).

REFERENCE
  -- `Irreducible p`: p is not a unit, and `p = a * b → IsUnit a ∨ IsUnit b` (over a field: p is not
  --   constant and has no factorization into two non-constant polynomials).
  #check Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    -- p.natDegree ∈ Finset.Icc 1 3 → (∀ x, ¬ p.IsRoot x) → Irreducible p     (over a field)
  #check Polynomial.degree_eq_one_of_irreducible_of_root   -- Irreducible p → p.IsRoot x → p.degree = 1
  #check Polynomial.IsRoot.def    -- p.IsRoot a ↔ eval a p = 0
  example : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!   -- also proves `degree = 2`
  example (x : ℚ) : (X ^ 2 + 1 : ℚ[X]).eval x = x ^ 2 + 1 := by simp   -- or `eval_add, eval_pow, eval_X, eval_one`
  example : (X ^ 2 + 1 : ℂ[X]).IsRoot Complex.I := by simp            -- `Complex.I` is i
  -- `natDegree : ℕ`, but `degree : WithBot ℕ` (so the zero polynomial has degree ⊥).
-/
import Mathlib

open Polynomial

namespace M062

-- BEGIN SPEC
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℚ[X]) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem irreducible_X_sq_add_X_add_one : Irreducible (X ^ 2 + X + 1 : ℚ[X]) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem not_irreducible_over_C : ¬ Irreducible (X ^ 2 + 1 : ℂ[X]) :=
-- END SPEC
  sorry

end M062

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Over ℚ: `apply irreducible_of_degree_le_three_of_not_isRoot` leaves a degree goal and a no-root
    goal. Over ℂ: assume irreducibility; the root `i` forces degree 1, but the degree is 2.
H2. Degree: compute `natDegree = 2` with `compute_degree!`, rewrite, then `decide`/`norm_num`.
    No root: unfold `IsRoot` and `eval`, then `x ^ 2 + 1 > 0` (`positivity`); for `x ^ 2 + x + 1`
    complete the square.
H3. `intro x; simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]; nlinarith [sq_nonneg (x + 1/2)]`;
    over ℂ: `have := degree_eq_one_of_irreducible_of_root h hroot`, `have hdeg : (X ^ 2 + 1 : ℂ[X]).degree = 2 := by compute_degree!`,
    then `rw [hdeg] at this` and refute `2 = 1` in `WithBot ℕ` (`exact absurd this (by decide)`).
-/
