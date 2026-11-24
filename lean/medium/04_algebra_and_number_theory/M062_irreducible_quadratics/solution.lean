/- M062 | Irreducible quadratics | 10-15 min | Polynomial, Irreducible, IsRoot, compute_degree, mathlib
GOAL
  Show `X² + 1` and `X² + X + 1` are irreducible over ℚ (over a field, a polynomial of degree 2 or 3
  is irreducible iff it has no root), and that `X² + 1` is not irreducible over ℂ (it has the root `i`).
  `ℚ[X]` is the type of polynomials in `X` with rational coefficients (`open Polynomial`).

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Polynomial

namespace M062

/- SKELETON · irreducible_X_sq_add_one
  1. The degree fact, before anything else:                                 have, R1
       hdeg : (X ^ 2 + 1 : ℚ[X]).natDegree = 2
  2. `Irreducible p` → a degree goal and a no-root goal:                    R2
  3. Degree goal `p.natDegree ∈ Finset.Icc 1 3`:                            rw [hdeg], R3
  4. No-root goal `∀ x, ¬ p.IsRoot x`:                                      intro x
       unfold `IsRoot`, evaluate p at x, all in one `simp only [...]`:      R4, R5, R6, R7, R8
       `¬ x ^ 2 + 1 = 0` (a square plus a positive constant):              R9
-/
-- BEGIN SPEC
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℚ[X]) :=
-- END SPEC
  by
    have hdeg : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      positivity

/- SKELETON · irreducible_X_sq_add_X_add_one
  1–3. As in irreducible_X_sq_add_one, with this polynomial:                have, R1; R2; rw [hdeg], R3
  4. No-root goal: intro x, then the same `simp only [...]`:                R4–R8
       `¬ x ^ 2 + x + 1 = 0`: R9 fails here (the lone term `x` may be negative).
       Complete the square, x² + x + 1 = (x + 1/2)² + 3/4:                 R10 → R11
-/
-- BEGIN SPEC
theorem irreducible_X_sq_add_X_add_one : Irreducible (X ^ 2 + X + 1 : ℚ[X]) :=
-- END SPEC
  by
    have hdeg : (X ^ 2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      -- WHY: x² + x + 1 = (x + 1/2)² + 3/4 > 0
      nlinarith [sq_nonneg (x + 1 / 2)]

/- SKELETON · not_irreducible_over_C
  1. Assume irreducibility (h : Irreducible …, goal False):                 R12
  2. The root i:  hroot : (X ^ 2 + 1 : ℂ[X]).IsRoot Complex.I                have, `simp` (R4–R8, R13)
  3. Irreducible + root → degree 1:  h1 : (X ^ 2 + 1).degree = 1            R14
  4. The true degree:  hdeg : (X ^ 2 + 1 : ℂ[X]).degree = 2                  have, R1
  5. h1 becomes `2 = 1` (in WithBot ℕ):                                     R15
  6. Refute it:                                                              R16 with R17
-/
-- BEGIN SPEC
theorem not_irreducible_over_C : ¬ Irreducible (X ^ 2 + 1 : ℂ[X]) :=
-- END SPEC
  by
    intro h
    have hroot : (X ^ 2 + 1 : ℂ[X]).IsRoot Complex.I := by simp
    have h1 := degree_eq_one_of_irreducible_of_root h hroot
    have hdeg : (X ^ 2 + 1 : ℂ[X]).degree = 2 := by compute_degree!
    rw [hdeg] at h1
    exact absurd h1 (by decide)

end M062

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Over ℚ, a degree-2 polynomial is irreducible iff it has no root (R2): that leaves a degree goal and
    a no-root goal. Over ℂ, argue by contradiction: an irreducible polynomial with a root has degree 1
    (R14), but `X² + 1` has degree 2.
H2. Degree goal: `have hdeg : … .natDegree = 2 := by compute_degree!`, then `rw [hdeg]; decide`.
    No-root goal: `intro x; simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]`, then `positivity`
    for `x ^ 2 + 1`; for `x ^ 2 + x + 1` complete the square. Over ℂ: `intro h`, prove the root
    `Complex.I` with `simp`, get `degree = 1` from R14, compute `degree = 2` with R1, contradict.
H3. `nlinarith [sq_nonneg (x + 1 / 2)]` closes `¬ x ^ 2 + x + 1 = 0`. Over ℂ:
    `have h1 := degree_eq_one_of_irreducible_of_root h hroot`,
    `have hdeg : (X ^ 2 + 1 : ℂ[X]).degree = 2 := by compute_degree!`, `rw [hdeg] at h1`,
    `exact absurd h1 (by decide)`.
-/
