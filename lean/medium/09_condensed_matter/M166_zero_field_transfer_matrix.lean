/- M166 | Zero-field transfer matrix | 15-20 min | Matrix, !![…], matrix powers, induction, fin_cases, trace, cosh, mathlib
GOAL
  The zero-field Ising transfer matrix is `T = [[e^K, e^{-K}], [e^{-K}, e^K]]` with `K = βJ`. Prove
  `tr (Tⁿ) = (2 cosh K)ⁿ + (2 sinh K)ⁿ` (the eigenvalues of `T` are `2 cosh K` and `2 sinh K`;
  `tr Tⁿ` is the partition function of an `n`-spin Ising ring, see H097).

REFERENCE
  example (a b c d : ℝ) : !![a, b; c, d] 1 0 = c := by simp     -- `!![row; row]`, entries `M i j`
  #check Matrix.mul_apply    -- (M * N) i k = ∑ j, M i j * N j k
  #check Fin.sum_univ_two    -- ∑ i : Fin 2, f i = f 0 + f 1
  #check Matrix.trace_fin_two  -- A.trace = A 0 0 + A 1 1
  #check pow_succ            -- a ^ (n + 1) = a ^ n * a
  #check Real.cosh_eq        -- cosh x = (exp x + exp (-x)) / 2   (and Real.sinh_eq)
  example (M N : Matrix (Fin 2) (Fin 2) ℝ) (h : ∀ i j, M i j = N i j) : M = N := by ext i j; exact h i j
  -- after `ext i j`, `fin_cases i <;> fin_cases j <;> simp [...]` splits into the 4 entries
-/
import Mathlib

namespace M166

-- BEGIN SPEC
/-- Zero-field transfer matrix of the Ising chain, `K = β J`. -/
noncomputable def T0 (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp K, Real.exp (-K); Real.exp (-K), Real.exp K]
-- END SPEC

-- BEGIN SPEC
theorem trace_pow (K : ℝ) (n : ℕ) :
    Matrix.trace (T0 K ^ n) = (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n :=
-- END SPEC
  sorry

end M166

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Don't induct on the trace directly: the trace of `T^(n+1)` is not a function of the trace of `T^n`.
    Find a closed form for the whole matrix `T0 K ^ n` and take its trace at the end.
H2. With `c = 2 cosh K` and `s = 2 sinh K`, the matrix `T^n` has diagonal entries `(cⁿ + sⁿ)/2` and
    off-diagonal entries `(cⁿ - sⁿ)/2`. Prove that by induction on `n`, entry by entry.
H3. `have key : T0 K ^ n = !![(c^n + s^n)/2, (c^n - s^n)/2; (c^n - s^n)/2, (c^n + s^n)/2]` (with `c`, `s`
    written out); step: `rw [pow_succ, ih]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [T0, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq, pow_succ] <;> ring`.
-/
