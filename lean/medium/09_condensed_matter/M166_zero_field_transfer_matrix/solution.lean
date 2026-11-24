/- M166 | Zero-field transfer matrix | 15-20 min | Matrix, !![…], matrix powers, induction, fin_cases, trace, cosh, mathlib
GOAL
  The zero-field Ising transfer matrix is `T = [[e^K, e^{-K}], [e^{-K}, e^K]]` with `K = βJ`. Prove
  `tr (Tⁿ) = (2 cosh K)ⁿ + (2 sinh K)ⁿ` (the eigenvalues of `T` are `2 cosh K` and `2 sinh K`;
  `tr Tⁿ` is the partition function of an `n`-spin Ising ring, see H097).

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M166

-- BEGIN SPEC
/-- Zero-field transfer matrix of the Ising chain, `K = β J`. -/
noncomputable def T0 (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp K, Real.exp (-K); Real.exp (-K), Real.exp K]
-- END SPEC

/- SKELETON · trace_pow
  Write c = 2 * Real.cosh K and s = 2 * Real.sinh K (spelled out in Lean).
  1. MILESTONE first, the closed form of the whole power (not of its trace):           R1
       key : T0 K ^ n = !![(cⁿ + sⁿ)/2, (cⁿ - sⁿ)/2; (cⁿ - sⁿ)/2, (cⁿ + sⁿ)/2]
     proved inside its `by` block by induction on n:                                  R2
       zero: matrix equation → four entries; `simp` on all four (`<;>`) closes them   R3, R4, R5–R8, R11
       succ: T0 K ^ (n + 1) → T0 K ^ n * T0 K, then the hypothesis                     R9, rw [ih]
             matrix equation → four entries                                            R3, R4
             on all four (`<;>`): one `simp` with T0, the product lemmas,               R10, R11, R12, R13, R14, R15, R9
               cosh/sinh → exp and pow_succ
             each of the four entries is now a polynomial identity (`<;>` again)       R16
  2. Use the milestone: rw [key], then the trace of a 2×2 matrix                      rw [key], R17
  3. Evaluate the two diagonal entries and add the halves: `simp`                     R11, R18
-/
-- BEGIN SPEC
theorem trace_pow (K : ℝ) (n : ℕ) :
    Matrix.trace (T0 K ^ n) = (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n :=
-- END SPEC
  by
    have key : T0 K ^ n =
        !![((2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n) / 2,
            ((2 * Real.cosh K) ^ n - (2 * Real.sinh K) ^ n) / 2;
           ((2 * Real.cosh K) ^ n - (2 * Real.sinh K) ^ n) / 2,
            ((2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n) / 2] := by
      induction n with
      | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
      | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [T0, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq, pow_succ] <;>
          ring
    rw [key, Matrix.trace_fin_two]
    simp

end M166

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Don't induct on the trace directly: the trace of `T^(n+1)` is not a function of the trace of `T^n`.
    Find a closed form for the whole matrix `T0 K ^ n` (milestone `key`, R1) and take its trace at the end.
H2. With `c = 2 cosh K` and `s = 2 sinh K`, the matrix `T^n` has diagonal entries `(cⁿ + sⁿ)/2` and
    off-diagonal entries `(cⁿ - sⁿ)/2`. Prove that by induction on `n` (R2), entry by entry (R3, R4):
    the base case is plain `simp`; in the step, `rw [pow_succ, ih]`, unfold `T0`, expand the product
    (R12, R13), turn `cosh`/`sinh` into `exp` (R14, R15), finish with `ring` (R16). Then R17 and `simp`.
H3. `have key : T0 K ^ n = !![(c^n + s^n)/2, (c^n - s^n)/2; (c^n - s^n)/2, (c^n + s^n)/2]` (with `c`, `s`
    written out); step: `rw [pow_succ, ih]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [T0, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq, pow_succ] <;> ring`;
    finish: `rw [key, Matrix.trace_fin_two]; simp`.
-/
