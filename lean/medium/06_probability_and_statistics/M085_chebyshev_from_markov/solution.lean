/- M085 | Chebyshev from Markov | 10-15 min | variance, Markov, set rewriting, MemLp, mathlib
GOAL
  Chebyshev's inequality `P(|X - E X| ≥ c) ≤ Var X / c²` for `c > 0`, by applying Markov's
  inequality (allowed here) to the nonnegative variable `(X - E X)²`.
BANNED: meas_ge_le_variance_div_sq, meas_ge_le_evariance_div_sq, pow_mul_meas_ge_le_eLpNorm, mul_meas_ge_le_pow_eLpNorm, mul_meas_ge_le_pow_eLpNorm', meas_ge_le_mul_pow_eLpNorm_enorm

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M085

/- SKELETON · chebyshev
  1. The event in squared form, a `have` proved by:                               R1, R2, R3
       hset : {ω | c ≤ |X ω - μ[X]|} = {ω | c ^ 2 ≤ (X ω - μ[X]) ^ 2}
     after R3 the goal is `c ≤ |…| ↔ c ^ 2 ≤ |…| ^ 2`: close it with the
     monotonicity of squaring, flipped                                            R7 with R5, R4, R6, then R8
  2. Integrability of the squared deviation (state the type in lambda form):
       hint : Integrable (fun ω => (X ω - μ[X]) ^ 2) μ                            R9 → R10
  3. Markov for that function at level c ^ 2 (a `have` with no type):            R11
       its a.e. argument                                                          R12 with R13
  4. In Markov's fact: the integral → Var[X; μ], the set → the original event:   R15 with R14, R16 (hset)
  5. Clear the goal's denominator c ^ 2, then finish:                             R17 with R18, R19
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem chebyshev {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] / c ^ 2 :=
-- END SPEC
  by
    have hset : {ω | c ≤ |X ω - μ[X]|} = {ω | c ^ 2 ≤ (X ω - μ[X]) ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← sq_abs (X ω - μ[X])]
      exact (pow_le_pow_iff_left₀ hc.le (abs_nonneg _) two_ne_zero).symm
    have hint : Integrable (fun ω => (X ω - μ[X]) ^ 2) μ := (hX.sub (memLp_const _)).integrable_sq
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - μ[X])) hint (c ^ 2)
    rw [← variance_eq_integral hX.aemeasurable, ← hset] at hm
    rw [le_div_iff₀ (by positivity)]
    linarith

end M085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The event `c ≤ |X - E X|` is the same event as `c² ≤ (X - E X)²`, and the expectation of
    `(X - E X)²` is exactly `Var X`. So Markov for `(X - E X)²` at level `c²` is the whole proof.
H2. Prove the set equality `hset` with `ext ω` (R1–R8), the integrability `hint` (R9, R10), apply Markov
    (R11) to `fun ω => (X ω - μ[X]) ^ 2` at `c ^ 2`, then rewrite its right side into `Var[X; μ]` (R15) and
    its set back into the original event (R16). Clear the denominator (R17) and finish linearly (R19).
H3. In `hset` the key rewrite is `rw [← sq_abs (X ω - μ[X])]`; then R7 with `hc.le`, `abs_nonneg _`, `two_ne_zero`, flipped.
    `have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - μ[X])) hint (c ^ 2)`,
    then `rw [← variance_eq_integral hX.aemeasurable, ← hset] at hm`, `rw [le_div_iff₀ (by positivity)]`, `linarith`.
-/
