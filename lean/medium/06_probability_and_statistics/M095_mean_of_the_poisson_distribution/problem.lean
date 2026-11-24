/- M095 | Mean of the Poisson distribution | 20 min | poissonMeasure, tsum, HasSum, index shift, mathlib
GOAL
  The Poisson law `Po(r)`, `P(K = k) = e^{-r} r^k / k!`, has mean `r`. Mathlib does not have this: turn
  the expectation into a series, shift the index by one, and reuse that the probabilities sum to 1.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M095

/- SKELETON · poisson_mean
  1. Expectation → series:                                                 R1
  2. Name the summand  f n = (e^{-r} rⁿ / n!) • n  (goal becomes `tsum f = ↑r`):   R2
  3. MILESTONE A, prove it first in a `have`:
       hshift : HasSum (fun n => f (n + 1)) ↑r
     a. total probability, scaled by `(r : ℝ)`, then clean up `↑r * 1`:     R4 → R5 → R6
     b. the summand identity, as its own `have`:
          e : (fun n => f (n + 1)) = fun i => ↑r * (Real.exp (-↑r) * ↑r ^ i / ↑i.factorial)
        pointwise; unfold `f`, `•` and `(n + 1)!` (one `simp only`); casts; denominators; algebra:
                                                                            R7, R8 + R9 + R10, R11, R12, R13
     c. `rw [e]` in the goal, then `exact` the hypothesis from a.
  4. MILESTONE B, used in step 5:  HasSum f ↑r  from hshift (the term n = 0 is 0):
       tail from index 1, then simplify with `hf` and close with hshift:    R14 → R16 (R15, R8 inside)
  5. Conclude from milestone B:                                             R3
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem poisson_mean (r : ℝ≥0) :
    ∫ k, (k : ℝ) ∂(poissonMeasure r) = r :=
-- END SPEC
  sorry

end M095

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do not compute with `∑'`. Name the summand `f n = (e^{-r} rⁿ / n!) • n` (R2), prove `HasSum f r` and
    conclude with `.tsum_eq` (R3). The term `n = 0` is 0, and `f (n + 1) = r · (e^{-r} rⁿ / n!)`: the series
    shifted by one is `r` times the total probability (R4).
H2. Milestone A `hshift : HasSum (fun n => f (n + 1)) r`: start from `(hasSum_one_poissonMeasure r).mul_left (r : ℝ)`,
    `rw [mul_one] at h1`, and prove the function identity with `funext n`, `simp only [hf, smul_eq_mul,
    Nat.factorial_succ]`, `push_cast`, `field_simp`, `ring`. Milestone B: unshift with `hasSum_nat_add_iff' 1` (R14).
H3. `have : HasSum f r := by rw [← hasSum_nat_add_iff' 1]; simpa [hf] using hshift`, then `exact this.tsum_eq`.
-/
