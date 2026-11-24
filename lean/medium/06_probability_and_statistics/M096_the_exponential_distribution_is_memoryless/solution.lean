/- M096 | The exponential distribution is memoryless | 15-20 min | expMeasure, cdf, cond, ENNReal.ofReal, complements, mathlib
GOAL
  For `T ~ Exp(r)`: the tail is `P(T > x) = e^{-r x}` for `x ≥ 0`, and `T` is memoryless:
  `P(T > s + t | T > s) = P(T > t)` (having waited `s`, the remaining wait is again `Exp(r)`).

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M096

/- SKELETON · exp_tail
  1. Add the probability instance (R3 and R5 ask for it):                   R1
  2. One `rw [...]` chain on the left side, in this order:
       tail `Ioi x` → complement of `Iic x` → `1 - μ (Iic x)`                R2, R3 with R4
       `μ (Iic x)` → `ofReal (cdf …)` → the `if` → its `then` branch         R5, R6, R7
       `1` → `ofReal 1`, then merge the difference into one `ofReal`        R8, R9
         R9's side fact `0 ≤ 1 - exp (-(r * x))`:                            R10 → R11 → R12
  3. Both sides are now `ofReal (…)`: drop it                               R13
  4. Finish the real identity `1 - (1 - e) = e`:                             ring
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem exp_tail (r x : ℝ) (hr : 0 < r) (hx : 0 ≤ x) :
    expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) :=
-- END SPEC
  by
    haveI := isProbabilityMeasure_expMeasure hr
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr,
      if_pos hx, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))]
    congr 1
    ring

/- SKELETON · exp_memoryless
  1. Conditional probability → `(μ (Ioi s))⁻¹ * μ (Ioi s ∩ Ioi (s + t))`:   R14 with R15
  2. The intersection → `Ioi (s + t)` (side fact `s ≤ s + t`):              R16, R17 with R18
  3. Rewrite the three tails with your `exp_tail` at `s + t`, `s`, `t`
     (side fact `0 ≤ s + t`):                                               rw [exp_tail …], R18
  4. Merge the left side into one `ofReal (exp (…))`:                        R19 with R20, R21 with R22,
                                                                            R23, R24
  5. Drop `ofReal` and `exp` on both sides:                                 R25
  6. Finish the identity of exponents:                                      ring
-/
-- BEGIN SPEC
theorem exp_memoryless (r s t : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expMeasure r)[Set.Ioi (s + t) | Set.Ioi s] = expMeasure r (Set.Ioi t) :=
-- END SPEC
  by
    rw [cond_apply measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right (by linarith),
      exp_tail r (s + t) hr (by linarith), exp_tail r s hr hs, exp_tail r t hr ht,
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring

end M096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tail: `T > x` is the complement of `T ≤ x`, whose probability is the cdf, and Mathlib knows the cdf
    of `Exp(r)`. Memoryless: `P(A | B) = P(B)⁻¹ · P(B ∩ A)` and `{T > s} ∩ {T > s + t} = {T > s + t}`; then
    use `exp_tail` three times. `ring` cannot work inside `ENNReal.ofReal`: in both proofs, merge each side
    into a single `ofReal (…)`, strip it with `congr`, and finish with `ring` on real numbers.
H2. Tail: add the instance with `haveI` (R1); rewrite the left side complement → `1 - μ (Iic x)` → cdf →
    the `if` → its branch (R2–R7); write `1` as `ofReal 1` and merge the difference (R8, R9); `congr 1; ring`.
    Memoryless: `cond_apply`, then shrink the intersection to `Ioi (s + t)` (R14–R18); rewrite with
    `exp_tail` three times; merge the left side (R19–R24); `congr 2; ring`.
H3. Tail: `rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr,
    if_pos hx, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h]` with
    `h := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))`. Memoryless, after the three `exp_tail`s:
    `rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_neg, ← Real.exp_add]`.
-/
