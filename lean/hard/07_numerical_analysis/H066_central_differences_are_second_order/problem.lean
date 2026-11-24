/- H066 | Central differences are second order | 60-90 min | Taylor n=2 and n=3, iteratedDerivWithin, symmetric cancellation, mathlib
GOAL
  Two central-difference formulas, both with error O(h²) (`h > 0` is the step size):
  (1) if `|f'''| ≤ M` everywhere, `(f(x+h) - f(x-h))/(2h)` is within `M h²/6` of `f'(x)`;
  (2) if `|f''''| ≤ M` everywhere, `(f(x+h) - 2f(x) + f(x-h))/h²` is within `M h²/12` of `f''(x)`.
  Expand `f(x ± h)` by Taylor with a Lagrange remainder; by symmetry, (1) cancels the even terms, (2) the odd ones.

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Set

namespace H066

-- MILESTONE (optional: change or delete)
theorem uniqueDiffOn_uIcc (x y : ℝ) (hxy : x ≠ y) : UniqueDiffOn ℝ (uIcc x y) := by
  sorry

-- MILESTONE (optional: change or delete)
-- Second-order Taylor at `x`, for a step `h` of either sign.
theorem taylor2 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x h : ℝ) (hh : h ≠ 0) :
    ∃ ξ, f (x + h) = f x + h * deriv f x + h ^ 2 / 2 * iteratedDeriv 2 f x
      + iteratedDeriv 3 f ξ * h ^ 3 / 6 := by
  sorry

-- MILESTONE (optional: change or delete)
-- The exact error: only the two third-derivative remainders survive.
theorem central_error_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x h : ℝ) (hh : 0 < h) :
    ∃ ξ₁ ξ₂, (f (x + h) - f (x - h)) / (2 * h) - deriv f x
      = h ^ 2 / 12 * (iteratedDeriv 3 f ξ₁ + iteratedDeriv 3 f ξ₂) := by
  sorry

/- SKELETON · central_difference_error
  Prove the milestones above first, in this order; each one is used by the next.
  A. uniqueDiffOn_uIcc  (gives R12 its first argument inside taylor2 and taylor3)
     1. split on which of x, y is smaller:                                 R1
     2. each case: uIcc → Icc, then close                                  R2 (resp. R3), R4
  B. taylor2  (used twice in C: at h and at -h)
     1. hne : x ≠ x + h                                                    R5 → R6 → R7
     2. Taylor with remainder, degree 2 (n := 2), then pick its ξ          R8 with R9, refine ⟨ξ, ?_⟩
     3. hu : UniqueDiffOn ℝ (uIcc x (x + h))                               milestone A
     4. d1 : iteratedDerivWithin 1 f (uIcc x (x + h)) x = deriv f x        R12 (hu, R13 → R14 → R15, R16), R17
        d2 : iteratedDerivWithin 2 f (uIcc x (x + h)) x = iteratedDeriv 2 f x      R12 (same arguments)
     5. all at hξ: unfold the polynomial twice, degree 0, substitute d1 d2   R10, R10, R11, rw [d1, d2]
     6. only now evaluate the numerals, then close                         R18, R19
  C. central_error_eq  (used in the main proof)
     1. expand at h and at -h (side goals h ≠ 0, -h ≠ 0 from 0 < h)        milestone B twice, R7
     2. the second expansion says f (x + -h): make it f (x - h)            R20
     3. pick ξ₁ ξ₂, substitute both expansions, clear 2 * h, finish        refine, rw [h1, h2], R21, ring
  Main:
     1. the exact error e : … = h ^ 2 / 12 * (f'''(ξ₁) + f'''(ξ₂))          milestone C, obtain
     2. rewrite with e, split the |·| of the product, drop |h ^ 2 / 12|     rw [e], R22, R23 with R24
     3. triangle inequality on the two remainders                          R25
     4. calc through h ^ 2 / 12 * (M + M), then simplify                   R26: ≤ by R27, R28 [hM ξ₁, hM ξ₂]; = by ring
-/
-- BEGIN SPEC
theorem central_difference_error (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M x h : ℝ) (hh : 0 < h)
    (hM : ∀ y, |iteratedDeriv 3 f y| ≤ M) :
    |(f (x + h) - f (x - h)) / (2 * h) - deriv f x| ≤ M * h ^ 2 / 6 :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
-- Third-order Taylor at `x`: `taylor2` with one more `taylorWithinEval_succ` and one more coefficient.
theorem taylor3 (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x h : ℝ) (hh : h ≠ 0) :
    ∃ ξ, f (x + h) = f x + h * deriv f x + h ^ 2 / 2 * iteratedDeriv 2 f x
      + h ^ 3 / 6 * iteratedDeriv 3 f x + iteratedDeriv 4 f ξ * h ^ 4 / 24 := by
  sorry

-- MILESTONE (optional: change or delete)
-- The exact error of the second difference: now the odd terms `h f'(x)` and `h³/6 f'''(x)` cancel.
theorem second_diff_error_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x h : ℝ) (hh : 0 < h) :
    ∃ ξ₁ ξ₂, (f (x + h) - 2 * f x + f (x - h)) / h ^ 2 - iteratedDeriv 2 f x
      = h ^ 2 / 24 * (iteratedDeriv 4 f ξ₁ + iteratedDeriv 4 f ξ₂) := by
  sorry

/- SKELETON · second_difference_error
  Prove the milestones above first; they repeat Part 1 one degree higher.
  D. taylor3  (used twice in E)
     as B with n := 3: R10 three times before R11, and a third coefficient
     d3 : iteratedDerivWithin 3 f (uIcc x (x + h)) x = iteratedDeriv 3 f x   R12 (hu, R13 → R14 → R15, R16)
     then R18, R19
  E. second_diff_error_eq  (used in the main proof)
     as C with milestone D: R7, R20, refine, rw [h1, h2], R21, ring
  Main: as for central_difference_error, with milestone E and the factor h ^ 2 / 24:
     rw [e], R22, R23 with R24; R25; R26 through h ^ 2 / 24 * (M + M): ≤ by R27, R28; = by ring
-/
-- BEGIN SPEC
theorem second_difference_error (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M x h : ℝ) (hh : 0 < h)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) :
    |(f (x + h) - 2 * f x + f (x - h)) / h ^ 2 - iteratedDeriv 2 f x| ≤ M * h ^ 2 / 12 :=
-- END SPEC
  sorry

end H066

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `f(x+h)` and `f(x-h) = f(x + (-h))` as `f x ± h f'(x) + h²/2 f''(x) ± f'''(ξ)h³/6`. Subtract: the
    `f x` and `f''(x)` terms cancel, leaving `2h f'(x) + (f'''(ξ₁) + f'''(ξ₂)) h³/6`. For (2) expand one order
    further and add: `± h f'(x)` and `± h³/6 f'''(x)` cancel, leaving `h² f''(x) + (f''''(ξ₁) + f''''(ξ₂)) h⁴/24`.
H2. Milestones in the SKELETON order. `taylor2`: Taylor with Lagrange remainder (R8), unfold the polynomial
    (R10, R10, R11), and turn every coefficient `iteratedDerivWithin k f (uIcc x (x + h)) x` into
    `iteratedDeriv k f x` (R12; `deriv f x` for k = 1, R17) BEFORE `norm_num` (W4). `central_error_eq`: `taylor2`
    at `h` and at `-h`, then pure algebra. The bound: `|c * e| = c * |e|` for `c > 0`, the triangle inequality,
    then `|f'''| ≤ M` twice. Part 2 repeats this with `taylor3`.
H3. `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (x₀ := x) (x := x + h) hne hf.contDiffOn`;
    `rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval, d1, d2] at hξ`, then
    `norm_num [Nat.factorial] at hξ; linear_combination hξ`. `central_error_eq`: `rw [← sub_eq_add_neg] at h2`,
    `rw [h1, h2]; field_simp; ring`. Main: `rw [e, abs_mul, abs_of_pos (by positivity)]`, `have h12 := abs_add_le …`,
    `calc … ≤ h ^ 2 / 12 * (M + M) := by gcongr; linarith [hM ξ₁, hM ξ₂]` then `_ = M * h ^ 2 / 6 := by ring`.
-/
