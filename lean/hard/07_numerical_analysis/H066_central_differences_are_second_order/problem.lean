/- H066 | Central differences are second order | 60-90 min | Taylor n=2 and n=3, iteratedDerivWithin, symmetric cancellation, mathlib
GOAL
  Two central-difference formulas, both with error O(h²) (`h > 0` is the step size):
  (1) if `|f'''| ≤ M` everywhere, `(f(x+h) - f(x-h))/(2h)` is within `M h²/6` of `f'(x)`;
  (2) if `|f''''| ≤ M` everywhere, `(f(x+h) - 2f(x) + f(x-h))/h²` is within `M h²/12` of `f''(x)`.
  Expand `f(x ± h)` by Taylor with a Lagrange remainder; by symmetry, (1) cancels the even terms, (2) the odd ones.
  Builds on M111/H065 (one Taylor expansion, read off its coefficients); new here: two expansions that cancel.

REFERENCE
  `deriv f x` = f'(x);  `iteratedDeriv k f x` = k-th derivative;  `ContDiff ℝ k f`: f is k times continuously differentiable.
  -- Taylor with Lagrange remainder, degree 2 (needs hne : x ≠ x + h; `Set.uIcc a b` = [min a b, max a b]); n := 3 for (2):
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (x₀ := x) (x := x + h) hne hf.contDiffOn
  -- hξ : f (x + h) - taylorWithinEval f 2 (uIcc x (x + h)) x (x + h) = iteratedDeriv (2 + 1) f ξ * (x + h - x) ^ (2 + 1) / ↑(2 + 1).factorial
  #check taylorWithinEval_succ   -- degree n+1 = degree n + (coeff * (x - x₀)^(n+1)) • iteratedDerivWithin (n+1) f s x₀
  #check taylor_within_zero_eval -- taylorWithinEval f 0 s x₀ x = f x₀
  -- ORDER: first rewrite every coefficient `iteratedDerivWithin k f (uIcc ..) x` to `iteratedDeriv k f x` (k = 1:
  -- `deriv f x`), only then `norm_num [Nat.factorial] at hξ`; norm_num run first turns k = 1 into `derivWithin`.
  #check iteratedDerivWithin_eq_iteratedDeriv -- UniqueDiffOn ℝ s → ContDiffAt ℝ n f x → x ∈ s → (within s) = iteratedDeriv n f x
  example (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (x : ℝ) : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by norm_num)
  example (x y : ℝ) (h : x < y) : UniqueDiffOn ℝ (Set.uIcc x y) := by rw [Set.uIcc_of_le h.le]; exact uniqueDiffOn_Icc h
  #check iteratedDeriv_one   -- iteratedDeriv 1 f = deriv f;   also Set.uIcc_of_ge, Set.left_mem_uIcc : a ∈ uIcc a b
  #check abs_add_le          -- |a + b| ≤ |a| + |b|
NOTE: the two expansions only cancel after all `iteratedDerivWithin k f (uIcc x (x ± h)) x` become `iteratedDeriv k f x`.
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
H2. `taylor2`: Lagrange with `n := 2`, unfold `taylorWithinEval` twice with `taylorWithinEval_succ` and once with
    `taylor_within_zero_eval`, rewrite both `iteratedDerivWithin` coefficients (k = 1, 2) with
    `iteratedDerivWithin_eq_iteratedDeriv`, then `norm_num [Nat.factorial] at hξ; linear_combination hξ`.
    `taylor3`: the same with `n := 3`, three `taylorWithinEval_succ` and a third coefficient (k = 3).
H3. `central_error_eq`: `obtain ⟨ξ₂, h2⟩ := taylor2 f hf x (-h) (by linarith)`, `rw [← sub_eq_add_neg] at h2`,
    then `rw [h1, h2]; field_simp; ring`. Main: `rw [e, abs_mul, abs_of_pos (by positivity)]` and bound
    `|f'''(ξ₁) + f'''(ξ₂)| ≤ M + M` with `abs_add_le`. `second_diff_error_eq` and (2): same steps with `taylor3`.
-/
