/- M111 | Forward difference via Taylor | 15-20 min | taylor_mean_remainder_lagrange, iteratedDeriv, ContDiff, mathlib
GOAL
  If `|f''| ≤ M` everywhere, the forward difference `(f(x+h) - f(x))/h` approximates `f'(x)` within
  `M h / 2`. Use Mathlib's Taylor theorem (Lagrange remainder) and read off its coefficients.

REFERENCE
  `ContDiff ℝ 2 f`: f is twice continuously differentiable. `deriv f x` = f'(x); `iteratedDeriv 2 f y` = f''(y).
  `taylorWithinEval f n s x₀ x`: degree-n Taylor polynomial of f at x₀ evaluated at x, derivatives taken within s.
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (x₀ := x) (x := x + h) (by linarith) hf.contDiffOn
    -- hξ : f (x + h) - taylorWithinEval f 1 (Set.uIcc x (x + h)) x (x + h) = iteratedDeriv (1 + 1) f ξ * (x + h - x) ^ (1 + 1) / ↑(1 + 1).factorial
  #check taylorWithinEval_succ    -- degree n+1 = degree n + ((n+1) * n!)⁻¹ * (x - x₀)^(n+1) • iteratedDerivWithin (n+1) f s x₀
  #check taylor_within_zero_eval  -- taylorWithinEval f 0 s x₀ x = f x₀
  #check iteratedDerivWithin_one  -- iteratedDerivWithin 1 f s = derivWithin f s
  #check DifferentiableAt.derivWithin  -- DifferentiableAt ℝ f x → UniqueDiffWithinAt ℝ s x → derivWithin f s x = deriv f x
  #check uniqueDiffOn_Icc         -- a < b → UniqueDiffOn ℝ (Set.Icc a b)   (apply it to x and `x ∈ Icc a b`)
  #check Set.uIcc_of_le           -- a ≤ b → Set.uIcc a b = Set.Icc a b
  example (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ f := hf.differentiable (by norm_num)
-/
import Mathlib

namespace M111

-- MILESTONE (optional: change or delete)
-- Taylor with Lagrange remainder, degree 1
theorem taylor_one (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x h : ℝ) (hh : 0 < h) :
    ∃ ξ, f (x + h) - (f x + h * deriv f x) = iteratedDeriv 2 f ξ * h ^ 2 / 2 := by
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (x₀ := x) (x := x + h)
    (by linarith) hf.contDiffOn
  refine ⟨ξ, ?_⟩
  -- WHY: Taylor's coefficient is a derivative *within* `[x, x+h]`; at an endpoint it still equals
  -- `deriv f x` because `f` is differentiable at `x` and the interval is a non-degenerate segment.
  have hd : iteratedDerivWithin 1 f (Set.uIcc x (x + h)) x = deriv f x := by
    rw [iteratedDerivWithin_one, Set.uIcc_of_le (by linarith)]
    exact (hf.differentiable (by norm_num) x).derivWithin
      (uniqueDiffOn_Icc (by linarith) x ⟨le_rfl, by linarith⟩)
  rw [taylorWithinEval_succ, taylor_within_zero_eval, hd] at hξ
  norm_num at hξ
  exact hξ

-- BEGIN SPEC
theorem forward_difference_error (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M x h : ℝ) (hh : 0 < h)
    (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) :
    |(f (x + h) - f x) / h - deriv f x| ≤ M * h / 2 :=
-- END SPEC
  by
    obtain ⟨ξ, hξ⟩ := taylor_one f hf x h hh
    have e : (f (x + h) - f x) / h - deriv f x = iteratedDeriv 2 f ξ * h / 2 := by
      field_simp
      linear_combination 2 * hξ
    rw [e, abs_div, abs_mul, abs_of_pos hh, abs_two]
    gcongr
    exact hM ξ

end M111

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestone `taylor_one` first (it is Taylor's theorem with the coefficients read off).
    Then the difference quotient error is exactly `iteratedDeriv 2 f ξ * h / 2`.
H2. In the helper, unfold the degree-1 Taylor polynomial with `taylorWithinEval_succ` and
    `taylor_within_zero_eval`; its one coefficient needs
    `hd : iteratedDerivWithin 1 f (Set.uIcc x (x + h)) x = deriv f x`
    (`iteratedDerivWithin_one`, `Set.uIcc_of_le`, then `DifferentiableAt.derivWithin` with `uniqueDiffOn_Icc`).
H3. After `rw [taylorWithinEval_succ, taylor_within_zero_eval, hd] at hξ; norm_num at hξ`, `taylor_one` is `hξ`.
    Main: `have e : … = iteratedDeriv 2 f ξ * h / 2 := by field_simp; linear_combination 2 * hξ`, then
    `rw [e, abs_div, abs_mul, abs_of_pos hh, abs_two]; gcongr; exact hM ξ`.
-/
