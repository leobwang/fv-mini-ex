/- M111 | Forward difference via Taylor | 15-20 min | taylor_mean_remainder_lagrange, iteratedDeriv, ContDiff, mathlib
GOAL
  If `|f''| ≤ M` everywhere, the forward difference `(f(x+h) - f(x))/h` approximates `f'(x)` within
  `M h / 2`. Use Mathlib's Taylor theorem (Lagrange remainder) and read off its coefficients.

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M111

/- SKELETON · taylor_one   (milestone; prove it FIRST; forward_difference_error uses it in step 1)
  1. Taylor's theorem of degree 1 at `x`, evaluated at `x + h`, into the context:         R1 with R2
       arguments: `x ≠ x + h` by R4, and `hf.contDiffOn` (R3)
       hξ : f (x + h) - taylorWithinEval f 1 (Set.uIcc x (x + h)) x (x + h)
              = iteratedDeriv (1 + 1) f ξ * (x + h - x) ^ (1 + 1) / ↑(1 + 1).factorial
  2. Use that `ξ`:                                                                        refine ⟨ξ, ?_⟩
  3. Prove the coefficient fact first:                                                    have
       hd : iteratedDerivWithin 1 f (Set.uIcc x (x + h)) x = deriv f x
     proof: R5 → R6 (side goal by R4), then close with R8 applied to R7 (at `x`),
            its uniqueness argument by R9, the membership `x ∈ Set.Icc x (x + h)` by R10, R4
  4. Unfold the degree-1 polynomial in `hξ`:                                              R11 → R12 → rw [hd] at hξ
  5. Clean the numerals; `hξ` is now the goal:                                            R13, exact hξ
-/
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

/- SKELETON · forward_difference_error
  0. Prove the milestone taylor_one first (used in step 1).
  1. Get `ξ` and `hξ` from the milestone:                                                 R1 (no `-`)
  2. Prove the exact error first:                                                         have
       e : (f (x + h) - f x) / h - deriv f x = iteratedDeriv 2 f ξ * h / 2
     proof: R14, then R15 with `hξ` (read the coefficient off the goal R14 leaves)
  3. rw [e], then split the absolute value:                                               R16, R17, R18 (with hh), R19
  4. Strip the common factors `* h / 2`, then use the bound at `ξ`:                       R20, exact hM ξ
-/
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
H1. Prove the milestone `taylor_one` first: it is Taylor's theorem (R2) with the degree-1 polynomial
    read off as `f x + h * deriv f x`. Then the error of the difference quotient is EXACTLY
    `iteratedDeriv 2 f ξ * h / 2`, and only the bound `hM ξ` remains.
H2. Milestone: `obtain` the remainder from R2 at `(n := 1) (x₀ := x) (x := x + h)`, unfold the polynomial
    in `hξ` with R11 and R12, and replace its one coefficient (a derivative within `Set.uIcc x (x + h)`)
    by `deriv f x` with a fact `hd` (R5, R6, R7–R10). Main theorem: `field_simp` clears the `/ h`,
    `linear_combination` uses `hξ`, then absolute-value rewrites and `gcongr`.
H3. Milestone, key line: `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
      (x₀ := x) (x := x + h) (by linarith) hf.contDiffOn`.
    `hd` ends with `(hf.differentiable (by norm_num) x).derivWithin (uniqueDiffOn_Icc _ x _)`.
    Main, key line: `e` closes by `field_simp` then `linear_combination 2 * hξ`. After `rw [e]` and the
    absolute-value rewrites R16–R19, `gcongr` leaves exactly `|iteratedDeriv 2 f ξ| ≤ M`.
-/
