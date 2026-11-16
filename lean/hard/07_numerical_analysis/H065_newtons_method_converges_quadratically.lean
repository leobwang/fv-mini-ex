/- H065 | Newton's method converges quadratically | 45-75 min | Taylor, iteration, quadratic convergence, mathlib
GOAL
  Newton's step is `newton f x = x - f x / f'(x)`. If `|f'| ≥ m > 0` and `|f''| ≤ M`, one step from `x` toward
  a root `r` gives `|newton f x - r| ≤ C|x - r|²` with `C = M/(2m)`; iterating, `C|xₙ - r| ≤ (Cδ)^(2ⁿ)` (digits double),
  where `xₙ = (newton f)^[n] x₀` is the n-th iterate and `δ` bounds the initial error, `|x₀ - r| ≤ δ`.

REFERENCE
  `deriv f x` = f'(x);  `iteratedDeriv 2 f t` = f''(t);  `ContDiff ℝ 2 f`: f is C²;  `g^[n] x` = g applied n times to x.
  -- Taylor with Lagrange remainder (hxy : x ≠ y; `Set.uIcc x y` = [min x y, max x y]):
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  -- hξ : f y - taylorWithinEval f 1 (uIcc x y) x y = iteratedDeriv (1 + 1) f ξ * (y - x) ^ (1 + 1) / ↑(1 + 1).factorial
  #check taylorWithinEval_succ   -- degree n+1 = degree n + (coeff * (x - x₀)^(n+1)) • iteratedDerivWithin (n+1) f s x₀
  #check taylor_within_zero_eval -- taylorWithinEval f 0 s x₀ x = f x₀       (`•` on ℝ is `*`)
  -- ORDER: first rewrite the coefficient `iteratedDerivWithin 1 f (uIcc x y) x` to `deriv f x` (via the two lemmas below),
  -- then `norm_num at hξ` tidies; norm_num run first would turn the coefficient into `derivWithin f (uIcc x y) x`.
  #check iteratedDerivWithin_eq_iteratedDeriv -- UniqueDiffOn ℝ s → ContDiffAt ℝ n f x → x ∈ s → (within s) = iteratedDeriv n f x
  example (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : ℝ) : ContDiffAt ℝ 1 f x := hf.contDiffAt.of_le (by norm_num)
  example (x y : ℝ) (h : x < y) : UniqueDiffOn ℝ (Set.uIcc x y) := by rw [Set.uIcc_of_le h.le]; exact uniqueDiffOn_Icc h
  #check iteratedDeriv_one        -- iteratedDeriv 1 f = deriv f;   also Set.left_mem_uIcc : a ∈ uIcc a b, Set.uIcc_of_ge
  #check Function.iterate_succ_apply'  -- f^[n.succ] x = f (f^[n] x)
  #check div_le_iff₀  -- 0 < c → (b / c ≤ a ↔ b ≤ a * c);   pow_mul : a ^ (m * n) = (a ^ m) ^ n
NOTE: the hypotheses are global (all t) for simplicity, not vacuous: f x = 2x + sin x has f' ≥ 1, |f''| ≤ 1, root 0.
-/
import Mathlib

open Set

namespace H065

-- BEGIN SPEC
noncomputable def newton (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x
-- END SPEC

-- MILESTONE (optional: change or delete)
-- First-order Taylor with Lagrange remainder, for `y` on either side of `x` (M111's step, generalised).
theorem taylor1 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x y : ℝ) :
    ∃ ξ, f y = f x + deriv f x * (y - x) + iteratedDeriv 2 f ξ / 2 * (y - x) ^ 2 := by
  sorry

-- MILESTONE (optional: change or delete)
-- The exact Newton error: expand `f` at `x`, evaluate at the root `r`, divide by `f'(x)`.
theorem newton_error_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x : ℝ) (hroot : f r = 0)
    (hd0 : deriv f x ≠ 0) :
    ∃ ξ, newton f x - r = iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 / deriv f x := by
  sorry

-- MILESTONE (optional: change or delete)
theorem bound_nonneg (g : ℝ → ℝ) (M : ℝ) (hM : ∀ t, |g t| ≤ M) : 0 ≤ M := by
  sorry

-- BEGIN SPEC
theorem newton_quadratic (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x m M : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : m ≤ |deriv f x|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M) :
    |newton f x - r| ≤ M / (2 * m) * |x - r| ^ 2 :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
-- Multiply the one-step bound by `C = M/(2m)`: the scaled error squares at each step.
theorem scaled_step (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r x m M : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : m ≤ |deriv f x|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M) :
    M / (2 * m) * |newton f x - r| ≤ (M / (2 * m) * |x - r|) ^ 2 := by
  sorry

-- BEGIN SPEC
theorem newton_converges (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (r m M δ x₀ : ℝ) (hm : 0 < m)
    (hroot : f r = 0) (hd : ∀ t, m ≤ |deriv f t|) (hM : ∀ t, |iteratedDeriv 2 f t| ≤ M)
    (hx₀ : |x₀ - r| ≤ δ) (n : ℕ) :
    M / (2 * m) * |(newton f)^[n] x₀ - r| ≤ (M / (2 * m) * δ) ^ (2 ^ n) :=
-- END SPEC
  sorry

end H065

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Expand `f` around the iterate `x` and evaluate at the root: `0 = f r = f x + f'(x)(r - x) + f''(ξ)/2·(r - x)²`.
    Dividing by `f'(x)` shows `newton f x - r = f''(ξ)/2·(r - x)²/f'(x)`; then `|f''(ξ)| ≤ M` and `|f'(x)| ≥ m`.
H2. `taylor1`: case `x = y` (take `ξ = x`, `simp`) versus `x ≠ y` (Lagrange with `n := 1`; unfold with
    `taylorWithinEval_succ, taylor_within_zero_eval`; turn `iteratedDerivWithin 1 f (uIcc x y) x` into `deriv f x`,
    which needs `UniqueDiffOn` on `uIcc x y`: split `x < y` / `y < x`). Convergence: induction on `n`, with
    `C eₙ₊₁ ≤ (C eₙ)² ≤ ((Cδ)^(2ⁿ))² = (Cδ)^(2ⁿ⁺¹)`.
H3. `newton_error_eq`: from `h0 : f x + deriv f x * (r - x) + iteratedDeriv 2 f ξ / 2 * (r - x) ^ 2 = 0`,
    `unfold newton; field_simp; linear_combination -2 * h0`. Main bound: `rw [e, abs_div, abs_mul, abs_div, abs_two,
    abs_pow, abs_sub_comm r x, div_le_iff₀ hdpos]`, then `M/2·e² = (M/(2m))·e²·m ≤ (M/(2m))·e²·|f'(x)|`.
    Induction step: `rw [Function.iterate_succ_apply', pow_succ, pow_mul]` and chain `scaled_step` with the IH.
-/
