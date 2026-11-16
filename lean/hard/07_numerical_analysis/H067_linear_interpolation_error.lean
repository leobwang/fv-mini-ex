/- H067 | Linear interpolation error | 1-1.5 h | Rolle's theorem, auxiliary function, HasDerivAt, mathlib
GOAL
  The chord through `(a, f a)` and `(b, f b)` misses `f` at `x ∈ [a, b]` by at most `M/2 · (x - a)(b - x)` when
  `|f''| ≤ M` on `[a, b]`. Classic proof: an auxiliary function with three zeros `a, x, b`, then Rolle three times.

REFERENCE
  `Set.Icc a b` = [a, b], `Set.Ioo a b` = (a, b);  `HasDerivAt g d t`: g is differentiable at t with derivative d.
  #check exists_hasDerivAt_eq_zero  -- (Rolle) a < b → ContinuousOn g (Icc a b) → g a = g b → (∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) → ∃ c ∈ Ioo a b, g' c = 0
  example (t a b : ℝ) : HasDerivAt (fun t => (t - a) * (t - b)) (2 * t - a - b) t :=
    (((hasDerivAt_id' t).sub_const a).mul ((hasDerivAt_id' t).sub_const b)).congr_deriv (by ring)
  -- also `hf.sub hg`, `hf.const_mul c`, `hf.const_add c`; `.congr_deriv (by ring)` fixes the derivative's shape
  example (g g' : ℝ → ℝ) (h : ∀ t, HasDerivAt g (g' t) t) : Continuous g := continuous_iff_continuousAt.mpr fun t => (h t).continuousAt
  #check Continuous.continuousOn   -- Continuous g → ContinuousOn g s
  #check div_mul_cancel₀           -- b ≠ 0 → a / b * b = a     (more predictable than `field_simp` on these goals)
  #check Set.Ioo_subset_Icc_self   -- Ioo a b ⊆ Icc a b
  set φ := fun t => f t - K * t   -- tactic: names the auxiliary function in the goal; `simp only [φ]` unfolds it
NOTE: Mathlib's Rolle is allowed here (H049 proves it from scratch); the point is the auxiliary-function argument.
-/
import Mathlib

open Set

namespace H067

-- MILESTONE (optional: change or delete)
-- The auxiliary function `φ t = (f t - chord t) - K (t - a)(t - b)` and its derivative.
theorem aux_deriv (f f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t) (a b s K t : ℝ) :
    HasDerivAt (fun t => f t - (f a + s * (t - a)) - K * ((t - a) * (t - b)))
      (f' t - s - K * (2 * t - a - b)) t := by
  sorry

-- MILESTONE (optional: change or delete)
-- The exact error at an interior point (the Cauchy remainder for linear interpolation).
theorem interp_error_eq (f f' f'' : ℝ → ℝ) (a b x : ℝ) (hax : a < x) (hxb : x < b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t) :
    ∃ η ∈ Ioo a b, f x - (f a + (f b - f a) / (b - a) * (x - a)) = f'' η / 2 * ((x - a) * (x - b)) := by
  sorry

-- BEGIN SPEC
theorem linear_interp_error (f f' f'' : ℝ → ℝ) (a b x M : ℝ) (hx : x ∈ Icc a b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |f x - (f a + (f b - f a) / (b - a) * (x - a))| ≤ M / 2 * ((x - a) * (b - x)) :=
-- END SPEC
  sorry

end H067

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Endpoints first: at `x = a` and `x = b` both sides are 0. For `a < x < b`, let `g t = f t - chord t` and choose
    the constant `K = g x / ((x - a)(x - b))` so that `φ t = g t - K (t - a)(t - b)` vanishes at `a`, `x` and `b`.
H2. Rolle on `[a, x]` and `[x, b]` gives `ξ₁ < ξ₂` with `φ'(ξᵢ) = 0`; Rolle on `φ'` over `[ξ₁, ξ₂]` gives `η` with
    `φ''(η) = f''(η) - 2K = 0`. So `g x = K (x - a)(x - b) = f''(η)/2 · (x - a)(x - b)`; bound `|f''(η)| ≤ M`.
H3. `φ' t = f' t - s - K * (2 * t - a - b)` and `HasDerivAt φ' (f'' t - 2 * K) t`. Zeros: `φ a = 0` by `simp`,
    `φ b = 0` from `s * (b - a) = f b - f a` (`div_mul_cancel₀`), `φ x = 0` by `div_mul_cancel₀ _ hden; ring`. Final
    bound: rewrite `(x - a) * (x - b) = -((x - a) * (b - x))`, then `abs_mul, abs_div, abs_neg, abs_of_nonneg`.
-/
