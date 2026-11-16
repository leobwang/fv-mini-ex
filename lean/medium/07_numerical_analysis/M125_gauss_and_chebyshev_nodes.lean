/- M125 | Gauss and Chebyshev nodes | 15-20 min | intervalIntegral, method of moments, linear_combination, Chebyshev polynomials, trig, mathlib
GOAL
  (1) Any two-point rule `w₁ f(x₁) + w₂ f(x₂)` that integrates `1, x, x², x³` exactly on `[-1, 1]` is forced to be
  Gauss–Legendre: `x₁ + x₂ = 0`, `x₁ x₂ = -1/3` (nodes `±1/√3`, the roots of `3x² - 1`) and `w₁ = w₂ = 1`;
  (2) that rule is not exact for `x⁴`, so 3 is its exact degree; (3) the Chebyshev nodes
  `cos((2k+1)π/(2n))`, `k < n`, are roots of the Chebyshev polynomial `Tₙ` (`Tₙ(cos θ) = cos(nθ)`).

REFERENCE
  example : ∫ x in (-1:ℝ)..1, x ^ 2 = 2 / 3 := by norm_num [integral_pow]   -- `∫ x in a..b, f x` over [a, b]
  #check integral_pow   -- ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1)
  example (w x : ℝ) (h : ∀ k ≤ 3, w * x ^ k = 0) : w * x ^ 2 = 0 := h 2 (by norm_num)  -- specialize a `∀ k ≤ 3`
  example (a b : ℝ) (h₁ : a + b = 2) (h₂ : a - b = 0) : a = 1 := by linear_combination (h₁ + h₂) / 2
  --   ^ `linear_combination e` closes `lhs = rhs` when `lhs - rhs - (e.lhs - e.rhs)` is 0 by `ring`; `e` may mix `hᵢ` with polynomial coefficients
  #check mul_eq_zero    -- a * b = 0 ↔ a = 0 ∨ b = 0      (and `sub_eq_zero : a - b = 0 ↔ a = b`)
  #check Real.sq_sqrt   -- 0 ≤ x → √x ^ 2 = x
  #check Polynomial.Chebyshev.T_real_cos   -- (T ℝ n).eval (cos θ) = cos (n * θ)    (n : ℤ)
  #check Real.cos_eq_zero_iff              -- cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2
  `p.eval x` evaluates the polynomial `p` at `x`.
NOTE: `Polynomial.Chebyshev.T` is indexed by `ℤ`, so `T ℝ n` with `n : ℕ` carries a cast; `push_cast` tidies casts.
-/
import Mathlib

namespace M125

-- BEGIN SPEC
theorem gauss_nodes_forced (w₁ w₂ x₁ x₂ : ℝ)
    (hexact : ∀ k ≤ 3, w₁ * x₁ ^ k + w₂ * x₂ ^ k = ∫ x in (-1:ℝ)..1, x ^ k) :
    x₁ + x₂ = 0 ∧ x₁ * x₂ = -1 / 3 ∧ w₁ = 1 ∧ w₂ = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem gauss_not_exact_quartic :
    ∫ x in (-1:ℝ)..1, x ^ 4 ≠ (-1 / √3) ^ 4 + (1 / √3) ^ 4 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem chebyshev_node_root (n k : ℕ) (hk : k < n) :
    (Polynomial.Chebyshev.T ℝ n).eval (Real.cos ((2 * k + 1) * Real.pi / (2 * n))) = 0 :=
-- END SPEC
  sorry

end M125

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) Get the four moment equations `h0`–`h3` (`hexact k (by norm_num)`, then `norm_num [integral_pow] at …`); the right sides are `2, 0, 2/3, 0`. With `s = x₁ + x₂`, `P = x₁ x₂`, the polynomial `x² - s x + P` vanishes at both nodes. (3) Turn `T` at `cos θ` into `cos (n θ)` and use where cosine vanishes.
H2. (1) Weight that vanishing: `Σ wᵢ (xᵢ² - s xᵢ + P) = 0` reads `h2 - s·h1 + P·h0`, i.e. `2/3 + 2P = 0`; `Σ wᵢ xᵢ (xᵢ² - s xᵢ + P) = 0` reads `h3 - s·h2 + P·h1`, i.e. `-(2/3) s = 0`. Then `x₁ ≠ 0` (else `P = 0`) and `h1` give `w₁ = w₂`. (2) Both node powers equal `1 / (√3 ^ 2) ^ 2`. (3) The witness integer is `k`; you need `(n : ℝ) ≠ 0`.
H3. (1) `linear_combination (-1 / 2 : ℝ) * (h2 - (x₁ + x₂) * h1 + (x₁ * x₂) * h0)` proves `x₁ * x₂ = -1 / 3`; `(3 / 2 : ℝ) * (h3 - …)` likewise proves `x₁ + x₂ = 0`; for the weights, `(w₁ - w₂) * x₁ = 0` is `linear_combination h1 - w₂ * hs`. (2) `rw [integral_pow, show (1 / √3) ^ 4 = 1 / (√3 ^ 2) ^ 2 by ring, …, Real.sq_sqrt …]; norm_num`. (3) `rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]; refine ⟨k, ?_⟩; push_cast; field_simp`.
-/
