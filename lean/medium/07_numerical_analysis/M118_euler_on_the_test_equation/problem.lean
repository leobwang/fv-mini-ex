/- M118 | Euler's method on y' = λy | 15-20 min | recursion, closed form, exp bounds, stability, Tendsto atTop, mathlib
GOAL
  Forward Euler `yₙ₊₁ = yₙ + h·(λ yₙ)` on the test equation `y' = λy` gives `yₙ = (1 + hλ)ⁿ y₀`. For λ ≥ 0 it
  underestimates the exact solution `e^(λ·nh) y₀`. For λ ≤ 0 it is stable (`|yₙ| ≤ |y₀|`) if `h|λ| ≤ 2`, and if
  `h|λ| > 2` every nonzero start blows up (`|yₙ| → ∞`), so the step-size restriction is sharp.

REFERENCE
  #check Real.add_one_le_exp      -- x + 1 ≤ exp x
  #check Real.exp_nat_mul         -- exp (n * x) = exp x ^ n
  #check abs_le                   -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  #check abs_of_neg               -- a < 0 → |a| = -a       (also `abs_mul`, `abs_pow`, `abs_pos : 0 < |a| ↔ a ≠ 0`)
  #check tendsto_pow_atTop_atTop_of_one_lt  -- 1 < r → Tendsto (fun n => r ^ n) atTop atTop
  #check Filter.Tendsto.atTop_mul_const     -- 0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop
  example (a b : ℝ) (n : ℕ) (h0 : 0 ≤ a) (h : a ≤ b) : a ^ n ≤ b ^ n := by gcongr
  `Tendsto u atTop atTop` means `u n → ∞` as `n → ∞`. `lam` stands for λ (`λ` is reserved syntax in Lean).
BANNED: try?
NOTE: `try?` is banned because it closes the closed-form warm-up; prove that one by induction on `n`.
-/
import Mathlib

open Filter

namespace M118

-- BEGIN SPEC
def euler (lam h y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => euler lam h y₀ n + h * (lam * euler lam h y₀ n)
-- END SPEC

-- BEGIN SPEC
theorem euler_closed_form (lam h y₀ : ℝ) (n : ℕ) : euler lam h y₀ n = (1 + h * lam) ^ n * y₀ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem euler_le_exact (lam h y₀ : ℝ) (hl : 0 ≤ lam) (hh : 0 ≤ h) (hy : 0 ≤ y₀) (n : ℕ) :
    euler lam h y₀ n ≤ Real.exp (lam * (n * h)) * y₀ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem euler_stable (lam h y₀ : ℝ) (hl : lam ≤ 0) (hh : 0 ≤ h) (hstab : h * (-lam) ≤ 2) (n : ℕ) :
    |euler lam h y₀ n| ≤ |y₀| :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem euler_unstable (lam h y₀ : ℝ) (hstab : 2 < h * (-lam)) (hy : y₀ ≠ 0) :
    Tendsto (fun n => |euler lam h y₀ n|) atTop atTop :=
-- END SPEC
  sorry

end M118

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the closed form first (induction on n) and rewrite every other goal with it. Everything then
    is a statement about the amplification factor `1 + hλ`.
H2. Exact: `1 + hλ ≤ e^(hλ)`, raise to the n-th power, and `(e^(hλ))ⁿ = e^(n·hλ)`. Stable: `|1 + hλ| ≤ 1`
    from `abs_le` (two linear facts). Unstable: `2 < h(-λ)` forces `1 + hλ < -1`, so `1 < |1 + hλ|`.
H3. Closed form step: `rw [euler, ih, pow_succ]; ring`. Exact: `rw [euler_closed_form]; gcongr`, then
    `calc (1 + h * lam) ^ n ≤ Real.exp (h * lam) ^ n := by gcongr; linarith [Real.add_one_le_exp (h * lam)]`.
    Unstable: `simp_rw [euler_closed_form, abs_mul, abs_pow]` and
    `exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (abs_pos.mpr hy)`.
-/
