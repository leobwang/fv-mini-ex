/- M123 | Backward Euler is A-stable | 15-20 min | implicit methods, field_simp, geometric sequences, Tendsto, mathlib
GOAL
  Backward (implicit) Euler for y' = λy defines yₙ₊₁ by `yₙ₊₁ = yₙ + hλyₙ₊₁`, solved as `yₙ₊₁ = yₙ / (1 - hλ)`.
  Show it solves the implicit equation, never grows when λ ≤ 0 for *every* step h ≥ 0 (A-stability: no
  step-size limit, unlike explicit Euler's `h|λ| ≤ 2`), and decays to 0 when λ < 0.

REFERENCE
  example (a b : ℝ) (hb : b ≠ 0) : a / b * b = a := by field_simp   -- clears denominators known to be ≠ 0
  #check abs_inv            -- |a⁻¹| = |a|⁻¹      (also `abs_mul`, `abs_pow`, `abs_of_pos`)
  #check inv_le_one_of_one_le₀  -- 1 ≤ a → a⁻¹ ≤ 1   (and `inv_lt_one_of_one_lt₀`)
  #check pow_le_one₀        -- 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  #check Filter.Tendsto.mul_const  -- Tendsto f l (𝓝 a) → Tendsto (fun x => f x * b) l (𝓝 (a * b))
  #check Filter.Tendsto.congr      -- (∀ x, f₁ x = f₂ x) → Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂
  `Tendsto u atTop (𝓝 L)` means `u n → L` as `n → ∞` (`open Filter Topology` provides `atTop` and `𝓝`).
BANNED: grind, try?
NOTE: `lam` is λ (`λ` is reserved); `noncomputable` as real division is not computable; `grind [beuler]` would skip `field_simp`.
-/
import Mathlib
open Filter Topology

namespace M123

-- BEGIN SPEC
/-- backward Euler for y' = λy, with the implicit equation already solved for yₙ₊₁ -/
noncomputable def beuler (lam h y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => beuler lam h y₀ n / (1 - h * lam)
-- END SPEC

-- BEGIN SPEC
theorem beuler_implicit (lam h y₀ : ℝ) (hne : 1 - h * lam ≠ 0) (n : ℕ) :
    beuler lam h y₀ (n + 1) = beuler lam h y₀ n + h * (lam * beuler lam h y₀ (n + 1)) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem beuler_stable (lam h y₀ : ℝ) (hl : lam ≤ 0) (hh : 0 ≤ h) (n : ℕ) :
    |beuler lam h y₀ n| ≤ |y₀| :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem beuler_tendsto_zero (lam h y₀ : ℝ) (hl : lam < 0) (hh : 0 < h) :
    Tendsto (beuler lam h y₀) atTop (𝓝 0) :=
-- END SPEC
  sorry

end M123

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything is easier with a closed form: the iterates are a geometric sequence with ratio `r = (1 - hλ)⁻¹`.
H2. Prove a helper `beuler lam h y₀ n = (1 - h * lam)⁻¹ ^ n * y₀` by induction. For λ ≤ 0, h ≥ 0 we have `1 ≤ 1 - hλ`, so `0 ≤ r ≤ 1`; for λ < 0, h > 0, `r < 1`.
H3. Implicit: `simp only [beuler]; field_simp; ring`. Stable: `rw [closed, abs_mul, abs_pow]` and bound `|r| ≤ 1` via `abs_inv`, `abs_of_pos`, `inv_le_one_of_one_le₀`. Limit: `(tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const y₀`, then `zero_mul` and `.congr` with the closed form.
-/
