/- M124 | Catastrophic cancellation and the stable quadratic formula | 15-20 min | relative error, condition number, Real.sqrt, let, field_simp, linear_combination, mathlib
GOAL
  (1) If `x` and `y` carry relative errors `δ₁, δ₂` with `|δᵢ| ≤ u`, their difference has relative error
  at most `u (|x| + |y|) / |x - y|`, and for `x > y > 0`, `δ₁ = u`, `δ₂ = -u` it equals that bound, which is
  unbounded as `x → y` (catastrophic cancellation).
  (2) For `b > 0`, compute `x₁ = (-b - √D) / (2a)`, `D = b² - 4ac` (no cancellation), then the other root
  as `c / (a x₁)`: prove `x₁` is a root and `c / (a x₁)` equals the textbook root `(-b + √D) / (2a)`.

REFERENCE
  #check abs_sub        -- |a - b| ≤ |a| + |b|       (at this Mathlib version)
  #check abs_mul        -- |a * b| = |a| * |b|
  #check abs_pos        -- 0 < |a| ↔ a ≠ 0           (with `sub_ne_zero : a - b ≠ 0 ↔ a ≠ b`)
  #check abs_of_nonneg  -- 0 ≤ a → |a| = a           (and `abs_of_pos : 0 < a → |a| = a`)
  #check Real.sq_sqrt   -- 0 ≤ x → √x ^ 2 = x        (and `Real.sqrt_nonneg x : 0 ≤ √x`)
  example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by gcongr
  `intro x₁` enters the `let`; `simp only [x₁]` unfolds it.
  `generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢` -- replace the root by a fresh `s` everywhere; with
  `hs : √D ^ 2 = D` and `hsn : 0 ≤ √D` in context first, you keep `s ^ 2 = D` and `0 ≤ s`
  `field_simp` clears denominators it can prove ≠ 0 (give it `hne : … ≠ 0` in context); then
  `linear_combination k * hs` uses `s ^ 2 = b ^ 2 - 4 * a * c`.
NOTE: `field_simp` also rewrites inside `√(…)`, so generalize the square root away first.
-/
import Mathlib

namespace M124

-- BEGIN SPEC
theorem sub_rel_error (x y δ₁ δ₂ u : ℝ) (hxy : x ≠ y) (h1 : |δ₁| ≤ u) (h2 : |δ₂| ≤ u) :
    |(x * (1 + δ₁) - y * (1 + δ₂)) - (x - y)| / |x - y| ≤ u * (|x| + |y|) / |x - y| :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sub_rel_error_sharp (x y u : ℝ) (hu : 0 ≤ u) (hy : 0 < y) (hxy : y < x) :
    |(x * (1 + u) - y * (1 - u)) - (x - y)| / |x - y| = u * (|x| + |y|) / |x - y| :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem stable_quadratic (a b c : ℝ) (ha : a ≠ 0) (hb : 0 < b) (hD : 0 ≤ b ^ 2 - 4 * a * c) :
    let x₁ := (-b - √(b ^ 2 - 4 * a * c)) / (2 * a)
    a * x₁ ^ 2 + b * x₁ + c = 0 ∧ (-b + √(b ^ 2 - 4 * a * c)) / (2 * a) = c / (a * x₁) :=
-- END SPEC
  sorry

end M124

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) Both sides share the denominator `|x - y| > 0`, so compare numerators; for the sharp case, the numerator is `u (x + y)` and every `|·|` has a known sign. (2) Name `s = √D`; all you know is `s² = D` and `s ≥ 0`.
H2. (1) The numerator is `x δ₁ - y δ₂` (by `ring`); bound it with `abs_sub`, `abs_mul`, `gcongr`. (2) `-b - s ≠ 0` because `b > 0` and `s ≥ 0`, which makes `x₁ ≠ 0`; each conjunct is then "clear denominators, use `s² = D`".
H3. (1) Sharp: `rw [show … = u * (x + y) by ring, abs_of_nonneg …, abs_of_pos hy, abs_of_pos …]`. Bound: after `gcongr`: `calc |x * δ₁ - y * δ₂| ≤ |x * δ₁| + |y * δ₂| := abs_sub _ _` … (2) `intro x₁; simp only [x₁]; generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢`, `have hne : -b - s ≠ 0 := by linarith`, then `constructor <;> field_simp` and `linear_combination (±1) * hs`.
-/
