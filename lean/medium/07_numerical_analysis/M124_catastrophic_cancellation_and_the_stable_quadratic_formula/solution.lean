/- M124 | Catastrophic cancellation and the stable quadratic formula | 15-20 min | relative error, condition number, Real.sqrt, let, field_simp, linear_combination, mathlib
GOAL
  (1) If `x` and `y` carry relative errors `δ₁, δ₂` with `|δᵢ| ≤ u`, their difference has relative error
  at most `u (|x| + |y|) / |x - y|`, and for `x > y > 0`, `δ₁ = u`, `δ₂ = -u` it equals that bound, which is
  unbounded as `x → y` (catastrophic cancellation).
  (2) For `b > 0`, compute `x₁ = (-b - √D) / (2a)`, `D = b² - 4ac` (no cancellation), then the other root
  as `c / (a x₁)`: prove `x₁` is a root and `c / (a x₁)` equals the textbook root `(-b + √D) / (2a)`.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M124

/- SKELETON · sub_rel_error
  1. (Optional) the denominator is positive, hpos : 0 < |x - y|:          R2 with R1 (`.mpr`)
     `gcongr` in step 2 proves the `0 ≤ |x - y|` it needs by itself.
  2. Drop the common denominator |x - y|:                                  R3
  3. Rewrite the numerator to x * δ₁ - y * δ₂:                             R4
  4. Bound it by a chain  |x * δ₁ - y * δ₂| ≤ … ≤ u * (|x| + |y|), one `calc` line per sub-step:  R5
       a. triangle inequality for a difference                            R6
       b. split the absolute values of the two products                   R7 (twice)
       c. replace |δ₁|, |δ₂| by u (uses h1, h2)                           R8
       d. rearrange                                                       ring
-/
-- BEGIN SPEC
theorem sub_rel_error (x y δ₁ δ₂ u : ℝ) (hxy : x ≠ y) (h1 : |δ₁| ≤ u) (h2 : |δ₂| ≤ u) :
    |(x * (1 + δ₁) - y * (1 + δ₂)) - (x - y)| / |x - y| ≤ u * (|x| + |y|) / |x - y| :=
-- END SPEC
  by
    have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    gcongr
    rw [show x * (1 + δ₁) - y * (1 + δ₂) - (x - y) = x * δ₁ - y * δ₂ by ring]
    calc |x * δ₁ - y * δ₂| ≤ |x * δ₁| + |y * δ₂| := abs_sub _ _
      _ = |x| * |δ₁| + |y| * |δ₂| := by rw [abs_mul, abs_mul]
      _ ≤ |x| * u + |y| * u := by gcongr
      _ = u * (|x| + |y|) := by ring

/- SKELETON · sub_rel_error_sharp
  1. A single `rw [ … ]` with four rewrites, in this order:
       a. the numerator is u * (x + y)                                    R4
       b. |u * (x + y)| = u * (x + y); its argument 0 ≤ u * (x + y)       R9, argument by R10 with R11
       c. |y| = y                                                         R12 (uses hy)
       d. |x| = x; its argument (… : 0 < x)                               R12, argument by R11
     Both sides are then identical and `rw` closes the goal by `rfl`.
-/
-- BEGIN SPEC
theorem sub_rel_error_sharp (x y u : ℝ) (hu : 0 ≤ u) (hy : 0 < y) (hxy : y < x) :
    |(x * (1 + u) - y * (1 - u)) - (x - y)| / |x - y| = u * (|x| + |y|) / |x - y| :=
-- END SPEC
  by
    -- WHY: the two errors push in opposite directions, so the triangle inequality is an equality
    rw [show x * (1 + u) - y * (1 - u) - (x - y) = u * (x + y) by ring,
      abs_of_nonneg (mul_nonneg hu (by linarith)), abs_of_pos hy, abs_of_pos (by linarith : 0 < x)]

/- SKELETON · stable_quadratic        (D stands for b ^ 2 - 4 * a * c)
  1. Enter the `let`:                                                      R13
  2. Record hs : √D ^ 2 = D and hsn : 0 ≤ √D:                              R14, R15
  3. Unfold x₁ in the goal:                                                R16
  4. Replace √D by a fresh s in hs, hsn and the goal:                      R17
  5. Prove hne : -b - s ≠ 0 (from hb, hsn), so field_simp can divide:      R11
  6. Split the ∧:                                                          constructor
  7. In each half: clear denominators, then use hs with the right
     coefficient (read it off the goal field_simp leaves):                R18 → R19
-/
-- BEGIN SPEC
theorem stable_quadratic (a b c : ℝ) (ha : a ≠ 0) (hb : 0 < b) (hD : 0 ≤ b ^ 2 - 4 * a * c) :
    let x₁ := (-b - √(b ^ 2 - 4 * a * c)) / (2 * a)
    a * x₁ ^ 2 + b * x₁ + c = 0 ∧ (-b + √(b ^ 2 - 4 * a * c)) / (2 * a) = c / (a * x₁) :=
-- END SPEC
  by
    intro x₁
    have hs := Real.sq_sqrt hD
    have hsn := Real.sqrt_nonneg (b ^ 2 - 4 * a * c)
    simp only [x₁]
    -- WHY: `field_simp` would also rewrite inside `√(…)`; hide the root behind a variable
    generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢
    have hne : -b - s ≠ 0 := by linarith
    constructor
    · field_simp
      linear_combination hs
    · field_simp
      linear_combination (-1 : ℝ) * hs

end M124

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) In both statements the two sides divide by the same `|x - y|`, so only the numerators matter, and
    the numerator simplifies by `ring`. In the sharp case every `|·|` has a known sign. (2) All Lean knows
    about `√D` is `√D ^ 2 = D` and `0 ≤ √D`: record those, then treat `√D` as an unknown `s`.
H2. (1) `gcongr` drops the denominator; `rw [show … = x * δ₁ - y * δ₂ by ring]`; then a `calc`: `abs_sub`,
    `abs_mul`, `gcongr`, `ring`. Sharp: rewrite the numerator to `u * (x + y)`, then `abs_of_nonneg`,
    `abs_of_pos` (twice); `rw` closes the goal. (2) `intro x₁`, `have` the two `√` facts, `simp only [x₁]`,
    `generalize`, `hne : -b - s ≠ 0` by `linarith`, `constructor`, and in each half `field_simp` then
    `linear_combination`.
H3. (1) `calc |x * δ₁ - y * δ₂| ≤ |x * δ₁| + |y * δ₂| := abs_sub _ _`, then the steps
    `_ = |x| * |δ₁| + |y| * |δ₂|`, `_ ≤ |x| * u + |y| * u`, `_ = u * (|x| + |y|)`.
    Sharp: `rw [show … = u * (x + y) by ring, abs_of_nonneg (mul_nonneg hu …), abs_of_pos hy, abs_of_pos …]`.
    (2) `generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢`; after `field_simp`, the first half closes with
    `linear_combination hs` and the second with `linear_combination (-1 : ℝ) * hs`.
-/
