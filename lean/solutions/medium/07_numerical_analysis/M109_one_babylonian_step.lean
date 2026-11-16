/- M109 | One Babylonian step | 10-15 min | Real.sqrt, field_simp, nlinarith, mathlib
GOAL
  Newton's method for `x² = a` is the Babylonian step `x ↦ (x + a/x)/2`. Show its error is exactly
  `(x - √a)² / (2x)` (quadratic in the old error), so one step lands at or above `√a`, and from
  there each step moves down (toward `√a`).

REFERENCE
  `√a` is `Real.sqrt a`; for `a < 0` it is `0`, so facts about it need `0 ≤ a`.
  #check Real.sq_sqrt      -- 0 ≤ a → √a ^ 2 = a
  #check Real.sqrt_nonneg  -- (a : ℝ) : 0 ≤ √a
  #check div_le_iff₀       -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)
  example (x y : ℝ) (hx : 0 < x) : y / x * x = y := by field_simp   -- clears denominators known ≠ 0
  example (x s : ℝ) (hx : 0 < x) : 0 ≤ (x - s) ^ 2 / (2 * x) := by positivity
  `nlinarith [h₁, h₂]` = `linarith` that also multiplies pairs of the hints/hypotheses (for products).
  `unfold babylon` (or `simp only [babylon]`) replaces `babylon a x` by its definition.
BANNED: grind, try?
NOTE: `grind` (via `try?`) closes the error identity once `babylon` is unfolded; do the algebra yourself.
-/
import Mathlib

namespace M109

-- BEGIN SPEC
-- the Babylonian (Newton) step for √a
noncomputable def babylon (a x : ℝ) : ℝ := (x + a / x) / 2
-- END SPEC

-- BEGIN SPEC
theorem babylon_error (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    babylon a x - √a = (x - √a) ^ 2 / (2 * x) :=
-- END SPEC
  by
    unfold babylon
    have hs := Real.sq_sqrt ha
    field_simp
    nlinarith [hs]

-- BEGIN SPEC
theorem sqrt_le_babylon (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ babylon a x :=
-- END SPEC
  by
    have he := babylon_error a x ha hx
    have : 0 ≤ (x - √a) ^ 2 / (2 * x) := by positivity
    linarith

-- BEGIN SPEC
theorem babylon_le (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hsx : √a ≤ x) : babylon a x ≤ x :=
-- END SPEC
  by
    unfold babylon
    have : a / x ≤ x := by
      rw [div_le_iff₀ hx]
      nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt ha]
    linarith

end M109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Treat `√a` as a number `s ≥ 0` with `s ^ 2 = a`; then everything is rational-function algebra.
H2. Error identity: clear the denominators and use `s ^ 2 = a`. Lower bound: the error identity plus
    "a square over a positive number is ≥ 0". Monotone step: `babylon a x ≤ x` ⇔ `a / x ≤ x` ⇔ `a ≤ x * x`.
H3. With `s := √a` and `hs : s ^ 2 = a` (`Real.sq_sqrt ha`): after unfolding and clearing denominators, the
    identity is a polynomial identity modulo `hs`. For the step: `a / x ≤ x ↔ a ≤ x * x` is `div_le_iff₀ hx`.
-/
