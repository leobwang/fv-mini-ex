/- M109 | One Babylonian step | 10-15 min | Real.sqrt, field_simp, nlinarith, mathlib
GOAL
  Newton's method for `x² = a` is the Babylonian step `x ↦ (x + a/x)/2`. Show its error is exactly
  `(x - √a)² / (2x)` (quadratic in the old error), so one step lands at or above `√a`, and from
  there each step moves down (toward `√a`).
BANNED: grind, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M109

-- BEGIN SPEC
-- the Babylonian (Newton) step for √a
noncomputable def babylon (a x : ℝ) : ℝ := (x + a / x) / 2
-- END SPEC

/- SKELETON · babylon_error
  1. Replace `babylon a x` by its body:                                     R1
  2. Record the only fact about √a you need, `hs : √a ^ 2 = a`:             R2
  3. Clear the denominators `/ x`, `/ 2`, `/ (2 * x)` (uses `hx`):          R3
  4. The goal is now a polynomial identity in x, a, √a that holds
     once √a ^ 2 is read as a: close it with the hint `hs`:                 R4
-/
-- BEGIN SPEC
theorem babylon_error (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    babylon a x - √a = (x - √a) ^ 2 / (2 * x) :=
-- END SPEC
  sorry

/- SKELETON · sqrt_le_babylon
  1. Bring in Part 1 as a fact (no unfolding needed):
       he : babylon a x - √a = (x - √a) ^ 2 / (2 * x)      have he := babylon_error …
  2. The sign fact `0 ≤ (x - √a) ^ 2 / (2 * x)` as a `have`:                R5
  3. Combine he and the sign fact linearly:                                 R6
-/
-- BEGIN SPEC
theorem sqrt_le_babylon (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ babylon a x :=
-- END SPEC
  sorry

/- SKELETON · babylon_le
  1. Replace `babylon a x` by its body:                                     R1
  2. Prove first, as a `have`, the fact the goal is linear in:
       a / x ≤ x
     a. clear the positive denominator: goal becomes `a ≤ x * x`            R7
     b. close it with the hints `0 ≤ √a` and `√a ^ 2 = a` (plus hsx):       R8, R2 → R4
  3. Conclude `(x + a / x) / 2 ≤ x` from that fact:                         R6
-/
-- BEGIN SPEC
theorem babylon_le (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hsx : √a ≤ x) : babylon a x ≤ x :=
-- END SPEC
  sorry

end M109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Treat `√a` as an unknown `s ≥ 0` with `s ^ 2 = a`; then everything is rational-function algebra, and
    `a / x` is a single unknown wherever only linear reasoning is needed.
H2. Error identity: `unfold babylon`, add `√a ^ 2 = a`, `field_simp`, then a polynomial identity modulo that
    fact. Lower bound: Part 1 plus "a square over a positive number is ≥ 0" (`positivity`), then `linarith`.
    Monotone step: `babylon a x ≤ x` ⇐ `a / x ≤ x` ⇔ `a ≤ x * x`.
H3. Part 1: `have hs := Real.sq_sqrt ha`, then `field_simp`, then `nlinarith [hs]`.
    Part 3: `have : a / x ≤ x := by rw [div_le_iff₀ hx]; nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt ha]`.
-/
