/- E069 | Junk values | 2 min | division by zero, Real.sqrt, Real.log, total functions, mathlib
GOAL
  Mathlib's partial operations are total and return "junk" values (`x / 0 = 0`, `√(-4) = 0`, `log 0 = 0`),
  so honest lemmas such as `x / x = 1` carry side conditions. Find and use those lemmas.

REFERENCE
  #check div_zero                      -- a / 0 = 0
  #check div_self                      -- a ≠ 0 → a / a = 1
  #check Real.sqrt_eq_zero_of_nonpos   -- x ≤ 0 → √x = 0      (`Real.sqrt x` prints as `√x`)
  #check Real.log_zero                 -- Real.log 0 = 0      (`Real.log` is the natural log)
  #check zero_ne_one                   -- (0 : α) ≠ 1
  example (n : ℕ) : n / 0 = 0 := Nat.div_zero n   -- ℕ and ℤ also divide by zero to 0
  example (a : ℝ) (h : a * 1 = 2) : a = 2 := by rw [mul_one] at h; exact h   -- rewrite in a hypothesis
BANNED: simp, simp_all, norm_num, field_simp, grind, try?
NOTE: a side condition such as `(-4 : ℝ) ≤ 0` closes with `by linarith` (`norm_num` is banned here). `field_simp` is
  banned because it uses `hx` silently; the point is to see which lemma needs it.
-/
import Mathlib

namespace E069

-- BEGIN SPEC
theorem real_div_zero (x : ℝ) : x / 0 = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sqrt_neg : Real.sqrt (-4) = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem log_zero' : Real.log 0 = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem div_self' (x : ℝ) (hx : x ≠ 0) : x / x = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem not_div_self : ¬ ∀ x : ℝ, x / x = 1 :=
-- END SPEC
  sorry

end E069

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each of the first four is one library lemma from the REFERENCE; match its conclusion and supply any premise.
H2. `sqrt_neg` needs the premise `-4 ≤ 0`. `not_div_self`: assume the `∀`, use it at `x = 0`, and turn
    `0 / 0 = 1` into `0 = 1`.
H3. `Real.sqrt_eq_zero_of_nonpos (by linarith)`;
    `not_div_self`: `intro h; have h0 := h 0; rw [div_zero] at h0; exact zero_ne_one h0`.
-/
