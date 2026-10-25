/- E37 | positivity | 1-2 min | positivity, mathlib
GOAL
  Prove goals of the form `0 < e` or `0 ≤ e` by the syntactic structure of `e`.

REFERENCE
  example (x : ℝ) : 0 ≤ x ^ 2 + |x| := by positivity      -- squares, abs, sums, products
  example (x : ℝ) : 0 < Real.exp x := by positivity        -- knows exp, sqrt, norms, ...
  example (a : ℝ) (ha : 0 < a) : 0 < a / (a + 1) := by positivity   -- uses `0 < a` atoms from context
  `positivity` only proves `0 < e`, `0 ≤ e`, `e ≠ 0`; it does not do arithmetic like `x > y`.
-/
import Mathlib

-- BEGIN SPEC
theorem sq_add_one_pos (x : ℝ) : 0 < x ^ 2 + 1 :=
-- END SPEC
  by positivity

-- BEGIN SPEC
theorem prod_pos (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a * (b + 1) :=
-- END SPEC
  by positivity

-- BEGIN SPEC
theorem exp_abs_pos (x : ℝ) : 0 < Real.exp x + |x| :=
-- END SPEC
  by positivity

-- BEGIN SPEC
theorem nat_pow_pos (n : ℕ) : 0 < 2 ^ n + n :=
-- END SPEC
  by positivity

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal is `0 < (expression built from positive pieces)`.
H2. `positivity` walks the expression tree, using hypotheses `0 < a` / `0 ≤ b` for atoms.
H3. Each proof is `positivity`.
-/
