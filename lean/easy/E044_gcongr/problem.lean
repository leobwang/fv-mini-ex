/- E044 | gcongr | 2 min | gcongr, monotonicity, mathlib
GOAL
  Prove inequalities between expressions with the same shape using `gcongr`.

REFERENCE
  example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by gcongr      -- matches shapes, uses h
  example (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by gcongr  -- needs 0 ≤ a
  example (x y : ℝ) (hx : 0 < x) (h : x < y) : 1 / y < 1 / x := by gcongr  -- antitone spots too
  `gcongr` reduces `f a ≤ f b` to `a ≤ b` for the differing parts; side goals (positivity)
  are closed from hypotheses or `positivity`; leftover goals remain for you.
-/
import Mathlib

-- BEGIN SPEC
theorem add_mono_sq (a b c : ℝ) (h : a ≤ b) (ha : 0 ≤ a) : a ^ 2 + c ≤ b ^ 2 + c :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem cube_mono (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 3 ≤ y ^ 3 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mul_mono_nat (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a * c + 5 ≤ b * d + 5 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem recip_anti (x y : ℝ) (hx : 0 < x) (h : x < y) : 3 / y < 3 / x :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides of every goal have the same shape and differ in one or two places.
H2. `gcongr` finds the differing places and asks for exactly the hypotheses you have.
H3. Each proof is `gcongr`.
-/
