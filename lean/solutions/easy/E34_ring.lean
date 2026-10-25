/- E34 | ring | 1-2 min | ring, mathlib
GOAL
  Prove polynomial identities in commutative (semi)rings with `ring`.

REFERENCE
  -- `import Mathlib` (top of file) brings ℕ ℤ ℚ ℝ and the Mathlib tactics
  example (a b : ℤ) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
  example (x : ℝ) (h : x = 2) : x ^ 2 + x = 6 := by rw [h]; ring   -- substitute, then ring
  example (a b : ℕ) (h : a = b + 1) : a * a = b * b + 2 * b + 1 := by subst h; ring
  `ring` proves equalities that hold by the commutative-ring axioms alone; it ignores hypotheses.
  Type ℝ as `\R`, ℕ as `\N`, ℤ as `\Z`, ℚ as `\Q`.
-/
import Mathlib

-- BEGIN SPEC
theorem square_sum (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
-- END SPEC
  by ring

-- BEGIN SPEC
theorem cube_succ (n : ℕ) : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 :=
-- END SPEC
  by ring

-- BEGIN SPEC
theorem with_hyp (a b c : ℚ) (h : a = b + c) : a ^ 2 - 2 * b * c = b ^ 2 + c ^ 2 :=
-- END SPEC
  by
    subst h
    ring

-- BEGIN SPEC
theorem four_squares (x y : ℝ) : (x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2) :=
-- END SPEC
  by ring

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three goals are pure identities; one needs the hypothesis first.
H2. `ring` does not use hypotheses: substitute with `subst h` or `rw [h]` before calling it.
H3. `by ring` three times, and `subst h; ring` for `with_hyp`.
-/
