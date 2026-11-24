/- E068 | nlinarith with hints | 2-3 min | nlinarith, product hints, sq_nonneg, mathlib
GOAL
  Prove polynomial inequalities with `nlinarith`, supplying the squares or products it needs as hints.
BANNED: gcongr, pow_lt_pow_left₀, pow_le_pow_iff_left₀, le_of_sq_le_sq, abs_le_of_sq_le_sq, abs_le_of_sq_le_sq', grind, polyrith, exact?, apply?, try?

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E068

/- SKELETON · nl_sq
  1. No hint: the negated goal `b < a` times `hb` and times itself already gives
     the certificate, so the plain tactic closes it (it runs R1 at the end).    R2
-/
-- BEGIN SPEC
theorem nl_sq (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
-- END SPEC
  by nlinarith

/- SKELETON · nl_sym
  1. On paper: factor `rhs - lhs` as (nonnegative factor) × (square);
     check the factorisation with `ring` in a scratch `example` (W1).
  2. Build the proof of `0 ≤ factor * square`:
       the factor is a sum of `x` and `y`                                       R3
       the square                                                               R4
       their product                                                            R5
  3. Pass that one proof term as a hint.                                        R6
-/
-- BEGIN SPEC
theorem nl_sym (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 + y ^ 3 :=
-- END SPEC
  by nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

/- SKELETON · nl_three
  1. On paper: write `2 * (rhs - lhs)` as a sum of three squares of differences.
  2. One `sq_nonneg` term per square.                                           R4
  3. Pass all three as hints (the factor `2` is found by `linarith`).           R6
-/
-- BEGIN SPEC
theorem nl_three (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 :=
-- END SPEC
  by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

end E068

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try plain `nlinarith` first (R2); it is enough for `nl_sq`. For the other two it fails: compute
    `rhs - lhs` and write it as a sum of (nonnegative factor) × (square) terms.
H2. `x³ + y³ - x²y - xy² = (x + y)(x - y)²` and `2(a² + b² + c² - ab - bc - ca) = (a - b)² + (b - c)² + (c - a)²`.
    Turn each summand into a proof of `0 ≤ summand` (R3–R5) and pass them in `nlinarith [ … ]` (R6).
H3. `nl_sym`: `nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]`.
    `nl_three`: `nlinarith [...]` with one `sq_nonneg` hint (R4) per square in H2.
-/
