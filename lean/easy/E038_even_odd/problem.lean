/- E038 | Even and Odd | 3 min | Even, Odd, obtain rfl, mathlib
GOAL
  Prove parity facts by unpacking the definitions of `Even` (`∃ r, n = r + r`) and `Odd`
  (`∃ m, n = 2 * m + 1`): take the hypotheses apart, then give a witness for the goal.
BANNED: Even.mul_right, Odd.add_odd, Odd.pow, parity_simps

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · even_mul_any
  1. Unpack `h : Even m` and substitute `m` by `k + k` everywhere:              R2
       the goal becomes `Even ((k + k) * n)`
  2. Distribute by hand to see the half of `(k + k) * n`; give it as witness:   R4 (or R7)
  3. Close the witness equation:                                                R6
-/
-- BEGIN SPEC
theorem even_mul_any (m n : ℕ) (h : Even m) : Even (m * n) :=
-- END SPEC
  sorry

/- SKELETON · odd_add_odd_even
  1. Unpack `hm` and `hn` with substitution, witness names `a` and `b`:          R3, R3
       the goal becomes `Even (2 * a + 1 + (2 * b + 1))`
  2. Expand: the sum is `2a + 2b + 2`; its half is the witness:                 R4 (or R7)
  3. Close the witness equation:                                                R6
-/
-- BEGIN SPEC
theorem odd_add_odd_even (m n : ℕ) (hm : Odd m) (hn : Odd n) : Even (m + n) :=
-- END SPEC
  sorry

/- SKELETON · odd_square
  1. Unpack `h : Odd n` and substitute `n` by `2 * k + 1`:                      R3
       the goal becomes `Odd ((2 * k + 1) ^ 2)`
  2. Expand the square and write it as `2 * (…) + 1`; `(…)` is the witness:      R5 (or R7)
  3. Close the witness equation:                                                R6
-/
-- BEGIN SPEC
theorem odd_square (n : ℤ) (h : Odd n) : Odd (n ^ 2) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Even` and `Odd` are `∃`-statements. Unpack each hypothesis with `obtain ⟨k, rfl⟩ := h` (R2, R3), which
    also replaces the variable by `k + k` or `2 * k + 1`; then prove the goal by giving a witness (R4, R5).
H2. Find each witness by expanding the substituted goal by hand:
    `(k + k) * n = k * n + k * n`, `(2a + 1) + (2b + 1) = (a + b + 1) + (a + b + 1)`,
    `(2k + 1)² = 2 · (2k² + 2k) + 1`. The equation left after the witness is a ring identity (R6).
H3. Witnesses `k * n`, `a + b + 1`, `2 * k ^ 2 + 2 * k`; each goal closes with `exact ⟨w, by ring⟩` (R7).
-/
