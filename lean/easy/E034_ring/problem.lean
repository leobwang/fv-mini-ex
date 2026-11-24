/- E034 | ring | 1-2 min | ring, mathlib
GOAL
  Prove polynomial identities in commutative (semi)rings with `ring`.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · square_sum
  1. The equation holds in every commutative ring (`ℤ` is one); no hypothesis
     is involved. Close in one step:                                        R1
-/
-- BEGIN SPEC
theorem square_sum (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
-- END SPEC
  by
  ring

/- SKELETON · cube_succ
  1. Only `+`, `*`, `^` occur, so this is an identity of commutative semirings
     (`ℕ` is one); `ℕ` subtraction plays no role. Close in one step:         R2
-/
-- BEGIN SPEC
theorem cube_succ (n : ℕ) : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 :=
-- END SPEC
  by
  ring

/- SKELETON · with_hyp
  1. Not an identity in `a, b, c` (fails at `a = b = c = 1`), and `ring` never
     reads `h`: eliminate `a` with `h` first:                               R3 (or R4)
  2. The goal is now an identity in `b, c` over `ℚ`; close it:              R1
-/
-- BEGIN SPEC
theorem with_hyp (a b c : ℚ) (h : a = b + c) : a ^ 2 - 2 * b * c = b ^ 2 + c ^ 2 :=
-- END SPEC
  by
  rw [h]
  ring

/- SKELETON · four_squares
  1. An identity of commutative rings (`ℝ` is one); nothing about `ℝ`
     beyond the ring laws is needed. Close in one step:                     R1
-/
-- BEGIN SPEC
theorem four_squares (x y : ℝ) : (x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2) :=
-- END SPEC
  by
  ring


/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three statements are identities in their variables; one (`with_hyp`) is true only because of `h`.
H2. `ring` closes identities of commutative (semi)rings (R1, R2) but never reads the context: use `h`
    first by eliminating `a` (R3, or R4), then the goal is an identity.
H3. `ring` for `square_sum`, `cube_succ`, `four_squares`; `subst h` then `ring` for `with_hyp`.
-/
