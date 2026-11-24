/- M053 | Sums of two squares mod 4 | 10-15 min | ZMod, Int.cast, push_cast, decide, mathlib
GOAL
  Squares are 0 or 1 in `ZMod 4`; conclude that no integer `a² + b²` is `3 mod 4`.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M053

/- SKELETON · sq_mod_four
  1. Move `x` into the goal, so it reads `∀ x : ZMod 4, …` with no free variable:   R1
  2. Check all four residues:                                                    R2
-/
-- BEGIN SPEC
theorem sq_mod_four (x : ZMod 4) : x ^ 2 = 0 ∨ x ^ 2 = 1 :=
-- END SPEC
  sorry

/- SKELETON · two_squares_ne_three
  1. `≠` is `= → False`: assume `h : (a ^ 2 + b ^ 2) % 4 = 3`, goal `False`:          R3
  2. Transport the integer equation into `ZMod 4`:
       h1 : ↑((a ^ 2 + b ^ 2) % ↑4) = ↑(a ^ 2 + b ^ 2)                             R4
  3. Push the casts inward and rewrite with `h` in one call:                         R7 (= R5 + R6 + rw [h])
       h1 : 3 = ↑a ^ 2 + ↑b ^ 2
  4. Replace `↑a` by a fresh `x : ZMod 4`, then `↑b` by `y`:                          R8, R8
  5. Move `x y` (and `h1` with them) into the goal:                                  R9
       ⊢ ∀ (x y : ZMod 4), 3 = x ^ 2 + y ^ 2 → False
  6. Check all 16 pairs:                                                           R2
  (Part 1 is not used: `decide` handles both squares at once.)
-/
-- BEGIN SPEC
theorem two_squares_ne_three (a b : ℤ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 :=
-- END SPEC
  sorry

end M053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ZMod 4` has four elements, so a closed statement about all of them is decided by `decide` (R2).
    `ℤ` is infinite: for Part 2, first move the hypothesis into `ZMod 4`.
H2. Part 1: `revert x` (R1), then `decide`. Part 2: `intro h`; `ZMod.intCast_mod` (R4) turns
    `(a ^ 2 + b ^ 2) % 4 = 3` into `(3 : ZMod 4) = ↑a ^ 2 + ↑b ^ 2` after `push_cast [h]` (R7);
    then forget that the residues came from `a`, `b` (R8), revert them (R9) and `decide`.
H3. `have h1 := ZMod.intCast_mod (a ^ 2 + b ^ 2) 4; push_cast [h] at h1`, then `generalize` both
    casts at `h1` (R8) and `revert x y; decide`.
-/
