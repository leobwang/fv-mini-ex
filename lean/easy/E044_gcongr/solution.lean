/- E044 | gcongr | 2 min | gcongr, monotonicity, mathlib
GOAL
  Prove inequalities between expressions with the same shape using `gcongr`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · add_mono_sq
  1. Compare the two sides: shared outer `_ + c`, shared inner `_ ^ 2`, and `a` facing `b`.
  2. One call of the shape-matching tactic peels both layers:                  R1 → R2
  3. Its goals (side goal `0 ≤ a`, main goal `a ≤ b`) are hypotheses, so they
     close on their own; nothing should be left in the infoview:                R3
-/
-- BEGIN SPEC
theorem add_mono_sq (a b c : ℝ) (h : a ≤ b) (ha : 0 ≤ a) : a ^ 2 + c ≤ b ^ 2 + c :=
-- END SPEC
  by gcongr

/- SKELETON · cube_mono
  1. One shared layer `_ ^ 3`: peel it (side goal `0 ≤ x`, main goal `x ≤ y`):   R2
  2. Both goals are hypotheses:                                                  R3
-/
-- BEGIN SPEC
theorem cube_mono (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 3 ≤ y ^ 3 :=
-- END SPEC
  by gcongr

/- SKELETON · mul_mono_nat
  1. Shared outer `_ + 5`: peel it:                                              R1
  2. Under it both factors differ: two main goals `a ≤ b`, `c ≤ d`; in `ℕ` the
     side goals of a product are automatic:                                     R4
  3. Both main goals are hypotheses:                                             R3
-/
-- BEGIN SPEC
theorem mul_mono_nat (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a * c + 5 ≤ b * d + 5 :=
-- END SPEC
  by gcongr

/- SKELETON · recip_anti
  1. Shared numerator `3`, differing denominators: peel `3 / _`; the main goal
     is FLIPPED to `x < y`, side goals `0 < 3` and `0 < x`:                      R5
  2. `0 < 3` is a numeral fact, closed automatically:                            R6
  3. `0 < x` and `x < y` are hypotheses:                                         R3
-/
-- BEGIN SPEC
theorem recip_anti (x y : ℝ) (hx : 0 < x) (h : x < y) : 3 / y < 3 / x :=
-- END SPEC
  by gcongr

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides of every goal have the same shape and differ in one or two places. Find the shared layers
    (`_ + c`, `_ ^ n`, `_ * _`, `3 / _`) and what sits in the differing positions.
H2. `gcongr` peels the shared layers off and reduces each goal to inequalities between the differing parts
    (for `3 / _` in the reverse order), plus side goals like `0 ≤ a`; it closes every one of them that is a
    hypothesis or a numeral fact (`positivity`).
H3. Each proof is the single tactic `gcongr`; afterwards the infoview should say "no goals".
-/
