/- M105 | Interval arithmetic | 15 min | structure, min, max, case split, soundness, nlinarith, mathlib
GOAL
  Interval arithmetic is sound: if `Ival.Mem x I` (`x ∈ I`) and `Ival.Mem y J`, then
  `Ival.Mem (x + y) (I.add J)` and `Ival.Mem (x * y) (I.mul J)`, where the endpoints of `I.mul J` are
  the min and max of the four endpoint products. `add_sound` is a warm-up; `mul_sound` is the problem.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M105

-- BEGIN SPEC
/-- the closed interval `[lo, hi]` (empty if `hi < lo`) -/
structure Ival where
  lo : ℝ
  hi : ℝ

def Ival.Mem (x : ℝ) (I : Ival) : Prop := I.lo ≤ x ∧ x ≤ I.hi

def Ival.add (I J : Ival) : Ival := ⟨I.lo + J.lo, I.hi + J.hi⟩

noncomputable def Ival.mul (I J : Ival) : Ival :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
-- END SPEC

/- SKELETON · add_sound
  1. Split both hypotheses into their two bounds:                          R1, R1
  2. Split the goal into the lower and the upper bound:                    R2
  3. In each goal: unfold `Ival.add`, then add the two matching bounds:    R3, R4
-/
-- BEGIN SPEC
theorem add_sound (x y : ℝ) (I J : Ival) (hx : Ival.Mem x I) (hy : Ival.Mem y J) :
    Ival.Mem (x + y) (I.add J) :=
-- END SPEC
  sorry

/- SKELETON · mul_sound
  0. MILESTONE, prove it first, as a separate theorem above this one:
       between (a b x y : ℝ) (h1 : a ≤ x) (h2 : x ≤ b) :
         min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y)
     a. split on the sign of `y`:                                          R5
     b. in each case split the `∧`:                                        R2
     c. lower bound: through `a * y` or `b * y` (whichever the `min` is),
        then the product inequality:                                       R6, R7, R9
     d. upper bound, the mirror image:                                     R6, R9, R8
  1. Split `hx`, `hy`:                                                     R1
  2. Use the milestone three times, each split into two halves:            R10
       in `x` (endpoints `I.lo`, `I.hi`, factor `y`)       → bounds on `x * y`
       in `y` with factor `I.lo`, and with factor `I.hi`   → bounds on `y * I.lo`, `y * I.hi`
  3. Flip the products of the last four facts to `I.lo * J.lo` order:      R11
  4. Split the goal (optionally unfold `Ival.mul` first to see the `min`s): R2 (R3)
  5. Lower bound: through `min (I.lo * y) (I.hi * y)` (the `x`-call's lower half),
     then below a `min`, each half reached from one half of the big `min`
     through the lower half of the matching `y`-call:                      R6, R12, R6 + R7
  6. Upper bound, the mirror image (upper halves):                         R6, R13, R6 + R8
-/
-- BEGIN SPEC
theorem mul_sound (x y : ℝ) (I J : Ival) (hx : Ival.Mem x I) (hy : Ival.Mem y J) :
    Ival.Mem (x * y) (I.mul J) :=
-- END SPEC
  sorry

end M105

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `x * y` is monotone in `x` for fixed `y` (antitone if `y ≤ 0`), so for `a ≤ x ≤ b` it lies between
    `min (a * y) (b * y)` and `max (a * y) (b * y)`. Prove that once as the milestone `between`.
H2. `between`: `rcases le_total 0 y with hy | hy`, then in each case `refine ⟨?_, ?_⟩` and chain with
    `le_trans` through `min_le_left/right` / `le_max_left/right` and `nlinarith`. `mul_sound`: three
    `obtain ⟨_, _⟩ := between …` (in `x`; in `y` with factor `I.lo`; in `y` with factor `I.hi`), flip the
    products with `simp only [mul_comm _ I.lo, mul_comm _ I.hi] at …`, then combine with `le_min`/`max_le`.
H3. Main: `obtain ⟨A1, A2⟩ := between I.lo I.hi x y h1 h2`, `obtain ⟨B1, B2⟩ := between J.lo J.hi y I.lo h3 h4`,
    `obtain ⟨C1, C2⟩ := between J.lo J.hi y I.hi h3 h4`; after the flip the lower bound is
    `le_trans (le_min (le_trans (min_le_left _ _) B1) (le_trans (min_le_right _ _) C1)) A1`.
-/
