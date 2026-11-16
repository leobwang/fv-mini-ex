/- M105 | Interval arithmetic | 15 min | structure, min, max, case split, soundness, nlinarith, mathlib
GOAL
  Interval arithmetic is sound: if `Ival.Mem x I` (`x ∈ I`) and `Ival.Mem y J`, then
  `Ival.Mem (x + y) (I.add J)` and `Ival.Mem (x * y) (I.mul J)`, where the endpoints of `I.mul J` are
  the min and max of the four endpoint products. `add_sound` is a warm-up; `mul_sound` is the problem.

REFERENCE
  #check le_min       -- a ≤ b → a ≤ c → a ≤ min b c     (dually `max_le`)
  example (a b : ℝ) : min a b ≤ a := min_le_left a b    -- also min_le_right, le_max_left, le_max_right
  example (y : ℝ) (P : Prop) (h1 : 0 ≤ y → P) (h2 : y ≤ 0 → P) : P := by
    rcases le_total 0 y with hy | hy; exacts [h1 hy, h2 hy]
  example (a x y : ℝ) (h : a ≤ x) (hy : 0 ≤ y) : a * y ≤ x * y := by nlinarith
  example (a b c : ℝ) (h : c ≤ b * a) : c ≤ a * b := by simp only [mul_comm _ a] at h; exact h
  `simp only [Ival.Mem, Ival.mul]` unfolds the definitions; `obtain ⟨h1, h2⟩ := hx` splits `x ∈ I`.
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

-- BEGIN SPEC
theorem add_sound (x y : ℝ) (I J : Ival) (hx : Ival.Mem x I) (hy : Ival.Mem y J) :
    Ival.Mem (x + y) (I.add J) :=
-- END SPEC
  by
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hy
    exact ⟨by simp only [Ival.add]; linarith, by simp only [Ival.add]; linarith⟩

-- `x * y` lies between the products of `y` with the endpoints of `x`'s interval
theorem between (a b x y : ℝ) (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

-- BEGIN SPEC
theorem mul_sound (x y : ℝ) (I J : Ival) (hx : Ival.Mem x I) (hy : Ival.Mem y J) :
    Ival.Mem (x * y) (I.mul J) :=
-- END SPEC
  by
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hy
    obtain ⟨A1, A2⟩ := between I.lo I.hi x y h1 h2
    obtain ⟨B1, B2⟩ := between J.lo J.hi y I.lo h3 h4
    obtain ⟨C1, C2⟩ := between J.lo J.hi y I.hi h3 h4
    -- WHY: `between` puts `I.lo` on the right; flip so the products match `Ival.mul`
    simp only [mul_comm _ I.lo, mul_comm _ I.hi] at B1 B2 C1 C2
    exact ⟨le_trans (le_min (le_trans (min_le_left _ _) B1) (le_trans (min_le_right _ _) C1)) A1,
      le_trans A2 (max_le (le_trans B2 (le_max_left _ _)) (le_trans C2 (le_max_right _ _)))⟩

end M105

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `x * y` is linear in `x` for fixed `y`, so it lies between `I.lo * y` and `I.hi * y` (which one is
    smaller depends on the sign of `y`). Prove that as a helper lemma.
H2. Use the helper three times: once in `x` (with `y` fixed), and twice in `y` (with `x` replaced by the
    fixed numbers `I.lo` and `I.hi`). Then `x * y` is squeezed by products of endpoints.
H3. Helper: `theorem between (a b x y : ℝ) (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y)`, by `rcases le_total 0 y` and `nlinarith`.
    Main: after the three calls, flip `J.lo * I.lo` to `I.lo * J.lo` with `simp only [mul_comm _ I.lo, mul_comm _ I.hi] at …`;
    the lower bound is `le_trans (le_min (le_trans (min_le_left _ _) B1) (le_trans (min_le_right _ _) C1)) A1`.
-/
