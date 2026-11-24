/- M073 | x² is continuous (ε-δ) | 10-15 min | epsilon-delta, min, abs, gcongr, mathlib
GOAL
  From the explicit ε-δ definition, prove that `x ↦ x ^ 2` is continuous at every point `a`.
  A choice that works: `δ = min 1 (ε / (2 * |a| + 1))`.

BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, continuous_pow, continuousAt_pow
BANNED: continuous_mul, continuous_id, Metric.continuous_iff, Metric.continuousAt_iff

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M073

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

/- SKELETON · sq_contAt
  1. Open the definition: context gains `ε`, `hε : ε > 0`:                    R1
  2. Choose `δ = min 1 (ε / (2 * |a| + 1))`; close `δ > 0` on the spot;
     context gains `y`, `hy : |y - a| < δ`:                                   R2, R3
     (optional) the goal shows `(fun x => x ^ 2) y`; simplify it:             R4
  3. Split `hy` into two facts (one `have` each):                             R5 → R6
       h1 : |y - a| < 1
       h2 : |y - a| < ε / (2 * |a| + 1)
  4. Milestone, a `have` proved by a three-step `calc`:                       R7
       hya : |y + a| ≤ 2 * |a| + 1
       |y + a| = |(y - a) + 2 * a|                                            R8
       _ ≤ |y - a| + |2 * a|                                                  R9
       _ ≤ 2 * |a| + 1      split `|2 * a|`, then use h1                      R10, R11, R12
  5. The main `calc`, from `|y ^ 2 - a ^ 2|` to `ε`:                          R7
       = |y - a| * |y + a|                    merge the two `|·|`, normalise  rw [← abs_mul] (R10), R8
       ≤ |y - a| * (2 * |a| + 1)              uses hya                        R13
       < ε / (2 * |a| + 1) * (2 * |a| + 1)    uses h2                         R14
       = ε                                                                    R15
-/
-- BEGIN SPEC
theorem sq_contAt (a : ℝ) : ContAt (fun x => x ^ 2) a :=
-- END SPEC
  by
    intro ε hε
    refine ⟨min 1 (ε / (2 * |a| + 1)), by positivity, fun y hy => ?_⟩
    have h1 : |y - a| < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have h2 : |y - a| < ε / (2 * |a| + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have hya : |y + a| ≤ 2 * |a| + 1 := by
      calc |y + a| = |(y - a) + 2 * a| := by ring_nf
        _ ≤ |y - a| + |2 * a| := abs_add_le _ _
        _ ≤ 2 * |a| + 1 := by rw [abs_mul, abs_two]; linarith
    calc |y ^ 2 - a ^ 2| = |y - a| * |y + a| := by rw [← abs_mul]; ring_nf
      _ ≤ |y - a| * (2 * |a| + 1) := by gcongr
      _ < ε / (2 * |a| + 1) * (2 * |a| + 1) := by gcongr
      _ = ε := by field_simp

end M073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `|y² - a²| = |y - a| * |y + a|`. Being within 1 of `a` keeps `|y + a|` at most `2 * |a| + 1`, so
    `δ = min 1 (ε / (2 * |a| + 1))` makes the product smaller than `ε`.
H2. `intro ε hε; refine ⟨min 1 (ε / (2 * |a| + 1)), by positivity, fun y hy => ?_⟩`. Get
    `h1 : |y - a| < 1` and `h2 : |y - a| < ε / (2 * |a| + 1)` from `hy` with `lt_of_lt_of_le` and
    `min_le_left`/`min_le_right`. Prove `hya : |y + a| ≤ 2 * |a| + 1` by a `calc` through
    `|(y - a) + 2 * a|` and `abs_add_le`, finishing with `rw [abs_mul, abs_two]; linarith`.
H3. `calc |y ^ 2 - a ^ 2| = |y - a| * |y + a| := by rw [← abs_mul]; ring_nf
      _ ≤ |y - a| * (2 * |a| + 1) := by gcongr
      _ < ε / (2 * |a| + 1) * (2 * |a| + 1) := by gcongr
      _ = ε := by field_simp`
-/
