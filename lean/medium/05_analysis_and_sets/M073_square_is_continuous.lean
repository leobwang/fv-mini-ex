/- M073 | x² is continuous (ε-δ) | 10-15 min | epsilon-delta, min, abs, gcongr, mathlib
GOAL
  From the explicit ε-δ definition, prove that `x ↦ x ^ 2` is continuous at every point `a`.
  A choice that works: `δ = min 1 (ε / (2 * |a| + 1))`.

REFERENCE
  example (x b c : ℝ) (h : x < min b c) : x < b := lt_of_lt_of_le h (min_le_left b c)  -- (and min_le_right)
  example (ε a : ℝ) (h : 0 < ε) : 0 < min 1 (ε / (2 * |a| + 1)) := by positivity
  #check abs_add_le   -- (a b : α) : |a + b| ≤ |a| + |b|
  #check abs_mul      -- (a b : α) : |a * b| = |a| * |b|
  example (y a : ℝ) : y ^ 2 - a ^ 2 = (y - a) * (y + a) := by ring
  example (x y z : ℝ) (h : x < y) (hz : 0 < z) : x * z < y * z := by gcongr  -- compare the parts that differ
  example (ε c : ℝ) (hc : 0 < c) : ε / c * c = ε := by field_simp
  `calc` chains `=`, `≤`, `<` steps into a final `<`.
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, continuous_pow, continuousAt_pow
BANNED: continuous_mul, continuous_id, Metric.continuous_iff, Metric.continuousAt_iff
NOTE: the bans block the route through Mathlib's `Continuous`/filters: build `δ` by hand.
-/
import Mathlib

namespace M073

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

-- BEGIN SPEC
theorem sq_contAt (a : ℝ) : ContAt (fun x => x ^ 2) a :=
-- END SPEC
  sorry

end M073

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `|y² - a²| = |y - a| * |y + a|`. Being within 1 of `a` keeps `|y + a|` at most `2 * |a| + 1`.
H2. `intro ε hε; refine ⟨min 1 (ε / (2 * |a| + 1)), by positivity, fun y hy => ?_⟩`, then extract
    `|y - a| < 1` and `|y - a| < ε / (2 * |a| + 1)` from `hy`. Bound `|y + a| = |(y - a) + 2 * a|` by `abs_add_le`.
H3. `calc |y ^ 2 - a ^ 2| = |y - a| * |y + a| := by rw [← abs_mul]; ring_nf
      _ ≤ |y - a| * (2 * |a| + 1) := by gcongr
      _ < ε / (2 * |a| + 1) * (2 * |a| + 1) := by gcongr
      _ = ε := by field_simp`
-/
