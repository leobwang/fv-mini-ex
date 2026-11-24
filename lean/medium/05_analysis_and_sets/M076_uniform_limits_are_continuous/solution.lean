/- M076 | Uniform limits are continuous | 15 min | epsilon/3, uniform convergence, triangle inequality, mathlib
GOAL
  If every `F n` is continuous (ε-δ) and `F n → f` uniformly, then `f` is continuous at every `x`:
  the classic ε/3 argument.
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity
BANNED: TendstoUniformly.continuous, TendstoLocallyUniformly.continuous, TendstoUniformlyOn.continuousOn

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M076

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

-- BEGIN SPEC
def UnifConv (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε
-- END SPEC

/- SKELETON · uniform_limit_contAt
  1. Open the goal `ContAt f x`:                                            R1
       ε : ℝ, hε : ε > 0
  2. One index for all points, from `hu` at tolerance ε / 3:                R2, R3
       N : ℕ, hN : ∀ n ≥ N, ∀ x, |F n x - f x| < ε / 3
  3. A δ from the continuity of that single `F N` at `x`, tolerance ε / 3:  R4 (applied as in R2, R3)
       δ : ℝ, hδ : δ > 0, hc : ∀ y, |y - x| < δ → |F N y - F N x| < ε / 3
  4. Give `δ`, take `y` and `hy : |y - x| < δ`:                             R5
  5. The three ε/3 facts, BEFORE the chain (step 6 needs them in context):
       h1 : |F N y - f y| < ε / 3      at y, same N                         R7
       h2 : |F N y - F N x| < ε / 3                                         R6
       h3 : |F N x - f x| < ε / 3      at x, same N                         R7
  6. The chain |f y - f x| = … ≤ … < ε/3 + ε/3 + ε/3 = ε:                   R8
       regroup into (f y - F N y) + (F N y - F N x) + (F N x - f x)         R9
       triangle inequality                                                  R10
       flip the first summand to match h1, then termwise `<`                R11 → R12
       ε/3 + ε/3 + ε/3 = ε                                                  R13
-/
-- BEGIN SPEC
theorem uniform_limit_contAt (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hF : ∀ n x, ContAt (F n) x)
    (hu : UnifConv F f) (x : ℝ) : ContAt f x :=
-- END SPEC
  by
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hc⟩ := hF N x (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have h1 := hN N le_rfl y
    have h2 := hc y hy
    have h3 := hN N le_rfl x
    calc |f y - f x| = |(f y - F N y) + (F N y - F N x) + (F N x - f x)| := by ring_nf
      _ ≤ |f y - F N y| + |F N y - F N x| + |F N x - f x| := abs_add_three _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm (f y)]; gcongr
      _ = ε := by ring

end M076

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Uniform convergence gives ONE index `N` that is `ε/3`-close to `f` at every point. Fix it first, then
    use the continuity of that single function `F N` at `x` (tolerance `ε/3`) to get `δ`.
H2. Order: `intro ε hε` (R1) → `N` from `hu (ε / 3) (by positivity)` (R2) → `δ` from `hF N x (ε / 3) …` (R4)
    → `refine ⟨δ, hδ, fun y hy => ?_⟩` (R5) → `have` the three ε/3 facts: `hN` at `y` and at `x` with the
    same `N` (R7), `hc y hy` (R6) → a `calc` through the three-term split (R8–R13).
H3. `calc |f y - f x| = |(f y - F N y) + (F N y - F N x) + (F N x - f x)| := by ring_nf
      _ ≤ |f y - F N y| + |F N y - F N x| + |F N x - f x| := abs_add_three _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm (f y)]; gcongr
      _ = ε := by ring`
-/
