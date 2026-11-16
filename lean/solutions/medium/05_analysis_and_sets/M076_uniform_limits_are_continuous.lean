/- M076 | Uniform limits are continuous | 15 min | epsilon/3, uniform convergence, triangle inequality, mathlib
GOAL
  If every `F n` is continuous (ε-δ) and `F n → f` uniformly, then `f` is continuous at every `x`:
  the classic ε/3 argument.

REFERENCE
  #check abs_add_three   -- (a b c : α) : |a + b + c| ≤ |a| + |b| + |c|
  #check abs_sub_comm    -- (a b : α) : |a - b| = |b - a|
  example (ε : ℝ) (h : 0 < ε) : 0 < ε / 3 := by positivity
  example (u v w z : ℝ) : u - z = (u - v) + (v - w) + (w - z) := by ring
  example (a b c d e f : ℝ) (h1 : a < d) (h2 : b < e) (h3 : c < f) : a + b + c < d + e + f := by gcongr
  -- `obtain ⟨δ, hδ, hc⟩ := h (ε / 3) (by positivity)` unpacks `∃ δ > 0, ...`
  `calc` chains `=`, `≤`, `<` steps into a final `<`.
NOTE: in `UnifConv`, one `N` works for every `x` at once; that is what makes the argument go through.
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto
BANNED: nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop
BANNED: tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def
BANNED: cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity
BANNED: TendstoUniformly.continuous, TendstoLocallyUniformly.continuous, TendstoUniformlyOn.continuousOn
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
H1. Fix one index `N` that is `ε/3`-close to `f` everywhere, then use the continuity of that single `F N` at `x`.
H2. `obtain ⟨N, hN⟩ := hu (ε / 3) ...` and `obtain ⟨δ, hδ, hc⟩ := hF N x (ε / 3) ...`; use that `δ`. Split
    `f y - f x = (f y - F N y) + (F N y - F N x) + (F N x - f x)`.
H3. `calc |f y - f x| = |(f y - F N y) + (F N y - F N x) + (F N x - f x)| := by ring_nf
      _ ≤ _ := abs_add_three _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm (f y)]; gcongr  -- uses hN N le_rfl y, hc y hy, hN N le_rfl x
      _ = ε := by ring`
-/
