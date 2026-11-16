/- H048 | Riemann sums of monotone functions | 1-1.5 h | intervalIntegral, sandwich, telescoping, epsilon-N, mathlib
GOAL
  For monotone `f` (`x ≤ y → f x ≤ f y`), the left Riemann sums `leftSum f n` on `N = n + 1` equal pieces of
  `[0, 1]` converge to `∫₀¹ f`. On each piece `f(k/N)/N ≤ ∫ ≤ f((k+1)/N)/N`; summing squeezes the integral
  between `leftSum f n` and an upper sum that telescopes to `leftSum f n + (f 1 - f 0)/N`.

REFERENCE
  #check intervalIntegral.integral_mono_on  -- a ≤ b → IntervalIntegrable f μ a b → (same for g) → (∀ x ∈ Icc a b, f x ≤ g x) → ∫ f ≤ ∫ g
  #check intervalIntegral.integral_const    -- ∫ x in a..b, c = (b - a) • c      (`•` is `*` here: `smul_eq_mul`)
  example (c a b : ℝ) : IntervalIntegrable (fun _ => c) MeasureTheory.volume a b := intervalIntegrable_const
  #check Monotone.intervalIntegrable        -- Monotone u → IntervalIntegrable u μ a b
  #check intervalIntegral.sum_integral_adjacent_intervals  -- ∑ k ∈ range n, ∫ x in a k..a (k+1), f x = ∫ x in a 0..a n, f x
  #check Finset.sum_range_sub               -- ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0
  #check Finset.sum_le_sum                  -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  #check Finset.sum_div                     -- (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a   (also `Finset.sum_sub_distrib`)
  #check exists_nat_gt                      -- ∃ n : ℕ, x < n
  #check abs_sub_lt_iff                     -- |a - b| < c ↔ a - b < c ∧ b - a < c
  #check div_lt_iff₀                        -- 0 < c → (b / c < a ↔ b < a * c)   (clear a positive denominator)
NOTE: `∫ x in a..b, f x` integrates against `MeasureTheory.volume`; pass `(μ := MeasureTheory.volume)` when Lean can't infer it.
BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric
BANNED: CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity
BANNED: MonotoneOn.sum_le_integral, MonotoneOn.integral_le_sum, MonotoneOn.sum_le_integral_Ico, MonotoneOn.integral_le_sum_Ico, AntitoneOn.sum_le_integral, AntitoneOn.integral_le_sum, AntitoneOn.sum_le_integral_Ico, AntitoneOn.integral_le_sum_Ico
BANNED: sum_Ico_le_integral_of_le, integral_le_sum_Ico_of_le, sum_mul_Ico_le_integral_of_monotone_antitone, integral_le_sum_mul_Ico_of_antitone_monotone
-/
import Mathlib

namespace H048

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
/-- Left Riemann sum of `f` on `[0, 1]` with `n + 1` equal pieces. -/
noncomputable def leftSum (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), f (k / (n + 1))) / (n + 1)
-- END SPEC

-- MILESTONE (optional: change or delete)
-- One piece `[k/N, (k+1)/N]` of width `1/N`: the integral lies between the endpoint values times `1/N`.
theorem piece (f : ℝ → ℝ) (hf : Monotone f) (N : ℝ) (hN : 0 < N) (k : ℕ) :
    f (k / N) / N ≤ ∫ x in (k / N)..((k + 1) / N), f x ∧
      ∫ x in (k / N)..((k + 1) / N), f x ≤ f ((k + 1) / N) / N := by
  sorry

-- MILESTONE (optional: change or delete)
theorem split_integral (f : ℝ → ℝ) (hf : Monotone f) (n : ℕ) :
    ∫ x in (0 : ℝ)..1, f x =
      ∑ k ∈ Finset.range (n + 1), ∫ x in (k / (n + 1 : ℝ))..((k + 1) / (n + 1 : ℝ)), f x := by
  sorry

-- MILESTONE (optional: change or delete)
theorem upper_sum (f : ℝ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f ((k + 1) / (n + 1 : ℝ)) / (n + 1) =
      leftSum f n + (f 1 - f 0) / (n + 1) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem sandwich (f : ℝ → ℝ) (hf : Monotone f) (n : ℕ) :
    leftSum f n ≤ ∫ x in (0 : ℝ)..1, f x ∧
      ∫ x in (0 : ℝ)..1, f x ≤ leftSum f n + (f 1 - f 0) / (n + 1) := by
  sorry

-- BEGIN SPEC
theorem riemann_monotone (f : ℝ → ℝ) (hf : Monotone f) :
    ConvergesTo (leftSum f) (∫ x in (0 : ℝ)..1, f x) :=
-- END SPEC
  sorry

end H048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work piece by piece: on `[k/N, (k+1)/N]`, compare `f` with the constants `f (k/N)` and `f ((k+1)/N)` (monotonicity), and integrate a constant over an interval of width `1/N`.
H2. Split `∫₀¹` with `sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / (n + 1)) (n := n + 1)` (then `div_self` turns `(n+1)/(n+1)` into `1`), sum the per-piece bounds with `Finset.sum_le_sum`, and telescope the upper sum with `Finset.sum_range_sub (fun k : ℕ => f (k / (n + 1)))`. Finally the gap `(f 1 - f 0)/(n+1)` goes to 0.
H3. `piece`: `have := intervalIntegral.integral_mono_on hle (intervalIntegrable_const (μ := MeasureTheory.volume)) hf.intervalIntegrable (fun x hx => hf hx.1)`, then `rw [intervalIntegral.integral_const, smul_eq_mul, hw] at this` with `hw : (k + 1) / N - k / N = 1 / N`. Main: `obtain ⟨N, hN⟩ := exists_nat_gt ((f 1 - f 0) / ε)`; prove `have h3 : (f 1 - f 0) / (n + 1) < ε` by `rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hε] at hN; nlinarith` (also needs `0 ≤ f 1 - f 0` and `(N : ℝ) ≤ n`), then `rw [abs_sub_lt_iff]; constructor <;> linarith`.
-/
