/- M116 | Composite trapezoid from the panel bound | 15 min | sum_integral_adjacent_intervals, Finset sums, abs, gcongr, mathlib
GOAL
  If every trapezoid panel of width `h` has error ≤ `M h³ / 12`, then the composite rule with `n` panels on
  `[a, a + n h]` has error ≤ `n · (M h³ / 12)` (that is `(b - a) M h² / 12` with b = a + n h: second order).
  Split the integral into the `n` panel integrals and add up the panel errors.

REFERENCE
  #check intervalIntegral.sum_integral_adjacent_intervals
    -- (∀ k < n, IntervalIntegrable f μ (a k) (a (k+1))) → ∑ k ∈ range n, ∫ x in a k..a (k+1), f x ∂μ = ∫ x in a 0..a n, f x ∂μ
  example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable a b
  #check Finset.sum_sub_distrib      -- ∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i
  #check Finset.abs_sum_le_sum_abs   -- |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|
  example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by gcongr with i hi; exact h i hi
  example (n : ℕ) (c : ℝ) : ∑ _k ∈ Finset.range n, c = n * c := by simp
  Named arguments choose the partition: `sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (a := fun k : ℕ => a + k * h) ...`.
  `∫ t in x..y, f t` is the integral of f from x to y (∂μ omitted means Lebesgue measure `volume`).
NOTE: the partition's points come out as `a + ↑k * h` and `a + ↑(k + 1) * h`; `push_cast` / `Nat.cast_succ` tidy the casts.
-/
import Mathlib

namespace M116

-- BEGIN SPEC
theorem composite_trapezoid (f : ℝ → ℝ) (hf : Continuous f) (M a h : ℝ) (n : ℕ)
    (hpanel : ∀ x, |(∫ t in x..x + h, f t) - h / 2 * (f x + f (x + h))| ≤ M * h ^ 3 / 12) :
    |(∫ t in a..a + n * h, f t) - ∑ k ∈ Finset.range n, h / 2 * (f (a + k * h) + f (a + (k + 1) * h))|
      ≤ n * (M * h ^ 3 / 12) :=
-- END SPEC
  sorry

end M116

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Instantiate the adjacent-intervals lemma with the nodes `fun k : ℕ => a + k * h`: it rewrites
    `∫ t in a..a + n * h, f t` as a sum of panel integrals over `[a + k h, a + (k+1) h]`.
H2. Turn "sum of integrals minus sum of trapezoids" into one sum of panel errors (`Finset.sum_sub_distrib`),
    bound `|∑ …| ≤ ∑ |…|`, bound each term by `hpanel (a + k * h)`, and sum the constant.
H3. `have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := fun k : ℕ => a + k * h) (n := n) (fun k _ => hf.intervalIntegrable _ _)`, `simp only [Nat.cast_zero,
    zero_mul, add_zero, Nat.cast_succ] at hsum`, `rw [← hsum, ← Finset.sum_sub_distrib]`; per panel
    `rwa [show a + k * h + h = a + (k + 1) * h by ring] at this` with `this := hpanel (a + k * h)`.
-/
