/- M116 | Composite trapezoid from the panel bound | 15 min | sum_integral_adjacent_intervals, Finset sums, abs, gcongr, mathlib
GOAL
  If every trapezoid panel of width `h` has error ≤ `M h³ / 12`, then the composite rule with `n` panels on
  `[a, a + n h]` has error ≤ `n · (M h³ / 12)` (that is `(b - a) M h² / 12` with b = a + n h: second order).
  Split the integral into the `n` panel integrals and add up the panel errors.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M116

/- SKELETON · composite_trapezoid
  1. Split the integral at the nodes `a + k h` (k = 0..n); context gains `hsum`:     R1, with R2
       nodes `(a := fun k : ℕ => a + k * h)`; the integrability argument is R2
  2. Tidy hsum's endpoints: `a + ↑0 * h` → `a`, `↑(k + 1)` → `↑k + 1`:                R3, R4
  3. Whole integral → panel sum, then merge the two sums into one:                  rw [← hsum], R5
  4. Chain three steps:                                                              R6
       a. |∑ eₖ| ≤ ∑ |eₖ|   (eₖ the error of panel k)                                 R7
            type the middle sum out yourself: the goal's summand with index `k` and
            integration variable `t`, inside `|…|` (only the first and last `_` are free)
       b. ∑ |eₖ| ≤ ∑ M h³ / 12, termwise:                                            R8
            the panel bound at the left node `a + ↑k * h`:                           R9
            its right node `a + ↑k * h + h` → `a + (↑k + 1) * h`, then close:        R10 → R11
       c. ∑ of the constant = `↑n * (M * h ^ 3 / 12)`:                                R12
-/
-- BEGIN SPEC
theorem composite_trapezoid (f : ℝ → ℝ) (hf : Continuous f) (M a h : ℝ) (n : ℕ)
    (hpanel : ∀ x, |(∫ t in x..x + h, f t) - h / 2 * (f x + f (x + h))| ≤ M * h ^ 3 / 12) :
    |(∫ t in a..a + n * h, f t) - ∑ k ∈ Finset.range n, h / 2 * (f (a + k * h) + f (a + (k + 1) * h))|
      ≤ n * (M * h ^ 3 / 12) :=
-- END SPEC
  by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
      (a := fun k : ℕ => a + k * h) (n := n) (fun k _ => hf.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at hsum
    rw [← hsum, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k ∈ Finset.range n,
            |(∫ t in a + k * h..a + (k + 1) * h, f t) - h / 2 * (f (a + k * h) + f (a + (k + 1) * h))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, M * h ^ 3 / 12 := by
          gcongr with k
          have := hpanel (a + k * h)
          rwa [show a + k * h + h = a + (k + 1) * h by ring] at this
      _ = _ := by simp

end M116

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The integral over `[a, a + n h]` is the sum of the `n` panel integrals over `[a + k h, a + (k + 1) h]`
    (R1, once you name the nodes). After that it is a finite-sum estimate: triangle inequality, then the
    panel bound `hpanel` term by term, then a sum of `n` equal constants.
H2. `have hsum := …` from R1 with nodes `fun k : ℕ => a + k * h` and integrability from `hf` (R2); tidy its
    casts with `simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at hsum` (R3, R4); then
    `rw [← hsum, ← Finset.sum_sub_distrib]` and a `calc`: `Finset.abs_sum_le_sum_abs`, `gcongr with k` plus
    `hpanel (a + k * h)`, and `simp` for the constant sum.
H3. `have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := fun k : ℕ => a + k * h) (n := n) (fun k _ => hf.intervalIntegrable _ _)`; per panel
    `have := hpanel (a + k * h)` then `rwa [show a + k * h + h = a + (k + 1) * h by ring] at this`.
-/
