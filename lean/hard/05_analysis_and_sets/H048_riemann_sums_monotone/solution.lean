/- H048 | Riemann sums of monotone functions | 1-1.5 h | intervalIntegral, sandwich, telescoping, epsilon-N, mathlib
GOAL
  For monotone `f` (`x ≤ y → f x ≤ f y`), the left Riemann sums `leftSum f n` on `N = n + 1` equal pieces of
  `[0, 1]` converge to `∫₀¹ f`. On each piece `f(k/N)/N ≤ ∫ ≤ f((k+1)/N)/N`; summing squeezes the integral
  between `leftSum f n` and an upper sum that telescopes to `leftSum f n + (f 1 - f 0)/N`.

BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric
BANNED: CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity
BANNED: MonotoneOn.sum_le_integral, MonotoneOn.integral_le_sum, MonotoneOn.sum_le_integral_Ico, MonotoneOn.integral_le_sum_Ico, AntitoneOn.sum_le_integral, AntitoneOn.integral_le_sum, AntitoneOn.sum_le_integral_Ico, AntitoneOn.integral_le_sum_Ico
BANNED: sum_Ico_le_integral_of_le, integral_le_sum_Ico_of_le, sum_mul_Ico_le_integral_of_monotone_antitone, integral_le_sum_mul_Ico_of_antitone_monotone

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · piece   (milestone 1)
  1. Two facts first:
       hle : ↑k / N ≤ (↑k + 1) / N                                          R1, R2
       hw  : (↑k + 1) / N - ↑k / N = 1 / N                                  R3, then ring
  2. Split the ∧:                                                          constructor
  3. Lower half: compare the constant `f (↑k / N)` with `f` on the piece, forward,
       have h := R4 applied to hle, R5 (with μ := …), R6, and the pointwise bound
       `fun x hx => …` built from R7 (hx.1) and R8
     Upper half: the same with the two functions swapped and hx.2.
  4. Evaluate the constant's integral inside h:                             R9, R10, rw [hw] (all `at h`)
  5. h now has `1 / N * f (…)`, the goal `f (…) / N`: give linarith that equation   R11
-/
-- MILESTONE (optional: change or delete)
-- One piece `[k/N, (k+1)/N]` of width `1/N`: the integral lies between the endpoint values times `1/N`.
theorem piece (f : ℝ → ℝ) (hf : Monotone f) (N : ℝ) (hN : 0 < N) (k : ℕ) :
    f (k / N) / N ≤ ∫ x in (k / N)..((k + 1) / N), f x ∧
      ∫ x in (k / N)..((k + 1) / N), f x ≤ f ((k + 1) / N) / N := by
  have hle : (k : ℝ) / N ≤ (k + 1) / N := by gcongr; linarith
  have hw : (k + 1) / N - k / N = 1 / N := by field_simp; ring
  constructor
  · have := intervalIntegral.integral_mono_on hle (intervalIntegrable_const (μ := MeasureTheory.volume))
      hf.intervalIntegrable (fun x hx => hf hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hw] at this
    linarith [show f (k / N) / N = 1 / N * f (k / N) by ring]
  · have := intervalIntegral.integral_mono_on hle hf.intervalIntegrable
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun x hx => hf hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hw] at this
    linarith [show f ((k + 1) / N) / N = 1 / N * f ((k + 1) / N) by ring]

/- SKELETON · split_integral   (milestone 2)
  1. hN : (n + 1 : ℝ) ≠ 0                                                   R12
  2. Forward: h := R13 with the cut points a k = ↑k / (↑n + 1) and n + 1 pieces
     (named arguments, W4); integrability of each piece by R6               R13, R6
  3. Clean the casts in h, in one `simp only […] at h`:
       ↑(k + 1) → ↑k + 1,  ↑0 / _ → 0,  (↑n + 1) / (↑n + 1) → 1             R14, R15, R16
  4. h is now the statement read right to left:                             R17
-/
-- MILESTONE (optional: change or delete)
theorem split_integral (f : ℝ → ℝ) (hf : Monotone f) (n : ℕ) :
    ∫ x in (0 : ℝ)..1, f x =
      ∑ k ∈ Finset.range (n + 1), ∫ x in (k / (n + 1 : ℝ))..((k + 1) / (n + 1 : ℝ)), f x := by
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / (n + 1)) (n := n + 1) (fun k _ => hf.intervalIntegrable)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hN] at this
  exact this.symm

/- SKELETON · upper_sum   (milestone 3)
  1. hN : (n + 1 : ℝ) ≠ 0                                                   R12
  2. tel := the telescoping sum of k ↦ f (↑k / (↑n + 1)) up to n + 1         R18
  3. Clean tel's casts as in split_integral (f 1 - f 0 appears)              R14, R15, R16
  4. Split the sum of differences in tel:                                   R19 (at tel)
  5. Goal: unfold leftSum, then make each side one fraction over ↑n + 1:     R20, R21 (←), R22 (←)
  6. Strip the common denominator and finish with tel:                      R23, R2
-/
-- MILESTONE (optional: change or delete)
theorem upper_sum (f : ℝ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f ((k + 1) / (n + 1 : ℝ)) / (n + 1) =
      leftSum f n + (f 1 - f 0) / (n + 1) := by
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  have tel := Finset.sum_range_sub (fun k : ℕ => f (k / (n + 1 : ℝ))) (n + 1)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hN] at tel
  rw [Finset.sum_sub_distrib] at tel
  unfold leftSum
  rw [← Finset.sum_div, ← add_div]
  congr 1
  linarith

/- SKELETON · sandwich   (milestone 4; uses milestones 1–3)
  1. hN : (0 : ℝ) < ↑n + 1                                                  R12
  2. Split the ∧:                                                          constructor
  3. Left:  rw [split_integral …]; unfold leftSum and push `/ (↑n + 1)` into the sum;
            compare termwise with the lower half of `piece`                 R20, R21, R24
  4. Right: rw [split_integral …, ← upper_sum];
            compare termwise with the upper half of `piece`                 R24
-/
-- MILESTONE (optional: change or delete)
theorem sandwich (f : ℝ → ℝ) (hf : Monotone f) (n : ℕ) :
    leftSum f n ≤ ∫ x in (0 : ℝ)..1, f x ∧
      ∫ x in (0 : ℝ)..1, f x ≤ leftSum f n + (f 1 - f 0) / (n + 1) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  constructor
  · rw [split_integral f hf n]
    unfold leftSum
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun k _ => (piece f hf _ hN k).1
  · rw [split_integral f hf n, ← upper_sum]
    exact Finset.sum_le_sum fun k _ => (piece f hf _ hN k).2

/- SKELETON · riemann_monotone
  Prove the milestones first: piece, then split_integral and upper_sum, then sandwich.
  Only sandwich is used here.
  1. ε and hε : ε > 0 (`intro` sees through ConvergesTo):                   R25
  2. N with (f 1 - f 0) / ε < ↑N:                                           R26
  3. Give N; get n and hn : n ≥ N:                                          R27
  4. h1, h2: the two halves of sandwich f hf n                              R28
  5. hd : 0 ≤ f 1 - f 0       (monotonicity at `zero_le_one : 0 ≤ 1`)       R29, R8
     hn' : (N : ℝ) ≤ ↑n                                                     R30
  6. The key step, h3 : (f 1 - f 0) / (↑n + 1) < ε:
       clear the goal's denominator (side goal by R12), then hN's (with hε)  R31, R12, R31
       finish from hd, hn', hε (a product of hypotheses)                    R32
  7. |…| < ε → two inequalities, each linear in h1, h2, h3:                 R33, constructor, R2
-/
-- BEGIN SPEC
theorem riemann_monotone (f : ℝ → ℝ) (hf : Monotone f) :
    ConvergesTo (leftSum f) (∫ x in (0 : ℝ)..1, f x) :=
-- END SPEC
  by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((f 1 - f 0) / ε)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := sandwich f hf n
    have hd : 0 ≤ f 1 - f 0 := sub_nonneg.mpr (hf zero_le_one)
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    -- WHY: `(f 1 - f 0) / (n + 1) < ε` is the only analytic step; clear denominators and compare with `N`.
    have h3 : (f 1 - f 0) / (n + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hN
      nlinarith
    rw [abs_sub_lt_iff]
    constructor <;> linarith

end H048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work piece by piece: on `[k/N, (k+1)/N]` compare `f` with the constants `f (k/N)` and `f ((k+1)/N)`
    (monotonicity), and integrate a constant over an interval of width `1/N` (R4, R9). Then add the pieces
    up (R13, R24) and telescope the upper sum (R18). The gap `(f 1 - f 0)/(n+1)` goes to 0.
H2. `split_integral`: `sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / (n + 1)) (n := n + 1)`
    then `simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hN] at this`.
    `upper_sum`: `Finset.sum_range_sub (fun k : ℕ => f (k / (n + 1 : ℝ))) (n + 1)`, the same clean-up and
    `Finset.sum_sub_distrib` at it; then `unfold leftSum; rw [← Finset.sum_div, ← add_div]; congr 1`.
    `sandwich`: `rw [split_integral f hf n]` and `Finset.sum_le_sum fun k _ => (piece f hf _ hN k).1` (`.2`).
H3. `piece`: `have := intervalIntegral.integral_mono_on hle (intervalIntegrable_const (μ := MeasureTheory.volume))
    hf.intervalIntegrable (fun x hx => hf hx.1)`, then `rw [intervalIntegral.integral_const, smul_eq_mul, hw] at this`
    with `hw : (k + 1) / N - k / N = 1 / N`. Main: `obtain ⟨N, hN⟩ := exists_nat_gt ((f 1 - f 0) / ε)`;
    `have h3 : (f 1 - f 0) / (n + 1) < ε` by `rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hε] at hN; nlinarith`
    (with `0 ≤ f 1 - f 0` and `(N : ℝ) ≤ n` in context), then `rw [abs_sub_lt_iff]; constructor <;> linarith`.
-/
