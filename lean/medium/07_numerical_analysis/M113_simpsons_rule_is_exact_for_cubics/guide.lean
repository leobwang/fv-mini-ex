/- Guide for M113 (Simpson's rule is exact for cubics).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (lines, quadratics, the trapezoid rule).
Assumed: Lean basics.
-/
import Mathlib

namespace M113Guide

/-! # Part R · Reference entries -/

/-! ## Setting up -/

/-! ### R1. `unfold D` · goal: the defined name `D` → its body, also under `∫` -/
def sq (x : ℝ) : ℝ := x * x
example (a b : ℝ) (P : ℝ → Prop) (h : P (∫ x in a..b, x * x)) : P (∫ x in a..b, sq x) := by
  unfold sq
  exact h

/-! ### R2. `have i : ∀ (n : ℕ) (c : ℝ), T n c := fun n c => …` · context gains a family of facts
`i 3 c` is then the fact `T 3 c`, for any `c`. -/
example (T : ℕ → ℝ → Prop) (t : ∀ n c, T n c) (G : Prop) (c : ℝ) (g : T 3 c → G) : G := by
  have i : ∀ (n : ℕ) (c : ℝ), T n c := fun n c => t n c
  exact g (i 3 c)

/-! ## Integrability -/

/-! ### R3. `Continuous.intervalIntegrable` · goal: integrable on `[a, b]` → continuous
Statement: `Continuous u → ∀ (a b : ℝ), IntervalIntegrable u μ a b`. As a term:
`Continuous.intervalIntegrable hu a b`. -/
example (f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f) : IntervalIntegrable f MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact hf

/-! ### R4. `fun_prop` · closes `Continuous (fun x => …)` built from `+`, `*`, `^`, constants -/
example (c : ℝ) (n : ℕ) : Continuous (fun x : ℝ => c * x ^ n) := by
  fun_prop

/-! ### R5. `intervalIntegrable_const` · closes integrability of a constant function -/
example (c a b : ℝ) : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := by
  exact intervalIntegrable_const

/-! ## Splitting and evaluating integrals -/

/-! ### R6. `intervalIntegral.integral_add hf hg` · goal: `∫ f x + g x` → `∫ f x + ∫ g x`
Statement: `IntervalIntegrable f μ a b → IntervalIntegrable g μ a b →
  ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ`. -/
example (f g : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) (P : ℝ → Prop)
    (h : P ((∫ x in a..b, f x) + ∫ x in a..b, g x)) : P (∫ x in a..b, f x + g x) := by
  rw [intervalIntegral.integral_add hf hg]
  exact h

/-! ### R7. `intervalIntegral.integral_const_mul` · goal: `∫ r * f x` → `r * ∫ f x` -/
example (r : ℝ) (f : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (r * ∫ x in a..b, f x)) :
    P (∫ x in a..b, r * f x) := by
  rw [intervalIntegral.integral_const_mul]
  exact h

/-! ### R8. `integral_pow` · goal: `∫ x ^ n` → `(b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)`
`↑n` is the natural number `n` cast into `ℝ`. -/
example (n : ℕ) (a b : ℝ) (P : ℝ → Prop) (h : P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))) :
    P (∫ x in a..b, x ^ n) := by
  rw [integral_pow]
  exact h

/-! ### R9. `intervalIntegral.integral_const` · goal: `∫ c` → `(b - a) • c` -/
example (c a b : ℝ) (P : ℝ → Prop) (h : P ((b - a) • c)) : P (∫ _ in a..b, c) := by
  rw [intervalIntegral.integral_const]
  exact h

/-! ### R10. `smul_eq_mul` · goal: `r • c` → `r * c` (scalar action of `ℝ` on itself is `*`) -/
example (r c : ℝ) (P : ℝ → Prop) (h : P (r * c)) : P (r • c) := by
  rw [smul_eq_mul]
  exact h

/-! ### R11. `integral_id` · goal: `∫ x` → `(b ^ 2 - a ^ 2) / 2` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P ((b ^ 2 - a ^ 2) / 2)) : P (∫ x in a..b, x) := by
  rw [integral_id]
  exact h

/-! ## Closing -/

/-! ### R12. `ring` · closes a polynomial identity; numerals, `/ 6`, and casts `↑2` of numerals included -/
example (a b : ℝ) :
    (b ^ (2 + 1) - a ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ) = (b - a) * (a ^ 2 + a * b + b ^ 2) / 3 := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `simp only` with R7 and R8 rewrites `∫ d * x ^ 2`, but leaves `∫ e * x` (bare `x`) alone
`simp` cannot read `fun x => e * x` as `fun x => e * f x`; `rw` can (W2). -/
example (d e a b : ℝ) :
    (∫ x in a..b, d * x ^ 2) + ∫ x in a..b, e * x =
      d * ((b ^ 3 - a ^ 3) / 3) + e * ((b ^ 2 - a ^ 2) / 2) := by
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ### W2. The trapezoid rule is exact for lines: R6 (with R5, R3, R4), R9, R10, R7, R11, R12 -/
example (d e a b : ℝ) :
    ∫ x in a..b, d + e * x = (b - a) / 2 * ((d + e * a) + (d + e * b)) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) a b)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ### W3. Split the LAST `+` first: `p + q + r` is `(p + q) + r` -/
example (d e a b : ℝ) :
    ∫ x in a..b, d * x + e * x ^ 2 + x ^ 3 =
      (∫ x in a..b, d * x + e * x ^ 2) + ∫ x in a..b, x ^ 3 := by
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) a b)
    (Continuous.intervalIntegrable (by fun_prop) a b)]

end M113Guide
