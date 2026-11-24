/- Guide for E106 (Interval integrals).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on integrands that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

namespace E106Guide

/-! # Part R · Reference entries -/

/-! ## The power rule -/

/-! ### R1. `integral_pow` · goal: `∫ x in a..b, x ^ n` → `(b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)` -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))) :
    P (∫ x in a..b, x ^ n) := by
  rw [integral_pow]
  exact h

/-! ### R2. `norm_num` · closes a goal made of numerals: powers, `/`, and casts `↑k` of numerals -/
example : ((2 : ℝ) ^ (3 + 1) - 0 ^ (3 + 1)) / (((3 : ℕ) : ℝ) + 1) = 4 := by norm_num

/-! ## Linearity: splitting a sum, pulling out a factor -/

/-! ### R3. `intervalIntegral.integral_add hf hg` · goal: integral of a sum → sum of integrals
`hf`, `hg` prove that each summand is integrable on `[a, b]`. -/
example (f g : ℝ → ℝ) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) (P : ℝ → Prop)
    (h : P ((∫ x in a..b, f x) + ∫ x in a..b, g x)) : P (∫ x in a..b, (f x + g x)) := by
  rw [intervalIntegral.integral_add hf hg]
  exact h

/-! ### R4. `Continuous.intervalIntegrable` · goal: `IntervalIntegrable u volume a b` → `Continuous u`
As a term: `Continuous.intervalIntegrable hu a b`; inside `rw [...]` write `_ _` for `a b`. -/
example (u : ℝ → ℝ) (a b : ℝ) (hu : Continuous u) : IntervalIntegrable u MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact hu

/-! ### R5. `fun_prop` · closes `Continuous (fun x => …)` built from `+`, `*`, `^`, constants and `x` -/
example (k : ℝ) : Continuous fun x : ℝ => k * x + x ^ 3 := by fun_prop

/-! `fun x => k * x` may print as `HMul.hMul k` (the same function, written without `fun`): this is
what `case hf` shows after a bare `rw [intervalIntegral.integral_add]` on `∫ (k * x + …)`.
R4 then R5 handle it the same way. -/
example (k a b : ℝ) : IntervalIntegrable (HMul.hMul k) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

/-! ### R6. `intervalIntegrable_const` · closes `IntervalIntegrable (fun x => c) volume a b` -/
example (c a b : ℝ) : IntervalIntegrable (fun _ => c) MeasureTheory.volume a b := by
  exact intervalIntegrable_const

/-! ### R7. `intervalIntegral.integral_const_mul` · goal: `∫ r * f x` → `r * ∫ f x` -/
example (r : ℝ) (f : ℝ → ℝ) (a b : ℝ) (P : ℝ → Prop) (h : P (r * ∫ x in a..b, f x)) :
    P (∫ x in a..b, r * f x) := by
  rw [intervalIntegral.integral_const_mul]
  exact h

/-! ## Basic integrals -/

/-! ### R8. `integral_id` · goal: `∫ x in a..b, x` → `(b ^ 2 - a ^ 2) / 2` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P ((b ^ 2 - a ^ 2) / 2)) : P (∫ x in a..b, x) := by
  rw [integral_id]
  exact h

/-! ### R9. `intervalIntegral.integral_const` · goal: `∫ x in a..b, c` → `(b - a) • c` -/
example (c a b : ℝ) (P : ℝ → Prop) (h : P ((b - a) • c)) : P (∫ _ in a..b, c) := by
  rw [intervalIntegral.integral_const]
  exact h

/-! ### R10. `smul_eq_mul` · goal: `a • b` → `a * b` (scalar action of a type on itself) -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R11. `ring` · closes an identity of commutative rings (here: polynomial identities in `ℝ`) -/
example (k a b : ℝ) : k * ((b ^ 2 - a ^ 2) / 2) = k * (b - a) * (a + b) / 2 := by ring

/-! ## Integrability of a scaled function -/

/-! ### R12. `IntervalIntegrable.const_mul` · goal: integrability of `fun x => c * f x` → of `f`
As a term: `hf.const_mul c` (dot notation: `hf : IntervalIntegrable f …`). -/
example (f : ℝ → ℝ) (a b c : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => c * f x) MeasureTheory.volume a b := by
  apply IntervalIntegrable.const_mul
  exact hf

/-! # Part W · Worked combinations (not the exercise's integrands) -/

/-! ### W1. Power rule, then numerals: R1, R2 -/
example : ∫ x in (0 : ℝ)..2, x ^ 3 = 4 := by
  rw [integral_pow]
  norm_num

/-! ### W2. Bare `rw [intervalIntegral.integral_add]` leaves the two integrability facts as goals
`case hf` and `case hg`, proved afterwards: R3, then R7, R1, R9, R10, R2, R11; then R4 → R5 and R6. -/
example (k c a b : ℝ) :
    ∫ x in a..b, (k * x ^ 2 + c) = k * (b ^ 3 - a ^ 3) / 3 + (b - a) * c := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const,
      smul_eq_mul]
    norm_num
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) a b
  · exact intervalIntegrable_const

/-! ### W3. A known integral as a hypothesis: R3 with R4 → R5 and `hg`, then R8, `rw [hI]` -/
example (g : ℝ → ℝ) (a b : ℝ) (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hI : ∫ x in a..b, g x = 5) : ∫ x in a..b, (x + g x) = (b ^ 2 - a ^ 2) / 2 + 5 := by
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) hg]
  rw [integral_id, hI]

end E106Guide
