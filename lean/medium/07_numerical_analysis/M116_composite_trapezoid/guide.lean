/- Guide for M116 (Composite trapezoid from the panel bound).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" (or of a hypothesis): the step changes only the part shown
inside `P (…)`. A hypothesis `h` or `g` in an entry is only there to finish the example.
Part W: worked combinations on objects that are NOT the exercise's (unit panels, abstract sums).
Assumed: Lean basics.
-/
import Mathlib

namespace M116Guide

/-! # Part R · Reference entries -/

/-! ## Splitting one integral into panel integrals -/

/-! ### R1. `intervalIntegral.sum_integral_adjacent_intervals` · context gains `hsum`
`∑ k ∈ range n, ∫ x in u k..u (k+1), f x = ∫ x in u 0..u n, f x`, given integrability on each panel.
The named arguments `(μ := …) (f := …) (a := …) (n := …)` choose the measure, the integrand, the nodes
`a : ℕ → ℝ` and the number of panels; the last, unnamed argument is the integrability proof. -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hu : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (u k) (u (k + 1))) (G : Prop) (g : G) :
    G := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := u) (n := n) hu
  exact g

/-! ### R2. `Continuous.intervalIntegrable` · closes the integrability goal R1 asks for
`hf.intervalIntegrable x y : IntervalIntegrable f volume x y` for `hf : Continuous f`, any `x y`. -/
example (f : ℝ → ℝ) (hf : Continuous f) (u : ℕ → ℝ) (n : ℕ) :
    ∀ k < n, IntervalIntegrable f MeasureTheory.volume (u k) (u (k + 1)) := by
  exact fun k _ => hf.intervalIntegrable _ _

/-! ### R3. `simp only [Nat.cast_zero, zero_mul, add_zero] at hp` · context: `a + ↑0 * h` → `a`
`Nat.cast_zero : ((0 : ℕ) : R) = 0`, `zero_mul : 0 * x = 0`, `add_zero : x + 0 = x`. -/
example (a h : ℝ) (G : Prop) (P : ℝ → Prop) (hp : P (a + ((0 : ℕ) : ℝ) * h)) (g : P a → G) : G := by
  simp only [Nat.cast_zero, zero_mul, add_zero] at hp
  exact g hp

/-! ### R4. `Nat.cast_succ` · `↑(k + 1) = ↑k + 1` (cast of a successor); here used `at hp` · context -/
example (k : ℕ) (G : Prop) (P : ℝ → Prop) (hp : P ((k + 1 : ℕ) : ℝ)) (g : P ((k : ℝ) + 1) → G) :
    G := by
  simp only [Nat.cast_succ] at hp
  exact g hp

/-! ## Sums and absolute values -/

/-! ### R5. `Finset.sum_sub_distrib` · `∑ (u i - v i) = ∑ u i - ∑ v i`; `rw [← …]` merges · goal -/
example {ι G : Type} [AddCommGroup G] (s : Finset ι) (u v : ι → G) (P : G → Prop)
    (h : P (∑ i ∈ s, (u i - v i))) : P (∑ i ∈ s, u i - ∑ i ∈ s, v i) := by
  rw [← Finset.sum_sub_distrib]
  exact h

/-! ### R6. `calc` · goal `a ≤ d` → one goal per step (here left open with `?_`)
`_` as the first term means the goal's left side; `_ = _` in the last step means "up to the goal's
right side". Steps chain `≤`/`=` into `≤`. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c = d) : a ≤ d := by
  calc _ ≤ b := ?_
    _ ≤ c := ?_
    _ = _ := ?_
  exacts [h1, h2, h3]

/-! ### R7. `Finset.abs_sum_le_sum_abs` · closes `|∑ i ∈ s, u i| ≤ ∑ i ∈ s, |u i|` (triangle inequality) -/
example {ι : Type} (s : Finset ι) (u : ι → ℝ) : |∑ i ∈ s, u i| ≤ ∑ i ∈ s, |u i| := by
  exact Finset.abs_sum_le_sum_abs _ _

/-! ### R8. `gcongr with k hk` · goal `∑ u ≤ ∑ v` → termwise `u k ≤ v k`; context gains `k`, `hk` -/
example {ι : Type} (s : Finset ι) (u v : ι → ℝ) (h : ∀ i ∈ s, u i ≤ v i) :
    ∑ i ∈ s, u i ≤ ∑ i ∈ s, v i := by
  gcongr with k hk
  exact h k hk

/-! ## Using the per-panel bound -/

/-! ### R9. `have := hall x` · context gains `this : Q x` (instantiate a `∀` hypothesis) -/
example (Q : ℝ → Prop) (hall : ∀ y, Q y) (x : ℝ) (G : Prop) (g : Q x → G) : G := by
  have := hall x
  exact g this

/-! ### R10. `rw [show e₁ = e₂ by ring] at hp` · context: `e₁` → `e₂` inside `hp`
`show e₁ = e₂ by ring` is a term: an equation proved on the spot. -/
example (x c y : ℝ) (G : Prop) (P : ℝ → Prop) (hp : P (x + c * y + y)) (g : P (x + (c + 1) * y) → G) :
    G := by
  rw [show x + c * y + y = x + (c + 1) * y by ring] at hp
  exact g hp

/-! ### R11. `rwa [e] at hp` · closes the goal: `rw [e] at hp`, then `hp` is exactly the goal -/
example (x z : ℝ) (P : ℝ → Prop) (e : x = z) (hp : P x) : P z := by
  rwa [e] at hp

/-! ### R12. `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul` · goal: sum of a constant → `↑n * c`
`sum_const : ∑ _x ∈ s, c = s.card • c`, `card_range : (range n).card = n`, `nsmul_eq_mul : n • c = ↑n * c`.
`simp` applies all three by itself. -/
example (n : ℕ) (c : ℝ) (P : ℝ → Prop) (h : P (n * c)) : P (∑ _i ∈ Finset.range n, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_range]
  rw [nsmul_eq_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Unit panels `[k, k+1]` on `[0, n]`: R1 with R2, then R3/R4 to tidy the casts -/
example (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k : ℝ) + 1, f x = ∫ x in (0 : ℝ)..(n : ℝ), f x := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f)
    (a := fun k : ℕ => (k : ℝ)) (n := n) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, Nat.cast_succ] at hsum
  exact hsum

/-! ### W2. A sum of errors each `≤ ε`: R5, then `calc` with R7, R8 + R9, R12 -/
example (u v : ℕ → ℝ) (ε : ℝ) (n : ℕ) (hε : ∀ k, |u k - v k| ≤ ε) :
    |∑ k ∈ Finset.range n, u k - ∑ k ∈ Finset.range n, v k| ≤ n * ε := by
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range n, |u k - v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ε := by
        gcongr with k
        have := hε k
        exact this
    _ = _ := by simp

end M116Guide
