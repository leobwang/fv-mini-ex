/- Guide for M086 (Gaussian tail bound).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `g : T → G` (or `h`) in an entry is only there to finish the example; it shows what the
step produced.
Part W: worked combinations on objects that are NOT the exercise's (another exponent, a Gaussian with
mean `m` and a fixed `t = 1`).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory
open scoped NNReal

namespace M086Guide

/-! # Part R · Reference entries -/

/-! ## Facts about the numbers -/

/-! ### R1. `have hv' : (0 : ℝ) < v := hv` (lemma `NNReal.coe_pos`) · context gains the fact on `↑v`
`v : ℝ≥0` is a nonnegative real; `↑v : ℝ` is the same number seen in `ℝ`. `0 < ↑v` and `0 < v` are
the same statement (`NNReal.coe_pos : 0 < ↑r ↔ 0 < r` is true by unfolding), so `hv` itself is a proof. -/
example (v : ℝ≥0) (hv : 0 < v) (G : Prop) (g : (0 : ℝ) < v → G) : G := by
  have hv' : (0 : ℝ) < v := hv
  exact g hv'

/-! ### R2. `set t : ℝ := e with ht` · context gains `t : ℝ := e` and `ht : t = e`; goal: `e` → `t` -/
example (a b : ℝ) (P : ℝ → Prop) (h : ∀ x, P x) : P (a / b) := by
  set t : ℝ := a / b with ht
  exact h t

/-! ### R3. `div_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a / b` · context gains `0 ≤ a / b` -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (G : Prop) (g : 0 ≤ a / b → G) : G := by
  have hab : 0 ≤ a / b := div_nonneg ha hb
  exact g hab

/-! ### R4. `h.le` (lemma `LT.lt.le`) · `a < b → a ≤ b` · context gains `a ≤ b` -/
example (a b : ℝ) (h : a < b) (G : Prop) (g : a ≤ b → G) : G := by
  have h' : a ≤ b := h.le
  exact g h'

/-! ## The moment generating function of a Gaussian -/

/-! ### R5. `HasLaw.map_eq` · `HasLaw X ν μ → Measure.map X μ = ν` · context gains the law as an equation -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (ν : Measure ℝ)
    (hX : HasLaw X ν μ) (G : Prop) (g : μ.map X = ν → G) : G := by
  have hmap : μ.map X = ν := hX.map_eq
  exact g hmap

/-! ### R6. `mgf_gaussianReal` · `Measure.map X μ = gaussianReal m v → mgf X μ t = exp (m t + v t² / 2)`
· goal: `mgf X μ t` → the explicit exponential -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hmap : μ.map X = gaussianReal m v) (t : ℝ) (P : ℝ → Prop)
    (h : P (Real.exp (m * t + v * t ^ 2 / 2))) : P (mgf X μ t) := by
  rw [mgf_gaussianReal hmap]
  exact h

/-! ### R7. `simp` (lemmas `zero_mul`, `zero_add`) · goal: `0 * t + c` → `c` -/
example (t c : ℝ) (P : ℝ → Prop) (h : P c) : P (0 * t + c) := by
  simp
  exact h

/-! ### R8. `mgf_pos_iff` · `0 < mgf X μ t ↔ Integrable (fun ω => exp (t * X ω)) μ`
· goal: integrability → positivity of the mgf (with `apply mgf_pos_iff.mp`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (t : ℝ) (hpos : 0 < mgf X μ t) : Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply mgf_pos_iff.mp
  exact hpos

/-! ### R9. `Real.exp_pos` · `0 < Real.exp x` · closes the goal -/
example (x : ℝ) : 0 < Real.exp x := by
  exact Real.exp_pos x

/-! ## The Chernoff bound -/

/-! ### R10. `calc` · goal `A ≤ C` → one goal per step whose proof is `?_` -/
example (A B C : ℝ) (h1 : A ≤ B) (h2 : B = C) : A ≤ C := by
  calc A ≤ B := h1
    _ = C := ?_
  exact h2

/-! ### R11. `measure_ge_le_exp_mul_mgf` (Chernoff) · goal: the tail bound → integrability
`μ.real {ω | a ≤ X ω} ≤ exp (-t * a) * mgf X μ t` from `0 ≤ t` and integrability of `exp (t X)`.
Given both arguments (`measure_ge_le_exp_mul_mgf a ht hint`) it is a complete proof term. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (a t : ℝ) (ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    μ.real {ω | a ≤ X ω} ≤ Real.exp (-t * a) * mgf X μ t := by
  apply measure_ge_le_exp_mul_mgf a ht
  exact hint

/-! ## The exponent -/

/-! ### R12. `Real.exp_add` · `exp (x + y) = exp x * exp y`; right to left: `rw [← Real.exp_add]` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R13. `congr 1` · goal `f a = f b` → `a = b` -/
example (a b : ℝ) : Real.exp (a + b) = Real.exp (b + a) := by
  congr 1
  ring

/-! ### R14. `field_simp` · goal: denominators cleared (needs each denominator `≠ 0`, e.g. `0 < b`, in context) -/
example (a b : ℝ) (hb : 0 < b) : a / (3 * b) + a / b = 4 * a / (3 * b) := by
  field_simp
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An optimised exponent: `-t a + c t²` at `t = a / (2c)` equals `-a² / (4c)`: R14, then `ring` -/
example (a c : ℝ) (hc : 0 < c) :
    -(a / (2 * c)) * a + c * (a / (2 * c)) ^ 2 = -a ^ 2 / (4 * c) := by
  field_simp
  ring

/-! ### W2. Chernoff at the fixed value `t = 1` for `Y ~ N(m, w)`: R5, R6, R8, R9, R10, R11, R12, R13 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (m : ℝ) (w : ℝ≥0) (hY : HasLaw Y (gaussianReal m w) μ) (a : ℝ) :
    μ.real {ω | a ≤ Y ω} ≤ Real.exp (-a + m + w / 2) := by
  have hmgf : mgf Y μ 1 = Real.exp (m * 1 + w * 1 ^ 2 / 2) := mgf_gaussianReal hY.map_eq 1
  have hint : Integrable (fun ω => Real.exp (1 * Y ω)) μ :=
    mgf_pos_iff.mp (by rw [hmgf]; exact Real.exp_pos _)
  calc μ.real {ω | a ≤ Y ω} ≤ Real.exp (-1 * a) * mgf Y μ 1 :=
        measure_ge_le_exp_mul_mgf a zero_le_one hint
    _ = Real.exp (-a + m + w / 2) := ?_
  rw [hmgf, ← Real.exp_add]
  congr 1
  ring

end M086Guide
