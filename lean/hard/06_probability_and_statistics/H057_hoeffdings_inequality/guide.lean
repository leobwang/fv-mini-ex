/- Guide for H057 (Hoeffding's inequality).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one variable `Y`, other bounds).
Assumed: Lean basics (E001–E033), including `calc`, `have`, `funext`, `refine`, `ring`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H057Guide

/-! # Part R · Reference entries -/

/-! ## Hoeffding's lemma for one variable -/

/-! ### R1. `Measurable.aemeasurable` · closes the goal: measurable → almost-everywhere measurable -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y) :
    AEMeasurable Y μ := by
  exact hY.aemeasurable

/-! ### R2. `Filter.Eventually.of_forall` · goal: `∀ᵐ ω ∂μ, p ω` (almost surely) → `∀ ω, p ω` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop) (h : ∀ ω, p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  apply Filter.Eventually.of_forall
  exact h

/-! ### R3. `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero` (Hoeffding's lemma) · context gains the bound
The lemma is `protected`: write the full name even after `open ProbabilityTheory`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (c d s : ℝ) (hY : AEMeasurable Y μ) (hb : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc c d) (hm : μ[Y] = 0)
    (hs : 0 < s) (G : Prop) (k : mgf Y μ s ≤ Real.exp ((‖d - c‖₊ / 2) ^ 2 * s ^ 2 / 2) → G) : G := by
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hY hb hm hs
  exact k h

/-! ### R4. `convert h using k` · goal → goals for the places where it differs from `h`
`using k` stops after `k` levels of matching: a larger `k` leaves a smaller differing piece.
Each leftover goal reads `(piece of the goal) = (piece of h)`. -/
example (u v w : ℝ) (h : Real.exp (u / 2 * w) ≤ 1) (huv : v - u = 0) :
    Real.exp (v / 2 * w) ≤ 1 := by
  convert h using 2
  rw [show v = u by linarith]

example (u v w : ℝ) (h : Real.exp (u / 2 * w) ≤ 1) (huv : v - u = 0) :
    Real.exp (v / 2 * w) ≤ 1 := by
  convert h using 4
  linarith

/-! ## Turning `↑‖x‖₊` into `x` -/

/-! ### R5. `coe_nnnorm` · `↑‖a‖₊ = ‖a‖` · goal: the cast of the `ℝ≥0`-norm → the real norm -/
example (x : ℝ) (P : ℝ → Prop) (h : P ‖x‖) : P ‖x‖₊ := by
  rw [coe_nnnorm]
  exact h

/-! ### R6. `Real.norm_eq_abs` · `‖r‖ = |r|` · goal: norm of a real → absolute value -/
example (x : ℝ) (P : ℝ → Prop) (h : P |x|) : P ‖x‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R7. `abs_of_pos` · `0 < a → |a| = a` · goal rewritten, plus side goal `0 < a`
Write `rw [abs_of_pos (by linarith)]` to close the side goal on the spot. -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 < x) : P |x| := by
  rw [abs_of_pos]
  exact h
  exact hx

/-! ### R8. `linarith` · closes a linear (in)equality that follows from linear hypotheses -/
example (c d : ℝ) (hcd : c < d) : 0 < d - c := by
  linarith

/-! ## The mgf of an independent sum -/

/-! ### R9. `Finset.sum_apply` · goal: a sum of functions applied at `ω` → the sum of the values
`simp` uses it by itself; with `funext ω; simp` it proves `(fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i`. -/
example {Ω : Type} (s : Finset ℕ) (f : ℕ → Ω → ℝ) (ω : Ω) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, f i ω)) : P ((∑ i ∈ s, f i) ω) := by
  rw [Finset.sum_apply]
  exact h

/-! ### R10. `iIndepFun.mgf_sum` · goal: mgf of an independent sum → product of the mgfs
`hind.mgf_sum hY s : mgf (∑ i ∈ s, Y i) μ t = ∏ i ∈ s, mgf (Y i) μ t`. The sum is of *functions*. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ)
    (hY : ∀ i, Measurable (Y i)) (s : Finset ℕ) (t : ℝ) (P : ℝ → Prop)
    (h : P (∏ i ∈ s, mgf (Y i) μ t)) : P (mgf (∑ i ∈ s, Y i) μ t) := by
  rw [hind.mgf_sum hY]
  exact h

/-! ### R11. `Real.exp_nat_mul` · `exp (↑m * x) = exp x ^ m` · goal -/
example (x : ℝ) (m : ℕ) (P : ℝ → Prop) (h : P (Real.exp x ^ m)) : P (Real.exp (m * x)) := by
  rw [Real.exp_nat_mul]
  exact h

/-! ### R12. `Finset.prod_le_prod` · goal `∏ f ≤ ∏ g` → two goals: `0 ≤ f i` and `f i ≤ g i` for `i ∈ s` -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  apply Finset.prod_le_prod
  exact h0
  exact h1

/-! ### R13. `mgf_nonneg` · closes `0 ≤ mgf Y μ t` (an mgf is an integral of `exp`, so `≥ 0`) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (t : ℝ) : 0 ≤ mgf Y μ t := by
  exact mgf_nonneg

/-! ### R14. `Finset.prod_const` · `∏ _ ∈ s, b = b ^ s.card` · goal -/
example (s : Finset ℕ) (b : ℝ) (P : ℝ → Prop) (h : P (b ^ s.card)) : P (∏ _i ∈ s, b) := by
  rw [Finset.prod_const]
  exact h

/-! ### R15. `Finset.card_range` · `(Finset.range m).card = m` · goal -/
example (m : ℕ) (P : ℕ → Prop) (h : P m) : P (Finset.range m).card := by
  rw [Finset.card_range]
  exact h

/-! ## Chernoff for the sum -/

/-! ### R16. `integrable_exp_mul_of_mem_Icc` · goal `Integrable (fun ω => exp (t * Y ω)) μ` → two goals
Name the bounds with `(a := c) (b := d)`: Lean would read them off the `∀ᵐ` argument, but that is `?_`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (c d t : ℝ) (hY : AEMeasurable Y μ) (hb : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc c d) :
    Integrable (fun ω => Real.exp (t * Y ω)) μ := by
  refine integrable_exp_mul_of_mem_Icc (a := c) (b := d) ?_ ?_
  exact hY
  exact hb

/-! ### R17. `Finset.measurable_sum` · goal: a finite sum of measurable functions is measurable → each term -/
example {Ω : Type} [MeasurableSpace Ω] (s : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) : Measurable fun ω => ∑ i ∈ s, f i ω := by
  apply Finset.measurable_sum
  exact fun i _ => hf i

/-! ### R18. `Set.mem_Icc` · `x ∈ Set.Icc c d ↔ c ≤ x ∧ x ≤ d` · goal → two goals with `⟨?_, ?_⟩`
A hypothesis `hx : x ∈ Set.Icc c d` gives `hx.1 : c ≤ x` and `hx.2 : x ≤ d`. -/
example (x c d : ℝ) (h1 : c ≤ x) (h2 : x ≤ d) : x ∈ Set.Icc c d := by
  refine ⟨?_, ?_⟩
  exact h1
  exact h2

/-! ### R19. `Finset.sum_le_sum` · goal `∑ f ≤ ∑ g` → `∀ i ∈ s, f i ≤ g i` -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  apply Finset.sum_le_sum
  exact h

/-! ### R20. `Finset.sum_const` · `∑ _ ∈ s, b = s.card • b` · goal (`•`: `ℕ`-multiple) -/
example (s : Finset ℕ) (b : ℝ) (P : ℝ → Prop) (h : P (s.card • b)) : P (∑ _i ∈ s, b) := by
  rw [Finset.sum_const]
  exact h

/-! ### R21. `nsmul_eq_mul` · `m • a = ↑m * a` · goal: `ℕ`-multiple → product with the cast -/
example (m : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (m * a)) : P (m • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R22. `measure_ge_le_exp_mul_mgf` (Chernoff) · goal `μ.real {ω | ε ≤ Y ω} ≤ exp (-t * ε) * mgf Y μ t`
→ two goals: `0 ≤ t` and integrability of `exp (t * Y)`. Give `ε` explicitly. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (e t : ℝ) (ht : 0 ≤ t) (hi : Integrable (fun ω => Real.exp (t * Y ω)) μ) :
    μ.real {ω | e ≤ Y ω} ≤ Real.exp (-t * e) * mgf Y μ t := by
  apply measure_ge_le_exp_mul_mgf e
  exact ht
  exact hi

/-! ### R23. `LT.lt.le` · `h : a < b` gives `h.le : a ≤ b` · closes the goal -/
example (t : ℝ) (ht : 0 < t) : 0 ≤ t := by
  exact ht.le

/-! ### R24. `gcongr` · goal `c * A ≤ c * B` → `A ≤ B` (side goal `0 ≤ c` closed by itself)
If a hypothesis is exactly `A ≤ B`, `gcongr` uses it and closes the goal. -/
example (u A B : ℝ) (h : A - B ≤ 0) : Real.exp u * A ≤ Real.exp u * B := by
  gcongr
  linarith

/-! ### R25. `Real.exp_add` · `exp (x + y) = exp x * exp y`; right to left merges two exponentials -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ## Choosing `t` -/

/-! ### R26. `positivity` · closes `0 < e` / `0 ≤ e` for `e` built from `+ * / ^`, casts, `exp`;
it uses hypotheses `0 < x` about the atoms `x` -/
example (x y : ℝ) (m : ℕ) (hx : 0 < x) (hy : 0 < y) (hm : 0 < m) : 0 < x / (m * y ^ 2) := by
  positivity

/-! ### R27. `LE.le.trans_eq` · `a ≤ b → b = c → a ≤ c` · goal `a ≤ c` → `b = c` -/
example (A B C : ℝ) (h₁ : A ≤ B) (h₂ : B = C) : A ≤ C := by
  refine h₁.trans_eq ?_
  exact h₂

/-! ### R28. `congr 1` · goal `f x = f y` → `x = y`
If a hypothesis is exactly `x = y`, `congr 1` uses it and closes the goal. -/
example (u v : ℝ) (h : u - v = 0) : Real.exp u = Real.exp v := by
  congr 1
  linarith

/-! ### R29. `field_simp` · goal: clear the denominators (it needs them `≠ 0`, from hypotheses `0 < y`) -/
example (e y : ℝ) (he : 0 < e) (hy : 0 < y) : -(e / y) * e + (e / y) ^ 2 * y / 2 = -e ^ 2 / (2 * y) := by
  field_simp
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `↑‖x - 1‖₊ = x - 1` for `1 < x`: R5, R6, R7 with R8 -/
example (x : ℝ) (hx : 1 < x) : (‖x - 1‖₊ : ℝ) = x - 1 := by
  rw [coe_nnnorm]
  rw [Real.norm_eq_abs]
  rw [abs_of_pos (by linarith)]

/-! ### W2. A sum of `m` terms each `≤ d` is `≤ m * d`: `calc` with R19, then `simp` (R20, R15, R21) -/
example (m : ℕ) (f : ℕ → ℝ) (d : ℝ) (hf : ∀ i, f i ≤ d) : ∑ i ∈ Finset.range m, f i ≤ m * d := by
  calc ∑ i ∈ Finset.range m, f i ≤ ∑ i ∈ Finset.range m, d := Finset.sum_le_sum fun i _ => hf i
    _ = m * d := by simp

/-! ### W3. Chernoff for one bounded variable `Y ∈ [-1, 1]`: R22 with R23, R16, R1, R2 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hb : ∀ ω, Y ω ∈ Set.Icc (-1) 1) (e t : ℝ) (ht : 0 < t) :
    μ.real {ω | e ≤ Y ω} ≤ Real.exp (-t * e) * mgf Y μ t :=
  measure_ge_le_exp_mul_mgf e ht.le
    (integrable_exp_mul_of_mem_Icc (a := -1) (b := 1) hY.aemeasurable (Filter.Eventually.of_forall hb))

/-! ### W4. `exp (-t) * exp (t ^ 2) ≤ exp (-t) * exp B` from `t ^ 2 ≤ B`, then merge: R24, R25 -/
example (t B : ℝ) (h : t ^ 2 ≤ B) : Real.exp (-t) * Real.exp (t ^ 2) ≤ Real.exp (-t + B) := by
  rw [Real.exp_add]
  gcongr

end H057Guide
