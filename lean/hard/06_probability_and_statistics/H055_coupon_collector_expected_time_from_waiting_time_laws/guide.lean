/- Guide for H055 (Coupon collector: expected time from waiting-time laws).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact from a lemma (`hX.map_eq`, `hf.add hg`, …) use `have h := …`, so the
context gains `h` and you can read off exactly what the lemma produced.
Part W: worked combinations on objects that are NOT the exercise's (other sums, other laws).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H055Guide

/-! # Part R · Reference entries -/

/-! ## The geometric law: from an integral to a series -/

/-! ### R1. `integral_geometricMeasure` · goal: `∫ … ∂geometricMeasure p` → a series `∑'`
`p ≠ 0 → ∫ n, f n ∂geometricMeasure p = ∑' n, ((1 - ↑p) ^ n * ↑p) • f n` -/
example (p : unitInterval) (hp : p ≠ 0) (f : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑' n, ((1 - (p : ℝ)) ^ n * p) • f n)) : P (∫ n, f n ∂geometricMeasure p) := by
  rw [integral_geometricMeasure hp]
  exact h

/-! ### R2. `p.2.1`, `p.2.2` · context gains the bounds `0 ≤ ↑p`, `↑p ≤ 1` of `p : unitInterval` -/
example (p : unitInterval) : 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 1 := by
  have h1 := p.2.1
  have h2 := p.2.2
  exact ⟨h1, h2⟩

/-! ### R3. `apply Subtype.ext` · goal `p = q` (in `unitInterval`) → `↑p = ↑q` (in `ℝ`) -/
example (p q : unitInterval) (h : (p : ℝ) = q) : p = q := by
  apply Subtype.ext
  exact h

/-! ### R4. `apply lt_of_le_of_ne` · `a ≤ b → a ≠ b → a < b` · goal `a < b` → two goals -/
example (a b : ℝ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  apply lt_of_le_of_ne
  exact h1
  exact h2

/-! ### R5. `Real.norm_eq_abs` · goal: `‖r‖` → `|r|` (on `ℝ` the norm is the absolute value) -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R6. `abs_lt` · `|a| < b ↔ -b < a ∧ a < b` · goal -/
example (a b : ℝ) (h : -b < a ∧ a < b) : |a| < b := by
  rw [abs_lt]
  exact h

/-! ### R7. `linarith [t]` · closes a linear (in)equality from the hypotheses and the extra fact `t` -/
example (a b : ℝ) (hb : b ≤ 1) (ha : 0 < a) : a - b > -1 := by
  linarith [hb]

/-! ### R8. `funext n` · goal `f = g` (functions) → `f n = g n` for a new `n` -/
example (f g : ℕ → ℝ) (h : ∀ n, f n = g n) : f = g := by
  funext n
  exact h n

/-! ### R9. `smul_eq_mul` · goal: `a • b` → `a * b` (scalar action of `ℝ` on itself is `*`) -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R10. `tsum_mul_left` · `∑' x, a * f x = a * ∑' x, f x` · goal: pull a constant out of `∑'` -/
example (a : ℝ) (f : ℕ → ℝ) (P : ℝ → Prop) (h : P (a * ∑' n, f n)) : P (∑' n, a * f n) := by
  rw [tsum_mul_left]
  exact h

/-! ### R11. `tsum_coe_mul_geometric_of_norm_lt_one` · `‖r‖ < 1 → ∑' n, ↑n * r ^ n = r / (1 - r) ^ 2` -/
example (r : ℝ) (hr : ‖r‖ < 1) (P : ℝ → Prop) (h : P (r / (1 - r) ^ 2)) :
    P (∑' n : ℕ, (n : ℝ) * r ^ n) := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
  exact h

/-! ### R12. `sub_sub_cancel` · `a - (a - b) = b` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P b) : P (a - (a - b)) := by
  rw [sub_sub_cancel]
  exact h

/-! ### R13. `field_simp` · goal: clears denominators that the context shows are nonzero
It reads `hb : 0 < b` or `hb : b ≠ 0` from the context. What is left is closed by `field_simp`
itself or by `ring`. -/
example (a b : ℝ) (hb : 0 < b) : b * (a / b ^ 2) = a / b := by
  field_simp

/-! ## Integrability as summability -/

/-! ### R14. `integrable_geometricMeasure_iff` · goal: `Integrable f (geometricMeasure p)` → `Summable …`
`p ≠ 0 → (Integrable f (geometricMeasure p) ↔ Summable fun n => (1 - ↑p) ^ n * ↑p * ‖f n‖)` -/
example (p : unitInterval) (hp : p ≠ 0) (f : ℕ → ℝ)
    (h : Summable fun n => (1 - (p : ℝ)) ^ n * p * ‖f n‖) : Integrable f (geometricMeasure p) := by
  rw [integrable_geometricMeasure_iff hp]
  exact h

/-! ### R15. `Real.norm_natCast` · `‖(↑n : ℝ)‖ = ↑n` · goal -/
example (n : ℕ) (P : ℝ → Prop) (h : P n) : P ‖(n : ℝ)‖ := by
  rw [Real.norm_natCast]
  exact h

/-! ### R16. `summable_pow_mul_geometric_of_norm_lt_one k hr` · context gains `Summable fun n => ↑n ^ k * r ^ n` -/
example (r : ℝ) (hr : ‖r‖ < 1) (k : ℕ) : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n := by
  have h := summable_pow_mul_geometric_of_norm_lt_one k hr
  exact h

/-! ### R17. `Summable.mul_left a` · from `hf : Summable f`, context gains `Summable fun i => a * f i` -/
example (f : ℕ → ℝ) (a : ℝ) (hf : Summable f) : Summable fun i => a * f i := by
  have h := hf.mul_left a
  exact h

/-! ## Facts about naturals cast into `ℝ` -/

/-! ### R18. `intro k hk h` on `∀ k < n, Q k ≠ 0` · `≠` is `→ False`, so `h : Q k = 0` and goal `False` -/
example (n : ℕ) (Q : ℕ → ℝ) (hQ : ∀ k < n, Q k = 0 → False) : ∀ k < n, Q k ≠ 0 := by
  intro k hk h
  exact hQ k hk h

/-! ### R19. `exact_mod_cast hk` · closes `↑k < ↑n` in `ℝ` from `hk : k < n` in `ℕ` -/
example (k n : ℕ) (hk : k < n) : (k : ℝ) < n := by
  exact_mod_cast hk

/-! ### R20. `Set.Icc.coe_zero` · `↑(0 : unitInterval) = (0 : ℝ)` · context, with `rw … at h` -/
example (x : ℝ) (G : Prop) (h : ((0 : unitInterval) : ℝ) = x) (g : (0 : ℝ) = x → G) : G := by
  rw [Set.Icc.coe_zero] at h
  exact g h

/-! ### R21. `eq_comm` · `a = b ↔ b = a` · context: flip an equation with `rw [eq_comm] at h` -/
example (a b : ℝ) (G : Prop) (h : a = b) (g : b = a → G) : G := by
  rw [eq_comm] at h
  exact g h

/-! ### R22. `div_eq_zero_iff` · `a / b = 0 ↔ a = 0 ∨ b = 0` · context -/
example (a b : ℝ) (G : Prop) (h : a / b = 0) (g : a = 0 ∨ b = 0 → G) : G := by
  rw [div_eq_zero_iff] at h
  exact g h

/-! ### R23. `rcases h with h | h` · context loses `h : A ∨ B`; goal list: one goal with `h : A`, one with `h : B` -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h | h
  exact ga h
  exact gb h

/-! ### R24. `Nat.cast_nonneg` · `0 ≤ (↑k : ℝ)` · context (or as `linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]`) -/
example (k : ℕ) : (0 : ℝ) ≤ k := by
  have h : (0 : ℝ) ≤ k := k.cast_nonneg
  exact h

/-! ## Laws: moving between a random variable and its distribution -/

/-! ### R25. `StronglyMeasurable.of_discrete.aestronglyMeasurable` · context gains measurability of any `ℕ → ℝ`
`ℕ` is countable with every set measurable, so every function out of it is measurable. -/
example (g : ℕ → ℝ) (ν : Measure ℕ) : AEStronglyMeasurable g ν := by
  have h : AEStronglyMeasurable g ν := StronglyMeasurable.of_discrete.aestronglyMeasurable
  exact h

/-! ### R26. `hX.aemeasurable` · from `hX : HasLaw X ν μ`, context gains `AEMeasurable X μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (ν : Measure ℕ)
    (hX : HasLaw X ν μ) : AEMeasurable X μ := by
  have h := hX.aemeasurable
  exact h

/-! ### R27. `refine (integrable_map_measure hg hX).1 ?_` · goal: `Integrable (g ∘ X) μ` → `Integrable g (map X μ)`
`integrable_map_measure hg hX : Integrable g (Measure.map X μ) ↔ Integrable (g ∘ X) μ`; `.1` is `→`.
A goal `Integrable (fun ω => g (X ω)) μ` is accepted too: it is `g ∘ X` by definition. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (g : ℕ → ℝ)
    (hg : AEStronglyMeasurable g (Measure.map X μ)) (hX : AEMeasurable X μ)
    (h : Integrable g (Measure.map X μ)) : Integrable (fun ω => g (X ω)) μ := by
  refine (integrable_map_measure hg hX).1 ?_
  exact h

/-! ### R28. `hX.map_eq` · `Measure.map X μ = ν` · goal: the pushforward → the law itself -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (ν : Measure ℕ)
    (hX : HasLaw X ν μ) (Q : Measure ℕ → Prop) (h : Q ν) : Q (Measure.map X μ) := by
  rw [hX.map_eq]
  exact h

/-! ## Expectation: linearity, constants, change of variables -/

/-! ### R29. `integral_add hf hg` · `∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P ((∫ ω, f ω ∂μ) + ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω + g ω ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R30. `integrable_const c` · context gains `Integrable (fun _ => c) μ` (needs a finite measure) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (c : ℝ) :
    Integrable (fun _ : Ω => c) μ := by
  have h := integrable_const (μ := μ) c
  exact h

/-! ### R31. `integral_const c` · `∫ _, c ∂μ = μ.real Set.univ • c` · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (P : ℝ → Prop)
    (h : P (μ.real Set.univ • c)) : P (∫ _ : Ω, c ∂μ) := by
  rw [integral_const]
  exact h

/-! ### R32. `probReal_univ` · `μ.real Set.univ = 1` for a probability measure · goal -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ℝ → Prop)
    (h : P 1) : P (μ.real Set.univ) := by
  rw [probReal_univ]
  exact h

/-! ### R33. `one_smul` · `1 • c = c` · goal -/
example (c : ℝ) (P : ℝ → Prop) (h : P c) : P ((1 : ℝ) • c) := by
  rw [one_smul]
  exact h

/-! ### R34. `hX.integral_comp hf` · from `hX : HasLaw X ν μ`, context gains `∫ (f ∘ X) ∂μ = ∫ f ∂ν`
Name `f` with `(f := …)` when Lean cannot guess it from the goal. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (ν : Measure ℕ)
    (hX : HasLaw X ν μ) (f : ℕ → ℝ) : ∫ x, (f ∘ X) x ∂μ = ∫ m, f m ∂ν := by
  have h := hX.integral_comp (f := f) StronglyMeasurable.of_discrete.aestronglyMeasurable
  exact h

/-! ### R35. `simp only [Function.comp_def] at h` · context: `(f ∘ X) x` → `f (X x)` -/
example {Ω : Type} (X : Ω → ℕ) (f : ℕ → ℝ) (x : Ω) (G : Prop) (h : (f ∘ X) x = 0)
    (g : f (X x) = 0 → G) : G := by
  simp only [Function.comp_def] at h
  exact g h

/-! ## Finite sums -/

/-! ### R36. `Finset.mem_range` · `k ∈ Finset.range n ↔ k < n`; `.1` turns `hk : k ∈ range n` into `k < n` -/
example (k n : ℕ) (hk : k ∈ Finset.range n) : k < n := by
  have h := Finset.mem_range.1 hk
  exact h

/-! ### R37. `hf.add hg` (`Integrable.add`) · context gains `Integrable (f + g) μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (fun ω => f ω + g ω) μ := by
  have h := hf.add hg
  exact h

/-! ### R38. `integral_finsetSum s hf` · goal: `∫ ∑` → `∑ ∫` (each summand integrable)
`(∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (P : ℝ → Prop) (h : P (∑ i ∈ s, ∫ ω, f i ω ∂μ)) :
    P (∫ ω, ∑ i ∈ s, f i ω ∂μ) := by
  rw [integral_finsetSum s hf]
  exact h

/-! ### R39. `rw [Finset.sum_congr rfl hfg]` · goal: rewrite every summand with `hfg : ∀ i ∈ s, f i = g i` -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (hfg : ∀ i ∈ s, f i = g i) (P : ℝ → Prop)
    (h : P (∑ i ∈ s, g i)) : P (∑ i ∈ s, f i) := by
  rw [Finset.sum_congr rfl hfg]
  exact h

/-! ### R40. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: push a factor into a sum -/
example (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ s, a * f i)) :
    P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R41. `Finset.sum_range_reflect` · `∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j`
Used right to left, `rw [← Finset.sum_range_reflect]` reverses the order of summation. -/
example (f : ℕ → ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (∑ j ∈ Finset.range n, f (n - 1 - j))) :
    P (∑ j ∈ Finset.range n, f j) := by
  rw [← Finset.sum_range_reflect]
  exact h

/-! ### R42. `refine Finset.sum_congr rfl (fun k hk => ?_)` · goal: equal sums → equal summands
The context gains `k` and `hk : k ∈ s`. -/
example (s : Finset ℕ) (f g : ℕ → ℝ) (hfg : ∀ k ∈ s, f k = g k) :
    ∑ k ∈ s, f k = ∑ k ∈ s, g k := by
  refine Finset.sum_congr rfl (fun k hk => ?_)
  exact hfg k hk

/-! ### R43. `Nat.cast_sub h` · `m ≤ n → ↑(n - m) = ↑n - ↑m` · goal; side goal `m ≤ n`
`n - m` on `ℕ` is truncated (`2 - 5 = 0`), so the cast only distributes when `m ≤ n`. -/
example (m n : ℕ) (hmn : m ≤ n) (P : ℝ → Prop) (h : P ((n : ℝ) - m)) : P ((n - m : ℕ) : ℝ) := by
  rw [Nat.cast_sub hmn]
  exact h

/-! ### R44. `omega` · closes linear arithmetic over `ℕ`/`ℤ` (truncated `-` included) from the context -/
example (k n : ℕ) (hk : k < n) : 1 ≤ n - k := by
  omega

/-! ### R45. `push_cast` · goal: moves casts `↑` inward and evaluates casts of numerals (`↑1` → `1`) -/
example (a b : ℕ) (P : ℝ → Prop) (h : P ((a : ℝ) + b + 1)) : P (((a + b + 1 : ℕ) : ℝ)) := by
  push_cast
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A series by R10 → R11 → R12: `∑' n, 3 * (↑n * (1/2) ^ n) = 6` -/
example : ∑' n : ℕ, (3 : ℝ) * ((n : ℝ) * (1 / 2) ^ n) = 6 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> norm_num
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hr]
  norm_num

/-! ### W2. Linearity with a constant: `E[X + 5]` from `E[X]`, by R29 (with R30) → R31 → R32 → R33 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable X μ) (hm : ∫ ω, X ω ∂μ = 4) : ∫ ω, X ω + 5 ∂μ = 9 := by
  rw [integral_add hX (integrable_const 5)]
  rw [integral_const, probReal_univ, one_smul]
  rw [hm]
  norm_num

/-! ### W3. Reversing a finite sum, then termwise: `∑_{j<n} (n - 1 - j) = ∑_{j<n} j` over `ℝ` -/
example (n : ℕ) : ∑ j ∈ Finset.range n, ((n - 1 - j : ℕ) : ℝ) = ∑ j ∈ Finset.range n, (j : ℝ) := by
  rw [Finset.sum_range_reflect (fun j => (j : ℝ)) n]

/-! ### W4. Change of variables for a law: `E[X]` from the law of `X` (R34, R35) -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (ν : Measure ℕ)
    (hX : HasLaw X ν μ) (hν : ∫ m, (m : ℝ) ∂ν = 7) : ∫ ω, (X ω : ℝ) ∂μ = 7 := by
  have h1 := hX.integral_comp (f := fun m : ℕ => (m : ℝ))
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  rw [h1, hν]

end H055Guide
