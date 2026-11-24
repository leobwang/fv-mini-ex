/- Guide for H091 (log Z is convex in β).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a generic `f`, other exponents).
Assumed: Lean basics (E001–E033). Mathlib's real analysis and physlib's `CanonicalEnsemble` are new.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.MeanInequalities

open CanonicalEnsemble Real

namespace H091Guide

/-! # Part R · Reference entries -/

/-! ## Exponentials and real powers (milestone `exp_rpow`) -/

/-! ### R1. `Real.exp_mul` · `exp (x * y) = exp x ^ y`; right to left: `rw [← Real.exp_mul]` · goal
`x ^ y` with `y : ℝ` is `Real.rpow`, the real power `exp (y log x)` (for `x > 0`). -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x * y))) : P (Real.exp x ^ y) := by
  rw [← Real.exp_mul]
  exact h

/-! ### R2. `congr 1` · goal `f a = f b` → `a = b` (strip one function application) -/
example (u v : ℝ) (h : v = u) : Real.exp u = Real.exp v := by
  congr 1
  exact h.symm

/-! ### R3. `field_simp` · goal: clears denominators, using `a ≠ 0` (or `0 < a`) from the context -/
example (u w a : ℝ) (ha : 0 < a) (h : u = a * w) : u / a = w := by
  field_simp
  exact h

/-! ## Hölder-conjugate exponents (milestone `holderConjugate_weights`) -/

/-! ### R4. `Real.holderConjugate_iff` · goal: `p.HolderConjugate q` → `1 < p ∧ p⁻¹ + q⁻¹ = 1` -/
example (p q : ℝ) (h : 1 < p ∧ p⁻¹ + q⁻¹ = 1) : p.HolderConjugate q := by
  rw [Real.holderConjugate_iff]
  exact h

/-! ### R5. `one_div`, `inv_inv` (via `simp`) · goal: `(1 / a)⁻¹` → `a` -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (1 / a)⁻¹ := by
  simp only [one_div, inv_inv]
  exact h

/-! ### R6. `lt_div_iff₀` · `0 < c → (a < b / c ↔ a * c < b)` · goal: multiply out a denominator -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c < b) : a < b / c := by
  rw [lt_div_iff₀ hc]
  exact h

/-! ### R7. `linarith` · closes a linear (in)equality that follows from the hypotheses -/
example (u v : ℝ) (h1 : u + v = 2) (h2 : 0 < v) : u * 1 < 2 := by
  linarith

/-! ## Hölder's inequality on a finite sum (milestone `holder_step`) -/

/-! ### R8. `Real.inner_le_Lp_mul_Lq_of_nonneg` · context gains Hölder's inequality
`∑ f g ≤ (∑ f ^ p) ^ (1/p) * (∑ g ^ q) ^ (1/q)` for `f, g ≥ 0` on `s` and conjugate `p, q`. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (G : Prop)
    (h : (∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)) → G) :
    G := by
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s) (f := f) (g := g) hpq hf hg
  exact h key

/-! ### R9. `Real.exp_pos`, then `.le` · `0 < exp x`, weakened to `0 ≤ exp x` · context gains it -/
example {ι : Type} (s : Finset ι) (u : ι → ℝ) (G : Prop)
    (h : (∀ i ∈ s, 0 ≤ Real.exp (u i)) → G) : G := by
  have hf : ∀ i ∈ s, 0 ≤ Real.exp (u i) := fun i _ => (Real.exp_pos _).le
  exact h hf

/-! ### R10. `one_div_one_div` · `1 / (1 / a) = a` · `simp only [...] at key` rewrites a hypothesis -/
example (a : ℝ) (P : ℝ → Prop) (key : P (1 / (1 / a))) : P a := by
  simp only [one_div_one_div] at key
  exact key

/-! ### R11. `Real.exp_add` · `exp (x + y) = exp x * exp y`; right to left merges a product -/
example (u v : ℝ) (P : ℝ → Prop) (key : P (Real.exp u * Real.exp v)) : P (Real.exp (u + v)) := by
  simp only [← Real.exp_add] at key
  exact key

/-! ### R12. Unfold `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal` · goal: `Z(b)` → its sum
`𝓒.mathematicalPartitionFunctionBetaReal b` is `Z(b) = ∑ i, exp (-b * 𝓒.energy i)`. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (b : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, Real.exp (-b * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunctionBetaReal b) := by
  simp only [CanonicalEnsemble.mathematicalPartitionFunctionBetaReal]
  exact h

/-! ### R13. `Eq.trans_le` · `a = b → b ≤ c → a ≤ c` · goal `a ≤ c` → `a = b` given `key : b ≤ c` -/
example (a b c : ℝ) (key : b ≤ c) (h : a = b) : a ≤ c := by
  refine Eq.trans_le ?_ key
  exact h

/-! ### R14. `Finset.sum_congr rfl` · goal: equal sums → equal summands, one `i ∈ s` at a time -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  exact h i hi

/-! ## Convexity and logarithms (theorem `logZ_convex`) -/

/-! ### R15. `ConvexOn`, `convex_univ` · goal: `ConvexOn ℝ Set.univ f` → the two-point inequality
`ConvexOn 𝕜 s f` is `Convex 𝕜 s ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ a b, 0 ≤ a → 0 ≤ b → a + b = 1 → …`. -/
example (f : ℝ → ℝ)
    (h : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  exact h x y a b ha hb hab

/-! ### R16. `smul_eq_mul` · goal: `a • x` → `a * x` (scalar action of `ℝ` on itself) -/
example (a x : ℝ) (P : ℝ → Prop) (h : P (a * x)) : P (a • x) := by
  simp only [smul_eq_mul]
  exact h

/-! ### R17. `rcases ha.eq_or_lt with rfl | ha'` · goal list: `0 ≤ a` splits into `a = 0` and `0 < a`
`LE.le.eq_or_lt : a ≤ b → a = b ∨ a < b`; the pattern `rfl` substitutes `a := 0` everywhere. -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h0 : P 0) (hpos : 0 < a → P a) : P a := by
  rcases ha.eq_or_lt with rfl | ha'
  · exact h0
  · exact hpos ha'

/-! ### R18. `obtain rfl : c = 1 := by linarith` · context: `c` is replaced by `1` everywhere -/
example (c : ℝ) (hc : 0 + c = 1) (P : ℝ → Prop) (h : P 1) : P c := by
  obtain rfl : c = 1 := by linarith
  exact h

/-! ### R19. `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z(b)`
Needs `[Nonempty ι]`: at least one microstate. -/
example {ι : Type} [Nonempty ι] [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)
    (G : Prop) (h : (∀ b, 0 < 𝓒.mathematicalPartitionFunctionBetaReal b) → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos
  exact h hZ

/-! ### R20. `calc` · goal list: `a ≤ c` → one goal per step, `a ≤ b` and `b = c` -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by
  calc a ≤ b := ?_
    _ = c := ?_
  exact h1
  exact h2

/-! ### R21. `Real.log_le_log` · `0 < x → x ≤ y → log x ≤ log y` · goal list: two side goals -/
example (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  apply Real.log_le_log
  exact hx
  exact hxy

/-! ### R22. `Real.rpow_pos_of_pos`, then `.ne'` · `0 < x → 0 < x ^ y`, turned into `x ^ y ≠ 0` -/
example (x y : ℝ) (hx : 0 < x) (G : Prop) (h : x ^ y ≠ 0 → G) : G := by
  have hne : x ^ y ≠ 0 := (Real.rpow_pos_of_pos hx y).ne'
  exact h hne

/-! ### R23. `Real.log_mul` · `x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y` · goal -/
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (P : ℝ → Prop) (h : P (Real.log x + Real.log y)) :
    P (Real.log (x * y)) := by
  rw [Real.log_mul hx hy]
  exact h

/-! ### R24. `Real.log_rpow` · `0 < x → log (x ^ y) = y * log x` · goal -/
example (x y : ℝ) (hx : 0 < x) (P : ℝ → Prop) (h : P (y * Real.log x)) :
    P (Real.log (x ^ y)) := by
  rw [Real.log_rpow hx]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An edge weight: with `a = 0`, `c = 1` the convexity inequality is trivial (`simp`) -/
example (f : ℝ → ℝ) (x y : ℝ) : f (0 * x + 1 * y) ≤ 0 * f x + 1 * f y := by
  simp

/-! ### W2. Conjugate exponents `3` and `3/2`: R4, then numerals (`norm_num`) -/
example : (3 : ℝ).HolderConjugate (3 / 2) := by
  rw [Real.holderConjugate_iff]
  norm_num

/-! ### W3. Log of a product of real powers: R22 → R23 → R24 -/
example (u v s t : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Real.log (u ^ s * v ^ t) = s * Real.log u + t * Real.log v := by
  rw [Real.log_mul (Real.rpow_pos_of_pos hu s).ne' (Real.rpow_pos_of_pos hv t).ne']
  rw [Real.log_rpow hu, Real.log_rpow hv]

/-! ### W4. A power of an exponential: R1 → R2 → R3 -/
example (u a : ℝ) (ha : 0 < a) : Real.exp (2 * a * u) ^ (1 / a) = Real.exp (2 * u) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp

end H091Guide
