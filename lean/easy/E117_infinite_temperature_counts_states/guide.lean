/- Guide for E117 (Infinite temperature counts states).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on sums that are NOT the exercise's (a plain function, `Fin 3`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble

namespace E117Guide

/-! # Part R · Reference entries -/

/-! ## From the partition function to a sum -/

/-! ### R1. `simp only [mathematicalPartitionFunctionBetaReal]` · goal: the name → its defining sum
`𝓒.mathematicalPartitionFunctionBetaReal b` is defined as `∑ i, Real.exp (-b * 𝓒.energy i)`. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (b : ℝ) (𝓒 : CanonicalEnsemble ι)
    (P : ℝ → Prop) (h : P (∑ i, Real.exp (-b * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunctionBetaReal b) := by
  simp only [mathematicalPartitionFunctionBetaReal]
  exact h

/-! ### R2. `simp only [hf]` with `hf : ∀ i, f i = c` · goal: every `f i` under the `∑` → `c`
`rw [hf]` fails here: `rw` cannot rewrite a term that mentions the bound variable `i` of the sum. -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (c : ℝ) (g : ℝ → ℝ) (hf : ∀ i, f i = c)
    (P : ℝ → Prop) (h : P (∑ _i : ι, g c)) : P (∑ i, g (f i)) := by
  simp only [hf]
  exact h

/-! ### R3. `neg_mul` · `-a * b = -(a * b)` · goal (`simp` applies it by itself, on both sides) -/
example {α : Type} [Ring α] (a b : α) (P : α → Prop) (h : P (-(a * b))) : P (-a * b) := by
  rw [neg_mul]
  exact h

/-! ## A sum of a constant -/

/-! ### R4. `Finset.sum_const` · `∑ _x ∈ s, c = s.card • c` · goal: constant sum → `card • c`
`∑ i, …` is a sum over `Finset.univ` (every element of `ι`); `•` here is `n • c = c + ⋯ + c`. -/
example {ι β : Type} [Fintype ι] [AddCommMonoid β] (c : β) (P : β → Prop)
    (h : P ((Finset.univ : Finset ι).card • c)) : P (∑ _i : ι, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R5. `Finset.card_univ` · `Finset.univ.card = Fintype.card α` · goal -/
example {ι β : Type} [Fintype ι] [AddCommMonoid β] (c : β) (P : β → Prop)
    (h : P (Fintype.card ι • c)) : P ((Finset.univ : Finset ι).card • c) := by
  rw [Finset.card_univ]
  exact h

/-! ### R6. `nsmul_eq_mul` · `n • a = ↑n * a` · goal: repeated addition → multiplication by a cast
`↑n` is the natural number `n` cast into `α` (here `ℝ`). -/
example {α : Type} [NonAssocSemiring α] (n : ℕ) (a : α) (P : α → Prop) (h : P (↑n * a)) :
    P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ## Setting `β = 0` -/

/-! ### R7. `neg_zero` · `-0 = 0` · goal -/
example {α : Type} [Ring α] (x : α) (P : α → Prop) (h : P (0 * x)) : P (-0 * x) := by
  rw [neg_zero]
  exact h

/-! ### R8. `zero_mul` · `0 * a = 0` · goal -/
example {α : Type} [Ring α] (x : α) (P : α → Prop) (h : P 0) : P (0 * x) := by
  rw [zero_mul]
  exact h

/-! ### R9. `Real.exp_zero` · `Real.exp 0 = 1` · goal -/
example (P : ℝ → Prop) (h : P 1) : P (Real.exp 0) := by
  rw [Real.exp_zero]
  exact h

/-! ### R10. `mul_one` · `a * 1 = a` · goal -/
example {α : Type} [Ring α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's sums) -/

/-! ### W1. Constant terms under a sum, one step at a time: R2, R4, R5, R6 -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (c : ℝ) (hf : ∀ i, f i = c) :
    ∑ i, Real.exp (f i) = Fintype.card ι * Real.exp c := by
  simp only [hf]
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [nsmul_eq_mul]

/-! ### W2. A zero exponent, one step at a time: R7, R8, R9, R4, R5, R6, R10
`Fintype.card (Fin 3)` is `3`, but `simp` only reduces that with `Fintype.card_fin`. -/
example (f : Fin 3 → ℝ) : ∑ i, Real.exp (-0 * f i) = 3 := by
  simp only [neg_zero]
  simp only [zero_mul]
  simp only [Real.exp_zero]
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [nsmul_eq_mul]
  rw [mul_one]
  simp

/-! ### W3. The same two sums, all at once: `simp [hf]` applies R2–R6 by itself -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (c : ℝ) (hf : ∀ i, f i = c) :
    ∑ i, Real.exp (f i) = Fintype.card ι * Real.exp c := by
  simp [hf]

example (f : Fin 3 → ℝ) : ∑ i, Real.exp (-0 * f i) = 3 := by
  simp

end E117Guide
