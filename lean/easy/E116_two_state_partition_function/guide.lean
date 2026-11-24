/- Guide for E116 (Two-state partition function).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a plain `f : Fin 2 → ℝ`,
numeric energies).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble

namespace E116Guide

/-! # Part R · Reference entries -/

/-! ## From the partition function to a finite sum -/

/-! ### R1. `partitionFunction_of_fintype` · goal: `𝓒.partitionFunction T` → `∑ i, Real.exp (-↑T.β * 𝓒.energy i)`
Needs `[Fintype ι]` (finitely many states), `[MeasurableSingletonClass ι]` and `[𝓒.IsFinite]`
(counting measure, no phase-space factor). For `twoState` Lean finds all three instances itself. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (∑ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i))) : P (𝓒.partitionFunction T) := by
  rw [partitionFunction_of_fintype]
  exact h

/-! ### R2. `Fin.sum_univ_two` · `∑ i, f i = f 0 + f 1` · goal: a sum over `Fin 2` → two terms -/
example {M : Type} [AddCommMonoid M] (f : Fin 2 → M) (P : M → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ## The two energies -/

/-! ### R3. `twoState_energy_fst` · `(twoState E₀ E₁).energy 0 = E₀` · goal -/
example (E₀ E₁ : ℝ) (P : ℝ → Prop) (h : P E₀) : P ((twoState E₀ E₁).energy 0) := by
  rw [twoState_energy_fst]
  exact h

/-! ### R4. `twoState_energy_snd` · `(twoState E₀ E₁).energy 1 = E₁` · goal -/
example (E₀ E₁ : ℝ) (P : ℝ → Prop) (h : P E₁) : P ((twoState E₀ E₁).energy 1) := by
  rw [twoState_energy_snd]
  exact h

/-! ## Cleaning up the zero energy -/

/-! ### R5. `mul_zero` · `a * 0 = 0` · goal -/
example {α : Type} [MulZeroClass α] (a : α) (P : α → Prop) (h : P 0) : P (a * 0) := by
  rw [mul_zero]
  exact h

/-! ### R6. `Real.exp_zero` · `Real.exp 0 = 1` · goal
When this `rw` leaves `x = x`, it closes the goal by itself (`rw` tries `rfl` at the end). -/
example (P : ℝ → Prop) (h : P 1) : P (Real.exp 0) := by
  rw [Real.exp_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A Boltzmann-type sum over `Fin 2` for a plain `f` with `f 0 = 0`: R2, `rw [hf0]`, R5, R6
The last `rw` closes the goal: both sides are then the same. -/
example (f : Fin 2 → ℝ) (x : ℝ) (hf0 : f 0 = 0) :
    ∑ i, Real.exp (-x * f i) = 1 + Real.exp (-x * f 1) := by
  rw [Fin.sum_univ_two]
  rw [hf0]
  rw [mul_zero]
  rw [Real.exp_zero]

/-! ### W2. Reading off energies of a two-level system with numeric levels: R3, R4, then `norm_num` -/
example : (twoState 1 2).energy 0 + (twoState 1 2).energy 1 = 3 := by
  rw [twoState_energy_fst]
  rw [twoState_energy_snd]
  norm_num

end E116Guide
