/- Guide for M173 (Independent subsystems).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on plain functions `f g p q : α → ℝ`, NOT the exercise's ensembles.
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M173Guide

/-! # Part R · Reference entries -/

/-! ## Finite ensembles: from `Z`, `p`, `U` to finite sums
A `CanonicalEnsemble α` (physlib) has microstates `α` and `energy : α → ℝ`. `[𝓐.IsFinite]` says the
measure on `α` is the counting measure (and `dof = 0`, `phaseSpaceunit = 1`), so integrals are sums.
`T : Temperature`; `T.β : ℝ≥0` is `1 / (k_B T)`, and `↑T.β` is its cast to `ℝ`. `rexp` is `Real.exp`. -/

/-! ### R1. `partitionFunction_of_fintype` · goal: `𝓐.partitionFunction T` → `∑ i, rexp (-↑T.β * 𝓐.energy i)` -/
example {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝓐 : CanonicalEnsemble α) [𝓐.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (∑ i, Real.exp (-(T.β : ℝ) * 𝓐.energy i))) : P (𝓐.partitionFunction T) := by
  rw [partitionFunction_of_fintype]
  exact h

/-! ### R2. `Fintype.sum_prod_type` · goal: a sum over pairs `α × β` → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α × β → M) (P : M → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ x, f x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R3. `Finset.sum_mul_sum` · goal: a product of two sums → a double sum of products
`(∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`; `∑ i, f i` is `∑ i ∈ Finset.univ, f i`. -/
example {α β R : Type} [Fintype α] [Fintype β] [CommRing R] (f : α → R) (g : β → R) (P : R → Prop)
    (h : P (∑ i, ∑ j, f i * g j)) : P ((∑ i, f i) * ∑ j, g j) := by
  rw [Finset.sum_mul_sum]
  exact h

/-! ### R4. `refine Finset.sum_congr rfl fun i _ => ?_` · goal: two sums over the same Finset → one summand
The context gains `i` and an unnamed `x✝ : i ∈ Finset.univ`. Nest it once more for a double sum. -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M) (h : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i

/-! ### R5. `energy_add_apply` · goal: energy of the product system → sum of the two energies
`𝓐 + 𝓑 : CanonicalEnsemble (α × β)`; `x.1`, `x.2` are the two components of `x : α × β`. -/
example {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (𝓐 : CanonicalEnsemble α)
    (𝓑 : CanonicalEnsemble β) (x : α × β) (P : ℝ → Prop) (h : P (𝓐.energy x.1 + 𝓑.energy x.2)) :
    P ((𝓐 + 𝓑).energy x) := by
  rw [energy_add_apply]
  exact h

/-! ### R6. `mul_add` · `a * (b + c) = a * b + a * c` · goal -/
example {R : Type} [CommRing R] (a b c : R) (P : R → Prop) (h : P (a * b + a * c)) :
    P (a * (b + c)) := by
  rw [mul_add]
  exact h

/-! ### R7. `Real.exp_add` · `rexp (x + y) = rexp x * rexp y` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp x * Real.exp y)) : P (Real.exp (x + y)) := by
  rw [Real.exp_add]
  exact h

/-! ## The Boltzmann probability -/

/-! ### R8. `simp only [probability]` · goal: unfold `𝓐.probability T i`
`probability T i = rexp (-↑T.β * energy i) / mathematicalPartitionFunction T` (a definition, not a lemma).
`mathematicalPartitionFunction` is `Z` before dividing by `phaseSpaceunit ^ dof`; for a finite ensemble the two agree. -/
example {α : Type} [MeasurableSpace α] (𝓐 : CanonicalEnsemble α) (T : Temperature) (i : α)
    (P : ℝ → Prop)
    (h : P (Real.exp (-(T.β : ℝ) * 𝓐.energy i) / 𝓐.mathematicalPartitionFunction T)) :
    P (𝓐.probability T i) := by
  simp only [probability]
  exact h

/-! ### R9. `mathematicalPartitionFunction_of_fintype` · goal: `𝓐.mathematicalPartitionFunction T` → a finite sum -/
example {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝓐 : CanonicalEnsemble α) [𝓐.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (∑ i, Real.exp (-(T.β : ℝ) * 𝓐.energy i))) : P (𝓐.mathematicalPartitionFunction T) := by
  rw [mathematicalPartitionFunction_of_fintype]
  exact h

/-! ### R10. `div_mul_div_comm` · `a / b * (c / d) = a * c / (b * d)` · goal -/
example {K : Type} [Field K] (a b c d : K) (P : K → Prop) (h : P (a * c / (b * d))) :
    P (a / b * (c / d)) := by
  rw [div_mul_div_comm]
  exact h

/-! ## The mean energy -/

/-! ### R11. `meanEnergy_of_fintype` · goal: `𝓐.meanEnergy T` → `∑ i, 𝓐.energy i * 𝓐.probability T i` -/
example {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (𝓐 : CanonicalEnsemble α) [𝓐.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (∑ i, 𝓐.energy i * 𝓐.probability T i)) : P (𝓐.meanEnergy T) := by
  rw [meanEnergy_of_fintype]
  exact h

/-! ### R12. `add_mul` · `(a + b) * c = a * c + b * c` · goal -/
example {R : Type} [CommRing R] (a b c : R) (P : R → Prop) (h : P (a * c + b * c)) :
    P ((a + b) * c) := by
  rw [add_mul]
  exact h

/-! ### R13. `Finset.sum_add_distrib` · goal: a sum of `f x + g x` → the sum of `f` plus the sum of `g`
With `simp only` it also works under an outer `∑` (inside a binder), where `rw` cannot reach. -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M) (P : M → Prop)
    (h : P (∑ x, f x + ∑ x, g x)) : P (∑ x, (f x + g x)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R14. `have h1 := sum_probability_eq_one 𝓐 T` · context gains `h1 : ∑ i, 𝓐.probability T i = 1`
Needs `[Nonempty α]` (otherwise `Z = 0`) besides `[𝓐.IsFinite]`. -/
example {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    (𝓐 : CanonicalEnsemble α) [𝓐.IsFinite] (T : Temperature) (G : Prop)
    (g : ∑ i, 𝓐.probability T i = 1 → G) : G := by
  have h1 := sum_probability_eq_one 𝓐 T
  exact g h1

/-! ### R15. `congr 1` · goal `a + b = c + d` → two goals `a = c` and `b = d`
`congr` closes a new goal by itself when it is `rfl` or a hypothesis; here `h1`, `h2` are stated the
other way round so that both goals stay visible. -/
example {R : Type} [CommRing R] (a b c d : R) (h1 : c = a) (h2 : d = b) : a + b = c + d := by
  congr 1
  exacts [h1.symm, h2.symm]

/-! ### R16. `mul_assoc` · `a * b * c = a * (b * c)`; right to left: `simp only [← mul_assoc]` · goal
`*` groups to the left: `a * b * c` is `(a * b) * c`. -/
example {R : Type} [CommRing R] (a b c : R) (P : R → Prop) (h : P (a * b * c)) :
    P (a * (b * c)) := by
  simp only [← mul_assoc]
  exact h

/-! ### R17. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left pulls a factor out
`simp only [← Finset.mul_sum]` needs the summand to be `(something not using i) * f i`. -/
example {α R : Type} [Fintype α] [CommRing R] (a : R) (f : α → R) (P : R → Prop)
    (h : P (a * ∑ i, f i)) : P (∑ i, a * f i) := by
  simp only [← Finset.mul_sum]
  exact h

/-! ### R18. `mul_one` · `a * 1 = a` · goal -/
example {R : Type} [CommRing R] (a : R) (P : R → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R19. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M) (P : M → Prop)
    (h : P (∑ y, ∑ x, f x y)) : P (∑ x, ∑ y, f x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R20. `simp only [mul_comm (f _)]` · goal: swap the factors of `f x * g x`, also under `∑`
`mul_comm a b : a * b = b * a`. Fixing the first factor's shape `f _` stops `simp` from swapping
every product (and from undoing its own swap). -/
example {α R : Type} [Fintype α] [CommRing R] (f g : α → R) (P : R → Prop)
    (h : P (∑ x, g x * f x)) : P (∑ x, f x * g x) := by
  simp only [mul_comm (f _)]
  exact h

/-! # Part W · Worked combinations (plain functions, not the exercise's ensembles) -/

/-! ### W1. A product weight on `α × β` factorises: R2, then R3; `rw` closes the rest by `rfl`
`f (x, y).1` is `f x` by definition, which the closing `rfl` sees. -/
example {α β : Type} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    ∑ x : α × β, f x.1 * g x.2 = (∑ a, f a) * ∑ b, g b := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-! ### W2. Normalised weights `p q` make a double sum collapse: R16, R17, `rw [hq]`, R18 -/
example {α β : Type} [Fintype α] [Fintype β] (a p : α → ℝ) (q : β → ℝ) (hq : ∑ j, q j = 1) :
    ∑ i, ∑ j, a i * (p i * q j) = ∑ i, a i * p i := by
  simp only [← mul_assoc]
  simp only [← Finset.mul_sum]
  simp only [hq, mul_one]

/-! ### W3. The same when the factor depends on the INNER index: R19 first, then R20 -/
example {α β : Type} [Fintype α] [Fintype β] (p : α → ℝ) (b q : β → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, ∑ j, b j * (p i * q j) = ∑ j, b j * q j := by
  rw [Finset.sum_comm]
  simp only [mul_comm (p _)]
  simp only [← mul_assoc, ← Finset.mul_sum, hp, mul_one]

/-! ### W4. A ratio of exponentials splits: R7, R10 right to left (`rw [← div_mul_div_comm]`) -/
example (x y A B : ℝ) :
    Real.exp (x + y) / (A * B) = Real.exp x / A * (Real.exp y / B) := by
  rw [Real.exp_add]
  rw [← div_mul_div_comm]

end M173Guide
