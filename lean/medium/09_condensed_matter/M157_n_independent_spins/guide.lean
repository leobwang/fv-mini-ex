/- Guide for M157 (N independent spins).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓒 : CanonicalEnsemble ι` is any physlib canonical ensemble with microstates `ι`; `T : Temperature`.
Part W: worked combinations on objects that are NOT the exercise's (`twoState 0 e`, energies `0`, `e`).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M157Guide

/-! # Part R · Reference entries -/

/-! ## The partition function of `N` copies -/

/-! ### R1. `partitionFunction_nsmul` · goal: `Z` of `n` independent copies → `Z ^ n`
`nsmul n 𝓒` is `n` distinguishable, non-interacting copies of `𝓒`: microstates `Fin n → ι`, energy
`∑ k, 𝓒.energy (f k)`. Its partition function factorises. -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature)
    (P : ℝ → Prop) (h : P (𝓒.partitionFunction T ^ n)) :
    P ((nsmul n 𝓒).partitionFunction T) := by
  rw [partitionFunction_nsmul]
  exact h

/-! ### R2. `partitionFunction_of_fintype` · goal: `Z` of a finite system → `∑ i, rexp (-↑T.β * E i)`
Needs `[Fintype ι]`, `[MeasurableSingletonClass ι]` and `[IsFinite 𝓒]` (counting measure, `dof = 0`,
phase-space unit `1`); `twoState a b` over `Fin 2` has all three. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [IsFinite 𝓒] (T : Temperature)
    (P : ℝ → Prop) (h : P (∑ i, rexp (-↑T.β * 𝓒.energy i))) :
    P (𝓒.partitionFunction T) := by
  rw [partitionFunction_of_fintype]
  exact h

/-! ### R3. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {M : Type} [AddCommMonoid M] (f : Fin 2 → M) (P : M → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R4. `twoState_energy_fst`, `twoState_energy_snd` · goal: the two energies of `twoState a b`
`twoState a b : CanonicalEnsemble (Fin 2)` has state `0` at energy `a`, state `1` at energy `b`.
Both lemmas are `@[simp]`. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P a b) :
    P ((twoState a b).energy 0) ((twoState a b).energy 1) := by
  simp only [twoState_energy_fst, twoState_energy_snd]
  exact h

/-! ### R5. `neg_mul`, `mul_neg`, `neg_neg` · goal: signs pulled out of products, `- -x` → `x`
`neg_mul a b : -a * b = -(a * b)`, `mul_neg a b : a * -b = -(a * b)`, `neg_neg x : - -x = x`.
Plain `simp` uses all three by itself. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P (a * b) (-(a * b))) : P (-a * -b) (-a * b) := by
  simp only [neg_mul, mul_neg, neg_neg]
  exact h

/-! ### R6. `Real.cosh_eq` · `cosh x = (rexp x + rexp (-x)) / 2` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((rexp x + rexp (-x)) / 2)) : P (Real.cosh x) := by
  rw [Real.cosh_eq]
  exact h

/-! ### R7. `ring_nf` · closes a goal whose two sides have the same ring normal form
`2 * (a / 2)` normalises to `a`; `ring_nf` works under `^ n` with a variable exponent `n`. -/
example (a : ℝ) (n : ℕ) : a ^ n = (2 * (a / 2)) ^ n := by
  ring_nf

/-! ## The free energy -/

/-! ### R8. `rw [helmholtzFreeEnergy]` · goal: `F` → `-kB * ↑T.val * log Z` (unfold the definition)
`kB : ℝ` is Boltzmann's constant (`Constants.kB`); `↑T.val` is the temperature cast from `ℝ≥0` to `ℝ`. -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (P : ℝ → Prop) (h : P (-kB * ↑T.val * Real.log (𝓒.partitionFunction T))) :
    P (𝓒.helmholtzFreeEnergy T) := by
  rw [helmholtzFreeEnergy]
  exact h

/-! ### R9. `rw [thm]` with an earlier theorem `thm : ∀ x, f x = g x` · goal: `f k` → `g k`
A proved theorem is a universally quantified equation; `rw` finds its arguments by matching the left
side against the goal. Here `thm` plays the role of a theorem proved earlier in the file. -/
example (f g : ℕ → ℝ) (thm : ∀ x, f x = g x) (k : ℕ) (P : ℝ → Prop) (h : P (g k)) :
    P (f k) := by
  rw [thm]
  exact h

/-! ### R10. `Real.log_pow` · `log (x ^ n) = ↑n * log x` (no positivity hypothesis) · goal -/
example (x : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (↑n * Real.log x)) : P (Real.log (x ^ n)) := by
  rw [Real.log_pow]
  exact h

/-! ### R11. `ring` · closes an identity of commutative rings; `kB`, `↑T.val`, `↑n`, `log …` are atoms -/
example (a b c : ℝ) (n : ℕ) : -a * b * (↑n * c) = -↑n * a * b * c := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `N` copies of `twoState 0 e` (ground state at `0`): R1, R2, then `simp` with R3, R4
`simp` also turns `rexp (-↑T.β * 0)` into `1`. -/
theorem Z_ground_zero (e : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState 0 e)).partitionFunction T = (1 + rexp (-(↑T.β * e))) ^ N := by
  rw [partitionFunction_nsmul, partitionFunction_of_fintype]
  simp [Fin.sum_univ_two]

/-! ### W2. Its free energy, reusing W1 by name: R8, R9, R10, R11 -/
example (e : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState 0 e)).helmholtzFreeEnergy T =
      -N * kB * T.val * Real.log (1 + rexp (-(↑T.β * e))) := by
  rw [helmholtzFreeEnergy]
  rw [Z_ground_zero]
  rw [Real.log_pow]
  ring

/-! ### W3. `rexp x + rexp (-x)` as `2 * cosh x`, for any `x`: R6, then R7 -/
example (x : ℝ) : rexp x + rexp (-x) = 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  ring_nf

end M157Guide
