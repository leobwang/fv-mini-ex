/- Guide for E101 (Laws: the Gaussian).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The underlying probability measure is called `Q` here (the exercise calls it `P`), the random
variable `Y`, its law `μ`.
Part W: worked combinations on objects that are NOT the exercise's (the point mass `dirac c`).
Assumed: Lean basics.
-/
import Mathlib

open ProbabilityTheory MeasureTheory
open scoped NNReal

namespace E101Guide

/-! # Part R · Reference entries -/

/-! ## Two goals, one per moment -/

/-! ### R1. `refine ⟨?_, ?_⟩` · goal `A ∧ B` → two goals
`constructor` does the same; as a term, `⟨by tac₁, by tac₂⟩` proves both halves in place. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  refine ⟨?_, ?_⟩
  exacts [ha, hb]

/-! ## The mean: to the law, then the Gaussian -/

/-! ### R2. `HasLaw.integral_eq` · goal: `Q[Y]` (= `∫ x, Y x ∂Q`) → `∫ x, x ∂μ`
From `hY : HasLaw Y μ Q`, the dot-notation term `hY.integral_eq` is the equation
`∫ x, Y x ∂Q = ∫ x, x ∂μ`: the mean of `Y` is the mean of its law. -/
example {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (Y : Ω → ℝ) (μ : Measure ℝ)
    (hY : HasLaw Y μ Q) (P : ℝ → Prop) (h : P (∫ x, x ∂μ)) : P (Q[Y]) := by
  rw [hY.integral_eq]
  exact h

/-! ### R3. `integral_id_gaussianReal` · goal: `∫ x, x ∂gaussianReal m v` → `m` -/
example (m : ℝ) (v : ℝ≥0) (P : ℝ → Prop) (h : P m) : P (∫ x, x ∂gaussianReal m v) := by
  rw [integral_id_gaussianReal]
  exact h

/-! ## The variance: to the law, then the Gaussian -/

/-! ### R4. `HasLaw.variance_eq` · goal: `Var[Y; Q]` → `Var[id; μ]`
`id` is the identity function `fun x => x` on `ℝ`: under the law `μ` it plays the role of `Y`. -/
example {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (Y : Ω → ℝ) (μ : Measure ℝ)
    (hY : HasLaw Y μ Q) (P : ℝ → Prop) (h : P (Var[id; μ])) : P (Var[Y; Q]) := by
  rw [hY.variance_eq]
  exact h

/-! ### R5. `variance_id_gaussianReal` · goal: `Var[id; gaussianReal m v]` → `↑v`
`↑v : ℝ` is `v : ℝ≥0` cast to the reals (`NNReal.toReal v`). -/
example (m : ℝ) (v : ℝ≥0) (P : ℝ → Prop) (h : P v) : P (Var[id; gaussianReal m v]) := by
  rw [variance_id_gaussianReal]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A point mass: R2 then `integral_dirac`, R4 then `variance_dirac`
`Measure.dirac c` puts all mass on `c`. `integral_dirac f c : ∫ x, f x ∂dirac c = f c` and
`variance_dirac c : Var[X; dirac c] = 0` are its two facts, playing the roles of R3 and R5. -/
example {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (Y : Ω → ℝ) (c : ℝ)
    (hY : HasLaw Y (Measure.dirac c) Q) : Q[Y] + Var[Y; Q] = c := by
  rw [hY.integral_eq]
  rw [integral_dirac]
  rw [hY.variance_eq]
  rw [variance_dirac]
  simp

/-! ### W2. The same two facts as one term: R1's `⟨by …, by …⟩`, each half two rewrites
After its rewrites, `rw` closes a goal of the form `a = a` by itself. -/
example {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (Y : Ω → ℝ) (c : ℝ)
    (hY : HasLaw Y (Measure.dirac c) Q) : Q[Y] = c ∧ Var[Y; Q] = 0 :=
  ⟨by rw [hY.integral_eq, integral_dirac], by rw [hY.variance_eq, variance_dirac]⟩

end E101Guide
