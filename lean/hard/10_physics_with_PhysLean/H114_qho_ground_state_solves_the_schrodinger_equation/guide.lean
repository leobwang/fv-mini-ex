/- Guide for H114 (The QHO ground state solves the Schrödinger equation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G : Prop`
is an arbitrary goal, and a hypothesis `k : … → G` is only there to consume a new fact, so the entry
shows what entered the context. A hypothesis `h` that finishes an example shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`exp (3x)`, `-y / c`, a generic
`r ^ 2 = a / b`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension HarmonicOscillator Constants

namespace H114Guide

/-! # Part R · Reference entries -/

/-! ## Derivatives of functions `ℝ → ℂ` (milestone `deriv_gauss`) -/

/-! ### R1. `simp only [pow_two]` · goal: `a ^ 2` → `a * a`, also under a `fun`
`rw` cannot rewrite under `fun x => …` when the term mentions `x`; `simp only` can. -/
example (P : (ℝ → ℂ) → Prop) (h : P (fun x => (x : ℂ) * (x : ℂ))) :
    P (fun x : ℝ => (x : ℂ) ^ 2) := by
  simp only [pow_two]
  exact h

/-! ### R2. `deriv_fun_mul hc hd` · goal: product rule
`deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x`, given both factors differentiable at `x`. -/
example (c d : ℝ → ℂ) (x : ℝ) (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (P : ℂ → Prop) (h : P (deriv c x * d x + c x * deriv d x)) :
    P (deriv (fun y => c y * d y) x) := by
  rw [deriv_fun_mul hc hd]
  exact h

/-! ### R3. `Complex.differentiableAt_ofReal` · closes: the cast `ℝ → ℂ` is differentiable at every `x` -/
example (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ)) x := Complex.differentiableAt_ofReal

/-! ### R4. `simp only [Complex.deriv_ofReal]` · goal: `deriv Complex.ofReal x` → `1`
After R2 with R3 the cast shows as `Complex.ofReal`; `fun y => ↑y` is the same function and works too. -/
example (x : ℝ) (P : ℂ → Prop) (h : P 1) : P (deriv Complex.ofReal x) := by
  simp only [Complex.deriv_ofReal]
  exact h

/-! ### R5. `Complex.ofReal_ne_zero.mpr` · context gains `(↑r : ℂ) ≠ 0` from `r ≠ 0` -/
example (r : ℝ) (hr : r ≠ 0) (G : Prop) (k : (r : ℂ) ≠ 0 → G) : G := by
  have hc := Complex.ofReal_ne_zero.mpr hr
  exact k hc

/-! ### R6. `Q.ξ_ne_zero`, `Q.m_ne_zero`, `Q.ω_ne_zero`, `ℏ_ne_zero` · context gains `… ≠ 0` (in `ℝ`) -/
example (Q : HarmonicOscillator) (G : Prop) (k : Q.ξ ≠ 0 → Q.m ≠ 0 → Q.ω ≠ 0 → (ℏ : ℝ) ≠ 0 → G) :
    G := by
  have h1 := Q.ξ_ne_zero
  have h2 := Q.m_ne_zero
  have h3 := Q.ω_ne_zero
  have h4 := ℏ_ne_zero
  exact k h1 h2 h3 h4

/-! ### R7. `rw [show (fun x => g (u x)) = g ∘ u from rfl]` · goal: a nested function → a composition
`deriv_comp` (R8) is stated for `g ∘ u`; Lean does not see `fun x => g (u x)` as that by itself. -/
example (g : ℂ → ℂ) (u : ℝ → ℂ) (P : (ℝ → ℂ) → Prop) (h : P (g ∘ u)) : P (fun x => g (u x)) := by
  rw [show (fun x => g (u x)) = g ∘ u from rfl]
  exact h

/-! ### R8. `deriv_comp x hg hu` · goal: chain rule `deriv (g ∘ u) x = deriv g (u x) * deriv u x`
`g : ℂ → ℂ` must be differentiable over `ℂ` at `u x`, `u : ℝ → ℂ` over `ℝ` at `x`. -/
example (g : ℂ → ℂ) (u : ℝ → ℂ) (x : ℝ) (hg : DifferentiableAt ℂ g (u x))
    (hu : DifferentiableAt ℝ u x) (P : ℂ → Prop) (h : P (deriv g (u x) * deriv u x)) :
    P (deriv (g ∘ u) x) := by
  rw [deriv_comp x hg hu]
  exact h

/-! ### R9. `fun_prop` · closes `DifferentiableAt …` goals built from casts, `exp`, `+`, `*`, `-`, `^`, `/ c`
Use it for the side goals of R2 and R8: `rw [deriv_comp _ (by fun_prop) (by fun_prop)]`. -/
example (x : ℝ) (c : ℂ) : DifferentiableAt ℝ (fun y : ℝ => -(y : ℂ) ^ 2 / c) x := by
  fun_prop

example (z : ℂ) : DifferentiableAt ℂ Complex.exp z := by
  fun_prop

/-! ### R10. `simp only [Complex.deriv_exp]` · goal: `deriv Complex.exp` → `Complex.exp` -/
example (z : ℂ) (P : ℂ → Prop) (h : P (Complex.exp z)) : P (deriv Complex.exp z) := by
  simp only [Complex.deriv_exp]
  exact h

/-! ### R11. `simp only [deriv_div_const]` · goal: `deriv (fun y => f y / c) x` → `deriv f x / c` -/
example (f : ℝ → ℂ) (c : ℂ) (x : ℝ) (P : ℂ → Prop) (h : P (deriv f x / c)) :
    P (deriv (fun y => f y / c) x) := by
  simp only [deriv_div_const]
  exact h

/-! ### R12. `simp only [deriv.fun_neg']` · goal: `deriv (fun y => -f y) x` → `-deriv f x` -/
example (f : ℝ → ℂ) (x : ℝ) (P : ℂ → Prop) (h : P (-deriv f x)) :
    P (deriv (fun y => -f y) x) := by
  simp only [deriv.fun_neg']
  exact h

/-! ### R13. `field_simp` · goal: clears denominators whose `≠ 0` facts are in the context
It multiplies out and cancels; the result is usually finished by `ring`. -/
example (a b c : ℂ) (hc : c ≠ 0) (h : a = c * b) : a / c = b := by
  field_simp
  exact h

/-! ## Unfolding the ground state (milestone `deriv_ground`) -/

/-! ### R14. `rw [eigenfunction_zero]` · goal: `Q.eigenfunction 0` → its formula
`Q.eigenfunction 0 = fun x => 1 / ↑√(√Real.pi * Q.ξ) * Complex.exp (-↑x ^ 2 / (2 * ↑Q.ξ ^ 2))`. -/
example (Q : HarmonicOscillator) (P : (ℝ → ℂ) → Prop)
    (h : P (fun x : ℝ => 1 / (√(√Real.pi * Q.ξ) : ℂ) * Complex.exp (-x ^ 2 / (2 * Q.ξ ^ 2)))) :
    P (Q.eigenfunction 0) := by
  rw [eigenfunction_zero]
  exact h

/-! ### R15. `funext x` · goal: `f = g` (functions) → `f x = g x`; context gains `x` -/
example (f g : ℝ → ℂ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R16. `rw [deriv_const_mul_field']` · goal: `deriv (fun y => u * v y)` → `fun x => u * deriv v x`
The lemma is an equation of functions; applied at `x` it leaves `(fun x => …) x` (R17). -/
example (u : ℂ) (v : ℝ → ℂ) (x : ℝ) (P : ℂ → Prop) (h : P (u * deriv v x)) :
    P (deriv (fun y => u * v y) x) := by
  rw [deriv_const_mul_field']
  exact h

/-! ### R17. `dsimp only` · goal: `(fun y => t y) x` → `t x` (β-reduction); `simp only` does the same -/
example (f : ℝ → ℂ) (x : ℝ) (P : ℂ → Prop) (h : P (f x + 1)) : P ((fun y => f y + 1) x) := by
  dsimp only
  exact h

/-! ## The Schrödinger operator and the eigenvalue (main theorem) -/

/-! ### R18. `rw [schrodingerOperator_eq_ξ]` · goal: `Q.schrodingerOperator ψ` → its formula in `ξ`
`Q.schrodingerOperator ψ = fun x => ↑↑ℏ ^ 2 / (2 * ↑Q.m) * (-deriv (deriv ψ) x + (1 / ↑Q.ξ ^ 2) ^ 2 * ↑x ^ 2 * ψ x)`. -/
example (ψ : ℝ → ℂ) (Q : HarmonicOscillator) (P : (ℝ → ℂ) → Prop)
    (h : P (fun x : ℝ => (ℏ : ℂ) ^ 2 / (2 * Q.m) *
      (-deriv (deriv ψ) x + (1 / (Q.ξ : ℂ) ^ 2) ^ 2 * x ^ 2 * ψ x))) :
    P (Q.schrodingerOperator ψ) := by
  rw [schrodingerOperator_eq_ξ]
  exact h

/-! ### R19. `rw [eigenValue]` · goal: `Q.eigenValue n` → `(↑n + 1 / 2) * ↑ℏ * Q.ω` (a real number) -/
example (n : ℕ) (Q : HarmonicOscillator) (P : ℝ → Prop) (h : P ((n + 1 / 2) * ℏ * Q.ω)) :
    P (Q.eigenValue n) := by
  rw [eigenValue]
  exact h

/-! ### R20. `rw [← Complex.ofReal_pow]` · `↑(r ^ n) = ↑r ^ n`; right to left: goal `↑r ^ n` → `↑(r ^ n)` -/
example (r : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ((r ^ n : ℝ) : ℂ)) : P ((r : ℂ) ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R21. `rw [ξ_sq]` · goal: `Q.ξ ^ 2` → `↑ℏ / (Q.m * Q.ω)` (in `ℝ`, so it needs `ξ ^ 2` uncast: R20 first) -/
example (Q : HarmonicOscillator) (P : ℝ → Prop) (h : P (ℏ / (Q.m * Q.ω))) : P (Q.ξ ^ 2) := by
  rw [ξ_sq]
  exact h

/-! ### R22. `push_cast` · goal: casts `↑` pushed inward, onto the atoms: `↑(a / (b * c))` → `↑a / (↑b * ↑c)` -/
example (a b c : ℝ) (P : ℂ → Prop) (h : P ((a : ℂ) / ((b : ℂ) * (c : ℂ)))) :
    P (((a / (b * c) : ℝ) : ℂ)) := by
  push_cast
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Chain rule on `exp (3x)`: R7, R8 with R9, then R10, R16, R4 -/
example (x : ℝ) :
    deriv (fun y : ℝ => Complex.exp (3 * (y : ℂ))) x = 3 * Complex.exp (3 * (x : ℂ)) := by
  rw [show (fun y : ℝ => Complex.exp (3 * (y : ℂ))) = Complex.exp ∘ (fun y : ℝ => 3 * (y : ℂ)) from rfl]
  rw [deriv_comp _ (by fun_prop) (by fun_prop)]
  simp only [Complex.deriv_exp, deriv_const_mul_field', Complex.deriv_ofReal]
  ring

/-! ### W2. Peeling `/ c` and `-` off a derivative: R11, R12, R4 in one `simp only` -/
example (c : ℂ) (x : ℝ) : deriv (fun y : ℝ => -(y : ℂ) / c) x = -1 / c := by
  simp only [deriv_div_const, deriv.fun_neg', Complex.deriv_ofReal]

/-! ### W3. A real equation, moved into `ℂ`: R20, then `rw [h]`, then R22 -/
example (r a b : ℝ) (h : r ^ 2 = a / b) : (r : ℂ) ^ 2 = (a : ℂ) / b := by
  rw [← Complex.ofReal_pow]
  rw [h]
  push_cast
  rfl

/-! ### W4. Product rule, then clear denominators: R2 with R9, R11, R12, R4, R13 -/
example (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℂ) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (fun y : ℝ => -(y : ℂ) / c * f y) x * c = -f x - x * deriv f x := by
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [deriv_div_const, deriv.fun_neg', Complex.deriv_ofReal]
  field_simp
  ring

end H114Guide
