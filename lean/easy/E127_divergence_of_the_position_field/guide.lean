/- Guide for E127 (Divergence of the position field).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a constant sum of twos, an
off-diagonal partial derivative in `Space 3`).
Assumed: Lean basics (E001–E033).

Vocabulary (physlib, via `import Physlib.SpaceAndTime.Space.Derivatives.Div`):
* `Space d` is a structure with one field `val : Fin d → ℝ`: a point of ℝᵈ. `x.val i` is the `i`-th
  coordinate of `x`. `Space` alone means `Space 3`.
* `EuclideanSpace ℝ (Fin d)` is Mathlib's ℝᵈ with the Euclidean norm. Its elements are wrapped
  functions; `v.ofLp i` (printed for `v i`) is the `i`-th entry.
* `basis : OrthonormalBasis (Fin d) ℝ (Space d)` is the standard basis; `basis.repr y` is the
  coordinate vector of `y`, an element of `EuclideanSpace ℝ (Fin d)`.
* `∂[i] f x` is `Space.deriv i f x`, the partial derivative of `f : Space d → M` in direction `i`
  at `x`. The infoview prints `Space.deriv i f x`.
* `∇ ⬝ f` is `Space.div f`, the divergence of `f : Space d → EuclideanSpace ℝ (Fin d)`; with
  `open Space` the infoview prints `div f x`.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space

namespace E127Guide

/-! # Part R · Reference entries -/

/-! ## Divergence → a sum of partial derivatives -/

/-! ### R1. `rw [Space.div]` · goal: unfold `div f x` → `∑ i, ∂[i] (i-th component of f) x` -/
example {d : ℕ} (f : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d) (P : ℝ → Prop)
    (h : P (∑ i, ∂[i] (fun y => f y i) x)) : P ((∇ ⬝ f) x) := by
  rw [Space.div]
  exact h

/-! ### R2. `simp only [Space.basis_repr_apply]` · goal: `(basis.repr y).ofLp μ` → `y.val μ`
`Space.basis_repr_apply : (basis.repr p).ofLp i = p.val i`. Use `simp only`, not `rw`: the term sits
under `fun y =>`, and `rw` cannot rewrite a pattern that mentions the bound variable `y`. -/
example {d : ℕ} (μ : Fin d) (P : (Space d → ℝ) → Prop) (h : P (fun y => y.val μ)) :
    P (fun y => basis.repr y μ) := by
  simp only [Space.basis_repr_apply]
  exact h

/-! ### R3. `Space.deriv_component` · goal: `∂[ν]` of the `μ`-th coordinate → `if ν = μ then 1 else 0`
`Space.deriv_component : ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0` (a Kronecker delta).
Inside `simp only [...]` it also works under `∑ i, …`, and `simp` then turns `i = i` into `True`. -/
example {d : ℕ} (μ ν : Fin d) (x : Space d) (P : ℝ → Prop) (h : P (if ν = μ then 1 else 0)) :
    P (∂[ν] (fun y => y.val μ) x) := by
  rw [Space.deriv_component]
  exact h

/-! ### R4. `if_true` · `(if True then a else b) = a` · goal: drop a decided `if` -/
example {α : Type} (a b : α) (P : α → Prop) (h : P a) : P (if True then a else b) := by
  simp only [if_true]
  exact h

/-! ## A sum of ones → its number of terms -/

/-! ### R5. `Finset.sum_const` · `∑ _x ∈ s, b = s.card • b` · goal: constant sum → count `•` value
`∑ _i : ι, b` is `∑ _i ∈ Finset.univ, b`, so `s` is `Finset.univ` here. -/
example {ι M : Type} [Fintype ι] [AddCommMonoid M] (b : M) (P : M → Prop)
    (h : P ((Finset.univ : Finset ι).card • b)) : P (∑ _i : ι, b) := by
  rw [Finset.sum_const]
  exact h

/-! ### R6. `Finset.card_univ` · `Finset.univ.card = Fintype.card α` · goal: size of `univ` → size of the type -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) :
    P (Finset.univ : Finset α).card := by
  rw [Finset.card_univ]
  exact h

/-! ### R7. `Fintype.card_fin` · `Fintype.card (Fin n) = n` · goal: size of `Fin n` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R8. `nsmul_eq_mul` · `n • a = ↑n * a` · goal: `ℕ`-multiple `•` → product with the cast `↑n` -/
example {α : Type} [NonAssocSemiring α] (n : ℕ) (a : α) (P : α → Prop) (h : P (↑n * a)) :
    P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R9. `mul_one` · `a * 1 = a` · goal: drop `* 1` -/
example {α : Type} [MulOneClass α] (a : α) (P : α → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A constant sum of twos: R5 → R6 → R7 → R8 (`rw` closes `↑n * 2 = ↑n * 2` by `rfl`) -/
example (n : ℕ) : ∑ _i : Fin n, (2 : ℝ) = n * 2 := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  rw [nsmul_eq_mul]

/-! ### W2. An off-diagonal partial derivative in `Space 3`: R2 and R3 in one `simp only`, then
`simp` decides `0 = 1` in `Fin 3` is false -/
example (x : Space 3) : ∂[0] (fun y => basis.repr y 1) x = 0 := by
  simp only [Space.basis_repr_apply, Space.deriv_component]
  simp

/-! ### W3. `simp` alone does W1's chain R5 → R6 → R7 → R8 in one step -/
example (n : ℕ) : ∑ _i : Fin n, (2 : ℝ) = n * 2 := by simp

end E127Guide
