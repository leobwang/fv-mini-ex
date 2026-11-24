/- Guide for M181 (The magnetic force does no work).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`⟪a, a⟫`, other definitions).
Assumed: Lean basics (E001–E033).
-/
import Physlib.SpaceAndTime.Space.CrossProduct

open Space InnerProductSpace Matrix

namespace M181Guide

/-! # Part R · Reference entries -/

/-! ## The dot product as a sum of components -/

/-! ### R1. `PiLp.inner_apply` · goal: `⟪x, y⟫_ℝ` on `EuclideanSpace` → a sum over the index
`x.ofLp i` is the `i`-th component of `x` (what you type as `x i`). -/
example {ι : Type} [Fintype ι] (x y : EuclideanSpace ℝ ι) (P : ℝ → Prop)
    (h : P (∑ i, ⟪x.ofLp i, y.ofLp i⟫_ℝ)) : P ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply]
  exact h

/-! ### R2. `Fin.sum_univ_three` · goal: a sum over `Fin 3` → three terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 3 → β) (P : β → Prop) (h : P (f 0 + f 1 + f 2)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_three]
  exact h

/-! ### R3. `cross_apply` (via `simp`) · goal: a component of `a ⨯ₑ₃ b` → its formula
`⨯ₑ₃` is notation that wraps Mathlib's `⨯₃` (`crossProduct`, on `Fin 3 → ℝ`) in `WithLp.equiv`;
`simp` removes the wrappers, applies `cross_apply`, and picks the component of the `![…]` literal. -/
example (a b : EuclideanSpace ℝ (Fin 3)) (P : ℝ → Prop) (h : P (a 1 * b 2 - a 2 * b 1)) :
    P ((a ⨯ₑ₃ b) 0) := by
  simp [cross_apply]
  exact h

/-! ### R4. `RCLike.inner_apply`, `conj_trivial` · goal: `⟪x, y⟫_ℝ` of two reals → `y * x`
`simp` applies both by itself. `(starRingEnd ℝ) x` is the conjugate of `x`, which is `x` on `ℝ`. -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (y * x)) : P ⟪x, y⟫_ℝ := by
  rw [RCLike.inner_apply]
  rw [conj_trivial]
  exact h

/-! ### R5. `ring` · closes a polynomial identity, including one where all terms cancel -/
example (a b c : ℝ) : (a * b - b * a) * c + (b * c - c * b) * a = 0 := by
  ring

/-! ## Linearity of the inner product in its second argument -/

/-! ### R6. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def double (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) := (2 : ℝ) • x

example (x : EuclideanSpace ℝ (Fin 3)) (P : EuclideanSpace ℝ (Fin 3) → Prop)
    (h : P ((2 : ℝ) • x)) : P (double x) := by
  unfold double
  exact h

/-! ### R7. `real_inner_smul_right` · `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ` · goal: scalar pulled out -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) (r : ℝ) (P : ℝ → Prop)
    (h : P (r * ⟪x, y⟫_ℝ)) : P ⟪x, r • y⟫_ℝ := by
  rw [real_inner_smul_right]
  exact h

/-! ### R8. `inner_add_right` · `⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫` · goal: the sum split -/
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y z : F) (P : ℝ → Prop)
    (h : P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)) : P ⟪x, y + z⟫_ℝ := by
  rw [inner_add_right]
  exact h

/-! ### R9. `add_zero` · `a + 0 = a` · goal: a trailing `+ 0` removed (`zero_add` for `0 + a`) -/
example {α : Type} [AddZeroClass α] (a : α) (P : α → Prop) (h : P a) : P (a + 0) := by
  rw [add_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A dot product by components: R1, then `simp` with R2 (it applies R4), then R5 -/
example (a : EuclideanSpace ℝ (Fin 3)) : ⟪a, a⟫_ℝ = a 2 ^ 2 + a 1 ^ 2 + a 0 ^ 2 := by
  simp only [PiLp.inner_apply]
  simp [Fin.sum_univ_three]
  ring

/-! ### W2. One component of two cross products: R3, then R5 -/
example (a b : EuclideanSpace ℝ (Fin 3)) : (a ⨯ₑ₃ b) 2 + (b ⨯ₑ₃ a) 2 = 0 := by
  simp [cross_apply]
  ring

/-! ### W3. Unfold, pull out the scalar, split the sum, drop the zero term: R6, R7, R8, rw [h], `zero_add` -/
noncomputable def mix (r : ℝ) (u w : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  r • (w + u)

example (r : ℝ) (x u w : EuclideanSpace ℝ (Fin 3)) (h : ⟪x, w⟫_ℝ = 0) :
    ⟪x, mix r u w⟫_ℝ = r * ⟪x, u⟫_ℝ := by
  unfold mix
  rw [real_inner_smul_right]
  rw [inner_add_right]
  rw [h]
  rw [zero_add]

end M181Guide
