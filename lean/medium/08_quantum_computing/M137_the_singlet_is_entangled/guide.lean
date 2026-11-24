/- Guide for M137 (The singlet is entangled).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of the goal or hypothesis": the step changes only the part shown inside
`P (…)`. A hypothesis `h` in an entry is only there to finish the example; it shows what changed.
Part W: worked combinations on objects that are NOT the exercise's (the product state |00⟩, plain
complex numbers).
Assumed: Lean basics.
-/
import QuantumInfo.States.Pure.Braket

namespace M137Guide

/-! # Part R · Reference entries -/

/-! ## Entangled means "no product decomposition" -/

/-! ### R1. `unfold Ket.IsEntangled Ket.IsProd` · goal: `ψ.IsEntangled` → `¬∃ ξ φ, ψ = ξ ⊗ᵠ φ`
Optional: it only shows what the definitions say. R2 sees through them without it. -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (ψ : Ket (d₁ × d₂))
    (h : ¬∃ ξ φ, ψ = ξ ⊗ᵠ φ) : ψ.IsEntangled := by
  unfold Ket.IsEntangled Ket.IsProd
  exact h

/-! ### R2. `rintro ⟨ξ, φ, h⟩` · goal `¬∃ ξ φ, …` → context gains `ξ φ h`, goal `False`
`¬ A` is `A → False`, so `rintro` introduces the `∃` and takes it apart in one step. It works on
`ψ.IsEntangled` directly: `rintro` unfolds definitions until it sees the `¬`/`∃`. -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (ψ : Ket (d₁ × d₂))
    (hne : ∀ (ξ : Ket d₁) (φ : Ket d₂), ψ ≠ ξ ⊗ᵠ φ) : ψ.IsEntangled := by
  rintro ⟨ξ, φ, h⟩
  exact hne ξ φ h

/-! ## From an equation of kets to an equation of amplitudes -/

/-! ### R3. `have hi := congrArg (fun χ : Ket d => χ i) h` · context gains `hi : ψ i = χ i`
`congrArg f : a = b → f a = f b`. With `f` = "evaluate at basis index `i`", an equation of kets
gives an equation of complex amplitudes. -/
example {d : Type} [Fintype d] (ψ χ : Ket d) (i : d) (P : ℂ → Prop) (hP : P (χ i)) (h : ψ = χ) :
    P (ψ i) := by
  have hi := congrArg (fun χ : Ket d => χ i) h
  rw [hi]
  exact hP

/-! ### R4. `Ket.apply` · `ψ i = ψ.vec i` · context: the coercion `ψ i` → the field `ψ.vec i` -/
example {d : Type} [Fintype d] (ψ : Ket d) (i : d) (P : ℂ → Prop) (h : P (ψ i)) :
    P (ψ.vec i) := by
  rw [Ket.apply] at h
  exact h

/-! ### R5. `Ket.prod` · goal (or `at h`: context): amplitude of `ξ ⊗ᵠ φ` at `(i, j)` → `ξ.vec i * φ.vec j`
`simp only [Ket.prod]` exposes the structure literal; `Ket.apply` then reads off its `vec`. -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (ξ : Ket d₁) (φ : Ket d₂) (i : d₁) (j : d₂)
    (P : ℂ → Prop) (h : P (ξ.vec i * φ.vec j)) : P ((ξ ⊗ᵠ φ) (i, j)) := by
  simp only [Ket.prod]
  simp only [Ket.apply]
  exact h

/-! ### R6. `simp only [D]` · goal (or `at h`: context): a ket you defined → the body of its `vec` field
`D` is the product state |00⟩, defined here only for this entry and W1. -/
noncomputable def D : Ket (Fin 2 × Fin 2) where
  vec := fun p => if p = (0, 0) then 1 else 0
  normalized' := by simp [Fin.sum_univ_two, Fintype.sum_prod_type]

example (i : Fin 2 × Fin 2) (P : ℂ → Prop) (h : P (if i = (0, 0) then 1 else 0)) : P (D i) := by
  rw [Ket.apply]
  simp only [D]
  exact h

/-! ### R7. `simp` on `if (i, j) = (k, l) then …` with numerals · goal (or `at h`: context): the `if` → one branch
`simp` decides the pair equality (`Prod.mk.injEq`: `(a, b) = (c, d) ↔ a = c ∧ b = d`, and
`0 ≠ 1` in `Fin 2`), then keeps the true branch (`if_pos`) or drops the false one (`if_neg`). -/
example (a b c : ℂ) (P : ℂ → Prop) (h : P c) :
    P (if ((0 : Fin 2), (0 : Fin 2)) = (0, 1) then a
      else if ((0 : Fin 2), (0 : Fin 2)) = (1, 0) then b else c) := by
  simp
  exact h

/-! ## Reading the amplitude equations -/

/-! ### R8. `one_div` · `1 / a = a⁻¹` · context: why `simp` prints `1 / √2` as `(↑√2)⁻¹` -/
example (a : ℂ) (P : ℂ → Prop) (h : P (1 / a)) : P a⁻¹ := by
  rw [one_div] at h
  exact h

/-! ### R9. `zero_eq_mul` · `0 = a * b ↔ a = 0 ∨ b = 0` · context: a zero product → a disjunction
`mul_eq_zero` is the same with `a * b = 0` on the left. Both hold in `ℂ` (no zero divisors). -/
example (a b : ℂ) (P : Prop) (hP : a = 0 ∨ b = 0 → P) (h : 0 = a * b) : P := by
  rw [zero_eq_mul] at h
  exact hP h

/-! ### R10. `rcases h with h | h` · goal list: one goal per side of `h : A ∨ B` -/
example (A B G : Prop) (h : A ∨ B) (ha : A → G) (hb : B → G) : G := by
  rcases h with h | h
  exact ha h
  exact hb h

/-! ### R11. `simp [h] at h1` with `h : a = 0` · context: substitute `a := 0`, then `0 * b` → `0` -/
example (a b c : ℂ) (P : Prop) (hP : c = 0 → P) (h : a = 0) (h1 : c = a * b) : P := by
  simp [h] at h1
  exact hP h1

/-! ### R12. `simp at h` with a false `h` · goal list: the goal is closed
`simp` rewrites `h` to `False` and then closes any goal. For `(↑√3)⁻¹ = 0` it uses `inv_eq_zero`,
`Complex.ofReal_eq_zero` (`(↑x : ℂ) = 0 ↔ x = 0`), `Real.sqrt_eq_zero` (`0 ≤ x → (√x = 0 ↔ x = 0)`,
side condition by `Nat.ofNat_nonneg`) and `OfNat.ofNat_ne_zero` (`3 ≠ 0`);
for `-1 / ↑√3 = 0` it adds `div_eq_zero_iff`, `neg_eq_zero` and `one_ne_zero`. -/
example (G : Prop) (h : ((√3 : ℝ) : ℂ)⁻¹ = 0) : G := by
  simp at h

example (G : Prop) (h : -1 / ((√3 : ℝ) : ℂ) = 0) : G := by
  simp at h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Amplitudes of a product decomposition of |00⟩: R3 twice, then one `simp` (R4–R7, R9) -/
example (ξ φ : Ket (Fin 2)) (h : D = ξ ⊗ᵠ φ) : ξ.vec 0 * φ.vec 0 = 1 := by
  have h00 := congrArg (fun χ : Ket _ => χ (0, 0)) h
  have h01 := congrArg (fun χ : Ket _ => χ (0, 1)) h
  simp [D, Ket.prod, Ket.apply] at h00 h01
  exact h00.symm

/-! ### W2. Contradiction from amplitude equations: R9, R10, then R11 and R12 in both goals -/
example (a b c d : ℂ) (h1 : 1 = a * b) (h2 : 2 = c * d) (h0 : 0 = a * d) : False := by
  rw [zero_eq_mul] at h0
  rcases h0 with h | h <;> simp [h] at h1 h2

end M137Guide
