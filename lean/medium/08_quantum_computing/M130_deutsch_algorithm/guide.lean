/- Guide for M130 (Deutsch's algorithm).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (√3, a NOT gate, another oracle).
Assumed: Lean basics.
-/
import Mathlib

open Matrix Complex
open scoped Kronecker

namespace M130Guide

/-! # Part R · Reference entries -/

/-! ## Facts proved first -/

/-! ### R1. `decide` · closes a statement about finitely many concrete values
`Fin n` has exactly the elements `0, …, n-1`, so Lean can check a `∀` over it by trying each one. -/
example : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide

/-! ### R2. `rw [show a = b by ring]` · goal: rewrite with an equation proved on the spot
`show a = b by ring` is a proof term for `a = b`; `rw` then replaces `a` by `b`. -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((x ^ 2) ^ 3)) : P (x ^ 6) := by
  rw [show x ^ 6 = (x ^ 2) ^ 3 by ring]
  exact h

/-! ### R3. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal rewritten, plus side goal `0 ≤ x`
Write `rw [Real.sq_sqrt (by norm_num)]` to close the side goal on the spot. -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt]
  exact h
  exact hx

/-! ### R4. `norm_num` · closes a goal made of numerals (`^`, `/`, `⁻¹` included) -/
example : (2 : ℝ) ^ 3 * (1 / 8) = 1 := by norm_num

/-! ## Splitting on the values of a function `Fin 2 → Fin 2` -/

/-! ### R5. `rcases two (g 0) with h0 | h0` · goal list: one goal → two; context gains `h0`
`two (g 0)` instantiates the fact `two : ∀ x, x = 0 ∨ x = 1` at `x := g 0`. -/
example (g : Fin 2 → Fin 2) (two : ∀ x : Fin 2, x = 0 ∨ x = 1) (P : Fin 2 → Prop)
    (p0 : P 0) (p1 : P 1) : P (g 0) := by
  rcases two (g 0) with h0 | h0
  · rw [h0]; exact p0
  · rw [h0]; exact p1

/-! ### R6. `simp [h0, h1]` · goal: hypotheses `g 0 = 0`, `g 1 = 1` used as rewrite rules
After the values are substituted, `simp` decides the condition `0 = 1` and drops the `if`. -/
example (g : Fin 2 → Fin 2) (a b : ℂ) (P : ℂ → Prop) (h0 : g 0 = 0) (h1 : g 1 = 1) (h : P b) :
    P (if g 0 = g 1 then a else b) := by
  simp [h0, h1]
  exact h

/-! ## Unfolding the circuit (name R8, R9; `simp` applies R7, R10, R11, R14, R15 by itself,
and R12, R13 when the indices are numerals) -/

/-! ### R7. `Matrix.of_apply` · goal: entry of `Matrix.of f` → `f i j`
`Matrix.of` turns a function of two indices into a matrix. -/
example {m n α : Type} (f : m → n → α) (i : m) (j : n) (P : α → Prop) (h : P (f i j)) :
    P (Matrix.of f i j) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R8. `Matrix.mulVec`, `dotProduct` · goal: entry of `M *ᵥ v` → a sum
`M *ᵥ v` is the matrix `M` times the column vector `v`; `u ⬝ᵥ v` is the dot product. -/
example {α : Type} [NonUnitalNonAssocSemiring α] (M : Matrix (Fin 2) (Fin 2) α) (v : Fin 2 → α)
    (i : Fin 2) (P : α → Prop) (h : P (∑ j, M i j * v j)) : P ((M *ᵥ v) i) := by
  simp only [Matrix.mulVec]
  simp only [dotProduct]
  exact h

/-! ### R9. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β γ : Type} [Fintype α] [Fintype β] [AddCommMonoid γ] (f : α × β → γ) (P : γ → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ x, f x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R10. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R11. `Matrix.kroneckerMap_apply` · goal: entry of `A ⊗ₖ B` → product of two entries
Rows and columns of `A ⊗ₖ B` are pairs; `i.1`, `i.2` are the two components of `i`. -/
example {α : Type} [Mul α] (A B : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2 × Fin 2) (P : α → Prop)
    (h : P (A i.1 j.1 * B i.2 j.2)) : P ((A ⊗ₖ B) i j) := by
  rw [Matrix.kroneckerMap_apply]
  exact h

/-! ### R12. `Matrix.one_apply` · goal: entry of the identity matrix `1` → an `if` -/
example {α : Type} [Zero α] [One α] (i j : Fin 2) (P : α → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix (Fin 2) (Fin 2) α) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R13. `Pi.single_apply` · goal: entry of the basis vector `Pi.single i x` → an `if`
`Pi.single i x` is the vector with `x` at index `i` and `0` elsewhere. -/
example {α : Type} [Zero α] (i i' : Fin 2) (x : α) (P : α → Prop) (h : P (if i' = i then x else 0)) :
    P ((Pi.single i x : Fin 2 → α) i') := by
  rw [Pi.single_apply]
  exact h

/-! ### R14. Entry of `c • !![a, b; d, e]` (`Matrix.smul_apply`, `smul_eq_mul`, `Matrix.of_apply`,
`Matrix.cons_val_…`) · goal: → `c * (that entry)` -/
example (c a b d e : ℂ) (P : ℂ → Prop) (h : P (c * d)) : P ((c • !![a, b; d, e]) 1 0) := by
  simp
  exact h

/-! ### R15. `Fin 2` arithmetic and `if` · goal: `simp` computes `1 + 1 = 0` and drops a decided `if`
In `Fin 2`, `+` is addition mod 2, i.e. XOR. -/
example (a b : ℂ) (P : ℂ → Prop) (h : P a) : P (if (1 : Fin 2) + 1 = 0 then a else b) := by
  simp
  exact h

/-! ## Probabilities: `normSq`, real and imaginary parts -/

/-! ### R16. `Complex.normSq_apply` · goal: `normSq z` → `z.re * z.re + z.im * z.im` (= |z|²) -/
example (z : ℂ) (P : ℝ → Prop) (h : P (z.re * z.re + z.im * z.im)) : P (Complex.normSq z) := by
  rw [Complex.normSq_apply]
  exact h

/-! ### R17. `.re` of a product of real casts (`Complex.mul_re`, `Complex.ofReal_re`,
`Complex.ofReal_im`) · goal: `simp` turns it back into a real product -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (x * y)) : P ((↑x * ↑y : ℂ).re) := by
  simp
  exact h

/-! ### R18. `.re` of an inverse cast (`Complex.inv_re`, `Complex.normSq_ofReal`,
`Real.mul_self_sqrt`) · goal: `simp` turns `(↑√x)⁻¹.re` into `√x / x`; its `.im` is `0` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P (√x / x)) : P ((↑√x : ℂ)⁻¹.re) := by
  simp [hx]
  exact h

/-! ### R19. `ring_nf` · goal put in ring normal form: a product of `a / 2` → `a ^ 3 * (1 / 8)` -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a ^ 3 * (1 / 8))) : P (a / 2 * (a / 2 * (a / 2))) := by
  ring_nf
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A NOT gate on the first qubit of `|0⟩|0⟩`: R8–R13 in one `simp` call -/
def NOT : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
example :
    ((NOT ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ
      (fun p => (Pi.single 0 1 : Fin 2 → ℂ) p.1 * (Pi.single 0 1 : Fin 2 → ℂ) p.2)) (1, 0) = 1 := by
  simp [NOT, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Pi.single_apply]

/-! ### W2. Split on the value of `g 0`, then `simp [h]` (R5, R6, R15) -/
example (g : Fin 2 → Fin 2) : ∑ y : Fin 2, (if y = g 0 + 1 then (1 : ℂ) else 0) = 1 := by
  have two : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases two (g 0) with h | h
  all_goals simp [h]

/-! ### W3. A power of a square root (R2, R3, R4) -/
example : Real.sqrt 3 ^ 4 = 9 := by
  rw [show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring]
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

/-! ### W4. A probability with `(√3)⁻¹`: `simp` (R16–R18), then `ring_nf` (R19), `rw [s4]`, R4 -/
example : Complex.normSq ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹) * 9 = 1 := by
  have s4 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num)]
    norm_num
  simp [Complex.normSq_apply]
  ring_nf
  rw [s4]
  norm_num

end M130Guide
