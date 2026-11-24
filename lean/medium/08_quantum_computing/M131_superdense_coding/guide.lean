/- Guide for M131 (Superdense coding: four orthonormal messages).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other matrices, other sums).
Assumed: Lean basics (E001–E033). Mathlib and physlib names are explained in cheatsheet.md.
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M131Guide

/-! # Part R · Reference entries -/

/-! ## The maximally entangled state and the `√n` factor -/

/-! ### R1. `simp [Ket.MES]` · goal: an amplitude of `Φ = Ket.MES d` → an `if`
`Ket.MES d : Ket (d × d)` is physlib's Φ; `.vec : d × d → ℂ` is its amplitude function. -/
example {d : Type} [Fintype d] [Nonempty d] [DecidableEq d] (i j : d) (P : ℂ → Prop)
    (h : P (if i = j then ((Real.sqrt (Fintype.card d) : ℂ))⁻¹ else 0)) :
    P ((Ket.MES d).vec (i, j)) := by
  simp [Ket.MES]
  exact h

/-! ### R2. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R3. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R4. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact hx

/-! ### R5. `Nat.cast_nonneg` · `0 ≤ (n : α)` for a natural number cast into an ordered semiring
Write `rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]` to close R4's side goal on the spot. -/
example (n : ℕ) (P : ℝ → Prop) (h : P ↑n) : P (√↑n * √↑n) := by
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  exact h

/-! ### R6. `Complex.ofReal_natCast` · `((n : ℝ) : ℂ) = (n : ℂ)` · goal: a double cast → one cast -/
example (n : ℕ) (P : ℂ → Prop) (h : P (n : ℂ)) : P ((n : ℝ) : ℂ) := by
  rw [Complex.ofReal_natCast]
  exact h

/-! ## Inner products and matrix–vector products as sums -/

/-! ### R7. `dotProduct` · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {ι : Type} [Fintype ι] (v w : ι → ℂ) (P : ℂ → Prop) (h : P (∑ i, v i * w i)) :
    P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R8. `Matrix.mulVec` · goal: entry `i` of `M *ᵥ v` → row `i` of `M` dotted with `v` -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι) (P : ℂ → Prop)
    (h : P ((fun j => M i j) ⬝ᵥ v)) : P ((M *ᵥ v) i) := by
  simp only [mulVec]
  exact h

/-! ### R9. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℂ) (P : ℂ → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ x, f x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R10. `Matrix.kroneckerMap_apply` · goal: entry of `A ⊗ₖ B` → product of entries
`A ⊗ₖ B` prints as `kroneckerMap (fun x1 x2 => x1 * x2) A B`. -/
example {α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (i k : α) (j l : β) (P : ℂ → Prop)
    (h : P (A i k * B j l)) : P ((A ⊗ₖ B) (i, j) (k, l)) := by
  simp only [Matrix.kroneckerMap_apply]
  exact h

/-! ### R11. `Pi.star_apply` · goal: entry of a conjugated vector → conjugate of the entry -/
example {ι : Type} (v : ι → ℂ) (i : ι) (P : ℂ → Prop) (h : P (star (v i))) :
    P ((star v) i) := by
  rw [Pi.star_apply]
  exact h

/-! ### R12. `apply_ite star`, then `star_zero` · goal: `star` moves into both branches of an `if` -/
example (c : Prop) [Decidable c] (a : ℂ) (P : ℂ → Prop) (h : P (if c then star a else 0)) :
    P (star (if c then a else 0)) := by
  rw [apply_ite star]
  rw [star_zero]
  exact h

/-! ### R13. `mul_ite`, then `mul_zero` · goal: a factor on the left moves into the `if` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P (a * if c then b else 0) := by
  rw [mul_ite]
  rw [mul_zero]
  exact h

/-! ### R14. `ite_mul`, then `zero_mul` · goal: a factor on the right moves into the `if` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P ((if c then a else 0) * b) := by
  rw [ite_mul]
  rw [zero_mul]
  exact h

/-! ### R15. `Finset.sum_ite_eq`, `Finset.mem_univ`, `if_true` · goal: a sum of an indicator → one term
`Finset.sum_ite_eq` needs `i = j` with the bound variable `j` on the RIGHT (else `Finset.sum_ite_eq'`). -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ℂ) (P : ℂ → Prop)
    (h : P (f i)) : P (∑ j, if i = j then f j else 0) := by
  simp only [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R16. `Complex.star_def` · goal: `star z` on `ℂ` → `(starRingEnd ℂ) z`, the conjugate -/
example (z : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z)) : P (star z) := by
  rw [Complex.star_def]
  exact h

/-! ### R17. `map_inv₀` · goal: a ring map applied to `a⁻¹` → `(f a)⁻¹` (here `f` is the conjugate) -/
example (z : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z)⁻¹) : P ((starRingEnd ℂ) z⁻¹) := by
  rw [map_inv₀]
  exact h

/-! ### R18. `Complex.conj_ofReal` · goal: conjugate of a real cast → the cast itself -/
example (r : ℝ) (P : ℂ → Prop) (h : P ↑r) : P ((starRingEnd ℂ) ↑r) := by
  rw [Complex.conj_ofReal]
  exact h

/-! ### R19. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: factor pushed into a sum -/
example {ι : Type} [Fintype ι] (a : ℂ) (f : ι → ℂ) (P : ℂ → Prop) (h : P (∑ i, a * f i)) :
    P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R20. `refine Finset.sum_congr rfl fun i _ => ?_` · goal: equal sums → equal summands
The context gains the index `i` and its (unused) membership proof `i ∈ Finset.univ`. -/
example {ι : Type} [Fintype ι] (f g : ι → ℂ) (h : ∀ i, f i = g i) : ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i

/-! ## Moving operators across the inner product -/

/-! ### R21. `Matrix.star_mulVec` · `star (M *ᵥ v) = star v ᵥ* Mᴴ` · goal: conjugate of `M v` → row form -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R22. `Matrix.dotProduct_mulVec` · `v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w`; right to left with `←` -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (v w : ι → ℂ) (P : ℂ → Prop)
    (h : P (v ⬝ᵥ (A *ᵥ w))) : P ((v ᵥ* A) ⬝ᵥ w) := by
  rw [← Matrix.dotProduct_mulVec]
  exact h

/-! ### R23. `Matrix.mulVec_mulVec` · `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v` · goal: two products → one -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P ((M * N) *ᵥ v)) : P (M *ᵥ (N *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R24. `Matrix.conjTranspose_kronecker` · `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ` -/
example {α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (P : Matrix (α × β) (α × β) ℂ → Prop)
    (h : P (Aᴴ ⊗ₖ Bᴴ)) : P (A ⊗ₖ B)ᴴ := by
  rw [Matrix.conjTranspose_kronecker]
  exact h

/-! ### R25. `Matrix.conjTranspose_one` · `1ᴴ = 1` · goal: the adjoint of the identity disappears -/
example {β : Type} [DecidableEq β] (P : Matrix β β ℂ → Prop) (h : P 1) :
    P (1 : Matrix β β ℂ)ᴴ := by
  rw [Matrix.conjTranspose_one]
  exact h

/-! ### R26. `Matrix.mul_kronecker_mul` · `(A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'`; use `←` -/
example {α β : Type} [Fintype α] [Fintype β] (A B : Matrix α α ℂ) (A' B' : Matrix β β ℂ)
    (P : Matrix (α × β) (α × β) ℂ → Prop) (h : P ((A * B) ⊗ₖ (A' * B'))) :
    P (A ⊗ₖ A' * B ⊗ₖ B') := by
  rw [← Matrix.mul_kronecker_mul]
  exact h

/-! ### R27. `one_mul` · `1 * a = a` · goal: here `1 * 1` of identity matrices → `1` -/
example {β : Type} [Fintype β] [DecidableEq β] (P : Matrix β β ℂ → Prop) (h : P 1) :
    P ((1 : Matrix β β ℂ) * 1) := by
  rw [one_mul]
  exact h

/-! ### R28. `Matrix.one_apply` · goal: an entry of the identity → `if i = j then 1 else 0` -/
example {ι : Type} [DecidableEq ι] (i j : ι) (P : ℂ → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix ι ι ℂ) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R29. `Matrix.trace`, `Matrix.diag_apply` · goal: `M.trace` → `∑ i, M i i` -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (P : ℂ → Prop) (h : P (∑ i, M i i)) :
    P M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact h

/-! ## The four messages on a qubit -/

/-! ### R30. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def D (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := (n : ℂ) • 1
example (n : ℕ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P ((n : ℂ) • 1)) : P (D n) := by
  unfold D
  exact h

/-! ### R31. `obtain ⟨a, b⟩ := p` · context: a pair `p : α × β` → its two components -/
example {α β : Type} (Q : α × β → Prop) (h : ∀ a b, Q (a, b)) (p : α × β) : Q p := by
  obtain ⟨a, b⟩ := p
  exact h a b

/-! ### R32. `Fintype.card_fin` · `Fintype.card (Fin n) = n` · goal: the dimension becomes a numeral -/
example (P : ℕ → Prop) (h : P 2) : P (Fintype.card (Fin 2)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R33. `Matrix.trace_fin_two` · goal: trace of a 2×2 matrix → `A 0 0 + A 1 1` -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop) (h : P (A 0 0 + A 1 1)) : P A.trace := by
  rw [Matrix.trace_fin_two]
  exact h

/-! ### R34. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (i k : ι) (P : ℂ → Prop)
    (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R35. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example (f : Fin 2 → ℂ) (P : ℂ → Prop) (h : P (f 0 + f 1)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R36. `Matrix.conjTranspose_apply` · goal: entry `(i, j)` of `Mᴴ` → `star` of entry `(j, i)` -/
example {ι : Type} (M : Matrix ι ι ℂ) (i j : ι) (P : ℂ → Prop) (h : P (star (M j i))) :
    P (Mᴴ i j) := by
  rw [Matrix.conjTranspose_apply]
  exact h

/-! ### R37. `Fin.val_one`, `pow_one` (and `Fin.val_zero`, `pow_zero`) · goal: `M ^ (bit : ℕ)` → `M` or `1`
`(b : ℕ)` for `b : Fin 2` is `Fin.val b`, printed `↑b`. -/
example (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P M) :
    P (M ^ ((1 : Fin 2) : ℕ)) := by
  rw [Fin.val_one]
  rw [pow_one]
  exact h

/-! ### R38. `Prod.mk.injEq` · goal: equality of pairs → equality of components -/
example {α β : Type} (a c : α) (b d : β) (P : Prop → Prop) (h : P (a = c ∧ b = d)) :
    P ((a, b) = (c, d)) := by
  rw [Prod.mk.injEq]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An operator crosses the inner product (R21 → R22 → R23): ⟨M v, N w⟩ = ⟨v, Mᴴ N w⟩ -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ ((Mᴴ * N) *ᵥ w) := by
  rw [Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec]

/-! ### W2. Two Kronecker products merge (R24 → R26): (A ⊗ B)ᴴ (C ⊗ D) = (Aᴴ C) ⊗ (Bᴴ D) -/
example {α β : Type} [Fintype α] [Fintype β] (A C : Matrix α α ℂ) (B E : Matrix β β ℂ) :
    (A ⊗ₖ B)ᴴ * (C ⊗ₖ E) = (Aᴴ * C) ⊗ₖ (Bᴴ * E) := by
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]

/-! ### W3. A diagonal indicator collapses a double sum (R13, R15) -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℂ) :
    ∑ i, ∑ j, f i j * (if i = j then 1 else 0) = ∑ i, f i i := by
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ### W4. Cases on a bit: `fin_cases`, then `simp` with R33–R35 (it applies R36, R37 itself) -/
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
example (b : Fin 2) : ((S ^ (b : ℕ))ᴴ * S ^ (b : ℕ)).trace = 2 := by
  fin_cases b
  all_goals simp [S, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

end M131Guide
