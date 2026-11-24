/- Guide for E114 (CNOT makes a Bell state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the SWAP gate, X on qubit 1).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix
open scoped Kronecker

namespace E114Guide

/-! # Part R · Reference entries -/

/-! ## A vector on pairs → its four entries -/

/-! ### R1. `ext ⟨a, b⟩` (lemma `funext`) · goal `v = w` on `Fin 2 × Fin 2` → one entry `(a, b)`
`ext` reduces an equation of functions to one input; the pattern `⟨a, b⟩` splits that input, a pair,
into its two components, so the context gains `a b : Fin 2` instead of one `p : Fin 2 × Fin 2`. -/
example {α : Type} (v w : Fin 2 × Fin 2 → α) (h : ∀ a b, v (a, b) = w (a, b)) : v = w := by
  ext ⟨a, b⟩
  exact h a b

/-! ### R2. `fin_cases a` · context loses `a : Fin 2`; goal → one goal per value of `a`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the value `0`. `fin_cases a <;> fin_cases b` gives 4 goals. -/
example {α : Type} (v w : Fin 2 × Fin 2 → α) (h : ∀ a b, v (a, b) = w (a, b))
    (a b : Fin 2) : v (a, b) = w (a, b) := by
  fin_cases a
  exacts [h 0 b, h 1 b]

/-! ## Evaluating one entry -/

/-! ### R3. Unfold a definition: `simp only [D]` · goal: the name `D` → its body -/
def D : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
example (P : Matrix (Fin 2) (Fin 2) ℂ → Prop) (h : P !![0, 1; 1, 0]) : P D := by
  simp only [D]
  exact h

/-! ### R4. `Matrix.mulVec` · goal: `(M *ᵥ v) i` → dot product of row `i` of `M` with `v`
`M *ᵥ v` is matrix times column vector. The index types `m`, `n` are any types; here both are
`Fin 2 × Fin 2`. `[Fintype n]` says `n` is finite, so the sum over it exists. -/
example {α : Type} [NonUnitalNonAssocSemiring α] {m n : Type} [Fintype n] (M : Matrix m n α)
    (v : n → α) (i : m) (P : α → Prop) (h : P ((fun j => M i j) ⬝ᵥ v)) : P ((M *ᵥ v) i) := by
  simp only [Matrix.mulVec]
  exact h

/-! ### R5. `dotProduct` · goal: `u ⬝ᵥ v` → `∑ j, u j * v j` -/
example {α : Type} [NonUnitalNonAssocSemiring α] {n : Type} [Fintype n] (u v : n → α)
    (P : α → Prop) (h : P (∑ j, u j * v j)) : P (u ⬝ᵥ v) := by
  simp only [dotProduct]
  exact h

/-! ### R6. `Matrix.mulVec_mulVec` · goal: `A *ᵥ (B *ᵥ v)` → `(A * B) *ᵥ v`
`simp` applies this by itself. `*ᵥ` groups to the right, so `A *ᵥ B *ᵥ v` means `A *ᵥ (B *ᵥ v)`. -/
example {α : Type} [NonUnitalSemiring α] {l m n : Type} [Fintype m] [Fintype n]
    (A : Matrix l m α) (B : Matrix m n α) (v : n → α) (P : (l → α) → Prop)
    (h : P ((A * B) *ᵥ v)) : P (A *ᵥ (B *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R7. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum
`∑ x, f x = ∑ x, ∑ y, f (x, y)`. `simp` does not apply it by itself. -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 × Fin 2 → β) (P : β → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ p, f p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R8. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms (`simp` does this by itself) -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R9. `Matrix.of_apply` · goal: entry of `Matrix.of f` → `f p q` (`simp` does this by itself) -/
example {α : Type} (f : Fin 2 × Fin 2 → Fin 2 × Fin 2 → α) (p q : Fin 2 × Fin 2) (P : α → Prop)
    (h : P (f p q)) : P (Matrix.of f p q) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R10. `Matrix.kroneckerMap_apply` · goal: entry of `A ⊗ₖ B` → `A i j * B k l`
`A ⊗ₖ B` is printed `kroneckerMap (fun x1 x2 => x1 * x2) A B`. `simp` does this by itself. -/
example {α : Type} [Mul α] (A B : Matrix (Fin 2) (Fin 2) α) (i j k l : Fin 2) (P : α → Prop)
    (h : P (A i j * B k l)) : P ((A ⊗ₖ B) (i, k) (j, l)) := by
  simp only [Matrix.kroneckerMap_apply]
  exact h

/-! ### R11. `Matrix.one_apply` · goal: entry of the identity matrix → `if i = j then 1 else 0` -/
example {α : Type} [Zero α] [One α] {n : Type} [DecidableEq n] (i j : n) (P : α → Prop)
    (h : P (if i = j then 1 else 0)) : P ((1 : Matrix n n α) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R12. `Pi.single_apply` · goal: `Pi.single i x j` → `if j = i then x else 0`
`Pi.single i x` is the vector with `x` at index `i` and `0` elsewhere. `simp` evaluates it by itself
once `i` and `j` are concrete. -/
example {α : Type} [Zero α] (i j : Fin 2) (x : α) (P : α → Prop) (h : P (if j = i then x else 0)) :
    P ((Pi.single i x : Fin 2 → α) j) := by
  rw [Pi.single_apply]
  exact h

/-! ### R13. `Matrix.smul_apply`, `smul_eq_mul` · goal: entry of `c • M` → `c * (entry of M)` -/
example (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (P : ℂ → Prop) (h : P (c * M i j)) :
    P ((c • M) i j) := by
  rw [Matrix.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R14. Entry of a literal `!![a, b; c, d] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ### R15. `Fin 2` arithmetic: `simp` (or `decide`) · goal: `1 + 1` → `0`
Addition in `Fin 2` is mod 2, i.e. XOR. -/
example (P : Fin 2 → Prop) (h : P 0) : P ((1 : Fin 2) + 1) := by
  simp
  exact h

/-! ### R16. `if` with a concrete condition: `simp` · goal: `if c then x else y` → the right branch
`simp` decides `c` when it is made of `Fin 2` numerals, `=`, `∧`, `+`. -/
example {α : Type} (x y : α) (P : α → Prop) (h : P y) :
    P (if (0 : Fin 2) = 1 ∧ (1 : Fin 2) = 1 then x else y) := by
  simp
  exact h

/-! ## A matrix on pairs → its sixteen entries -/

/-! ### R17. `ext ⟨a, b⟩ ⟨c, d⟩` (lemma `Matrix.ext`) · goal `M = N` → one entry `((a, b), (c, d))` -/
example {α : Type} (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) α)
    (h : ∀ a b c d, M (a, b) (c, d) = N (a, b) (c, d)) : M = N := by
  ext ⟨a, b⟩ ⟨c, d⟩
  exact h a b c d

/-! ### R18. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {α : Type} [Mul α] [AddCommMonoid α] {l m n : Type} [Fintype m] (M : Matrix l m α)
    (N : Matrix m n α) (i : l) (k : n) (P : α → Prop) (h : P (∑ j, M i j * N j k)) :
    P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R19. `Prod.mk.injEq` · goal: `(a, b) = (c, d)` → `a = c ∧ b = d` (`simp` does this by itself) -/
example {α : Type} (a b c d : α) (P : Prop → Prop) (h : P (a = c ∧ b = d)) :
    P ((a, b) = (c, d)) := by
  rw [Prod.mk.injEq]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- The SWAP gate: |a, b⟩ ↦ |b, a⟩. -/
def SW :=
  Matrix.of fun (p q : Fin 2 × Fin 2) => if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0
/-- |01⟩ and |10⟩, written as products of one-qubit vectors. -/
def v01 : Fin 2 × Fin 2 → ℂ := fun p => ![1, 0] p.1 * ![0, 1] p.2
def v10 : Fin 2 × Fin 2 → ℂ := fun p => ![0, 1] p.1 * ![1, 0] p.2

/-! ### W1. Without R7, `simp` stops at a sum over pairs it cannot expand -/
example : (SW *ᵥ v01) (1, 0) = 1 := by
  simp [SW, v01, Matrix.mulVec, dotProduct]
  simp [Fintype.sum_prod_type]

/-! ### W2. A vector equation on pairs: R1, R2, then `simp` with R3–R5 and R7 -/
example : SW *ᵥ v01 = v10 := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b
  all_goals simp [SW, v01, v10, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-! ### W3. A Kronecker product acting on a vector: `X ⊗ₖ 1` flips qubit 1 (R10, R11 inside `simp`) -/
example : (D ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v01 = fun p => ![0, 1] p.1 * ![0, 1] p.2 := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b
  all_goals simp [D, v01, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-! ### W4. A matrix equation on pairs: R17, R2 four times, then `simp` with R18 and R7 -/
example : SW * SW = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals simp [SW, Matrix.mul_apply, Fintype.sum_prod_type]

end E114Guide
