/- Guide for M129 (GHZ: Mermin's operator identity).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`Z`, `A`, two-qubit strings).
Assumed: Lean basics, and M126 (2×2 matrices, `!![…]`, `ext`, `fin_cases`).
-/
import Mathlib

open Matrix Complex
open scoped Kronecker

namespace M129Guide

/-! # Part R · Reference entries -/

/-! ## One-qubit products -/

/-! ### R1. `simp` on a product of literal matrices · goal: `!![…] * !![…]` → one literal matrix -/
example {α : Type} [CommRing α] (a b c d p q r s : α) (P : Matrix (Fin 2) (Fin 2) α → Prop)
    (h : P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]) :
    P (!![a, b; c, d] * !![p, q; r, s]) := by
  simp
  exact h

/-! ## Kronecker products -/

/-! ### R2. Unfold a definition built from `⊗ₖ`: `simp only [D]` · goal: `D A B` → `A ⊗ₖ B`
The infoview prints `A ⊗ₖ B` as `kroneckerMap (fun x1 x2 => x1 * x2) A B`. -/
def D (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := A ⊗ₖ B
example (A B : Matrix (Fin 2) (Fin 2) ℂ) (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → Prop)
    (h : P (A ⊗ₖ B)) : P (D A B) := by
  simp only [D]
  exact h

/-! ### R3. `Matrix.mul_kronecker_mul` · `(A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'`
Right to left (`←`): a product of two Kronecker products → the Kronecker product of the products. -/
example {α m n : Type} [CommSemiring α] [Fintype m] [Fintype n] (A B : Matrix m m α)
    (A' B' : Matrix n n α) (P : Matrix (m × n) (m × n) α → Prop) (h : P ((A * B) ⊗ₖ (A' * B'))) :
    P (A ⊗ₖ A' * B ⊗ₖ B') := by
  rw [← Matrix.mul_kronecker_mul]
  exact h

/-! ### R4. `Matrix.smul_kronecker` · `(r • A) ⊗ₖ B = r • (A ⊗ₖ B)` · goal: scalar out of the left factor -/
example {α m n : Type} [CommRing α] (r : α) (A : Matrix m m α) (B : Matrix n n α)
    (P : Matrix (m × n) (m × n) α → Prop) (h : P (r • A ⊗ₖ B)) : P ((r • A) ⊗ₖ B) := by
  rw [Matrix.smul_kronecker]
  exact h

/-! ### R5. `Matrix.kronecker_smul` · `A ⊗ₖ (r • B) = r • (A ⊗ₖ B)` · goal: scalar out of the right factor -/
example {α m n : Type} [CommRing α] (r : α) (A : Matrix m m α) (B : Matrix n n α)
    (P : Matrix (m × n) (m × n) α → Prop) (h : P (r • A ⊗ₖ B)) : P (A ⊗ₖ (r • B)) := by
  rw [Matrix.kronecker_smul]
  exact h

/-! ### R6. `neg_one_smul` · `(-1 : R) • x = -x` · goal: the scalar `-1` → a minus sign -/
example {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (x : M) (P : M → Prop) (h : P (-x)) :
    P ((-1 : R) • x) := by
  rw [neg_one_smul]
  exact h

/-! ## Matrices acting on a vector -/

/-! ### R7. `have h := congrArg f e` · context gains `h : f A = f B` from `e : A = B`
`(· *ᵥ v)` is the function `fun M => M *ᵥ v`; Lean beta-reduces `f A` to `A *ᵥ v` in `h`. -/
example {α n : Type} [CommRing α] [Fintype n] (A B : Matrix n n α) (v : n → α) (e : A = B)
    (G : Prop) (g : A *ᵥ v = B *ᵥ v → G) : G := by
  have h := congrArg (· *ᵥ v) e
  exact g h

/-! ### R8. `Matrix.mulVec_mulVec` · `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`; here `← … at h`
`at h` rewrites the hypothesis `h` instead of the goal: the context changes. -/
example {α n : Type} [CommRing α] [Fintype n] (M N : Matrix n n α) (v : n → α)
    (Q : (n → α) → Prop) (h : Q ((M * N) *ᵥ v)) : Q (M *ᵥ N *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec] at h
  exact h

/-! ### R9. `Matrix.mulVec_smul` · `M *ᵥ (b • v) = b • (M *ᵥ v)` · goal: scalar out of a vector -/
example {α n : Type} [CommRing α] [Fintype n] (M : Matrix n n α) (b : α) (v : n → α)
    (P : (n → α) → Prop) (h : P (b • M *ᵥ v)) : P (M *ᵥ (b • v)) := by
  rw [Matrix.mulVec_smul]
  exact h

/-! ### R10. `smul_smul` · `a • b • x = (a * b) • x` · goal: two scalars → one product -/
example {R M : Type} [Monoid R] [MulAction R M] (a b : R) (x : M) (P : M → Prop)
    (h : P ((a * b) • x)) : P (a • b • x) := by
  rw [smul_smul]
  exact h

/-! ### R11. `Matrix.neg_mulVec` · `(-A) *ᵥ v = -(A *ᵥ v)` · goal: minus sign out of the matrix -/
example {α n : Type} [CommRing α] [Fintype n] (A : Matrix n n α) (v : n → α)
    (P : (n → α) → Prop) (h : P (-(A *ᵥ v))) : P ((-A) *ᵥ v) := by
  rw [Matrix.neg_mulVec]
  exact h

/-! ## Cancelling the vector -/

/-! ### R12. `add_smul` · `(r + s) • x = r • x + s • x` · goal: distribute over a sum of scalars -/
example {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M) (P : M → Prop)
    (h : P (r • x + s • x)) : P ((r + s) • x) := by
  rw [add_smul]
  exact h

/-! ### R13. `rw [show t = u by ring]` · goal: a ring-equal form `u` in place of `t` -/
example {α : Type} [CommRing α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [show a * b = b * a by ring]
  exact h

/-! ### R14. `simp` (lemma `add_neg_cancel`) · closes `x + -x = 0` -/
example {M : Type} [AddCommGroup M] (x : M) : x + -x = 0 := by simp

/-! ### R15. `smul_eq_zero` · `r • x = 0 ↔ r = 0 ∨ x = 0`; `.mp` uses it left to right
Holds for complex scalars acting on complex vectors (no zero divisors). -/
example {n : Type} (r : ℂ) (x : n → ℂ) (h0 : r • x = 0) (G : Prop) (g : r = 0 ∨ x = 0 → G) :
    G := by
  have h := smul_eq_zero.mp h0
  exact g h

/-! ### R16. `rcases h with h1 | h1` · goal list: one goal per side of `h : A ∨ B` -/
example (A B G : Prop) (h : A ∨ B) (ga : A → G) (gb : B → G) : G := by
  rcases h with h1 | h1
  · exact ga h1
  · exact gb h1

/-! ### R17. `linear_combination h1` · closes `x = y` when `x - y` is (a multiple of) `lhs - rhs` of `h1` -/
example (x y : ℂ) (h1 : x - y = 0) : x = y := by linear_combination h1

/-! ### R18. `absurd h hn` · closes any goal from `h : A` and `hn : ¬A`
`v ≠ 0` is notation for `¬(v = 0)`. -/
example (A G : Prop) (h : A) (hn : ¬A) : G := by
  exact absurd h hn

/-! # Part W · Worked combinations (not the exercise's objects) -/

def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 3, 0]

/-! ### W1. One-qubit facts by `simp` (R1), and a sign written as `(-1 : ℂ) • _` -/
example : Z * Z * Z = Z := by simp [Z]
example : Z * A * Z = (-1 : ℂ) • A := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Z, A]

/-! ### W2. A two-qubit mixed product: R2, R3 (repeated by `simp only`), the one-qubit facts, R4, R6 -/
example : D Z Z * D A Z * D Z Z = -D A Z := by
  have hZAZ : Z * A * Z = (-1 : ℂ) • A := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Z, A]
  have hZZZ : Z * Z * Z = Z := by simp [Z]
  simp only [D]
  simp only [← Matrix.mul_kronecker_mul]
  rw [hZAZ, hZZZ]
  rw [Matrix.smul_kronecker]
  rw [neg_one_smul]

/-! ### W3. Apply a matrix identity to an eigenvector: R7, R8, `rw [eigen eq] at h`, R9, R10, R11 -/
example {n : Type} [Fintype n] (M N K : Matrix n n ℂ) (v : n → ℂ) (a b e : ℂ)
    (hMN : M * N = -K) (hm : M *ᵥ v = a • v) (hn : N *ᵥ v = b • v) (hk : K *ᵥ v = e • v) :
    (a * b) • v = -(e • v) := by
  have h := congrArg (· *ᵥ v) hMN
  rw [← Matrix.mulVec_mulVec] at h
  rw [hn] at h
  rw [Matrix.mulVec_smul] at h
  rw [hm] at h
  rw [smul_smul] at h
  rw [Matrix.neg_mulVec] at h
  rw [hk] at h
  rw [mul_comm]
  exact h

/-! ### W4. Cancel a nonzero vector: R12, R14, R15, R16, R17, R18 -/
example {n : Type} (x : n → ℂ) (hx : x ≠ 0) (r s : ℂ) (h : s • x = -(r • x)) : r = -s := by
  have h0 : (r + s) • x = 0 := by
    rw [add_smul, h]
    simp
  rcases smul_eq_zero.mp h0 with h1 | h1
  · linear_combination h1
  · exact absurd h1 hx

end M129Guide
