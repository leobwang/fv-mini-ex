/- M129 | GHZ: Mermin's operator identity | 10-15 min | Kronecker product, mixed product, Pauli strings, eigenvalues, mathlib
GOAL
  For three-qubit Pauli strings `P3 P Q R = P ⊗ Q ⊗ R`, prove `(XYY)(YXY)(YYX) = -XXX`. Hence on a joint
  eigenvector the eigenvalues satisfy `e = -abc`, while hidden ±1 values would give `e = abc` (GHZ paradox).

REFERENCE
  -- `A ⊗ₖ B` (open scoped Kronecker) is the Kronecker product, indexed by pairs: (A ⊗ₖ B) (i, k) (j, l) = A i j * B k l.
  #check Matrix.mul_kronecker_mul -- (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'   (rewrite right-to-left with ←)
  #check Matrix.smul_kronecker    -- (r • A) ⊗ₖ B = r • (A ⊗ₖ B)
  #check Matrix.kronecker_smul    -- A ⊗ₖ (r • B) = r • (A ⊗ₖ B)
  #check neg_one_smul             -- (-1 : R) • x = -x
  example : !![(0 : ℂ), 1; 1, 0] * !![(0 : ℂ), 1; 1, 0] = !![1, 0; 0, 1] := by simp  -- simp multiplies explicit matrices
  #check Matrix.mulVec_mulVec     -- M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v
  #check Matrix.neg_mulVec        -- (-A) *ᵥ v = -(A *ᵥ v)
  #check smul_eq_zero             -- r • m = 0 ↔ r = 0 ∨ m = 0
  example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := congrArg f h  -- apply both sides to something
NOTE: Mathlib has `smul_kronecker` but no `neg_kronecker`: write a sign as `(-1 : ℂ) • X`, not `-X`.
-/
import Mathlib

open Matrix Complex
open scoped Kronecker

namespace M129

-- BEGIN SPEC
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- three-qubit Pauli string `P ⊗ Q ⊗ R` -/
def P3 (P Q R : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  P ⊗ₖ (Q ⊗ₖ R)
-- END SPEC

-- BEGIN SPEC
theorem mermin_identity : P3 X Y Y * P3 Y X Y * P3 Y Y X = -P3 X X X :=
-- END SPEC
  by
    have hXY : X * Y * Y = X := by simp [X, Y]
    have hYX : Y * X * Y = (-1 : ℂ) • X := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [X, Y]
    have hYY : Y * Y * X = X := by simp [X, Y]
    simp only [P3, ← Matrix.mul_kronecker_mul, hXY, hYX, hYY]
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, neg_one_smul]

-- BEGIN SPEC
theorem mermin_eigen {v : Fin 2 × Fin 2 × Fin 2 → ℂ} (hv : v ≠ 0) (a b c e : ℂ)
    (ha : P3 X Y Y *ᵥ v = a • v) (hb : P3 Y X Y *ᵥ v = b • v) (hc : P3 Y Y X *ᵥ v = c • v)
    (he : P3 X X X *ᵥ v = e • v) : e = -(a * b * c) :=
-- END SPEC
  by
    have h := congrArg (· *ᵥ v) mermin_identity
    simp only [← Matrix.mulVec_mulVec, hc, hb, ha, Matrix.mulVec_smul, smul_smul,
      Matrix.neg_mulVec, he] at h
    have h0 : (e + a * b * c) • v = 0 := by
      rw [add_smul, show a * b * c = c * (b * a) by ring, h]
      simp
    rcases smul_eq_zero.mp h0 with h1 | h1
    · linear_combination h1
    · exact absurd h1 hv

end M129

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do not compute 8×8 matrices. The mixed-product rule turns a product of Kronecker products into a
    Kronecker product of three 2×2 products, one per qubit. For the eigen part, apply the identity to `v`.
H2. Per qubit you need `X * Y * Y = X`, `Y * X * Y = (-1 : ℂ) • X`, `Y * Y * X = X` (each by `simp [X, Y]`,
    or `ext i j; fin_cases i <;> fin_cases j <;> simp [X, Y]` when the sign gets in the way). Eigen part: `(P*Q*R) *ᵥ v = P *ᵥ (Q *ᵥ (R *ᵥ v))`,
    so the left side becomes `(c * (b * a)) • v`; get `(e + a * b * c) • v = 0`.
H3. With the three per-qubit facts as `hXY, hYX, hYY`: `simp only [P3, ← Matrix.mul_kronecker_mul, hXY, hYX, hYY]`,
    then pull the scalar `-1` out with the REFERENCE `smul` lemmas.
    Eigen: `have h := congrArg (· *ᵥ v) mermin_identity`, then split each product on `v` and substitute the eigen equations.
-/
