/- M129 | GHZ: Mermin's operator identity | 10-15 min | Kronecker product, mixed product, Pauli strings, eigenvalues, mathlib
GOAL
  For three-qubit Pauli strings `P3 P Q R = P ⊗ Q ⊗ R`, prove `(XYY)(YXY)(YYX) = -XXX`. Hence on a joint
  eigenvector the eigenvalues satisfy `e = -abc`, while hidden ±1 values would give `e = abc` (GHZ paradox).

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · mermin_identity
  Never compute an 8×8 matrix: the mixed-product rule works one qubit at a time.
  1. Prove the three one-qubit products first, as `have`s:                R1
       hXY : X * Y * Y = X
       hYX : Y * X * Y = (-1 : ℂ) • X      (write the sign as a scalar, see Traps)
       hYY : Y * Y * X = X
     each by `simp [X, Y]`; if `simp` stops, go entrywise first:          ext i j, fin_cases, R1
  2. Unfold `P3` and merge the Kronecker products qubit by qubit
     (repeat with `simp only`, not one `rw`):                               R2 → R3
  3. Substitute the one-qubit facts:                                        rw / simp only [hXY, hYX, hYY]
  4. The sign sits in the middle qubit: out of the inner `⊗ₖ`, then
     out of the outer one, then `-1 •` → `-`:                               R4 → R5 → R6
-/
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

/- SKELETON · mermin_eigen
  1. Apply `mermin_identity` to `v`:                                        R7
       h : (P3 X Y Y * P3 Y X Y * P3 Y Y X) *ᵥ v = -P3 X X X *ᵥ v
  2. In `h`, apply the product one factor at a time, innermost first, and
     substitute the eigen equations hc, hb, ha, he as they appear
     (one `simp only [...] at h` with all of them is easiest):             R8, R9, R10, R11
       target:  h : (c * (b * a)) • v = -(e • v)
  3. Prove  h0 : (e + a * b * c) • v = 0:                                   R12, R13, rw [h], R14
  4. Cancel `v`: split `smul_eq_zero` on h0:                                R15, R16
       case `e + a * b * c = 0`:                                            R17
       case `v = 0`: contradiction with hv:                                 R18
-/
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
H1. Do not compute 8×8 matrices. The mixed-product rule (R3) turns a product of Kronecker products into a
    Kronecker product of three 2×2 products, one per qubit. For the eigen part, apply the identity to `v`
    (R7) and cancel the nonzero `v` at the end (R15–R18).
H2. Per qubit: `X * Y * Y = X`, `Y * X * Y = (-1 : ℂ) • X`, `Y * Y * X = X` (R1; entrywise if `simp` stops).
    Substitute them after merging, then move the `-1` out of both `⊗ₖ` (R4, R5, R6). Eigen part: rewrite
    `h` until it reads `(c * (b * a)) • v = -(e • v)` (R8–R11), then show `(e + a * b * c) • v = 0` (R12–R14).
H3. Identity: `simp only [P3, ← Matrix.mul_kronecker_mul, hXY, hYX, hYY]`, then
    `rw [Matrix.smul_kronecker, Matrix.kronecker_smul, neg_one_smul]`.
    Eigen: `have h := congrArg (· *ᵥ v) mermin_identity`, then
    `simp only [← Matrix.mulVec_mulVec, hc, hb, ha, Matrix.mulVec_smul, smul_smul, Matrix.neg_mulVec, he] at h`;
    finish with `rcases smul_eq_zero.mp h0 with h1 | h1`.
-/
