/- M128 | Eigenvalues of involutions | 10-15 min | mulVec, eigenvectors, smul_eq_zero, IsHermitian, linear_combination, mathlib
GOAL
  A Hermitian unitary (like X, Y, Z, H) squares to `1`; any `U` with `U * U = 1` has only eigenvalues
  `±1`; and for Hermitian `U` a `+1` and a `-1` eigenvector are orthogonal (distinct outcomes are distinguishable).

BANNED: try?
GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix

namespace M128

/- SKELETON · herm_unitary_sq
  The proof rewrites the hypothesis `hU` until it is the goal.
  1. Membership → equation, in `hU`:  hU : U * star U = 1                  R1 (`at hU`)
  2. `star U` → `Uᴴ`, then Hermitian `Uᴴ` → `U`:  hU : U * U = 1            R2, R3 (both `at hU`)
  3. Close the goal with `hU`.                                             exact hU
-/
-- BEGIN SPEC
theorem herm_unitary_sq {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hH : U.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ) : U * U = 1 :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hH.eq] at hU
    exact hU

/- SKELETON · involution_eigenvalues
  1. Key fact first:  h2 : (μ * μ - 1) • v = 0                             have
     a. Inside it, a second fact:  this : U *ᵥ (U *ᵥ v) = v                R4, rw [hU], R5
     b. Rewrite `this` with the eigen-equation (all `at this`):
          rw [h], R6, rw [h], R7      →   this : (μ * μ) • v = v
     c. The goal of 1:  R8, rw [this], R9, R10   (the last rw closes `0 = 0`)
  2. Split `h2`:  μ * μ - 1 = 0   |   v = 0                                R11 → R12
  3. Case `μ * μ - 1 = 0`:
       factor:  (μ - 1) * (μ + 1) = 0                                      have, R13
       split:   μ - 1 = 0   |   μ + 1 = 0                                  R14 → R12
       each case: pick the side, then solve the linear equation            R15, R13
  4. Case `v = 0`: contradicts `hv`.                                       R16
-/
-- BEGIN SPEC
theorem involution_eigenvalues {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U * U = 1) (v : n → ℂ) (hv : v ≠ 0) (μ : ℂ) (h : U *ᵥ v = μ • v) :
    μ = 1 ∨ μ = -1 :=
-- END SPEC
  by
    have h2 : (μ * μ - 1) • v = 0 := by
      have : U *ᵥ (U *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      rw [h, Matrix.mulVec_smul, h, smul_smul] at this
      rw [sub_smul, this, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · have : (μ - 1) * (μ + 1) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp this with h4 | h4
      · left; linear_combination h4
      · right; linear_combination h4
    · exact absurd h3 hv

/- SKELETON · eigvec_orth
  1. Fact: move the Hermitian `U` across the inner product                have
       h : star v ⬝ᵥ (U *ᵥ w) = star (U *ᵥ v) ⬝ᵥ w        proof: R17, R3, R18
  2. Use the eigen-equations in `h` (all `at h`):                          rw [hv, hw], R19
       h : -(star v ⬝ᵥ w) = star v ⬝ᵥ w
  3. Fact:  (2 : ℂ) * (star v ⬝ᵥ w) = 0                                    have, R13 (coefficient -1)
  4. Cancel the 2.                                                         R20
-/
-- BEGIN SPEC
theorem eigvec_orth {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (hH : U.IsHermitian)
    (v w : n → ℂ) (hv : U *ᵥ v = v) (hw : U *ᵥ w = -w) : star v ⬝ᵥ w = 0 :=
-- END SPEC
  by
    -- WHY: a Hermitian `U` can be moved from one side of the inner product to the other.
    have h : star v ⬝ᵥ (U *ᵥ w) = star (U *ᵥ v) ⬝ᵥ w := by
      rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]
    rw [hv, hw, dotProduct_neg] at h
    have : (2 : ℂ) * (star v ⬝ᵥ w) = 0 := by linear_combination -h
    simpa using this

end M128

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) Unwrap `hU`: unitary means `U * star U = 1`, `star U` is `Uᴴ`, and Hermitian means `Uᴴ = U`.
    (2) Apply `U` twice to `v`: `U *ᵥ (U *ᵥ v)` is `v` (by `hU`) and also `(μ * μ) • v` (by `h` twice).
    (3) Compute `⟨v, U w⟩ = star v ⬝ᵥ (U *ᵥ w)` two ways: with `hw`, and by moving the Hermitian `U` onto `v`.
H2. (1) Three rewrites `at hU` (R1, R2, R3) turn it into the goal.
    (2) Prove `h2 : (μ * μ - 1) • v = 0`; `smul_eq_zero` splits it and `hv` rules out `v = 0`;
    factor `μ * μ - 1 = 0` into `(μ - 1) * (μ + 1) = 0` with `linear_combination` and split with `mul_eq_zero`.
    (3) You get `-⟨v, w⟩ = ⟨v, w⟩`, so `2 * ⟨v, w⟩ = 0`, so `⟨v, w⟩ = 0`.
H3. (1) `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hH.eq] at hU`.
    (2) `have : U *ᵥ (U *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]`, then
    `rw [h, Matrix.mulVec_smul, h, smul_smul] at this`; `rcases smul_eq_zero.mp h2 with h3 | h3`.
    (3) `have h : star v ⬝ᵥ (U *ᵥ w) = star (U *ᵥ v) ⬝ᵥ w := by rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]`,
    then `rw [hv, hw, dotProduct_neg] at h`; `linear_combination -h`; `simpa`.
-/
