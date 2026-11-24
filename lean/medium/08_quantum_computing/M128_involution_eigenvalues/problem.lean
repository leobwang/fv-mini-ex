/- M128 | Eigenvalues of involutions | 10-15 min | mulVec, eigenvectors, smul_eq_zero, IsHermitian, linear_combination, mathlib
GOAL
  A Hermitian unitary (like X, Y, Z, H) squares to `1`; any `U` with `U * U = 1` has only eigenvalues
  `±1`; and for Hermitian `U` a `+1` and a `-1` eigenvector are orthogonal (distinct outcomes are distinguishable).

REFERENCE
  -- `U *ᵥ v` is matrix·vector; `star v ⬝ᵥ w = ∑ i, conj (v i) * w i` is the inner product ⟨v, w⟩.
  #check Matrix.mulVec_mulVec   -- M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v
  #check Matrix.mulVec_smul     -- M *ᵥ (b • v) = b • (M *ᵥ v)
  #check smul_eq_zero           -- r • m = 0 ↔ r = 0 ∨ m = 0
  #check Matrix.IsHermitian.eq  -- (h : A.IsHermitian) : Aᴴ = A
  #check Matrix.star_mulVec     -- star (M *ᵥ v) = star v ᵥ* Mᴴ    (row vector times matrix)
  #check Matrix.dotProduct_mulVec  -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  example (μ : ℂ) (h : μ * μ - 1 = 0) : (μ - 1) * (μ + 1) = 0 := by linear_combination h
  #check Matrix.mem_unitaryGroup_iff  -- A ∈ unitaryGroup n α ↔ A * star A = 1
  #check Matrix.star_eq_conjTranspose -- star M = Mᴴ   (conjugate transpose)
  #check Matrix.one_mulVec            -- 1 *ᵥ v = v
BANNED: try?
NOTE: `try?` finds the two-rewrite warm-up `herm_unitary_sq` for you; do that unwrapping by hand.
-/
import Mathlib

open Matrix

namespace M128

-- BEGIN SPEC
theorem herm_unitary_sq {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hH : U.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ) : U * U = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem involution_eigenvalues {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U * U = 1) (v : n → ℂ) (hv : v ≠ 0) (μ : ℂ) (h : U *ᵥ v = μ • v) :
    μ = 1 ∨ μ = -1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem eigvec_orth {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (hH : U.IsHermitian)
    (v w : n → ℂ) (hv : U *ᵥ v = v) (hw : U *ᵥ w = -w) : star v ⬝ᵥ w = 0 :=
-- END SPEC
  sorry

end M128

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) Unitary says `U * Uᴴ = 1`, and Hermitian says `Uᴴ = U`. (2) Apply `U` twice to `v`. (3) Compute
    `⟨v, U w⟩` in two ways: once using `hw`, once by moving the Hermitian `U` onto `v`.
H2. (2) `U *ᵥ (U *ᵥ v)` is `v` (by `hU`) and also `(μ * μ) • v` (by `h` twice), so `(μ * μ - 1) • v = 0`;
    `smul_eq_zero` and `hv` leave `μ * μ - 1 = 0`; factor it and use `mul_eq_zero`.
    (3) You get `⟨v, w⟩ = -⟨v, w⟩`, i.e. `2 * ⟨v, w⟩ = 0`.
H3. (2) `have : U *ᵥ (U *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]`, then
    `rw [h, Matrix.mulVec_smul, h, smul_smul] at this`.
    (3) `have h : star v ⬝ᵥ (U *ᵥ w) = star (U *ᵥ v) ⬝ᵥ w := by rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]`,
    then `rw [hv, hw, dotProduct_neg] at h`.
-/
