/- M126 | The Hadamard gate | 10-15 min | Matrix, !![], ext, fin_cases, Real.sqrt casts, unitary group, mathlib
GOAL
  With the Pauli matrices `X, Y, Z` and the Hadamard gate `H = (1/√2)·[[1, 1], [1, -1]]`, prove
  `H² = 1`, `HXH = Z`, `HZH = X`, `HYH = -Y` (H swaps the X and Z bases), and that `H` is unitary.

REFERENCE
  example : !![(1 : ℂ), 2; 3, 4] 1 0 = 3 := rfl  -- `!![a, b; c, d]` is a 2×2 matrix, rows split by `;`
  example (A B : Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i j, A i j = B i j) : A = B := by
    ext i j; fin_cases i <;> fin_cases j <;> exact h _ _  -- prove a matrix equation entry by entry
  #check Matrix.mul_apply   -- (M * N) i k = ∑ j, M i j * N j k
  #check Fin.sum_univ_two   -- ∑ i : Fin 2, f i = f 0 + f 1
  example : ((Real.sqrt 2)⁻¹ : ℂ) ^ 2 = 1 / 2 := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num  -- the √2 clean-up
  #check Matrix.mem_unitaryGroup_iff  -- A ∈ unitaryGroup n α ↔ A * star A = 1
  #check Matrix.star_eq_conjTranspose -- star M = Mᴴ  (conjugate transpose; entry: Mᴴ j i = star (M i j))
  #check Complex.conj_ofReal          -- conj (↑r) = ↑r  for a real r cast to ℂ
NOTE: `I` is `Complex.I`; `(Real.sqrt 2 : ℂ)` is a real number cast to ℂ, so `simp` alone cannot square it.
-/
import Mathlib

open Matrix Complex

namespace M126

-- BEGIN SPEC
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • !![1, 1; 1, -1]
-- END SPEC

-- BEGIN SPEC
theorem hadamard_conj : H * H = 1 ∧ H * X * H = Z ∧ H * Z * H = X ∧ H * Y * H = -Y :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hadamard_unitary : H ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  sorry

end M126

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal is an equation of 2×2 matrices: reduce it to 4 scalar equations with `ext i j` and
    `fin_cases`. The only real work is the factor `(√2)⁻¹` that appears twice in every entry.
H2. Split the conjunction with `refine ⟨?_, ?_, ?_, ?_⟩` and treat all four goals the same way: entry by
    entry, unfold the definitions and expand each product with `Matrix.mul_apply` and `Fin.sum_univ_two`.
    What is left are scalar identities in which `(√2)⁻¹` appears squared.
H3. Key fact, proved once up front: `have h : ((Real.sqrt 2)⁻¹ : ℂ) ^ 2 = 1 / 2` (the REFERENCE example).
    After `simp`, normalise with `ring_nf` (it turns `(√2)⁻¹ * (√2)⁻¹` into `(√2)⁻¹ ^ 2`) and rewrite with `h`.
    For unitarity, add `Matrix.conjTranspose_apply` and `Complex.conj_ofReal` to the `simp` set.
-/
