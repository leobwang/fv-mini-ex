/- E074 | Matrix notation | 3 min | Matrix, !![..], ![..], mulVec, transpose, det_fin_two, fin_cases, mathlib
GOAL
  Write 2×2 matrices as `!![a, b; c, d]` (rows separated by `;`), read entries, and prove matrix
  identities entry by entry.

REFERENCE
  example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℕ) 1 0 = 3 := rfl   -- `M i j`: row i, column j, from 0
  #check Matrix.det_fin_two  -- A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0
  #check Matrix.mul_apply    -- (M * N) i k = ∑ j, M i j * N j k
  #check Fin.sum_univ_two    -- ∑ i, f i = f 0 + f 1
  #check Matrix.mulVec       -- `M *ᵥ v` (typed `*\_v`): (M *ᵥ v) i = dotProduct (row i of M) v
  #check dotProduct          -- dotProduct v w = ∑ i, v i * w i
  `Mᵀ` (typed `\^T`) is the transpose; `*ᵥ` and `ᵀ` need `open Matrix` (in the spec). `c • M` scales
  every entry by `c`; `(1 : Matrix _ _ ℝ)` is the identity.
  `ext i j` turns `M = N` into `M i j = N i j`; `fin_cases i <;> fin_cases j` then gives the 4 entries.
  `ext i` does the same for vectors `Fin 2 → ℝ`.
BANNED: exact?
-/
import Mathlib

namespace E074

-- BEGIN SPEC
open Matrix

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
-- END SPEC

-- BEGIN SPEC
theorem A_entry : A 0 1 = 2 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem A_det : A.det = -2 :=
-- END SPEC
  by
    simp [A, Matrix.det_fin_two]
    norm_num

-- BEGIN SPEC
theorem A_transpose : Aᵀ = !![1, 3; 2, 4] :=
-- END SPEC
  by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

-- BEGIN SPEC
theorem A_mulVec : A *ᵥ ![1, 1] = ![3, 7] :=
-- END SPEC
  by
    ext i
    fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

-- BEGIN SPEC
theorem adjugate_two (a b c d : ℝ) :
    !![a, b; c, d] * !![d, -b; -c, a] = (a * d - b * c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
-- END SPEC
  by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end E074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An entry of a literal matrix is computed by `rfl`; a matrix or vector equation holds entry by entry.
H2. `A_det`: unfold `A` and use `det_fin_two`, then `norm_num`. For the equations, `ext`, split the indices
    with `fin_cases`, and finish each entry with `rfl`, or with `simp [...]` (unfolding `A`, `mulVec`,
    `dotProduct`, `mul_apply`, `Fin.sum_univ_two`) followed by `norm_num`/`ring`.
H3. `rfl`; `simp [A, Matrix.det_fin_two]; norm_num`; `ext i j; fin_cases i <;> fin_cases j <;> rfl`;
    `ext i; fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num`;
    `adjugate_two`: the same pattern with `ext i j` and `simp [Matrix.mul_apply, Fin.sum_univ_two]`, then `ring`.
-/
