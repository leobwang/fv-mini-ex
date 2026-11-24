/- E110 | The unitary group | 2-3 min | Matrix.unitaryGroup, conjTranspose, star, Submonoid.mul_mem, ext, fin_cases, mathlib
GOAL
  A gate `U` is unitary when `U * Uᴴ = 1`, where `Uᴴ` is the conjugate transpose. Show that Pauli X
  and Z lie in `Matrix.unitaryGroup (Fin 2) ℂ`, that so does the circuit `X * Z` (unitaries are
  closed under products), and that every unitary also satisfies `Uᴴ * U = 1`.

REFERENCE
  #check Matrix.mem_unitaryGroup_iff   -- A ∈ unitaryGroup n α ↔ A * star A = 1
  #check Matrix.mem_unitaryGroup_iff'  -- A ∈ unitaryGroup n α ↔ star A * A = 1
  #check Matrix.star_eq_conjTranspose  -- star M = Mᴴ   (`Mᴴ`, typed `\^H`: Mᴴ i j = conj (M j i))
  #check Matrix.mul_apply              -- (M * N) i k = ∑ j, M i j * N j k
  #check Submonoid.mul_mem             -- (S : Submonoid M) : x ∈ S → y ∈ S → x * y ∈ S
  `Matrix.unitaryGroup n ℂ` is a `Submonoid (Matrix n n ℂ)` (so `Submonoid.mul_mem` applies).
  `simp` does not compute `!![..]ᴴ` as a literal, so prove a 2×2 matrix equation entrywise:
  `ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
import Mathlib

namespace E110

-- BEGIN SPEC
open Matrix

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
-- END SPEC

-- BEGIN SPEC
theorem X_unitary : X ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]

-- BEGIN SPEC
theorem Z_unitary : Z ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z, Matrix.mul_apply, Fin.sum_univ_two]

-- BEGIN SPEC
theorem XZ_unitary : X * Z ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  Submonoid.mul_mem _ X_unitary Z_unitary

-- BEGIN SPEC
theorem conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ * U = 1 :=
-- END SPEC
  by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU

end E110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Membership in the unitary group is an equation between matrices; the group is a submonoid.
H2. For X and Z: rewrite with `mem_unitaryGroup_iff` and `star_eq_conjTranspose`, then go entrywise.
    For `X * Z`: reuse the two previous theorems. For the last one: turn `Uᴴ` back into `star U`.
H3. `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [...]`;
    `Submonoid.mul_mem _ X_unitary Z_unitary`;
    `rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU`.
-/
