/- E110 | The unitary group | 2-3 min | Matrix.unitaryGroup, conjTranspose, star, Submonoid.mul_mem, ext, fin_cases, mathlib
GOAL
  A gate `U` is unitary when `U * Uᴴ = 1`, where `Uᴴ` is the conjugate transpose. Show that Pauli X
  and Z lie in `Matrix.unitaryGroup (Fin 2) ℂ`, that so does the circuit `X * Z` (unitaries are
  closed under products), and that every unitary also satisfies `Uᴴ * U = 1`.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E110

-- BEGIN SPEC
open Matrix

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
-- END SPEC

/- SKELETON · X_unitary
  1. Membership → the equation `X * Xᴴ = 1`:                                  R1, R2
  2. Matrix equation → four entry goals:                                      R3, R4
  3. Evaluate every entry with one `simp`, naming `X` and the product lemmas;
     the conjugate transpose, literal entries, `1` and `star` of numerals
     are then done by `simp` itself:                                          R5, R6, R7 (R8–R11)
-/
-- BEGIN SPEC
theorem X_unitary : X ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]

/- SKELETON · Z_unitary
  1. As for `X_unitary`: membership → equation:                               R1, R2
  2. Four entry goals:                                                        R3, R4
  3. One `simp` naming `Z` and the product lemmas (`star (-1)` is R11):       R5, R6, R7 (R8–R11)
-/
-- BEGIN SPEC
theorem Z_unitary : Z ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z, Matrix.mul_apply, Fin.sum_univ_two]

/- SKELETON · XZ_unitary
  1. No computation: the unitary group is a `Submonoid`, so it is closed under `*`.
     Feed it the two theorems above:                                          R12 with X_unitary, Z_unitary
-/
-- BEGIN SPEC
theorem XZ_unitary : X * Z ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  Submonoid.mul_mem _ X_unitary Z_unitary

/- SKELETON · conjTranspose_mul_self
  1. The size `n` is unknown, so no entries. Turn `Uᴴ` back into `star U`:    R13
  2. The goal is now the right-hand side of the primed membership lemma;
     get it from `hU`:                                                        R14
-/
-- BEGIN SPEC
theorem conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ * U = 1 :=
-- END SPEC
  by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU

end E110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Membership in the unitary group is an equation between matrices (R1); the group is also a
    `Submonoid`, so products of members are members (R12).
H2. X and Z: membership → `M * Mᴴ = 1` (R1, R2), then entry by entry (R3, R4) and one `simp` that knows
    the matrix name and how to expand a product (R5–R7). `X * Z`: reuse the two previous theorems.
    The last one: turn `Uᴴ` back into `star U` (R13) and use the other form of membership (R14).
H3. `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`, then
    `ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]`;
    `Submonoid.mul_mem _ X_unitary Z_unitary`; `Matrix.mem_unitaryGroup_iff'.mp hU` after the `rw [← …]`.
-/
