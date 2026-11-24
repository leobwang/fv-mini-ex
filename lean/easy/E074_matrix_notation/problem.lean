/- E074 | Matrix notation | 3 min | Matrix, !![..], ![..], mulVec, transpose, det_fin_two, fin_cases, mathlib
GOAL
  Write 2×2 matrices as `!![a, b; c, d]` (rows separated by `;`), read entries, and prove matrix
  identities entry by entry.
BANNED: exact?

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E074

-- BEGIN SPEC
open Matrix

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
-- END SPEC

/- SKELETON · A_entry
  1. Read the entry of the literal: `A` and `!![…]` unfold by computation, so one step closes it:   R1
-/
-- BEGIN SPEC
theorem A_entry : A 0 1 = 2 :=
-- END SPEC
  sorry

/- SKELETON · A_det
  1. One `simp` with the name `A` and the determinant formula:                            R2, R3
     it also reads off the literal's entries and leaves a goal of numerals:               R4
  2. Finish the arithmetic:                                                               R5
-/
-- BEGIN SPEC
theorem A_det : A.det = -2 :=
-- END SPEC
  sorry

/- SKELETON · A_transpose
  1. Matrix equation → one entry goal with `i j : Fin 2`:                                 R6
  2. Split both indices (four goals; use `<;>`):                                          R7
  3. Each entry: `Aᵀ i j` is `A j i` by definition, a literal entry; close it:             R8, R1
-/
-- BEGIN SPEC
theorem A_transpose : Aᵀ = !![1, 3; 2, 4] :=
-- END SPEC
  sorry

/- SKELETON · A_mulVec
  1. Vector equation → one entry goal with `i : Fin 2`:                                   R9
  2. Split the index (two goals; use `<;>`):                                              R7
  3. Each entry, in one `simp` with `A` and the three expansions:                         R2, R10 → R11 → R12
     (the literal entries of `A` and of `![…]` are read by `simp` itself):                R4, R13
  4. Finish the arithmetic:                                                               R5
-/
-- BEGIN SPEC
theorem A_mulVec : A *ᵥ ![1, 1] = ![3, 7] :=
-- END SPEC
  sorry

/- SKELETON · adjugate_two
  1. Matrix equation → entry goal, then split both indices (four goals; use `<;>`):       R6, R7
  2. Each entry, in one `simp` with the product expansion and the `Fin 2` sum:            R14, R12
     (`simp` itself reads the literals and the scaled identity on the right):             R4, R15, R16
  3. What is left is algebra in `a b c d`:                                                R17
-/
-- BEGIN SPEC
theorem adjugate_two (a b c d : ℝ) :
    !![a, b; c, d] * !![d, -b; -c, a] = (a * d - b * c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
-- END SPEC
  sorry

end E074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An entry of a literal matrix is computed by `rfl` (R1); a matrix or vector equation is proved entry by
    entry (`ext`, then `fin_cases`). Real arithmetic is not computed by `rfl`: finish numbers with `norm_num`,
    letters with `ring`.
H2. `A_det`: unfold `A` and expand the 2×2 determinant in one `simp`, then compute. `A_transpose`: `ext i j`,
    split both indices with `fin_cases`, read each entry. `A_mulVec`: `ext i`, `fin_cases i`, then `simp` with
    `A`, `Matrix.mulVec`, `dotProduct`, `Fin.sum_univ_two`. `adjugate_two`: `ext i j`, both `fin_cases`, then
    `simp` with `Matrix.mul_apply`, `Fin.sum_univ_two`.
H3. `simp [A, Matrix.det_fin_two]` then `norm_num`; `ext i j; fin_cases i <;> fin_cases j <;> rfl`;
    `ext i; fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num`;
    `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring`.
-/
