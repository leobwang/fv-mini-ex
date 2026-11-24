/- E109 | Pauli matrices | 2-3 min | Matrix, !![..], mul_fin_two, one_fin_two, Complex.I, smul, mathlib
GOAL
  A one-qubit gate is a 2×2 complex matrix. Check the Pauli algebra for X = [[0,1],[1,0]],
  Y = [[0,-i],[i,0]], Z = [[1,0],[0,-1]]: X² = 1, Y² = 1, ZX = −XZ (they anticommute), XY = iZ.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E109

-- BEGIN SPEC
open Matrix Complex

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
-- END SPEC

/- SKELETON · X_sq
  One `simp` call does every step; name what it cannot find by itself.
  1. Unfold `X` into its literal:                                           R1
  2. Multiply the two literals:                                             R2
  3. The right side `1` → the literal `!![1, 0; 0, 1]` (simp never does it): R3
  4. Clean the entries and compare the two literals entry by entry:         R7, R8
-/
-- BEGIN SPEC
theorem X_sq : X * X = 1 :=
-- END SPEC
  sorry

/- SKELETON · Y_sq
  As X_sq; the entries now contain `I * I` and signs.
  1. Unfold `Y`:                                                            R1
  2. Multiply the literals:                                                 R2
  3. The right side `1` → a literal:                                        R3
  4. `I * I = -1`, then clean the signs and compare:                        R4, R7, R8
-/
-- BEGIN SPEC
theorem Y_sq : Y * Y = 1 :=
-- END SPEC
  sorry

/- SKELETON · Z_mul_X
  1. Unfold `Z` and `X` (both sides):                                       R1
  2. Multiply the literals on both sides:                                   R2
  3. Push the outer `-` into the right-hand literal:                         R5
  4. Clean the entries and compare:                                         R7, R8
-/
-- BEGIN SPEC
theorem Z_mul_X : Z * X = -(X * Z) :=
-- END SPEC
  sorry

/- SKELETON · X_mul_Y
  1. Unfold `X`, `Y` and also `Z` (it sits under `I •` on the right):        R1
  2. Multiply the literals on the left:                                     R2
  3. Push the scalar `I` into the right-hand literal:                        R6
  4. Clean the entries and compare:                                         R7, R8
-/
-- BEGIN SPEC
theorem X_mul_Y : X * Y = I • Z :=
-- END SPEC
  sorry

end E109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every side becomes a literal 2×2 matrix once `X`, `Y`, `Z` are unfolded (R1), and `simp` computes
    products, negations and scalings of literals entry by entry (R2, R5, R6, R7, R8).
H2. One `simp [names]` per theorem, naming exactly the matrices that occur. `simp` never rewrites the
    identity `1` into a literal: where the right side is `1`, add `Matrix.one_fin_two` (R3). Where it is
    `I • Z`, unfold `Z` too.
H3. `simp [X, Matrix.one_fin_two]`; `simp [Y, Matrix.one_fin_two]` (it uses `I * I = -1`, R4, by itself);
    `simp [X, Z]`; `simp [X, Y, Z]`.
-/
