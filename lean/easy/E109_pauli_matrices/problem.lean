/- E109 | Pauli matrices | 2-3 min | Matrix, !![..], mul_fin_two, one_fin_two, Complex.I, smul, mathlib
GOAL
  A one-qubit gate is a 2×2 complex matrix. Check the Pauli algebra for X = [[0,1],[1,0]],
  Y = [[0,-i],[i,0]], Z = [[1,0],[0,-1]]: X² = 1, Y² = 1, ZX = −XZ (they anticommute), XY = iZ.

REFERENCE
  #check Matrix.mul_fin_two  -- !![a, b; c, d] * !![e, f; g, h] = !![a*e + b*g, a*f + b*h; c*e + d*g, c*f + d*h]
  #check Matrix.one_fin_two  -- (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]
  #check Complex.I_mul_I     -- I * I = -1   (`I` is `Complex.I`; `open Complex` is in the spec)
  example : (2 : ℂ) • !![1, 0; 0, (1 : ℂ)] = !![2, 0; 0, 2] := by simp   -- `c • M` scales every entry
  `simp [X]` unfolds the definition `X` and then multiplies, negates and scales literal matrices
  entry by entry. It never turns `1` into a literal, so a goal `!![1, 0; 0, 1] = 1` is left over:
  add `Matrix.one_fin_two` to the simp set for that.
-/
import Mathlib

namespace E109

-- BEGIN SPEC
open Matrix Complex

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
-- END SPEC

-- BEGIN SPEC
theorem X_sq : X * X = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Y_sq : Y * Y = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Z_mul_X : Z * X = -(X * Z) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem X_mul_Y : X * Y = I • Z :=
-- END SPEC
  sorry

end E109

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every side is a product of literal 2×2 matrices once `X`, `Y`, `Z` are unfolded.
H2. `simp` with the definitions computes both sides entry by entry. Where the right side is `1`, also
    give it `Matrix.one_fin_two`; where it is `I • Z`, unfold `Z` too.
H3. `simp [X, Matrix.one_fin_two]`; `simp [Y, Matrix.one_fin_two]` (it uses `I * I = -1` by itself);
    `simp [X, Z]`; `simp [X, Y, Z]`.
-/
