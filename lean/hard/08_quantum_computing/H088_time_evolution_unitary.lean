/- H088 | Time evolution: exp(−iθX/2) and unitarity | 45-75 min | matrix exponential, diagonalisation, Matrix.exp lemmas, Hermitian generators, mathlib
GOAL
  (1) Evolving under the Hamiltonian `X` (Pauli X) for time `θ/2` gives the x-rotation gate:
      `exp(−i(θ/2)X) = cos(θ/2)·1 − i·sin(θ/2)·X = Rx θ`  (prove it by diagonalising `X`).
  (2) For every Hermitian `H` and real `t`, `exp(−itH)` is unitary (Schrödinger evolution keeps norms).

REFERENCE
  -- `NormedSpace.exp A` is the series ∑ Aᵏ/k!;  `Aᴴ` conjugate transpose;  `diagonal v` has `v` on the diagonal;  `I` = √−1
  #check Matrix.exp_units_conj   -- (U : (Matrix m m 𝔸)ˣ) : exp (↑U * A * ↑U⁻¹) = ↑U * exp A * ↑U⁻¹
  #check Matrix.exp_diagonal     -- exp (diagonal v) = diagonal (exp v)
  #check Pi.exp_def              -- exp v = fun i => exp (v i)       (exp of a vector is entrywise)
  #check Complex.exp_eq_exp_ℂ    -- `cexp` (= Complex.exp) = NormedSpace.exp   (rewrite with ← to get `cexp` back)
  #check Complex.exp_mul_I       -- cexp (x * I) = cos x + sin x * I
  #check Matrix.exp_conjTranspose -- exp Aᴴ = (exp A)ᴴ
  #check Matrix.exp_add_of_commute -- Commute A B (i.e. A * B = B * A) → exp (A + B) = exp A * exp B
  #check Matrix.mem_unitaryGroup_iff -- A ∈ unitaryGroup n α ↔ A * star A = 1   (`Matrix.star_eq_conjTranspose`)
  example : (Matrix (Fin 2) (Fin 2) ℂ)ˣ := ⟨1, 1, mul_one 1, mul_one 1⟩  -- a unit: ⟨val, inv, val*inv=1, inv*val=1⟩
  example (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) : Hᴴ = H := hH.eq  -- Hermitian means Hᴴ = H
  #check Matrix.conjTranspose_smul -- (c • M)ᴴ = star c • Mᴴ   (`star c` is the complex conjugate)
NOTE: use `Matrix.exp_add_of_commute`; the generic `NormedSpace.exp_add_of_commute` does not rewrite on matrices.
-/
import Mathlib

open Matrix Complex

namespace H088

-- BEGIN SPEC
/-- Pauli X -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- rotation about the x-axis by angle `θ` -/
noncomputable def Rx (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -I * Real.sin (θ / 2); -I * Real.sin (θ / 2), (Real.cos (θ / 2) : ℂ)]
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- the (unnormalised) Hadamard matrix `!![1, 1; 1, -1]` as a unit, with inverse `½ · itself` -/
noncomputable def HU : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  ⟨!![1, 1; 1, -1], (1 / 2 : ℂ) • !![1, 1; 1, -1], sorry, sorry⟩

-- MILESTONE (optional: change or delete)
/-- `X` is diagonalised by `HU`, with eigenvalues `1, −1` -/
theorem diag_conj (c : ℂ) :
    c • X = (HU : Matrix (Fin 2) (Fin 2) ℂ) * diagonal ![c, -c] * (↑HU⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem exp_diag (v : Fin 2 → ℂ) :
    NormedSpace.exp (diagonal v) = diagonal (fun i => Complex.exp (v i)) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- the generator `−itH` is anti-Hermitian -/
theorem star_gen {n : Type} [Fintype n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    ((-(t : ℂ) * I) • H)ᴴ = -((-(t : ℂ) * I) • H) := by
  sorry

-- BEGIN SPEC
theorem time_evolution (θ : ℝ) : NormedSpace.exp ((-(θ / 2 : ℂ) * I) • X) = Rx θ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem evolution_unitary {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * I) • H) ∈ Matrix.unitaryGroup n ℂ :=
-- END SPEC
  sorry

end H088

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) The exponential of a diagonal matrix is easy, and `exp` commutes with conjugation by an invertible
    matrix; `X` has eigenvectors `(1, 1)` and `(1, −1)`. (2) `U` is unitary iff `U * Uᴴ = 1`; push `ᴴ`
    inside `exp`, and use that `−itH` and its conjugate transpose add up to `0`. (`Matrix.exp_neg` also
    works, but then needs invertibility of `exp A`; the commute route is shorter.)
H2. (1) `rw [diag_conj, Matrix.exp_units_conj, exp_diag]`, then compare the four entries of the 2×2 product
    (`ext i j; fin_cases i <;> fin_cases j`), writing each exponential as cos ± i·sin.
    (2) Unfold unitary membership to `U * Uᴴ = 1`, move `ᴴ` inside `exp`, turn the generator into `−A` with
    `star_gen`, then show `exp A * exp (−A) = exp (A + −A) = exp 0 = 1`.
H3. (1) After the `rw`, the diagonal is `fun i => cexp (![a, -a] i)` with `a = -(θ/2 : ℂ) * I`. Rewrite it
    first: `(fun i => …) = ![cos (θ/2) - sin (θ/2) * I, cos (θ/2) + sin (θ/2) * I]` by `funext i; fin_cases i`
    and `Complex.exp_mul_I`, `Complex.cos_neg`, `Complex.sin_neg`, `neg_neg`. Then compare entries with `simp`
    (unfold `HU`, `Rx`; `vecMul_diagonal` is needed) followed by `ring`.
    HU's proof fields and `diag_conj`: start with `ext i j; fin_cases i <;> fin_cases j`.
    (2) `exp A * exp (−A) = 1` via `Matrix.exp_add_of_commute` with `(Commute.refl A).neg_right`; write
    `A = (-(t : ℂ) * I) • H` out in full (from `_` Lean cannot infer its type).
-/
