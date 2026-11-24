/- H088 | Time evolution: exp(−iθX/2) and unitarity | 45-75 min | matrix exponential, diagonalisation, Matrix.exp lemmas, Hermitian generators, mathlib
GOAL
  (1) Evolving under the Hamiltonian `X` (Pauli X) for time `θ/2` gives the x-rotation gate:
      `exp(−i(θ/2)X) = cos(θ/2)·1 − i·sin(θ/2)·X = Rx θ`  (prove it by diagonalising `X`).
  (2) For every Hermitian `H` and real `t`, `exp(−itH)` is unitary (Schrödinger evolution keeps norms).

GUIDE
  Entries R1–R36: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · HU   (MILESTONE 1: the eigenvector matrix of `X`; used in `diag_conj` and `time_evolution`)
  The two `sorry`s are the proof fields `val * inv = 1` and `inv * val = 1`: write `by …` in each.   R1
  In each field:
    1. matrix equation → four entry goals                                    R2, R3
    2. evaluate the entries: `simp` with the product lemmas                  R4, R5 (R6 by itself)
    3. finish the numerals that remain                                       R7
-/
-- MILESTONE (optional: change or delete)
/-- the (unnormalised) Hadamard matrix `!![1, 1; 1, -1]` as a unit, with inverse `½ · itself` -/
noncomputable def HU : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  ⟨!![1, 1; 1, -1], (1 / 2 : ℂ) • !![1, 1; 1, -1], sorry, sorry⟩

/- SKELETON · diag_conj   (MILESTONE 2: `c • X = V diag(c, −c) V⁻¹`; used in `time_evolution`)
  1. matrix equation → four entry goals                                      R2, R3
  2. `simp` with `X`, `HU` and the product lemmas; it unfolds `↑HU`, `↑HU⁻¹` by itself (R8, R9).
     Also pass R10, or `simp` stops at `v ᵥ* diagonal w` (W4):                R4, R5, R10
  3. close what is left                                                      R11
-/
-- MILESTONE (optional: change or delete)
/-- `X` is diagonalised by `HU`, with eigenvalues `1, −1` -/
theorem diag_conj (c : ℂ) :
    c • X = (HU : Matrix (Fin 2) (Fin 2) ℂ) * diagonal ![c, -c] * (↑HU⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

/- SKELETON · exp_diag   (MILESTONE 3: used in `time_evolution`)
  1. exp of a diagonal → diagonal of the vector exp                          R12
  2. vector exp → entrywise exp                                              R13
  3. scalar `NormedSpace.exp` → `cexp`, under the `fun`                      R14
-/
-- MILESTONE (optional: change or delete)
theorem exp_diag (v : Fin 2 → ℂ) :
    NormedSpace.exp (diagonal v) = diagonal (fun i => Complex.exp (v i)) := by
  sorry

/- SKELETON · star_gen   (MILESTONE 4: `(−itH)ᴴ = −(−itH)`; used in `evolution_unitary`)
  1. pull `ᴴ` through the scalar, then drop it from `H`                       R15, R16
  2. move the outer minus onto the scalar                                    R17
  3. compare the scalars                                                     R18
  4. compute the conjugate `star (-↑t * I) = -(-↑t * I)` with plain `simp`  R22
     (it applies R19–R21 and the sign lemmas itself; by hand you would also need `map_neg`)
-/
-- MILESTONE (optional: change or delete)
/-- the generator `−itH` is anti-Hermitian -/
theorem star_gen {n : Type} [Fintype n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    ((-(t : ℂ) * I) • H)ᴴ = -((-(t : ℂ) * I) • H) := by
  sorry

/- SKELETON · time_evolution
  Prove MILESTONES 1–3 first (HU, diag_conj, exp_diag): step 1 rewrites with them.
  1. rw [diag_conj, Matrix.exp_units_conj, exp_diag]                         R23
     (now `↑HU * diagonal (fun i => cexp (![c, -c] i)) * ↑HU⁻¹ = Rx θ`, `c = -(↑θ / 2) * I`)
  2. BEFORE any `simp`, name the phases (`have`, TACTIC_STATES):
       hv : (fun i => cexp (![-(θ / 2 : ℂ) * I, -(-(θ / 2 : ℂ) * I)] i))
              = ![cos (θ / 2) - sin (θ / 2) * I, cos (θ / 2) + sin (θ / 2) * I]
     proof: R24, R3; then index 0: R25, R26, R27, R11;  index 1: R25, R28, R26   (pattern: W2)
  3. rw [hv]
  4. matrix equation → four entry goals                                      R2, R3
  5. `simp` with `HU`, `Rx` and the product lemmas (R8, R9, R29 by itself)   R4, R5, R10
  6. close each entry                                                        R11
-/
-- BEGIN SPEC
theorem time_evolution (θ : ℝ) : NormedSpace.exp ((-(θ / 2 : ℂ) * I) • X) = Rx θ :=
-- END SPEC
  sorry

/- SKELETON · evolution_unitary
  Prove MILESTONE 4 (star_gen) first: step 3 rewrites with it. Below, A = (-(t : ℂ) * I) • H.
  One `rw [...]` chain:
  1. membership → `exp A * star (exp A) = 1`, then `star` → `ᴴ`               R30, R31
  2. move `ᴴ` inside: `(exp A)ᴴ` → `exp Aᴴ`                                   R32
  3. rw [star_gen H hH t]: `Aᴴ` → `-A`
  4. merge `exp A * exp (-A)` → `exp (A + -A)`; give the commute proof with A written out   R33 inside R34
  5. `A + -A` → `0`, `exp 0` → `1`                                           R35, R36
-/
-- BEGIN SPEC
theorem evolution_unitary {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * I) • H) ∈ Matrix.unitaryGroup n ℂ :=
-- END SPEC
  sorry

end H088

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (1) `X` has eigenvectors `(1, 1)` and `(1, −1)` with eigenvalues `1, −1`, so `c • X = V diag(c, −c) V⁻¹`
    with `V = !![1, 1; 1, -1]` (`HU`). The exponential commutes with conjugation by a unit and acts entrywise on
    a diagonal; the two phases are `e^{∓iθ/2} = cos(θ/2) ∓ i sin(θ/2)`.
    (2) `U` is unitary iff `U * Uᴴ = 1`. Push `ᴴ` inside `exp`; the generator `A = −itH` satisfies `Aᴴ = −A`,
    and `A` commutes with `−A`, so `exp A * exp (−A) = exp 0 = 1`.
H2. Milestones first. `HU`, `diag_conj`: entry by entry (R2, R3), `simp` with `Matrix.mul_apply`,
    `Fin.sum_univ_two` (and `Matrix.vecMul_diagonal` for `diag_conj`), then `norm_num` / `ring`.
    `exp_diag`: `Matrix.exp_diagonal`, `Pi.exp_def`, `simp only [← Complex.exp_eq_exp_ℂ]`. `star_gen`:
    `Matrix.conjTranspose_smul`, `hH.eq`, `← neg_smul`, `congr 1`, `simp`.
    (1) `rw [diag_conj, Matrix.exp_units_conj, exp_diag]`, prove and `rw` the phase vector `hv` (SKELETON), then
    compare entries. (2) `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, star_gen H hH t, …]`.
H3. (1) `hv` by `funext i; fin_cases i`; index 0: `simp only [Fin.zero_eta, Matrix.cons_val_zero,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]` then `ring`; index 1: `simp only [Fin.mk_one,
    Matrix.cons_val_one, Matrix.cons_val_zero, neg_mul, neg_neg, Complex.exp_mul_I]`. After `rw [hv]`:
    `ext i j; fin_cases i <;> fin_cases j <;> simp [HU, Rx, Matrix.mul_apply, Matrix.vecMul_diagonal,
    Fin.sum_univ_two] <;> ring`.
    (2) finish the chain with `← Matrix.exp_add_of_commute _ _ ((Commute.refl ((-(t : ℂ) * I) • H)).neg_right),
    add_neg_cancel, NormedSpace.exp_zero`.
-/
