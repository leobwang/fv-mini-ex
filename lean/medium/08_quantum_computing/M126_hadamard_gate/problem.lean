/- M126 | The Hadamard gate | 10-15 min | Matrix, !![], ext, fin_cases, Real.sqrt casts, unitary group, mathlib
GOAL
  With the Pauli matrices `X, Y, Z` and the Hadamard gate `H = (1/√2)·[[1, 1], [1, -1]]`, prove
  `H² = 1`, `HXH = Z`, `HZH = X`, `HYH = -Y` (H swaps the X and Z bases), and that `H` is unitary.

GUIDE
  Entries R1–R26: one per tactic or lemma, with the proof state before and after.
    ../../guide/medium/08_quantum_computing/M126_hadamard_gate.md     read
    ../../guide/medium/08_quantum_computing/M126_hadamard_gate.lean   step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · hadamard_conj
  1. Prove the √2 fact once, BEFORE splitting, so all four goals get it:   R2
       h : (√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = 1 / 2         proof: R13 → R14 → R15 → R20
  2. Split the four equations:                                              R1
  3. In each of the four goals:
       matrix equation → four entry goals                                  R3, R4
       evaluate the entries: `simp` with the gate names it needs           R5–R11
       substitute the √2 fact                                              rw [h]
       finish the numbers                                                  R20
     In `H * Y * H = -Y` the factor `I` sits between the two (√2)⁻¹:
       move it out first, then rw [h], then finish                          R25, rw [h], R26
-/
-- BEGIN SPEC
theorem hadamard_conj : H * H = 1 ∧ H * X * H = Z ∧ H * Z * H = X ∧ H * Y * H = -Y := by
-- END SPEC
  have h : (√ 2 : ℂ)⁻¹ * (√ 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)];
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  . ext i j ; fin_cases i <;> fin_cases j <;> simp [H] <;> rw [h] <;> norm_num
  . ext i j ; fin_cases i <;> fin_cases j <;> simp [H, X, Z] <;> rw[h] <;> norm_num
  . ext i j ; fin_cases i <;> fin_cases j <;> simp [H, X, Z] <;> rw[h] <;> norm_num
  . ext i j ; fin_cases i <;> fin_cases j <;> simp [H, Y] <;> rw [mul_right_comm _ I, h] <;> ring

/- SKELETON · hadamard_unitary
  1. The same √2 fact `h` (a `have` belongs to one proof only):             R2, R13 → R14 → R15 → R20
  2. Membership → the equation `H * Hᴴ = 1`:                                 R21, R22
  3. Matrix equation → four entry goals:                                    R3, R4
  4. Evaluate the entries. Name the product lemmas, or `simp` stops at
     `v ᵥ* Hᴴ` (R12); R23, R24 are applied by `simp` itself:               R10, R11 with R5–R9
  5. rw [h], then finish the numbers:                                       R20
-/
-- BEGIN SPEC
theorem hadamard_unitary : H ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  sorry

end M126

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The √2 fact: `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num`.
H2. One conjunct: `ext i j; fin_cases i <;> fin_cases j <;> simp [H, X, Z] <;> rw [h] <;> norm_num`.
    For `H * Y * H = -Y`, end with `simp [H, Y] <;> rw [mul_right_comm _ I, h] <;> ring`.
H3. Unitary: `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`, then
    `ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.mul_apply, Fin.sum_univ_two] <;> rw [h] <;> norm_num`.
-/
