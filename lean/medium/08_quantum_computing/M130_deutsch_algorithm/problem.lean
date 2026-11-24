/- M130 | Deutsch's algorithm | 15-20 min | oracle, Kronecker, mulVec, case split, normSq, mathlib
GOAL
  One oracle query decides whether `f : Fin 2 → Fin 2` is constant: after the circuit
  `(H ⊗ 1) · U_f · (H ⊗ H)` on `|0⟩|1⟩`, the probability that the first qubit reads 1 is 0 if `f 0 = f 1`, else 1.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix Complex
open scoped Kronecker

namespace M130

-- BEGIN SPEC
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • !![1, 1; 1, -1]

/-- computational basis vector `|b⟩` -/
def ket (b : Fin 2) : Fin 2 → ℂ := Pi.single b 1

/-- product state `u ⊗ v` -/
def tensor (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => u p.1 * v p.2

/-- oracle `U_f |x, y⟩ = |x, y ⊕ f x⟩` -/
def Uf (f : Fin 2 → Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = q.2 + f q.1 then 1 else 0

noncomputable def deutsch (f : Fin 2 → Fin 2) : Fin 2 × Fin 2 → ℂ :=
  (H ⊗ₖ 1) *ᵥ (Uf f *ᵥ ((H ⊗ₖ H) *ᵥ tensor (ket 0) (ket 1)))
-- END SPEC

/- SKELETON · deutsch_correct
  1. Prove two facts BEFORE any split, so every case gets them:
       two : ∀ x : Fin 2, x = 0 ∨ x = 1                  proof: R1
       s6  : Real.sqrt 2 ^ 6 = 8   (in ℝ)               proof: R2 → R3 → R4
  2. Split on the value of `f 0`, then of `f 1`, joined by `<;>`
     (four cases: two constant, two balanced):                      R5, R5
  3. In every case, ONE `simp` call with
       the case hypotheses h0, h1                                    R6
       the five definitions deutsch, Uf, H, ket, tensor
       the lemmas simp never applies by itself                      R8, R9, R16
       optional: simp finds these here by itself, naming them is safe R10, R11, R12, R13
     (simp itself applies R7, R14, R15, R17, R18).
     The two constant cases close here.
  4. The balanced cases are left with a real polynomial in `√2 / 2`:
       collect it into `√2 ^ 6 * (1 / 8) = 1`                        R19
       substitute the fact                                           rw [s6]
       finish the numbers                                            R4
-/
-- BEGIN SPEC
theorem deutsch_correct (f : Fin 2 → Fin 2) :
    ∑ y, Complex.normSq (deutsch f (1, y)) = if f 0 = f 1 then 0 else 1 :=
-- END SPEC
  sorry

end M130

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. There are only four functions `Fin 2 → Fin 2`. Split on the values of `f 0` and `f 1` first (R5), so
    the `if f 0 = f 1` and the oracle's `q.2 + f q.1` become concrete; then every amplitude is a finite
    sum of explicit numbers that `simp` can expand.
H2. Facts first: `two : ∀ x : Fin 2, x = 0 ∨ x = 1` (R1) and `s6 : Real.sqrt 2 ^ 6 = 8` (R2 → R3 → R4).
    Then `rcases two (f 0) with h0 | h0 <;> rcases two (f 1) with h1 | h1 <;> simp [...]` with `h0, h1`,
    the five definitions and `mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Pi.single_apply, Complex.normSq_apply` (R6–R18).
H3. `have s6 : Real.sqrt 2 ^ 6 = 8 := by rw [show Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 by ring,
    Real.sq_sqrt (by norm_num)]; norm_num`. After `simp` the balanced cases become `√2 ^ 6 * (1 / 8) = 1`
    under `ring_nf` (R19), so end the pipeline with `<;> ring_nf <;> rw [s6] <;> norm_num`.
-/
