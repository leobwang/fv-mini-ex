/- E114 | CNOT makes a Bell state | 3 min | Fin 2 × Fin 2, mulVec, Kronecker, ext on pairs, Fintype.sum_prod_type, mathlib
GOAL
  A two-qubit state is a vector indexed by pairs `(a, b) : Fin 2 × Fin 2` (the basis state |ab⟩). Show
  that "Hadamard on qubit 1, then CNOT" maps |00⟩ to the Bell state (|00⟩ + |11⟩)/√2, and CNOT² = 1.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E114

-- BEGIN SPEC
open Matrix Complex
open scoped Kronecker

/-- Hadamard gate `(1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • !![1, 1; 1, -1]
/-- CNOT with control = first qubit: |a, b⟩ ↦ |a, b + a⟩. -/
def CNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = q.2 + q.1 then 1 else 0
/-- The basis vector |b⟩ of one qubit. -/
def ket (b : Fin 2) : Fin 2 → ℂ := Pi.single b 1
/-- The product state |u⟩ ⊗ |v⟩. -/
def tensor (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => u p.1 * v p.2
/-- The Bell state (|00⟩ + |11⟩)/√2. -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℂ) else 0
-- END SPEC

/- SKELETON · cnot_bell
  1. Vector equation → one goal for the entry at the pair (a, b):          R1
  2. One goal per basis state |00⟩, |01⟩, |10⟩, |11⟩:                        R2 on a, then on b (`<;>`)
  3. In every goal, ONE `simp` call that names:
       your definitions CNOT, H, ket, tensor, bell                          R3
       matrix × vector, unfolded (else `simp` only merges the gates, R6)    R4, R5
       the sum over pairs, split into a double sum                         R7 → R8
     `simp` then reads the entries by itself:                               R9, R10, R11, R12, R13, R14
     and decides the `Fin 2` conditions:                                    R15, R16
-/
-- BEGIN SPEC
theorem cnot_bell : CNOT *ᵥ ((H ⊗ₖ 1) *ᵥ tensor (ket 0) (ket 0)) = bell :=
-- END SPEC
  sorry

/- SKELETON · cnot_sq
  1. Matrix equation → one goal for the entry at ((a, b), (c, d)):         R17
  2. Sixteen goals:                                                         R2 on a, b, c, d (`<;>`)
  3. In every goal, ONE `simp` call that names:
       CNOT                                                                 R3
       the entry of a matrix product                                        R18
       the sum over the middle pair                                         R7 → R8
     `simp` then reads `of`, the identity and pair equalities by itself,    R9, R11 → R19
     and decides the `Fin 2` conditions:                                    R15, R16
-/
-- BEGIN SPEC
theorem cnot_sq : CNOT * CNOT = 1 :=
-- END SPEC
  sorry

end E114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides are finite objects indexed by pairs; compare them one basis entry at a time (R1, R17), and
    split every component into its two values (R2).
H2. After `ext` and `fin_cases`, one `simp` per goal does the arithmetic, but only if you name the
    definitions, the product (`Matrix.mulVec, dotProduct` for a matrix times a vector, R4–R5;
    `Matrix.mul_apply` for a matrix product, R18) and the sum over pairs (`Fintype.sum_prod_type`, R7).
H3. `ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [CNOT, H, ket, tensor, bell, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]`;
    `ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [CNOT, Matrix.mul_apply, Fintype.sum_prod_type]`.
-/
