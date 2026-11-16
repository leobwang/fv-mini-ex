/- E114 | CNOT makes a Bell state | 3 min | Fin 2 × Fin 2, mulVec, Kronecker, ext on pairs, Fintype.sum_prod_type, mathlib
GOAL
  A two-qubit state is a vector indexed by pairs `(a, b) : Fin 2 × Fin 2` (the basis state |ab⟩). Show
  that "Hadamard on qubit 1, then CNOT" maps |00⟩ to the Bell state (|00⟩ + |11⟩)/√2, and CNOT² = 1.

REFERENCE
  #check Matrix.mulVec             -- `M *ᵥ v`: (M *ᵥ v) i = ∑ j, M i j * v j   (unfold: `Matrix.mulVec, dotProduct`)
  #check Fintype.sum_prod_type     -- ∑ x, f x = ∑ x, ∑ y, f (x, y)   (a sum over pairs is a double sum)
  `H ⊗ₖ 1` (typed `\otimes\_k`, from `open scoped Kronecker`) is the Kronecker product: H on qubit 1
  (the control), identity on qubit 2. `Matrix.of f` is the matrix whose (p, q) entry is `f p q`.
  #check Matrix.kroneckerMap_apply -- (A ⊗ₖ B) (i, k) (j, l) = A i j * B k l   (simp applies it by itself)
  #check Pi.single_apply           -- Pi.single i x i' = if i' = i then x else 0
  example : (1 : Fin 2) + 1 = 0 := rfl   -- `Fin 2` addition is XOR: CNOT flips the target iff control = 1
  `ext ⟨a, b⟩` splits a vector equation on pairs into entries and names both components; then
  `fin_cases a <;> fin_cases b` makes the four cases |00⟩ … |11⟩. For a matrix: `ext ⟨a, b⟩ ⟨c, d⟩`.
  Close each case with `simp [<your defs>, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]`
  (for a matrix product use `Matrix.mul_apply` instead of `mulVec`/`dotProduct`).
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

-- BEGIN SPEC
theorem cnot_bell : CNOT *ᵥ ((H ⊗ₖ 1) *ᵥ tensor (ket 0) (ket 0)) = bell :=
-- END SPEC
  by
    ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [CNOT, H, ket, tensor, bell, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

-- BEGIN SPEC
theorem cnot_sq : CNOT * CNOT = 1 :=
-- END SPEC
  by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [CNOT, Matrix.mul_apply, Fintype.sum_prod_type]

end E114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both sides are finite objects indexed by pairs; compare them one basis entry at a time.
H2. `ext ⟨a, b⟩` (two `⟨…⟩` patterns for the matrix), split every component with `fin_cases`, and
    let `simp` unfold the definitions and the sums over `Fin 2 × Fin 2`.
H3. `ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [CNOT, H, ket, tensor, bell, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]`;
    `ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [CNOT, Matrix.mul_apply, Fintype.sum_prod_type]`.
-/
