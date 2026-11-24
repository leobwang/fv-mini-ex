/- M130 | Deutsch's algorithm | 15-20 min | oracle, Kronecker, mulVec, case split, normSq, mathlib
GOAL
  One oracle query decides whether `f : Fin 2 → Fin 2` is constant: after the circuit
  `(H ⊗ 1) · U_f · (H ⊗ H)` on `|0⟩|1⟩`, the probability that the first qubit reads 1 is 0 if `f 0 = f 1`, else 1.

REFERENCE
  -- Two-qubit states are `Fin 2 × Fin 2 → ℂ`; `M *ᵥ v` is matrix·vector; `A ⊗ₖ B` is the Kronecker product.
  example : (1 : Fin 2) + 1 = 0 := rfl          -- `Fin 2` addition is XOR, so `y + f x` is `y ⊕ f x`
  example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ x, P x := by intro x; fin_cases x <;> assumption
  #check Complex.normSq_apply      -- normSq z = z.re * z.re + z.im * z.im   (|z|², the Born probability)
  #check Matrix.kroneckerMap_apply -- (A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2
  #check Fintype.sum_prod_type     -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)
  #check Pi.single_apply           -- Pi.single i x i' = if i' = i then x else 0
  #check Matrix.one_apply          -- (1 : Matrix n n α) i j = if i = j then 1 else 0
  example : Real.sqrt 2 ^ 6 = 8 := by
    rw [show Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 by ring, Real.sq_sqrt (by norm_num)]; norm_num
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

-- BEGIN SPEC
theorem deutsch_correct (f : Fin 2 → Fin 2) :
    ∑ y, Complex.normSq (deutsch f (1, y)) = if f 0 = f 1 then 0 else 1 :=
-- END SPEC
  sorry

end M130

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. There are only four functions `Fin 2 → Fin 2`: split on the values `f 0` and `f 1` first, so the
    `if` and the oracle become concrete. Then everything is a finite sum you can expand.
H2. Split on `f 0` and `f 1` (each is `0` or `1`; `decide` proves `∀ x : Fin 2, x = 0 ∨ x = 1`). In each case
    unfold everything and expand the finite sums; the less obvious names are `Fintype.sum_prod_type` and
    `Matrix.kroneckerMap_apply`. Finish the arithmetic with `ring_nf`.
H3. After `ring_nf`, the two non-constant cases are left with `√2 ^ 6 * (1 / 8) = 1`: prove
    `have s6 : Real.sqrt 2 ^ 6 = 8` up front (the REFERENCE line) and end the pipeline with `<;> rw [s6] <;> norm_num`.
-/
