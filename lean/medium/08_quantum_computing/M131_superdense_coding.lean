/- M131 | Superdense coding: four orthonormal messages | 20 min | Ket.MES, adjoint moves, Kronecker mixed product, trace, physlib
GOAL
  Alice encodes by applying `P` to her half of the maximally entangled state `Φ` on `d × d`. Show the
  overlap `⟨(P⊗1)Φ, (Q⊗1)Φ⟩ = tr(Pᴴ Q) / n`, `n = Fintype.card d`; then for `d = Fin 2` the four encodings
  `Z^b₁ X^b₂` are orthonormal, so Bob decodes two bits from one qubit. Expect one helper lemma (MILESTONE).

REFERENCE
  -- `Ket.MES d : Ket (d × d)` is Φ = (1/√n) ∑ᵢ |i, i⟩ with n = `Fintype.card d`; `.vec` is its amplitude function.
  example {d : Type} [Fintype d] [Nonempty d] [DecidableEq d] (i j : d) : (Ket.MES d).vec (i, j) =
      if i = j then ((Real.sqrt (Fintype.card d) : ℂ))⁻¹ else 0 := by simp [Ket.MES]
  #check Matrix.star_mulVec            -- star (M *ᵥ v) = star v ᵥ* Mᴴ
  #check Matrix.dotProduct_mulVec      -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  #check Matrix.conjTranspose_kronecker -- (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ
  #check Matrix.mul_kronecker_mul      -- (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'   (rewrite with ←)
  #check Matrix.trace                  -- A.trace = ∑ i, A i i
  #check Finset.sum_ite_eq             -- ∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0
  example (n : ℝ) (h : 0 ≤ n) : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt h
  #check Matrix.trace_fin_two          -- A.trace = A 0 0 + A 1 1   for 2×2 A
NOTE: `star v ⬝ᵥ w` is the inner product ⟨v, w⟩; `Mᴴ` is the conjugate transpose; `(b.1 : ℕ)` turns a bit into 0 or 1.
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M131

-- MILESTONE (optional: change or delete)
/-- `⟨Φ, (A ⊗ B) Φ⟩ = (1/n) ∑ᵢⱼ Aᵢⱼ Bᵢⱼ` -/
theorem mes_expect {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (A B : Matrix d d ℂ) :
    star (Ket.MES d).vec ⬝ᵥ ((A ⊗ₖ B) *ᵥ (Ket.MES d).vec)
      = ((Fintype.card d : ℂ))⁻¹ * ∑ i, ∑ j, A i j * B i j := by
  sorry

-- BEGIN SPEC
theorem sdc_overlap {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (P Q : Matrix d d ℂ) :
    star ((P ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ (Ket.MES d).vec) ⬝ᵥ ((Q ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ (Ket.MES d).vec)
      = ((Fintype.card d : ℂ))⁻¹ * (Pᴴ * Q).trace :=
-- END SPEC
  sorry

-- BEGIN SPEC
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's encoding of the two bits `b = (b₁, b₂)`: apply `Z^b₁ X^b₂` -/
def enc (b : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Z ^ (b.1 : ℕ) * X ^ (b.2 : ℕ)

/-- the state Bob receives for message `b` -/
noncomputable def sdc (b : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  (enc b ⊗ₖ 1) *ᵥ (Ket.MES (Fin 2)).vec
-- END SPEC

-- BEGIN SPEC
theorem sdc_orthonormal (b c : Fin 2 × Fin 2) :
    star (sdc b) ⬝ᵥ sdc c = if b = c then 1 else 0 :=
-- END SPEC
  sorry

end M131

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Move `P ⊗ 1` to the other side of the inner product (it becomes `Pᴴ ⊗ 1`) and merge it with `Q ⊗ 1`.
    What is left is `⟨Φ, (M ⊗ 1) Φ⟩` with `M = Pᴴ Q`: a double sum in which only diagonal terms survive.
H2. `rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, one_mul]`. For the double sum, restate the `Ket.MES` REFERENCE
    example as a lemma `MES_apply` and unfold with `dotProduct, mulVec, Fintype.sum_prod_type, Matrix.kroneckerMap_apply`.
    The corollary: `unfold sdc; rw [sdc_overlap]`, then 16 cases of 2×2 traces.
H3. Prove the MILESTONE `mes_expect` first (then `B = 1` turns its double sum into the trace).
    Collapse with `simp only [..., MES_apply, apply_ite star, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]` and `(√n)⁻¹ * (√n)⁻¹ = (n : ℂ)⁻¹` (`← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt`).
    Corollary: `obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c`,
    `fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2 <;> simp [enc, X, Z, Matrix.trace_fin_two, ...]`.
-/
