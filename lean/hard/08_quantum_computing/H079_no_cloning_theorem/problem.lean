/- H079 | The no-cloning theorem | 30-45 min | unitarity, inner products, Ket.prod, Braket.dot, physlib
GOAL
  If one unitary `U` on two registers clones two states, `U(ψ ⊗ f) = ψ ⊗ ψ` and `U(φ ⊗ f) = φ ⊗ φ`
  (`f` is the blank state of the copy register), then `⟨ψ|φ⟩ = 0` or `⟨ψ|φ⟩ = 1`: only orthogonal
  or identical states can be cloned by the same machine.

REFERENCE
  -- `Ket d`: field `vec : d → ℂ` with ∑ ‖vec i‖² = 1.  `ψ ⊗ᵠ φ : Ket (d × d)` has vec (i, j) = ψ i * φ j
  -- `〈ψ‖φ〉` (needs `open Braket`) = ∑ i, conj (ψ i) * φ i;  `U : 𝐔[n]` is a unitary, `U.val` its matrix
  #check Braket.dot_self_eq_one     -- (ψ : Ket d) : 〈ψ‖ψ〉 = 1
  #check Fintype.sum_prod_type      -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)
  #check Finset.sum_mul_sum         -- (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j
  #check Matrix.star_mulVec         -- star (M *ᵥ v) = star v ᵥ* Mᴴ   (`ᵥ*` row vector · matrix)
  #check Matrix.dotProduct_mulVec   -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  #check Matrix.vecMul_vecMul       -- v ᵥ* M ᵥ* N = v ᵥ* (M * N)
  #check Matrix.UnitaryGroup.star_mul_self  -- star ↑U * ↑U = 1   (`Matrix.star_eq_conjTranspose`: star M = Mᴴ)
  #check Matrix.vecMul_one          -- v ᵥ* 1 = v
  example (a b : ℂ) (h : a = b) : a - b = 0 := by linear_combination h  -- goal = linear combination of hyps
  -- unfold a bra-ket: `simp [Braket.dot, Ket.prod, Ket.to_bra, Bra.apply, Ket.apply]`;  `mul_eq_zero`, `sub_eq_zero`
BANNED: no_cloning
NOTE: physlib's `MState.no_cloning` is banned; name your helpers differently.
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace H079

open Braket

-- MILESTONE (optional: change or delete)
/-- a bra-ket is the conjugate-linear dot product of the two vectors -/
theorem dot_eq_star_dotProduct {d : Type} [Fintype d] (ψ φ : Ket d) :
    〈ψ‖φ〉 = star ψ.vec ⬝ᵥ φ.vec := by
  sorry

-- MILESTONE (optional: change or delete)
/-- inner products of product states multiply -/
theorem dot_prod {d : Type} [Fintype d] (ψ₁ ψ₂ φ₁ φ₂ : Ket d) :
    〈ψ₁ ⊗ᵠ ψ₂‖φ₁ ⊗ᵠ φ₂〉 = 〈ψ₁‖φ₁〉 * 〈ψ₂‖φ₂〉 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- a unitary preserves inner products -/
theorem unitary_dot {n : Type} [Fintype n] [DecidableEq n] (U : 𝐔[n]) (x y : n → ℂ) :
    star (U.val *ᵥ x) ⬝ᵥ (U.val *ᵥ y) = star x ⬝ᵥ y := by
  sorry

-- BEGIN SPEC
theorem cloning_forces_orthogonal {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d × d])
    (ψ φ f : Ket d)
    (hψ : U.val *ᵥ (ψ ⊗ᵠ f).vec = (ψ ⊗ᵠ ψ).vec) (hφ : U.val *ᵥ (φ ⊗ᵠ f).vec = (φ ⊗ᵠ φ).vec) :
    〈ψ‖φ〉 = 0 ∨ 〈ψ‖φ〉 = 1 :=
-- END SPEC
  sorry

end H079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compute the inner product of the two inputs `ψ ⊗ f` and `φ ⊗ f` in two ways: before `U` and after `U`.
    Unitaries do not change inner products.
H2. Before: `⟨ψ⊗f|φ⊗f⟩ = ⟨ψ|φ⟩·⟨f|f⟩ = ⟨ψ|φ⟩`. After: `⟨ψ⊗ψ|φ⊗φ⟩ = ⟨ψ|φ⟩²`. So `z = z²` for `z = ⟨ψ|φ⟩`,
    i.e. `z * (z - 1) = 0`. `dot_prod`: unfold to sums, split with `Fintype.sum_prod_type`, factor the
    right side with `Finset.sum_mul_sum`, then match term by term (`Finset.sum_congr rfl fun i _ => ...`).
H3. Main: `have key : 〈ψ‖φ〉 * 〈f‖f〉 = 〈ψ‖φ〉 * 〈ψ‖φ〉`, proved by rewriting right-to-left with
    `dot_prod` (twice), then `dot_eq_star_dotProduct`, `← hψ`, `← hφ`, `unitary_dot`. Finish with
    `Braket.dot_self_eq_one`, `linear_combination` to get `z * (z - 1) = 0`, and `mul_eq_zero`.
    `unitary_dot`: `rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]`.
-/
