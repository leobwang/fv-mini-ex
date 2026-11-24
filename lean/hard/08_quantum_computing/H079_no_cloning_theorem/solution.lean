/- H079 | The no-cloning theorem | 30-45 min | unitarity, inner products, Ket.prod, Braket.dot, physlib
GOAL
  If one unitary `U` on two registers clones two states, `U(ψ ⊗ f) = ψ ⊗ ψ` and `U(φ ⊗ f) = φ ⊗ φ`
  (`f` is the blank state of the copy register), then `⟨ψ|φ⟩ = 0` or `⟨ψ|φ⟩ = 1`: only orthogonal
  or identical states can be cloned by the same machine.

BANNED: no_cloning

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace H079

open Braket

/- SKELETON · dot_eq_star_dotProduct   (MILESTONE 1: prove it first; used twice in step 2 of
                                         cloning_forces_orthogonal)
  1. Both sides are sums over `d`. Unfold the bra-ket on the left and `⬝ᵥ` on the right:   R1, R5
  2. Rewrite each summand into `ψ.vec`, `φ.vec` form:
       left:  bra entry `↑ψ x` → `conj (ψ.vec x)`, ket entry `φ x` → `φ.vec x`         R2 → R3, R4
       right: `star ψ.vec x` → `conj (ψ.vec x)`                                         R6
     One `simp [...]` naming the definitions of R1, R2, R4, R5 does steps 1–2 and closes the goal.
-/
-- MILESTONE (optional: change or delete)
/-- a bra-ket is the conjugate-linear dot product of the two vectors -/
theorem dot_eq_star_dotProduct {d : Type} [Fintype d] (ψ φ : Ket d) :
    〈ψ‖φ〉 = star ψ.vec ⬝ᵥ φ.vec := by
  simp [Braket.dot, dotProduct, Ket.to_bra, Bra.apply, Ket.apply]

/- SKELETON · dot_prod   (MILESTONE 2: used twice, right to left, in step 2 of
                          cloning_forces_orthogonal)
  1. Unfold all three bra-kets; split the sum over pairs; multiply out the product of sums:
       R1, R7, R8   (one `simp only [...]`)
  2. Both sides are now `∑ i, ∑ j, …`: reduce to one summand at fixed `i`, `j`:            R9 (nested)
  3. Evaluate the summand: product-state entries, bra entries, conjugate of a product:
       R10, R2, R4, R11   (one `simp [...]`)
  4. The same four factors, grouped differently:                                            ring
-/
-- MILESTONE (optional: change or delete)
/-- inner products of product states multiply -/
theorem dot_prod {d : Type} [Fintype d] (ψ₁ ψ₂ φ₁ φ₂ : Ket d) :
    〈ψ₁ ⊗ᵠ ψ₂‖φ₁ ⊗ᵠ φ₂〉 = 〈ψ₁‖φ₁〉 * 〈ψ₂‖φ₂〉 := by
  simp only [Braket.dot, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Ket.prod, Ket.to_bra, Bra.apply, Ket.apply]
  ring

/- SKELETON · unitary_dot   (MILESTONE 3: used in the last rewrite of step 2 of
                             cloning_forces_orthogonal)
  1. One `rw [...]` chain, ⟨Ux|Uy⟩ → ⟨x|Uᴴ U y⟩ → ⟨x|y⟩:
       move the left `U` across as `Uᴴ`                                  R12, R13
       combine `Uᴴ` and `U` into one matrix                              R14
       `Uᴴ` → `star U`, then `star U * U` → `1`, then `v ᵥ* 1` → `v`     R15, R16, R17
     After the last rewrite both sides agree and `rw` closes the goal.
-/
-- MILESTONE (optional: change or delete)
/-- a unitary preserves inner products -/
theorem unitary_dot {n : Type} [Fintype n] [DecidableEq n] (U : 𝐔[n]) (x y : n → ℂ) :
    star (U.val *ᵥ x) ⬝ᵥ (U.val *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]

/- SKELETON · cloning_forces_orthogonal   (prove MILESTONES 1–3 first)
  1. State the key fact (z = ⟨ψ|φ⟩; inputs before U on the left, outputs after U on the right):
       have key : 〈ψ‖φ〉 * 〈f‖f〉 = 〈ψ‖φ〉 * 〈ψ‖φ〉                       TACTIC_STATES "Adding facts"
  2. Prove `key` with one `rw [...]` chain, in this order:
       fold each product into one bra-ket of product states: ← dot_prod, twice     R18
       bra-kets → `star _ ⬝ᵥ _`: dot_eq_star_dotProduct, twice                     R18, left to right
       outputs → U applied to inputs: ← hψ, ← hφ                                   rw [← h]
       drop U: unitary_dot                                                         MILESTONE 3
  3. `〈f‖f〉` → `1` inside key:                                                      R19
  4. h : 〈ψ‖φ〉 * (〈ψ‖φ〉 - 1) = 0 from key:                                         R20
  5. Split on which factor is zero, and close each case:                           R21, R23 (+ R22)
-/
-- BEGIN SPEC
theorem cloning_forces_orthogonal {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d × d])
    (ψ φ f : Ket d)
    (hψ : U.val *ᵥ (ψ ⊗ᵠ f).vec = (ψ ⊗ᵠ ψ).vec) (hφ : U.val *ᵥ (φ ⊗ᵠ f).vec = (φ ⊗ᵠ φ).vec) :
    〈ψ‖φ〉 = 0 ∨ 〈ψ‖φ〉 = 1 :=
-- END SPEC
  by
    -- WHY: compare ⟨ψ⊗f|φ⊗f⟩ before and after U; unitaries preserve inner products
    have key : 〈ψ‖φ〉 * 〈f‖f〉 = 〈ψ‖φ〉 * 〈ψ‖φ〉 := by
      rw [← dot_prod, ← dot_prod, dot_eq_star_dotProduct, dot_eq_star_dotProduct, ← hψ, ← hφ,
        unitary_dot]
    rw [Braket.dot_self_eq_one] at key
    have h : 〈ψ‖φ〉 * (〈ψ‖φ〉 - 1) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

end H079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compute the inner product of the two inputs `ψ ⊗ f`, `φ ⊗ f` in two ways: before `U` it is
    `⟨ψ|φ⟩·⟨f|f⟩ = ⟨ψ|φ⟩`, after `U` it is `⟨ψ⊗ψ|φ⊗φ⟩ = ⟨ψ|φ⟩²`, and unitaries preserve inner
    products. So `z = z²` for `z = ⟨ψ|φ⟩`. The three MILESTONES are exactly the three facts used.
H2. MILESTONE 1: one `simp` that unfolds `Braket.dot`, `dotProduct`, `Ket.to_bra`, `Bra.apply`,
    `Ket.apply`. MILESTONE 2: `simp only [Braket.dot, Fintype.sum_prod_type, Finset.sum_mul_sum]`, then
    `Finset.sum_congr` twice down to one summand, then `simp [Ket.prod, …]` and `ring`. MILESTONE 3: a
    `rw` chain `star_mulVec`, `dotProduct_mulVec`, `vecMul_vecMul`, `← star_eq_conjTranspose`,
    `UnitaryGroup.star_mul_self`, `vecMul_one` (all in namespace `Matrix`).
    Main: `key`, rewrite `〈f‖f〉` to `1`, then `z * (z - 1) = 0` and `mul_eq_zero`.
H3. `have key : 〈ψ‖φ〉 * 〈f‖f〉 = 〈ψ‖φ〉 * 〈ψ‖φ〉 := by rw [← dot_prod, ← dot_prod,
    dot_eq_star_dotProduct, dot_eq_star_dotProduct, ← hψ, ← hφ, unitary_dot]`; then
    `rw [Braket.dot_self_eq_one] at key`, `have h : 〈ψ‖φ〉 * (〈ψ‖φ〉 - 1) = 0 := by linear_combination -key`,
    `rcases mul_eq_zero.mp h with h | h`, and `Or.inl h` / `Or.inr (sub_eq_zero.mp h)`.
-/
