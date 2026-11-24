/- M131 | Superdense coding: four orthonormal messages | 20 min | Ket.MES, adjoint moves, Kronecker mixed product, trace, physlib
GOAL
  Alice encodes by applying `P` to her half of the maximally entangled state `Φ` on `d × d`. Show the
  overlap `⟨(P⊗1)Φ, (Q⊗1)Φ⟩ = tr(Pᴴ Q) / n`, `n = Fintype.card d`; then for `d = Fin 2` the four encodings
  `Z^b₁ X^b₂` are orthonormal, so Bob decodes two bits from one qubit. Expect one helper lemma (MILESTONE).

GUIDE
  Entries R1–R38: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M131

theorem MES_apply {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (i j : d) :
    (Ket.MES d).vec (i, j) = if i = j then ((Real.sqrt (Fintype.card d) : ℂ))⁻¹ else 0 := by
  simp [Ket.MES]

theorem inv_sqrt_sq (n : ℕ) :
    ((Real.sqrt n : ℂ))⁻¹ * ((Real.sqrt n : ℂ))⁻¹ = ((n : ℂ))⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

/- SKELETON · mes_expect   (MILESTONE: prove it first; `sdc_overlap` ends with `rw [mes_expect]`)
  0. Two helper lemmas of your own, stated above `mes_expect`:
       MES_apply (i j : d) :
         (Ket.MES d).vec (i, j) = if i = j then ((√(Fintype.card d) : ℝ) : ℂ)⁻¹ else 0
                                                                            proof: R1
       inv_sqrt_sq (n : ℕ) : ((√n : ℝ) : ℂ)⁻¹ * ((√n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹
                                                                            proof: R2 → R3 → R4 (R5) → R6
  1. One `simp only [...]` with, in this order of effect:
       inner product and matrix–vector product → sums                      R7, R8 (then R7 again)
       sums over pairs → double sums                                        R9
       entries of `A ⊗ₖ B` and of `star Φ`                                  R10, R11
       amplitudes of Φ → `if`s                                              MES_apply
       `star`, then the factors, into the `if`s                             R12, R13, R14
       indicator sums keep one term                                         R15
  2. A second `simp only`: conjugate of the real `(√n)⁻¹`, scalar into sums R16 → R17 → R18, R19
  3. Compare the double sums summand by summand                             R20 (nested twice)
  4. `rw [← inv_sqrt_sq]` on the right side, then `ring`
-/
-- MILESTONE (optional: change or delete)
/-- `⟨Φ, (A ⊗ B) Φ⟩ = (1/n) ∑ᵢⱼ Aᵢⱼ Bᵢⱼ` -/
theorem mes_expect {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (A B : Matrix d d ℂ) :
    star (Ket.MES d).vec ⬝ᵥ ((A ⊗ₖ B) *ᵥ (Ket.MES d).vec)
      = ((Fintype.card d : ℂ))⁻¹ * ∑ i, ∑ j, A i j * B i j := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Pi.star_apply,
    MES_apply, apply_ite star, star_zero, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← inv_sqrt_sq]
  ring

/- SKELETON · sdc_overlap   (uses the MILESTONE `mes_expect`)
  1. Move `P ⊗ 1` across the inner product, as its adjoint:                R21, R22 with ←, R23    (W1)
  2. Merge the Kronecker products:                                          R24, R25, R26 with ←, R27 (W2)
       goal now: star Φ ⬝ᵥ ((Pᴴ * Q) ⊗ₖ 1) *ᵥ Φ = n⁻¹ * (Pᴴ * Q).trace
  3. rw [mes_expect]   (A := Pᴴ * Q, B := 1)
  4. Identity entries → `if`s, collapse, trace as a sum: one `simp` with    R28, R29 (it adds R13, R15) (W3)
-/
-- BEGIN SPEC
theorem sdc_overlap {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (P Q : Matrix d d ℂ) :
    star ((P ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ (Ket.MES d).vec) ⬝ᵥ ((Q ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ (Ket.MES d).vec)
      = ((Fintype.card d : ℂ))⁻¹ * (Pᴴ * Q).trace :=
-- END SPEC
  by
    -- WHY: `P ⊗ 1` crosses the inner product as its adjoint `Pᴴ ⊗ 1`.
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, one_mul,
      mes_expect]
    simp [Matrix.trace, Matrix.one_apply]

-- BEGIN SPEC
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's encoding of the two bits `b = (b₁, b₂)`: apply `Z^b₁ X^b₂` -/
def enc (b : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Z ^ (b.1 : ℕ) * X ^ (b.2 : ℕ)

/-- the state Bob receives for message `b` -/
noncomputable def sdc (b : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  (enc b ⊗ₖ 1) *ᵥ (Ket.MES (Fin 2)).vec
-- END SPEC

/- SKELETON · sdc_orthonormal   (uses `sdc_overlap`)
  1. Unfold the received states:                                            R30 (unfold sdc)
  2. rw [sdc_overlap]   goal: (↑(Fintype.card (Fin 2)))⁻¹ * ((enc b)ᴴ * enc c).trace = if b = c then 1 else 0
  3. Split both messages into their bits:                                   R31, twice
  4. 16 cases: `fin_cases` on all four bits, chained with `<;>`
  5. Evaluate every case: `simp` with `enc, X, Z` and                       R33, R34, R35 (R36)
       (it applies R32, R37, R38 by itself)                                                        (W4)
  6. 3 of the 4 diagonal cases stop at `2⁻¹ * (1 + 1) = 1`:                norm_num
-/
-- BEGIN SPEC
theorem sdc_orthonormal (b c : Fin 2 × Fin 2) :
    star (sdc b) ⬝ᵥ sdc c = if b = c then 1 else 0 :=
-- END SPEC
  by
    unfold sdc
    rw [sdc_overlap]
    obtain ⟨b1, b2⟩ := b
    obtain ⟨c1, c2⟩ := c
    fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2 <;>
      simp [enc, X, Z, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply] <;> norm_num

end M131

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Move `P ⊗ 1` to the other side of the inner product (it becomes `Pᴴ ⊗ 1`) and merge it with `Q ⊗ 1`.
    What is left is `⟨Φ, (M ⊗ 1) Φ⟩` with `M = Pᴴ Q`: a double sum in which only diagonal terms survive.
    The MILESTONE `mes_expect` computes `⟨Φ, (A ⊗ B) Φ⟩` for any `A, B`; prove it first.
H2. MILESTONE: unfold everything into sums (R7–R11), read Φ's amplitudes as `if`s through your own lemma
    `MES_apply` (R1), collapse the `if`s (R12–R15), clear the conjugate of `(√n)⁻¹` (R16–R18), then compare
    summands (R19, R20) using `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` (R2–R6). `sdc_overlap` is a `rw` chain (R21–R27), then
    `rw [mes_expect]` and one `simp` (R28, R29). The corollary: `unfold sdc; rw [sdc_overlap]`, then 16 cases
    of 2×2 traces (R31–R38).
H3. `sdc_overlap`: `rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, one_mul, mes_expect]`.
    MILESTONE: `simp only [dotProduct, mulVec, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Pi.star_apply,
    MES_apply, apply_ite star, star_zero, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]`, then `simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal, Finset.mul_sum]`
    and `refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_`.
    Corollary: `obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c`,
    `fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2 <;> simp [enc, X, Z, Matrix.trace_fin_two, ...]`.
-/
