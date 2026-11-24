/- M143 | Correlations of the maximally entangled state; the 2√2 value | 20-25 min | maximally entangled state, expectation value, Kronecker product, double sums, ite collapse, linearity, physlib
GOAL
  For `Φ = Σᵢ |i⟩|i⟩ / √d` (`Ket.MES d`) and any `A, B` on `ℂ^d`: `⟨Φ|A ⊗ B|Φ⟩ = (1/d) Σᵢⱼ Aᵢⱼ Bᵢⱼ`.
  Corollary: with `A₀ = Z`, `A₁ = X`, `B₀ = (Z+X)/√2`, `B₁ = (Z−X)/√2`, the Bell state reaches CHSH value
  `2√2`, above the local-hidden-variable bound 2 (M141).

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M143

/- SKELETON · mes_expect
  1. Prove two facts first (milestones), each with `have`; write the casts out in full:
       hΦ : ∀ i j : d, (Ket.MES d).vec (i, j) =
              if i = j then ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ else 0
            proof: intro i j, then                                           R1
       hn : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ =
              ((Fintype.card d : ℂ))⁻¹
            proof:                                                           R2 → R3 → R4 with R5 → R6
     hΦ is used in step 2, hn in step 5.
  2. Unfold ⟨Φ|A ⊗ B|Φ⟩ into a quadruple sum and insert the amplitudes:     R7, R8, R9, R10, R11 (with hΦ)
  3. Push every `if` to the front of its term and collapse the two sums
     the `if`s select (one `simp only` can hold steps 2 and 3):              R12, R13, R14 → R15
  4. Drop the conjugation of the real amplitude:                            R16
  5. Compare the sides sum by sum: outer sum                                R17 (right side), R18
                                   inner sum                                R17 twice (once per side), R18
     then turn (↑(card d))⁻¹ into the amplitude squared and finish:         rw [← hn], ring
-/
-- BEGIN SPEC
theorem mes_expect {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (A B : Matrix d d ℂ) :
    star (Ket.MES d).vec ⬝ᵥ ((A ⊗ₖ B) *ᵥ (Ket.MES d).vec) =
      ((Fintype.card d : ℂ))⁻¹ * ∑ i, ∑ j, A i j * B i j :=
-- END SPEC
  by
    have hΦ : ∀ i j : d, (Ket.MES d).vec (i, j) =
        if i = j then ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ else 0 := by
      intro i j
      simp [Ket.MES]
    have hn : ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ =
        ((Fintype.card d : ℂ))⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      simp
    simp only [dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply, Pi.star_apply, hΦ,
      apply_ite star, star_zero, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hn]
    ring

-- BEGIN SPEC
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
noncomputable def B₀ : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • (Z + X)
noncomputable def B₁ : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • (Z - X)
/-- the CHSH operator `A₀ ⊗ B₀ + A₀ ⊗ B₁ + A₁ ⊗ B₀ − A₁ ⊗ B₁` with `A₀ = Z`, `A₁ = X` -/
noncomputable def chsh : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Z ⊗ₖ B₀ + Z ⊗ₖ B₁ + X ⊗ₖ B₀ - X ⊗ₖ B₁
-- END SPEC

/- SKELETON · bell_chsh
  1. Never expand a 4×4 matrix. Unfold `chsh` (simp only [chsh]) and split it
     by linearity into four expectation values:                            R19, R20
  2. Rewrite each of the four with the milestone `mes_expect` (in the same
     `simp only` as step 1, as in R11):                                     simp only [mes_expect]
  3. Prove the √2 facts:
       h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2                                 R21 → R22 → R23
       hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0                                    R24
  4. Evaluate the 2×2 sums: `simp` with R25 and the names B₀, B₁, X, Z
     (it applies R26–R28 by itself)
  5. Clear the (√2)⁻¹ denominators, then finish with h2; read the
     coefficient of h2 off the goal R29 leaves (match the ↑√2 ^ 2 terms):  R29, R30
-/
-- BEGIN SPEC
theorem bell_chsh :
    star (Ket.MES (Fin 2)).vec ⬝ᵥ (chsh *ᵥ (Ket.MES (Fin 2)).vec) = 2 * Real.sqrt 2 :=
-- END SPEC
  by
    simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, mes_expect]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      simp
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
    simp [Fin.sum_univ_two, B₀, B₁, X, Z]
    field_simp
    linear_combination (-4) * h2

end M143

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `mes_expect`: unfolded, `⟨Φ|A ⊗ B|Φ⟩` is a quadruple sum over `(i, k)` and `(j, l)` of
    `conj Φ(i, k) * (A i j * B k l) * Φ(j, l)`. `Φ` vanishes off the diagonal, so two of the four sums collapse
    (`k = i`, `l = j`) and every surviving term carries the amplitude twice. `bell_chsh`: don't touch 4×4 matrices;
    split `chsh` by linearity and apply `mes_expect` to each term, which leaves 2×2 sums.
H2. Prove `hΦ` (R1) and `hn` (R2–R6) first. Then: one `simp only` that unfolds (R7–R10), inserts `hΦ` (R11), pushes
    the `if`s out and collapses the sums (R12–R15); then R16 for `star`; then R17, R18 for the outer sum, R17, R18 for
    the inner one, `rw [← hn]` and `ring`. Corollary: `simp only` with `chsh`, R19, R20 and `mes_expect`; state `h2`
    and `hne`; evaluate with `simp`; `field_simp`; `linear_combination` with `h2`.
H3. `simp only [dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply, Pi.star_apply, hΦ, apply_ite star, star_zero,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`, then
    `simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]`. Corollary:
    `simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, mes_expect]`, then
    `simp [Fin.sum_univ_two, B₀, B₁, X, Z]`, `field_simp`, `linear_combination (-4) * h2`.
-/
