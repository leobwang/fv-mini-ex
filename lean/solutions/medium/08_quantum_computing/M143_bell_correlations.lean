/- M143 | Correlations of the maximally entangled state; the 2√2 value | 20-25 min | maximally entangled state, expectation value, Kronecker product, double sums, ite collapse, linearity, physlib
GOAL
  For `Φ = Σᵢ |i⟩|i⟩ / √d` (`Ket.MES d`) and any `A, B` on `ℂ^d`: `⟨Φ|A ⊗ B|Φ⟩ = (1/d) Σᵢⱼ Aᵢⱼ Bᵢⱼ`.
  Corollary: with `A₀ = Z`, `A₁ = X`, `B₀ = (Z+X)/√2`, `B₁ = (Z−X)/√2`, the Bell state reaches CHSH value
  `2√2`, above the local-hidden-variable bound 2 (M141).

REFERENCE
  -- `star v ⬝ᵥ (M *ᵥ v)` is `⟨v|M|v⟩`; `simp only [dotProduct, mulVec]` turns it into sums. `A ⊗ₖ B` (open scoped Kronecker)
  -- is the Kronecker product; `(Ket.MES d).vec : d × d → ℂ` is the state vector of `Φ`.
  example {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (i j : d) :
      (Ket.MES d).vec (i, j) = if i = j then ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ else 0 := by simp [Ket.MES]
  #check @Fintype.sum_prod_type     -- ∑ x, f x = ∑ x, ∑ y, f (x, y)   (sum over pairs → double sum)
  #check @Matrix.kroneckerMap_apply -- (A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2
  #check @Finset.sum_ite_eq'        -- ∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0  (and `sum_ite_eq`)
  #check @apply_ite                 -- f (if P then x else y) = if P then f x else f y   (also `mul_ite`, `ite_mul`)
  #check @Matrix.add_mulVec         -- (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x   (also `sub_mulVec`, `dotProduct_add`, `dotProduct_sub`)
  example : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  example (x : ℂ) (h : x ^ 2 = 2) : x ^ 2 * 3 = 6 := by linear_combination 3 * h   -- goal = linear combo of hyps
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M143

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
H1. `mes_expect`: unfold to a quadruple sum over `(i, k)` and `(j, l)`; the factors `Φ(i, k)` and `Φ(j, l)` vanish unless
    `i = k` and `j = l`, so two of the four sums collapse. `bell_chsh`: don't touch 4×4 matrices; split `chsh` by linearity
    and apply `mes_expect` to each term, which leaves 2×2 sums.
H2. State `hΦ : ∀ i j, (Ket.MES d).vec (i, j) = if i = j then (√d : ℂ)⁻¹ else 0` and
    `hn : (√d : ℂ)⁻¹ * (√d : ℂ)⁻¹ = (d : ℂ)⁻¹` (`← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt`). After the collapse,
    `star` of a real cast is itself (`Complex.star_def`, `map_inv₀`, `Complex.conj_ofReal`); finish with `Finset.mul_sum`,
    `Finset.sum_congr` and `ring`.
H3. `simp only [dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply, Pi.star_apply, hΦ, apply_ite star, star_zero,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Corollary:
    `simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, mes_expect]`, then
    `simp [Fin.sum_univ_two, B₀, B₁, X, Z]`, `field_simp`, `linear_combination (-4) * h2` with `h2 : (√2 : ℂ) ^ 2 = 2`.
-/
