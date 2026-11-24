/- M179 | Time entry of a Lorentz matrix | 15-20 min | matrix entries, Matrix.mul_apply, Fintype.sum_sum_type, sums of squares, physlib
GOAL
  `|Λ⁰₀| ≥ 1`, and `Λ⁰₀ = 1` means no boost. For a Lorentz matrix `Λ`: (1) `|Λ⁰₀| ≥ 1`; (2) if
  `Λ⁰₀ = 1`, the rest of row 0 and column 0 vanishes (Λ mixes no time with space).
  Here `Λ⁰₀ = Λ.1 (Sum.inl 0) (Sum.inl 0)`.

REFERENCE
  -- `Λ.1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ`; index `Sum.inl 0` is time, `Sum.inr i` is space
  #check @LorentzGroup.transpose_mul_minkowskiMatrix_mul_self  -- Λᵀ * η * Λ = η   (`Λ` implicit: `(Λ := Λ)`)
  #check @LorentzGroup.mul_minkowskiMatrix_mul_transpose       -- Λ * η * Λᵀ = η
  #check minkowskiMatrix.as_diagonal  -- η = diagonal (Sum.elim 1 (-1))   (with `Matrix.diagonal_apply`)
  #check Matrix.mul_apply             -- (M * N) i k = ∑ j, M i j * N j k
  #check Fintype.sum_sum_type         -- ∑ x : α ⊕ β, f x = ∑ a, f (inl a) + ∑ b, f (inr b)
  #check one_le_sq_iff_one_le_abs     -- 1 ≤ a ^ 2 ↔ 1 ≤ |a|
  #check Finset.sum_eq_zero_iff_of_nonneg  -- (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
  example (M N : Matrix (Fin 2) (Fin 2) ℝ) (h : M = N) (i j : Fin 2) : M i j = N i j := congrFun (congrFun h i) j
BANNED: LorentzGroup.one_le_abs_timeComponent, LorentzGroup.isOrthochronous_iff_ge_one, LorentzGroup.not_isOrthochronous_iff_le_neg_one, LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one, LorentzGroup.toVector, Lorentz.Vector.minkowskiProduct_self_le_timeComponent_sq
NOTE: with `open minkowskiMatrix`, bare `sq` means `minkowskiMatrix.sq` (`η * η = 1`), so `simp only [sq]` makes no progress; write `_root_.sq` or `pow_two`.
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M179

-- BEGIN SPEC
theorem time_entry {d : ℕ} (Λ : LorentzGroup d) :
    1 ≤ |Λ.1 (Sum.inl 0) (Sum.inl 0)| ∧
      (Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 → ∀ i : Fin d,
        Λ.1 (Sum.inr i) (Sum.inl 0) = 0 ∧ Λ.1 (Sum.inl 0) (Sum.inr i) = 0) :=
-- END SPEC
  by
    have hc := congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
    have hr := congrFun (congrFun (mul_minkowskiMatrix_mul_transpose (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal,
      Matrix.diagonal_apply] at hc hr
    have col : Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := by
      simp only [_root_.sq]; linear_combination hc
    have row : Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 := by
      simp only [_root_.sq]; linear_combination hr
    have sc : 0 ≤ ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    refine ⟨(one_le_sq_iff_one_le_abs _).mp (by linarith), fun h1 i => ?_⟩
    rw [h1] at col row
    have zc : ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 = 0 := by linarith
    have zr : ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at zc zr
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp (zc i (Finset.mem_univ _)),
      pow_eq_zero_iff two_ne_zero |>.mp (zr i (Finset.mem_univ _))⟩

end M179

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Look at the `(0, 0)` entry of `Λᵀ η Λ = η` and of `Λ η Λᵀ = η`.
H2. They say `(Λ⁰₀)² - ∑ i, (Λⁱ₀)² = 1` (column) and `(Λ⁰₀)² - ∑ i, (Λ⁰ᵢ)² = 1` (row). Sums of squares are
    `≥ 0`, so `(Λ⁰₀)² ≥ 1`; if `Λ⁰₀ = 1` both sums are `0`, hence every term is `0`.
H3. `have hc := congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)`,
    `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc`,
    then `have col : Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := by
      simp only [_root_.sq]; linear_combination hc`.
-/
