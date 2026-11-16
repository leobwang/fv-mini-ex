/- H105 | Orthochronous transformations are closed under products | 1-1.5 h | IsOrthochronous, matrix entries, Cauchy–Schwarz on Finset sums, nlinarith, physlib
GOAL
  The product of two orthochronous Lorentz transformations (ones that keep the direction of time,
  `Λ⁰₀ ≥ 0`) is orthochronous. Classic proof: `(ΛΛ')⁰₀ = Λ⁰₀Λ'⁰₀ + ∑ᵢ Λ⁰ᵢΛ'ⁱ₀`, then Cauchy–Schwarz.

REFERENCE
  -- `IsOrthochronous Λ` is `0 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0)` (`unfold IsOrthochronous`); index `Sum.inl 0` = time, `Sum.inr i` = space
  -- so `Λ⁰₀ = Λ.1 (Sum.inl 0) (Sum.inl 0)`, `Λ⁰ᵢ = Λ.1 (Sum.inl 0) (Sum.inr i)` (row 0), `Λⁱ₀ = Λ.1 (Sum.inr i) (Sum.inl 0)` (column 0)
  -- `η` = Minkowski metric diag(1, -1, …, -1); Lorentz means `Λᵀ η Λ = η`. Their `(0,0)` entries give Λ⁰₀² = 1 + ∑ (as in M179)
  #check @LorentzGroup.transpose_mul_minkowskiMatrix_mul_self  -- Λᵀ * η * Λ = η   (`Λ` implicit: `(Λ := Λ)`)
  #check @LorentzGroup.mul_minkowskiMatrix_mul_transpose       -- Λ * η * Λᵀ = η
  #check minkowskiMatrix.as_diagonal     -- η = diagonal (Sum.elim 1 (-1))   (with `Matrix.diagonal_apply`)
  #check lorentzGroupIsGroup_mul_coe     -- ((A * B : LorentzGroup d) : Matrix ..) = A.1 * B.1
  #check Matrix.mul_apply                -- (M * N) i k = ∑ j, M i j * N j k   (and `Fintype.sum_sum_type`)
  #check Finset.sum_mul_sq_le_sq_mul_sq  -- (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
  #check Finset.sum_nonneg               -- (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i
  -- `generalize e = a at *` replaces a big subterm `e` by a variable, so `nlinarith` sees plain atoms
BANNED: LorentzGroup.isOrthochronous_mul, LorentzGroup.isOrthochronous_mul_iff, LorentzGroup.orthchroRep, LorentzGroup.orthchroMap, LorentzGroup.orthchroMapReal, LorentzGroup.IsOrthochronous.iff_in_orthchroRep_ker, LorentzGroup.isOrthochronous_iff_of_orthchroMap_eq, LorentzGroup.isOrthochronous_on_connected_component, LorentzGroup.isOrthochronous_iff_ge_one, LorentzGroup.one_le_abs_timeComponent, LorentzGroup.not_isOrthochronous_iff_le_neg_one, Lorentz.Velocity.zero_le_minkowskiProduct, LorentzGroup.orthochronoustoVelocity, LorentzGroup.smul_timeComponent_eq_toVector_minkowskiProduct, LorentzGroup.isOrthochronous_iff_toVector_timeComponet_nonneg, LorentzGroup.not_isOrthochronous_iff_toVector_timeComponet_nonpos, LorentzGroup.toVector_mul, LorentzGroup.toVector, exact?, apply?, try?, hint
NOTE: with `open minkowskiMatrix`, plain `sq` is ambiguous (`minkowskiMatrix.sq`); write `_root_.sq` or `pow_two`.
-/
import Physlib.Relativity.LorentzGroup.Orthochronous.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace H105

-- MILESTONE (optional: change or delete)
theorem col_sq {d : ℕ} (Λ : LorentzGroup d) :
    Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := by
  have hc := congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal,
    Matrix.diagonal_apply] at hc
  simp only [_root_.sq]
  linear_combination hc

-- MILESTONE (optional: change or delete)
theorem row_sq {d : ℕ} (Λ : LorentzGroup d) :
    Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 := by
  have hr := congrFun (congrFun (mul_minkowskiMatrix_mul_transpose (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal,
    Matrix.diagonal_apply] at hr
  simp only [_root_.sq]
  linear_combination hr

-- MILESTONE (optional: change or delete)
theorem mul_time {d : ℕ} (Λ Λ' : LorentzGroup d) :
    (Λ * Λ').1 (Sum.inl 0) (Sum.inl 0)
      = Λ.1 (Sum.inl 0) (Sum.inl 0) * Λ'.1 (Sum.inl 0) (Sum.inl 0)
        + ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) * Λ'.1 (Sum.inr i) (Sum.inl 0) := by
  simp [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]

-- BEGIN SPEC
theorem time_orientation_mul {d : ℕ} {Λ Λ' : LorentzGroup d}
    (h : IsOrthochronous Λ) (h' : IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') :=
-- END SPEC
  by
    unfold IsOrthochronous at *
    rw [mul_time]
    have ha := row_sq Λ
    have hb := col_sq Λ'
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Λ.1 (Sum.inl 0) (Sum.inr i)) (fun i => Λ'.1 (Sum.inr i) (Sum.inl 0))
    have hA : 0 ≤ ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hB : 0 ≤ ∑ i, Λ'.1 (Sum.inr i) (Sum.inl 0) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    generalize Λ.1 (Sum.inl 0) (Sum.inl 0) = a at *
    generalize Λ'.1 (Sum.inl 0) (Sum.inl 0) = b at *
    generalize ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) * Λ'.1 (Sum.inr i) (Sum.inl 0) = s at *
    generalize ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 = A at *
    generalize ∑ i, Λ'.1 (Sum.inr i) (Sum.inl 0) ^ 2 = B at *
    -- WHY: a² = 1 + A, b² = 1 + B and s² ≤ A B give s² ≤ (a² - 1)(b² - 1) < (a b)², so |s| < a b.
    have key : s ^ 2 < (a * b) ^ 2 := by nlinarith
    nlinarith [mul_nonneg h h']

end H105

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `a = Λ⁰₀ ≥ 0`, `b = Λ'⁰₀ ≥ 0` and `s = ∑ᵢ Λ⁰ᵢ Λ'ⁱ₀`. The goal is `0 ≤ a * b + s`. Use row 0 of `Λ`
    and column 0 of `Λ'`.
H2. `row_sq Λ`: `a² = 1 + A`, `col_sq Λ'`: `b² = 1 + B` (sums of squares `A, B ≥ 0`), so `a, b ≥ 1`.
    Cauchy–Schwarz: `s² ≤ A B = (a² - 1)(b² - 1) < a² b²`, hence `|s| < a b`. The milestones are `(0,0)`
    entries: `congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)`, then
    `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc`.
H3. Cauchy–Schwarz as a hypothesis: `have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Λ.1 (Sum.inl 0) (Sum.inr i)) (fun i => Λ'.1 (Sum.inr i) (Sum.inl 0))`. The intermediate target is
    `s ^ 2 < (a * b) ^ 2`, once `a, b, s, A, B` are atoms for `nlinarith`.
-/
