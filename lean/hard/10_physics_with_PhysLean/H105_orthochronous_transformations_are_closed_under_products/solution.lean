/- H105 | Orthochronous transformations are closed under products | 1-1.5 h | IsOrthochronous, matrix entries, Cauchy–Schwarz on Finset sums, nlinarith, physlib
GOAL
  The product of two orthochronous Lorentz transformations (ones that keep the direction of time,
  `Λ⁰₀ ≥ 0`) is orthochronous. Classic proof: `(ΛΛ')⁰₀ = Λ⁰₀Λ'⁰₀ + ∑ᵢ Λ⁰ᵢΛ'ⁱ₀`, then Cauchy–Schwarz.

BANNED: LorentzGroup.isOrthochronous_mul, LorentzGroup.isOrthochronous_mul_iff, LorentzGroup.orthchroRep, LorentzGroup.orthchroMap, LorentzGroup.orthchroMapReal, LorentzGroup.IsOrthochronous.iff_in_orthchroRep_ker, LorentzGroup.isOrthochronous_iff_of_orthchroMap_eq, LorentzGroup.isOrthochronous_on_connected_component, LorentzGroup.isOrthochronous_iff_ge_one, LorentzGroup.one_le_abs_timeComponent, LorentzGroup.not_isOrthochronous_iff_le_neg_one, Lorentz.Velocity.zero_le_minkowskiProduct, LorentzGroup.orthochronoustoVelocity, LorentzGroup.smul_timeComponent_eq_toVector_minkowskiProduct, LorentzGroup.isOrthochronous_iff_toVector_timeComponet_nonneg, LorentzGroup.not_isOrthochronous_iff_toVector_timeComponet_nonpos, LorentzGroup.toVector_mul, LorentzGroup.toVector, exact?, apply?, try?, hint

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Orthochronous.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace H105

/- SKELETON · col_sq   (milestone 1; used in `time_orientation_mul`, step 3, as `col_sq Λ'`)
  1. The (0,0) entry of `Λᵀ η Λ = η` as a hypothesis:
       hc := congrFun (congrFun (… (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)          R1, R2
  2. Evaluate both sides of hc with one `simp [R3, R4, R7, R8] at hc`
     (simp applies R5, R6, R9–R11 by itself):                                R3–R11
       now hc : Λ⁰₀ * Λ⁰₀ + -∑ x, Λˣ₀ * Λˣ₀ = 1   (products, not squares)
  3. Goal: every `^ 2` → `*`, so its sum matches the one in hc:              R12
  4. Close against hc:                                                       R13
-/
-- MILESTONE (optional: change or delete)
theorem col_sq {d : ℕ} (Λ : LorentzGroup d) :
    Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := by
  have hc := congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal,
    Matrix.diagonal_apply] at hc
  simp only [_root_.sq]
  linear_combination hc

/- SKELETON · row_sq   (milestone 2; used in `time_orientation_mul`, step 3, as `row_sq Λ`)
  1. The (0,0) entry of `Λ η Λᵀ = η` (row 0 of Λ, not column 0):             R14, R2
  2.–4. As in `col_sq`:                                                      R3–R11, R12, R13
-/
-- MILESTONE (optional: change or delete)
theorem row_sq {d : ℕ} (Λ : LorentzGroup d) :
    Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) ^ 2 := by
  have hr := congrFun (congrFun (mul_minkowskiMatrix_mul_transpose (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal,
    Matrix.diagonal_apply] at hr
  simp only [_root_.sq]
  linear_combination hr

/- SKELETON · mul_time   (milestone 3; used in `time_orientation_mul`, step 2)
  1. One `simp [R15, R3, R4]`: group product → matrix product, the entry as a
     sum, the sum split into time + space; simp itself does the one-term
     time sum (R5). With `rw` instead: R15, R3, R4, R5 in this order.        R15, R3, R4, R5
-/
-- MILESTONE (optional: change or delete)
theorem mul_time {d : ℕ} (Λ Λ' : LorentzGroup d) :
    (Λ * Λ').1 (Sum.inl 0) (Sum.inl 0)
      = Λ.1 (Sum.inl 0) (Sum.inl 0) * Λ'.1 (Sum.inl 0) (Sum.inl 0)
        + ∑ i, Λ.1 (Sum.inl 0) (Sum.inr i) * Λ'.1 (Sum.inr i) (Sum.inl 0) := by
  simp [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]

/- SKELETON · time_orientation_mul   (prove milestones 1 `col_sq`, 2 `row_sq`, 3 `mul_time` first)
  1. Hypotheses and goal → inequalities about (0,0) entries:                 R16
  2. Expand the goal's entry with milestone 3:                               rw [mul_time]
       goal: 0 ≤ a * b + s   (a = Λ⁰₀, b = Λ'⁰₀, s = ∑ᵢ Λ⁰ᵢ Λ'ⁱ₀)
  3. Collect the facts, all before step 4:
       ha := row_sq Λ    (a² = 1 + A, A = ∑ᵢ (Λ⁰ᵢ)²)                       milestone 2
       hb := col_sq Λ'   (b² = 1 + B, B = ∑ᵢ (Λ'ⁱ₀)²)                      milestone 1
       cs : s ^ 2 ≤ A * B   (Cauchy–Schwarz with `Finset.univ` and two `fun`s)  R17
       hA : 0 ≤ A,  hB : 0 ≤ B                                               R19, R18
  4. Turn a, b, s, A, B into variables, one `generalize … at *` each:        R20
  5. key : s ^ 2 < (a * b) ^ 2                                               R21
  6. Finish, with `0 ≤ a * b` as a hint term:                                R21, R22
-/
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
H1. After `unfold IsOrthochronous at *` and `rw [mul_time]` the goal is `0 ≤ a * b + s` with `a = Λ⁰₀ ≥ 0`,
    `b = Λ'⁰₀ ≥ 0`, `s = ∑ᵢ Λ⁰ᵢ Λ'ⁱ₀`. The milestones give `a² = 1 + A` (row 0 of `Λ`) and `b² = 1 + B`
    (column 0 of `Λ'`), with `A, B` sums of squares.
H2. Cauchy–Schwarz: `s² ≤ A B = (a² - 1)(b² - 1) < a² b²`, so `|s| < a b`. Milestones 1 and 2: the (0,0)
    entry `congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)`, then
    `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc`,
    `simp only [_root_.sq]`, `linear_combination hc`. Milestone 3: one `simp` with
    `lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type`.
H3. `have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Λ.1 (Sum.inl 0) (Sum.inr i))
    (fun i => Λ'.1 (Sum.inr i) (Sum.inl 0))` and `Finset.sum_nonneg (fun i _ => sq_nonneg _)` for `0 ≤ A`, `0 ≤ B`.
    After `generalize … = a at *` (and `b, s, A, B`): `have key : s ^ 2 < (a * b) ^ 2 := by nlinarith`, then
    `nlinarith [mul_nonneg h h']`.
-/
