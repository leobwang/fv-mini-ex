/- M179 | Time entry of a Lorentz matrix | 15-20 min | matrix entries, Matrix.mul_apply, Fintype.sum_sum_type, sums of squares, physlib
GOAL
  `|Λ⁰₀| ≥ 1`, and `Λ⁰₀ = 1` means no boost. For a Lorentz matrix `Λ`: (1) `|Λ⁰₀| ≥ 1`; (2) if
  `Λ⁰₀ = 1`, the rest of row 0 and column 0 vanishes (Λ mixes no time with space).
  Here `Λ⁰₀ = Λ.1 (Sum.inl 0) (Sum.inl 0)`.
BANNED: LorentzGroup.one_le_abs_timeComponent, LorentzGroup.isOrthochronous_iff_ge_one, LorentzGroup.not_isOrthochronous_iff_le_neg_one, LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one, LorentzGroup.toVector, Lorentz.Vector.minkowskiProduct_self_le_timeComponent_sq

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Basic

open LorentzGroup Matrix minkowskiMatrix

namespace M179

/- SKELETON · time_entry   (Λ⁰₀ = Λ.1 (Sum.inl 0) (Sum.inl 0), Λⁱ₀ = Λ.1 (Sum.inr i) (Sum.inl 0), Λ⁰ᵢ the transpose)
  1. The (0, 0) entries of both defining identities, as hypotheses:
       hc from Λᵀ * η * Λ = η (column 0)                                    R1 with R2
       hr from Λ * η * Λᵀ = η (row 0)                                       R1 with R3
  2. Evaluate both entries with ONE `simp [...] at hc hr`, naming R4, R6, R7, R9
     (it applies R5, R8, R10, R11 itself); it leaves `a * a` and `-∑ x, …`:  R4–R11
  3. Restate them with squares:                                             R12 → R13
       col : Λ⁰₀ ^ 2 = 1 + ∑ i, Λⁱ₀ ^ 2
       row : Λ⁰₀ ^ 2 = 1 + ∑ i, Λ⁰ᵢ ^ 2
  4. sc : 0 ≤ ∑ i, Λⁱ₀ ^ 2                                                   R14, R15
  5. Split: `1 ≤ |Λ⁰₀|`, and `h1 : Λ⁰₀ = 1, i : Fin d ⊢ … ∧ …`              R16
  6. First goal: `|·|` → square, then arithmetic from col, sc               R17, R18
  7. Second goal:
       substitute h1 into col and row                                       R19
       zc, zr : the two sums of squares are 0                               R18
       every term of each sum is 0                                          R20 (argument: R15)
       the i-th term, without its square, for both conjuncts               R21, R22
-/
-- BEGIN SPEC
theorem time_entry {d : ℕ} (Λ : LorentzGroup d) :
    1 ≤ |Λ.1 (Sum.inl 0) (Sum.inl 0)| ∧
      (Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 → ∀ i : Fin d,
        Λ.1 (Sum.inr i) (Sum.inl 0) = 0 ∧ Λ.1 (Sum.inl 0) (Sum.inr i) = 0) :=
-- END SPEC
  sorry

end M179

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Look at the `(0, 0)` entry of `Λᵀ η Λ = η` and of `Λ η Λᵀ = η` (R1 with R2, R3): one is about
    column 0 of `Λ`, the other about row 0.
H2. After `simp` (R4–R11) they say, in product form, `Λ⁰₀ * Λ⁰₀ + -∑ x, Λˣ₀ * Λˣ₀ = 1` (column) and
    `Λ⁰₀ * Λ⁰₀ + -∑ x, Λ⁰ₓ * Λ⁰ₓ = 1` (row); restate them with `^ 2` (R12, R13). Sums of squares
    are `≥ 0` (R14, R15), so `(Λ⁰₀)² ≥ 1` and `|Λ⁰₀| ≥ 1` (R17, R18); if `Λ⁰₀ = 1` both sums are `0`
    (R19, R18), hence every term is `0` (R20, R21, R22).
H3. `have hc := congrFun (congrFun (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)) (Sum.inl 0)) (Sum.inl 0)`,
    `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc`,
    then `have col : Λ.1 (Sum.inl 0) (Sum.inl 0) ^ 2 = 1 + ∑ i, Λ.1 (Sum.inr i) (Sum.inl 0) ^ 2 := by
      simp only [_root_.sq]; linear_combination hc`.
-/
