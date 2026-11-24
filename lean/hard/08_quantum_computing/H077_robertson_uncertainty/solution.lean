/- H077 | Robertson's uncertainty relation | 1-1.5 h | expectation values, Hermitian adjoints, shifted observables, Cauchy–Schwarz, mathlib
GOAL
  For Hermitian `A, B` and a unit vector `ψ`: `|⟨AB − BA⟩|² ≤ 4·Var(A)·Var(B)`, i.e. σ_A σ_B ≥ ½|⟨[A,B]⟩|,
  where `⟨M⟩ = ev ψ M = ⟨ψ|M|ψ⟩` and `Var(M) = var ψ M = Re(⟨M²⟩ − ⟨M⟩²)`.
BANNED: LinearPMap.commutator_half_sq_le_mul_norm_sq, LinearPMap.inner_im_of_commutator_eq, LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq, LinearPMap.sub_expectation_commutator_eq_raw, LinearPMap.raw_commutator_eq_of_symmetric, LinearPMap.inner_centered_commutator_of_raw_commutator, LinearPMap.state_uncertainty_squared_of_raw_commutator, LinearPMap.state_uncertainty_squared_of_centered_commutator, LinearPMap.state_uncertainty_squared_with_covariance_of_raw_commutator, LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator, LinearPMap.state_uncertainty_of_raw_commutator, LinearPMap.state_uncertainty_of_centered_commutator

GUIDE
  Entries R1–R41: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix

namespace H077

-- BEGIN SPEC
/-- expectation value `⟨ψ|M|ψ⟩` -/
def ev {n : Type} [Fintype n] (ψ : n → ℂ) (M : Matrix n n ℂ) : ℂ := star ψ ⬝ᵥ (M *ᵥ ψ)

/-- variance `⟨M²⟩ − ⟨M⟩²` (real for Hermitian `M`; we take the real part) -/
def var {n : Type} [Fintype n] (ψ : n → ℂ) (M : Matrix n n ℂ) : ℝ := (ev ψ (M * M) - ev ψ M ^ 2).re
-- END SPEC

/- SKELETON · herm_move   (milestone 1: ⟨x, Ay⟩ = ⟨Ax, y⟩; used in var_eq, ev_real and comm_ev)
  One `rw [...]` with three lemmas; the goal then closes by `rfl` on its own.
  1. Right side `star (A *ᵥ x) ⬝ᵥ y`: star of a matrix·vector → row vector · Aᴴ      R1
  2. `Aᴴ` → `A` (A is Hermitian)                                                   R2
  3. Left side `star x ⬝ᵥ A *ᵥ y` → `star x ᵥ* A ⬝ᵥ y`; both sides now agree        R3
-/
-- MILESTONE (optional: change or delete)
/-- a Hermitian operator moves across the inner product: `⟨x, A y⟩ = ⟨A x, y⟩` -/
theorem herm_move {n : Type} [Fintype n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (x y : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]

/-- `⟨A⟩` is real for Hermitian `A` -/
theorem ev_real {n : Type} [Fintype n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (ψ : n → ℂ) :
    ((ev ψ A).re : ℂ) = ev ψ A := by
  apply Complex.conj_eq_iff_re.mp
  unfold ev
  rw [show starRingEnd ℂ (star ψ ⬝ᵥ (A *ᵥ ψ)) = star (A *ᵥ ψ) ⬝ᵥ ψ by simp [dotProduct, mul_comm],
    herm_move A hA]

theorem shift_herm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (ψ : n → ℂ) : (A - ((ev ψ A).re : ℂ) • 1).IsHermitian :=
  hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])

/- SKELETON · comm_shift   (milestone 2: used in robertson, step 1)
  1. Expand both products in ONE `simp only [...]` holding all of:
       distribute `*` over `-`                                                     R4, R5
       pull a scalar out of a product                                              R6, R7
       drop the identity `1`                                                       R8
       distribute a scalar over `-`; merge two scalars                             R9, R10
       write `b * a` as `a * b`, so the two `(a * b) • 1` terms match              R11
  2. What is left holds in every commutative additive group                        R12
-/
-- MILESTONE (optional: change or delete)
/-- shifting by scalars does not change a commutator -/
theorem comm_shift {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (a b : ℂ) :
    (A - a • 1) * (B - b • 1) - (B - b • 1) * (A - a • 1) = A * B - B * A := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul,
    mul_comm b a]
  abel

/- SKELETON · var_eq   (milestone 3: Var A = ‖(A − ⟨A⟩•1)ψ‖²; used twice in robertson, step 2)
  Prove two facts FIRST, as lemmas above `var_eq` (robertson needs F2 again).
  `conj z` below is the complex conjugate; in Lean write it `starRingEnd ℂ z` (`conj` is not open here).
    F1 `ev_real`:  ((ev ψ A).re : ℂ) = ev ψ A           (⟨A⟩ is real; A Hermitian)
         goal → `conj (ev ψ A) = ev ψ A`                                           R13
         unfold `ev`                                                               R14
         rw with `conj (star ψ ⬝ᵥ A *ᵥ ψ) = star (A *ᵥ ψ) ⬝ᵥ ψ`, proved on the spot
           by `simp` with `dotProduct` and `mul_comm` (R15, R16)                   R17
         finish with milestone 1                                                   rw [herm_move A hA]
    F2 `shift_herm`:  (A - ((ev ψ A).re : ℂ) • 1).IsHermitian
         difference of Hermitian matrices                                          R18
         the scalar part `↑r • 1`: unfold, pull out the scalar, simp               R19, R20, R21
  1. Right side `star (A'ψ) ⬝ᵥ A'ψ` (A' the shifted matrix): move the left A'
     across with milestone 1 (it needs F2), then merge the two products           rw [← herm_move _ F2], R22
  2. `have h := F1 …`; unfold `var`                                                R14
  3. ONE `simp only [...]`: expand `A' * A'`, then `(…) *ᵥ ψ` and `⬝ᵥ`, and use
     `hψ` (ψ is a unit vector)                                                     R4–R8, R23–R27, hψ
  4. Unfold `ev` in `h` and in the goal, then put the real part in: rw [← h]       R14
  5. Real-part arithmetic                                                          R29 (does R28)
-/
-- MILESTONE (optional: change or delete)
/-- the variance is the squared length of `(A − ⟨A⟩)ψ` -/
theorem var_eq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    var ψ A = (star ((A - ((ev ψ A).re : ℂ) • 1) *ᵥ ψ) ⬝ᵥ ((A - ((ev ψ A).re : ℂ) • 1) *ᵥ ψ)).re := by
  rw [← herm_move _ (shift_herm A hA ψ), Matrix.mulVec_mulVec]
  have h := ev_real A hA ψ
  unfold var
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, hψ]
  unfold ev at h ⊢
  rw [← h]
  simp [sq]

/- SKELETON · cauchy_schwarz   (milestone 4: used in robertson, step 3)
  Plain vectors `n → ℂ` carry no ℓ² norm; wrap them as `WithLp.toLp 2 x : EuclideanSpace ℂ n`.
  1. Cauchy–Schwarz for the wrapped vectors, as `h`                                R30
  2. Fact hi: their inner product is `star x ⬝ᵥ y`:
       rewrite `inner`, then `simp [dotProduct_comm]`                              R31, R32, R33
  3. Fact hn: ∀ z, ‖toLp z‖ ^ 2 = (star z ⬝ᵥ z).re:
       intro z; rewrite `‖·‖ ^ 2`, then `inner`, then `simp [dotProduct_comm]`     R34, R31, R32, R33
  4. rw [hi] at h
  5. calc: square both sides of `h` (`norm_nonneg` gives `0 ≤ ‖…‖`), then split
     the square of the product and rewrite with hn twice                          R35, R36, R37, rw [hn]
-/
-- MILESTONE (optional: change or delete)
theorem cauchy_schwarz {n : Type} [Fintype n] (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y)
  have hi : inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]
  have hn : ∀ z : n → ℂ, ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ ^ 2 = (star z ⬝ᵥ z).re := by
    intro z
    rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]
  rw [hi] at h
  calc ‖star x ⬝ᵥ y‖ ^ 2
      ≤ (‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ n)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [mul_pow, hn, hn]

theorem conj_dot {n : Type} [Fintype n] (x y : n → ℂ) : starRingEnd ℂ (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, mul_comm]

/-- `⟨ψ, [A, B] ψ⟩ = z − conj z` with `z = ⟨Aψ, Bψ⟩` -/
theorem comm_ev {n : Type} [Fintype n] (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (ψ : n → ℂ) :
    ev ψ (A * B - B * A) = star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) - starRingEnd ℂ (star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ)) := by
  unfold ev
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    herm_move A hA ψ, herm_move B hB ψ, conj_dot]

theorem norm_sub_conj (z : ℂ) : ‖z - starRingEnd ℂ z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith [sq_nonneg z.re]

/- SKELETON · robertson
  Prove FIRST: milestones 1–4, F1 and F2 (var_eq's skeleton), and three more lemmas
  (`conj z` is written `starRingEnd ℂ z` in Lean):
    F3 `conj_dot`:  conj (star x ⬝ᵥ y) = star y ⬝ᵥ x               simp with R15, R16 and `mul_comm`
    F4 `comm_ev`:  for Hermitian A, B,
         ev ψ (A * B - B * A) = z - conj z   with   z = star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ)
         unfold `ev`; split `(AB − BA) *ᵥ ψ` and `⬝ᵥ (… - …)`; split each
         product `(A * B) *ᵥ ψ` (right to left)                                    R14, R23, R26, R22 twice
         move A, then B across (milestone 1), then F3                              rw [herm_move …, F3]
    F5 `norm_sub_conj`:  ‖z - conj z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2            R38, R39, R40, R41 (hint `sq_nonneg z.re`)
  1. Shift: rewrite the commutator BACKWARDS with milestone 2 at a = ⟨A⟩.re, b = ⟨B⟩.re
                                                       rw [← comm_shift A B (ev ψ A).re (ev ψ B).re, …]
  2. In the same `rw`: F4 for the shifted matrices (Hermitian by F2), then
     milestone 3 for A and for B                                    F4 _ _ (F2 …) (F2 …), var_eq …, var_eq …
  3. calc: `_ ≤ 4 * ‖z‖ ^ 2` by F5, then `_ ≤ _` from milestone 4 at A'ψ, B'ψ     R35, R41
-/
-- BEGIN SPEC
theorem robertson {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    ‖ev ψ (A * B - B * A)‖ ^ 2 ≤ 4 * var ψ A * var ψ B :=
-- END SPEC
  by
    rw [← comm_shift A B (ev ψ A).re (ev ψ B).re,
      comm_ev _ _ (shift_herm A hA ψ) (shift_herm B hB ψ), var_eq A hA ψ hψ, var_eq B hB ψ hψ]
    calc _ ≤ 4 * ‖star ((A - ((ev ψ A).re : ℂ) • 1) *ᵥ ψ) ⬝ᵥ ((B - ((ev ψ B).re : ℂ) • 1) *ᵥ ψ)‖ ^ 2 :=
          norm_sub_conj _
      _ ≤ _ := by
          have := cauchy_schwarz ((A - ((ev ψ A).re : ℂ) • 1) *ᵥ ψ) ((B - ((ev ψ B).re : ℂ) • 1) *ᵥ ψ)
          nlinarith

end H077

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Shift: `A' = A − ⟨A⟩•1`, `B' = B − ⟨B⟩•1` with `⟨A⟩ = (ev ψ A).re`. They are Hermitian because
    `⟨A⟩` is real (F1, F2), the commutator does not change (`comm_shift`), and
    `Var A = (star (A'ψ) ⬝ᵥ A'ψ).re` (`var_eq`). The rest is about one number `z = star (A'ψ) ⬝ᵥ (B'ψ)`.
H2. Three facts: `⟨ψ, (A'B' − B'A')ψ⟩ = z − conj z` (F4, rewritten in: `herm_move` for A' and B', then
    F3 `conj (star x ⬝ᵥ y) = star y ⬝ᵥ x`); then a two-step `calc`: `‖z − conj z‖² = 4 (Im z)² ≤ 4‖z‖²`
    (F5, R38–R41) and Cauchy–Schwarz `‖z‖² ≤ ‖A'ψ‖² ‖B'ψ‖²` (`cauchy_schwarz` via `EuclideanSpace`, R30–R37).
H3. `herm_move`: `rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]`. F3: `simp [dotProduct, mul_comm]`.
    Main proof: `rw [← comm_shift A B (ev ψ A).re (ev ψ B).re, comm_ev _ _ (shift_herm A hA ψ)
    (shift_herm B hB ψ), var_eq A hA ψ hψ, var_eq B hB ψ hψ]`, then
    `calc _ ≤ 4 * ‖z‖ ^ 2 := norm_sub_conj _` and `_ ≤ _ := by have := cauchy_schwarz (A'ψ) (B'ψ); nlinarith`.
-/
