/- H077 | Robertson's uncertainty relation | 1-1.5 h | expectation values, Hermitian adjoints, shifted observables, Cauchy–Schwarz, mathlib
GOAL
  For Hermitian `A, B` and a unit vector `ψ`: `|⟨AB − BA⟩|² ≤ 4·Var(A)·Var(B)`, i.e. σ_A σ_B ≥ ½|⟨[A,B]⟩|,
  where `⟨M⟩ = ev ψ M = ⟨ψ|M|ψ⟩` and `Var(M) = var ψ M = Re(⟨M²⟩ − ⟨M⟩²)`.

REFERENCE
  -- `star x ⬝ᵥ y` (= ∑ i, conj (x i) * y i) is ⟨x, y⟩;  `M *ᵥ v` matrix·vector;  `c • M` scalar·matrix;
  -- `Mᴴ` = conjugate transpose;  `WithLp.toLp 2 x : EuclideanSpace ℂ n` wraps a plain vector `x : n → ℂ`
  -- so it gets the ℓ² inner product `⟪·,·⟫` and norm `‖·‖`, and `.ofLp` unwraps it again
  #check Matrix.star_mulVec        -- star (M *ᵥ v) = star v ᵥ* Mᴴ    (`ᵥ*` row vector·matrix)
  #check Matrix.dotProduct_mulVec  -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  #check Matrix.mulVec_mulVec      -- M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v
  #check Matrix.IsHermitian.eq     -- (hA : A.IsHermitian) : Aᴴ = A
  #check Complex.conj_eq_iff_re    -- conj z = z ↔ (z.re : ℂ) = z     (`starRingEnd ℂ` is conj)
  #check norm_inner_le_norm        -- ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖   (Cauchy–Schwarz in an inner-product space)
  #check EuclideanSpace.inner_eq_star_dotProduct  -- ⟪x, y⟫ = y.ofLp ⬝ᵥ star x.ofLp
  #check norm_sq_eq_re_inner       -- ‖x‖ ^ 2 = re ⟪x, x⟫
  example {n : Type} [Fintype n] (x y : n → ℂ) :=     -- the same, for plain vectors wrapped with `toLp`
    norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y)
  -- expand products with scalars: `simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`, then `abel`
BANNED: LinearPMap.commutator_half_sq_le_mul_norm_sq, LinearPMap.inner_im_of_commutator_eq, LinearPMap.inner_norm_sq_eq_re_sq_add_commutator_half_sq, LinearPMap.sub_expectation_commutator_eq_raw, LinearPMap.raw_commutator_eq_of_symmetric, LinearPMap.inner_centered_commutator_of_raw_commutator, LinearPMap.state_uncertainty_squared_of_raw_commutator, LinearPMap.state_uncertainty_squared_of_centered_commutator, LinearPMap.state_uncertainty_squared_with_covariance_of_raw_commutator, LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator, LinearPMap.state_uncertainty_of_raw_commutator, LinearPMap.state_uncertainty_of_centered_commutator
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

-- MILESTONE (optional: change or delete)
/-- shifting by scalars does not change a commutator -/
theorem comm_shift {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (a b : ℂ) :
    (A - a • 1) * (B - b • 1) - (B - b • 1) * (A - a • 1) = A * B - B * A := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul,
    mul_comm b a]
  abel

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
H1. Replace `A, B` by the shifted `A' = A − ⟨A⟩•1`, `B' = B − ⟨B⟩•1` (still Hermitian, since `⟨A⟩` is
    real). The commutator does not change (`comm_shift`), and `Var A = ‖A'ψ‖²` (`var_eq`).
H2. For Hermitian `A', B'`, with `z = ⟨A'ψ, B'ψ⟩`: `⟨ψ, (A'B' − B'A')ψ⟩ = z − conj z` (move each operator
    across with `herm_move`; `conj ⟨x, y⟩ = ⟨y, x⟩` by `simp [dotProduct, mul_comm]`). Then
    `‖z − conj z‖² = 4 (Im z)² ≤ 4‖z‖²`, and Cauchy–Schwarz bounds `‖z‖²` by `‖A'ψ‖²‖B'ψ‖²`.
H3. `herm_move`: `rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]`. `⟨A⟩` real: show
    `conj (ev ψ A) = ev ψ A`, then `Complex.conj_eq_iff_re.mp`. Main proof:
    `rw [← comm_shift A B (ev ψ A).re (ev ψ B).re]`, rewrite the commutator to `z − conj z`, `var_eq` twice,
    then `‖z − conj z‖² ≤ 4‖z‖²` (`Complex.sq_norm`, `Complex.normSq_apply`, `nlinarith`) and `cauchy_schwarz`.
-/
