/- H081 | Tsirelson's bound | 1.5-2 h | CHSH, Cauchy–Schwarz, Hermitian involutions, EuclideanSpace, mathlib
GOAL
  Alice measures `A₀` or `A₁`, Bob `B₀` or `B₁`: Hermitian matrices with square 1 (±1-valued observables),
  each of Alice's commuting with each of Bob's. For every unit vector `ψ`, the CHSH value
  `⟨ψ| A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ |ψ⟩` is at most `2√2` (local hidden variables only reach 2).

REFERENCE
  -- `star x ⬝ᵥ y` (= ∑ i, conj (x i) * y i) is ⟨x, y⟩;  `M *ᵥ v` matrix · vector;  `Mᴴ` conjugate transpose
  #check Matrix.star_mulVec        -- star (M *ᵥ v) = star v ᵥ* Mᴴ    (`ᵥ*` row vector · matrix)
  #check Matrix.dotProduct_mulVec  -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  #check Matrix.conjTranspose_mul  -- (M * N)ᴴ = Nᴴ * Mᴴ
  #check Matrix.IsHermitian.eq     -- (hA : A.IsHermitian) : Aᴴ = A
  #check norm_inner_le_norm        -- ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖   (Cauchy–Schwarz in an inner-product space)
  #check EuclideanSpace.inner_eq_star_dotProduct  -- ⟪x, y⟫ = y.ofLp ⬝ᵥ star x.ofLp
  #check norm_sq_eq_re_inner (𝕜 := ℂ)  -- ‖x‖ ^ 2 = re ⟪x, x⟫  (name 𝕜 explicitly, or `rw` gets stuck)
  example {n : Type} [Fintype n] (x : n → ℂ) : EuclideanSpace ℂ n := WithLp.toLp 2 x  -- see `x` in ℓ²
  #check Complex.abs_re_le_norm    -- |z.re| ≤ ‖z‖
  -- `ring` fails on matrices: expand with `simp only [add_mul, mul_add, mul_assoc, ...]` + hypotheses; `noncomm_ring`
  -- cannot match the matrix numeral `4` with `4 • 1`, so spell it as `1 + 1 + 1 + 1` and close with `abel`:
  example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : A + 2 = 1 + A + 1 := by rw [show (2 : Matrix n n ℂ) = 1 + 1 by norm_num]; abel
-/
import Mathlib

open Matrix

namespace H081

-- MILESTONE (optional: change or delete)
/-- Cauchy–Schwarz for `star x ⬝ᵥ y` (same as H077's milestone) -/
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

-- MILESTONE (optional: change or delete)
/-- an isometry `W` (`Wᴴ W = 1`) has expectation values of modulus at most 1 -/
theorem unitary_expect {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (hW : Wᴴ * W = 1)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : ‖star ψ ⬝ᵥ (W *ᵥ ψ)‖ ≤ 1 := by
  have h := cauchy_schwarz ψ (W *ᵥ ψ)
  have h2 : star (W *ᵥ ψ) ⬝ᵥ (W *ᵥ ψ) = 1 := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hW, vecMul_one, hψ]
  rw [hψ, h2, Complex.one_re, one_mul] at h
  nlinarith [norm_nonneg (star ψ ⬝ᵥ (W *ᵥ ψ))]

-- MILESTONE (optional: change or delete)
/-- the CHSH operator squared (M142 on matrices) -/
theorem chsh_sq_matrix {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have sw : ∀ {a b : Matrix n n ℂ}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x) := by
    intro a b h x; rw [← mul_assoc, ← h, mul_assoc]
  have sq1 : ∀ {a : Matrix n n ℂ}, a * a = 1 → ∀ x, a * (a * x) = x := by
    intro a h x; rw [← mul_assoc, h, one_mul]
  simp only [add_mul, mul_add, sub_mul, mul_sub, mul_assoc, sw c₀₀, sw c₀₁, sw c₁₀, sw c₁₁,
    sq1 sA₀, sq1 sA₁, sB₀, sB₁]
  simp only [mul_one]
  rw [show (4 : Matrix n n ℂ) = 1 + 1 + 1 + 1 by norm_num]
  abel

-- MILESTONE (optional: change or delete)
/-- for Hermitian `C`: `⟨C⟩² ≤ ⟨C²⟩` -/
theorem expect_sq_le {n : Type} [Fintype n] [DecidableEq n] (C : Matrix n n ℂ) (hC : C.IsHermitian)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ (C *ᵥ ψ)).re ^ 2 ≤ (star ψ ⬝ᵥ ((C * C) *ᵥ ψ)).re := by
  have h := cauchy_schwarz ψ (C *ᵥ ψ)
  have e : star (C *ᵥ ψ) ⬝ᵥ (C *ᵥ ψ) = star ψ ⬝ᵥ ((C * C) *ᵥ ψ) := by
    rw [star_mulVec, hC.eq, ← dotProduct_mulVec, mulVec_mulVec]
  rw [hψ, e, Complex.one_re, one_mul] at h
  have hre := Complex.abs_re_le_norm (star ψ ⬝ᵥ (C *ᵥ ψ))
  nlinarith [abs_nonneg (star ψ ⬝ᵥ (C *ᵥ ψ)).re, sq_abs (star ψ ⬝ᵥ (C *ᵥ ψ)).re]

-- BEGIN SPEC
theorem tsirelson {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian) (hB₀ : B₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ ((A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ ψ)).re ≤ 2 * Real.sqrt 2 :=
-- END SPEC
  by
    set C := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ with hCdef
    have hC : C.IsHermitian := by
      simp only [hCdef, IsHermitian, conjTranspose_add, conjTranspose_sub, conjTranspose_mul,
        hA₀.eq, hA₁.eq, hB₀.eq, hB₁.eq, c₀₀, c₀₁, c₁₀, c₁₁]
    -- products of Hermitian involutions are unitary
    have u : ∀ {P : Matrix n n ℂ}, P.IsHermitian → P * P = 1 → Pᴴ * P = 1 := by
      intro P hP sP; rw [hP.eq, sP]
    have um : ∀ {P Q : Matrix n n ℂ}, Pᴴ * P = 1 → Qᴴ * Q = 1 → (P * Q)ᴴ * (P * Q) = 1 := by
      intro P Q hP hQ
      rw [conjTranspose_mul, mul_assoc, ← mul_assoc Pᴴ, hP, one_mul, hQ]
    have b : ∀ {P Q R S : Matrix n n ℂ}, P.IsHermitian → P * P = 1 → Q.IsHermitian → Q * Q = 1 →
        R.IsHermitian → R * R = 1 → S.IsHermitian → S * S = 1 →
        ‖star ψ ⬝ᵥ ((P * Q * (R * S)) *ᵥ ψ)‖ ≤ 1 := by
      intro P Q R S hP sP hQ sQ hR sR hS sS
      exact unitary_expect _ (um (um (u hP sP) (u hQ sQ)) (um (u hR sR) (u hS sS))) ψ hψ
    have e : star ψ ⬝ᵥ ((C * C) *ᵥ ψ) = 4 - (star ψ ⬝ᵥ ((A₀ * A₁ * (B₀ * B₁)) *ᵥ ψ)
        - star ψ ⬝ᵥ ((A₀ * A₁ * (B₁ * B₀)) *ᵥ ψ) - star ψ ⬝ᵥ ((A₁ * A₀ * (B₀ * B₁)) *ᵥ ψ)
        + star ψ ⬝ᵥ ((A₁ * A₀ * (B₁ * B₀)) *ᵥ ψ)) := by
      rw [hCdef, chsh_sq_matrix A₀ A₁ B₀ B₁ sA₀ sA₁ sB₀ sB₁ c₀₀ c₀₁ c₁₀ c₁₁]
      simp [sub_mul, mul_sub, sub_mulVec, dotProduct_sub, hψ]
      ring
    have h1 := Complex.abs_re_le_norm (star ψ ⬝ᵥ ((A₀ * A₁ * (B₀ * B₁)) *ᵥ ψ))
    have h2 := Complex.abs_re_le_norm (star ψ ⬝ᵥ ((A₀ * A₁ * (B₁ * B₀)) *ᵥ ψ))
    have h3 := Complex.abs_re_le_norm (star ψ ⬝ᵥ ((A₁ * A₀ * (B₀ * B₁)) *ᵥ ψ))
    have h4 := Complex.abs_re_le_norm (star ψ ⬝ᵥ ((A₁ * A₀ * (B₁ * B₀)) *ᵥ ψ))
    have b1 := b hA₀ sA₀ hA₁ sA₁ hB₀ sB₀ hB₁ sB₁
    have b2 := b hA₀ sA₀ hA₁ sA₁ hB₁ sB₁ hB₀ sB₀
    have b3 := b hA₁ sA₁ hA₀ sA₀ hB₀ sB₀ hB₁ sB₁
    have b4 := b hA₁ sA₁ hA₀ sA₀ hB₁ sB₁ hB₀ sB₀
    have h8 : (star ψ ⬝ᵥ (C *ᵥ ψ)).re ^ 2 ≤ 8 := by
      refine (expect_sq_le C hC ψ hψ).trans ?_
      rw [e]
      simp only [Complex.sub_re, Complex.add_re]
      norm_num
      rw [abs_le] at h1 h2 h3 h4
      linarith
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

end H081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Let `C` be the CHSH operator. It is Hermitian, so `⟨C⟩² ≤ ⟨C²⟩` (Cauchy–Schwarz). By `chsh_sq_matrix`,
    `C² = 4 − [A₀,A₁][B₀,B₁]`; the commutator product expands into four products like `A₀A₁B₀B₁`, and each
    product of Hermitian involutions is unitary, so each has expectation of modulus ≤ 1. Hence `⟨C²⟩ ≤ 8`.
H2. `cauchy_schwarz`: apply `norm_inner_le_norm` to `WithLp.toLp 2 x` and `WithLp.toLp 2 y`, rewrite the inner
    product to `star x ⬝ᵥ y` and each `‖·‖²` to `(star z ⬝ᵥ z).re`, then square (`pow_le_pow_left₀`).
    `chsh_sq_matrix`: helpers `sw : a * b = b * a → ∀ x, b * (a * x) = a * (b * x)` and
    `sq1 : a * a = 1 → ∀ x, a * (a * x) = x`; feed them (with `mul_assoc`) to `simp only`, then
    `simp only [mul_one]`, `rw [show (4 : Matrix n n ℂ) = 1 + 1 + 1 + 1 by norm_num]`, `abel`.
H3. `expect_sq_le`: `cauchy_schwarz ψ (C *ᵥ ψ)`, and `star (C *ᵥ ψ) ⬝ᵥ (C *ᵥ ψ) = star ψ ⬝ᵥ ((C * C) *ᵥ ψ)`
    by `rw [star_mulVec, hC.eq, ← dotProduct_mulVec, mulVec_mulVec]`. Unitarity: `Pᴴ P = 1` for a Hermitian
    involution and `(P Q)ᴴ (P Q) = 1` from `conjTranspose_mul`. Linearity: `simp [sub_mul, mul_sub, sub_mulVec,
    dotProduct_sub, hψ]` (`simp` knows `(4 : Matrix _ _ ℂ) *ᵥ ψ`). End: from `x ^ 2 ≤ 8` get `x ≤ 2√2` with
    `nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]`.
-/
