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
  sorry

-- MILESTONE (optional: change or delete)
/-- an isometry `W` (`Wᴴ W = 1`) has expectation values of modulus at most 1 -/
theorem unitary_expect {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (hW : Wᴴ * W = 1)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : ‖star ψ ⬝ᵥ (W *ᵥ ψ)‖ ≤ 1 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- the CHSH operator squared (M142 on matrices) -/
theorem chsh_sq_matrix {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- for Hermitian `C`: `⟨C⟩² ≤ ⟨C²⟩` -/
theorem expect_sq_le {n : Type} [Fintype n] [DecidableEq n] (C : Matrix n n ℂ) (hC : C.IsHermitian)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ (C *ᵥ ψ)).re ^ 2 ≤ (star ψ ⬝ᵥ ((C * C) *ᵥ ψ)).re := by
  sorry

-- BEGIN SPEC
theorem tsirelson {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian) (hB₀ : B₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ ((A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ ψ)).re ≤ 2 * Real.sqrt 2 :=
-- END SPEC
  sorry

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
