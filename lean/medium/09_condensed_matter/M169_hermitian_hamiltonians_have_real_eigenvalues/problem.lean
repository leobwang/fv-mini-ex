/- M169 | Hermitian Hamiltonians have real eigenvalues | 10-15 min | hermiticity, inner_smul_left, cancellation, physlib
GOAL
  If the tight-binding Hamiltonian has an eigenvector, `H ψ = E • ψ` with `ψ ≠ 0` and `E : ℂ`,
  then `E` is real (`E.im = 0`). Use only that `H` is Hermitian: `⟪H ψ, φ⟫ = ⟪ψ, H φ⟫`.

REFERENCE
  #check TightBindingChain.hamiltonian_hermitian  -- ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ
  #check inner_smul_left    -- ⟪r • x, y⟫ = conj r * ⟪x, y⟫   (`conj` is `starRingEnd ℂ`)
  #check inner_smul_right   -- ⟪x, r • y⟫ = r * ⟪x, y⟫
  #check inner_self_ne_zero -- ⟪x, x⟫ ≠ 0 ↔ x ≠ 0
  #check mul_right_cancel₀  -- b ≠ 0 → a * b = c * b → a = c
  #check Complex.conj_eq_iff_im  -- conj z = z ↔ z.im = 0
  example (a b : ℕ) (f : ℕ → ℕ) (h : f a = 0) (hab : a = b) : f b = 0 := by rw [hab] at h; exact h
BANNED: conj_eigenvalue_eq_self
NOTE: `⟪x, y⟫_ℂ` is the inner product, conjugate-linear in the first slot.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M169

-- BEGIN SPEC
theorem eigenvalue_real (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace) (hψ : ψ ≠ 0)
    (hE : T.hamiltonian ψ = E • ψ) : E.im = 0 :=
-- END SPEC
  sorry

end M169

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Apply hermiticity with `φ = ψ` and compute both sides using `H ψ = E • ψ`.
H2. You get `conj E * ⟪ψ, ψ⟫ = E * ⟪ψ, ψ⟫`; since `ψ ≠ 0`, the factor `⟪ψ, ψ⟫` cancels.
H3. `have h := T.hamiltonian_hermitian ψ ψ; rw [hE, inner_smul_left, inner_smul_right] at h`
    gives `h : conj E * ⟪ψ, ψ⟫ = E * ⟪ψ, ψ⟫`. Now cancel `⟪ψ, ψ⟫` (nonzero by `inner_self_ne_zero`)
    and turn `conj E = E` into `E.im = 0`.
-/
