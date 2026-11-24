/- E121 | Energy expectation values are real | 2-3 min | hermiticity, inner_conj_symm, Complex.im, physlib
GOAL
  The tight-binding Hamiltonian `T.hamiltonian` is Hermitian: `⟨Hψ, φ⟩ = ⟨ψ, Hφ⟩`. Deduce that every
  energy expectation value `⟨ψ, Hψ⟩` is real (its imaginary part is 0). Here `T.HilbertSpace` is ℂ^N
  (one basis state per lattice site, `T.N` sites), an inner-product space over ℂ.

REFERENCE
  #check CondensedMatter.TightBindingChain.hamiltonian_hermitian  -- (T) (ψ φ) : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ
  #check inner_conj_symm         -- conj ⟪y, x⟫_𝕜 = ⟪x, y⟫_𝕜     (`conj` prints as `(starRingEnd ℂ)`)
  #check Complex.conj_eq_iff_im  -- conj z = z ↔ z.im = 0
  example (T : TightBindingChain) :
      T.HilbertSpace = QuantumMechanics.FiniteHilbertSpace (Fin T.N) := rfl   -- ℂ^N, one state per site
  `⟪x, y⟫_ℂ` (after `open InnerProductSpace`) is the inner product, conjugate-linear in `x`.
  `rw [← inner_conj_symm] at h` rewrites the left-hand side of `h` into a conjugate.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace E121

-- BEGIN SPEC
theorem energy_real (T : TightBindingChain) (ψ : T.HilbertSpace) :
    (⟪ψ, T.hamiltonian ψ⟫_ℂ).im = 0 :=
-- END SPEC
  by
    have h := T.hamiltonian_hermitian ψ ψ
    rw [← inner_conj_symm] at h
    exact Complex.conj_eq_iff_im.mp h

end E121

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A complex number is real exactly when it equals its own conjugate.
H2. Specialise hermiticity to `φ = ψ`; then the left side `⟪Hψ, ψ⟫` is the conjugate of `⟪ψ, Hψ⟫`.
H3. `have h := T.hamiltonian_hermitian ψ ψ`, `rw [← inner_conj_symm] at h`, `exact Complex.conj_eq_iff_im.mp h`.
-/
