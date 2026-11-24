/- E121 | Energy expectation values are real | 2-3 min | hermiticity, inner_conj_symm, Complex.im, physlib
GOAL
  The tight-binding Hamiltonian `T.hamiltonian` is Hermitian: `⟨Hψ, φ⟩ = ⟨ψ, Hφ⟩`. Deduce that every
  energy expectation value `⟨ψ, Hψ⟩` is real (its imaginary part is 0). Here `T.HilbertSpace` is ℂ^N
  (one basis state per lattice site, `T.N` sites), an inner-product space over ℂ.

GUIDE
  Entries R1–R3: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace E121

/- SKELETON · energy_real
  1. Hermiticity with both states equal to ψ, as a fact in context:        R1
       h : ⟪T.hamiltonian ψ, ψ⟫_ℂ = ⟪ψ, T.hamiltonian ψ⟫_ℂ
  2. Rewrite the LEFT side of h as a conjugate (only it is rewritten):      R2 (at h)
       h : (starRingEnd ℂ) ⟪ψ, T.hamiltonian ψ⟫_ℂ = ⟪ψ, T.hamiltonian ψ⟫_ℂ
  3. `conj z = z` gives `z.im = 0`; close the goal with h:                  R3
-/
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
H1. A complex number is real exactly when it equals its own conjugate (R3). Hermiticity (R1) is the
    only fact about `T.hamiltonian` you need.
H2. Specialise hermiticity to `φ = ψ` (R1); its left side `⟪Hψ, ψ⟫_ℂ` is the conjugate of `⟪ψ, Hψ⟫_ℂ`
    (R2, right to left, inside `h`). Then `h` reads `conj z = z` for `z = ⟪ψ, Hψ⟫_ℂ`.
H3. `have h := T.hamiltonian_hermitian ψ ψ`, `rw [← inner_conj_symm] at h`, `exact Complex.conj_eq_iff_im.mp h`.
-/
