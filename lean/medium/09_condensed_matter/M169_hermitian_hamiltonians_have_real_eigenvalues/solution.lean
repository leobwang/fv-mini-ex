/- M169 | Hermitian Hamiltonians have real eigenvalues | 10-15 min | hermiticity, inner_smul_left, cancellation, physlib
GOAL
  If the tight-binding Hamiltonian has an eigenvector, `H ψ = E • ψ` with `ψ ≠ 0` and `E : ℂ`,
  then `E` is real (`E.im = 0`). Use only that `H` is Hermitian: `⟪H ψ, φ⟫ = ⟪ψ, H φ⟫`.

BANNED: conj_eigenvalue_eq_self

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M169

/- SKELETON · eigenvalue_real
  1. Hermiticity at φ = ψ, as a hypothesis:                                 R1
       h : ⟪T.hamiltonian ψ, ψ⟫_ℂ = ⟪ψ, T.hamiltonian ψ⟫_ℂ
  2. Rewrite h into scalars: substitute hE, then pull E out of each slot     R2 → R3 → R4
     (left slot: conjugated; right slot: as is):
       h : (starRingEnd ℂ) E * ⟪ψ, ψ⟫_ℂ = E * ⟪ψ, ψ⟫_ℂ
  3. Goal `E.im = 0` → `(starRingEnd ℂ) E = E`:                              R7
  4. Cancel the common right factor ⟪ψ, ψ⟫_ℂ; its `≠ 0` comes from hψ:      R6 with R5
     what is left is exactly h.
-/
-- BEGIN SPEC
theorem eigenvalue_real (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace) (hψ : ψ ≠ 0)
    (hE : T.hamiltonian ψ = E • ψ) : E.im = 0 :=
-- END SPEC
  by
    have h := T.hamiltonian_hermitian ψ ψ
    -- h : conj E * ⟪ψ, ψ⟫ = E * ⟪ψ, ψ⟫
    rw [hE, inner_smul_left, inner_smul_right] at h
    exact Complex.conj_eq_iff_im.mp (mul_right_cancel₀ (inner_self_ne_zero.mpr hψ) h)

end M169

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Specialize hermiticity to φ = ψ and substitute `hE` on both sides. Which scalar identity relates
    `E`, its conjugate and `⟪ψ, ψ⟫_ℂ`?
H2. `have h := T.hamiltonian_hermitian ψ ψ` and rewrite it at h (R2 → R3 → R4) into
    `(starRingEnd ℂ) E * ⟪ψ, ψ⟫_ℂ = E * ⟪ψ, ψ⟫_ℂ`. Then turn the goal into `(starRingEnd ℂ) E = E`
    (R7) and cancel `⟪ψ, ψ⟫_ℂ`, which is nonzero because `ψ ≠ 0` (R6, R5).
H3. `rw [hE, inner_smul_left, inner_smul_right] at h`, then
    `rw [← Complex.conj_eq_iff_im]; apply mul_right_cancel₀ (inner_self_ne_zero.mpr hψ)`.
-/
