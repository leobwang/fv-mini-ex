/- M149 | The PPT (Peres–Horodecki) criterion | 15-20 min | partial transpose, PosSemidef, separability, entanglement witness, mathlib
GOAL
  The partial transpose `ρ^{T_B}` of every separable state `∑ k, p k • (ρ k ⊗ₖ σ k)` is PSD. For the Bell
  state it is not (the singlet vector gives `-1`), so the Bell density matrix is not separable.

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix
open scoped Kronecker ComplexOrder

namespace M149

-- BEGIN SPEC
/-- partial transpose on the second factor: `(M^{T_B}) (a, b) (c, e) = M (a, e) (c, b)` -/
def ptB {d₁ d₂ : Type} (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) : Matrix (d₁ × d₂) (d₁ × d₂) ℂ :=
  Matrix.of fun p q => M (p.1, q.2) (q.1, p.2)
-- END SPEC

/-- on a product state, `ptB` transposes only the second factor -/
theorem ptB_kron {d₁ d₂ : Type} (ρ : Matrix d₁ d₁ ℂ) (σ : Matrix d₂ d₂ ℂ) :
    ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp [ptB]

/- SKELETON · ptB_sep
  0. MILESTONE first, as your own helper lemma between `ptB` and this comment (outside the spec regions):
       ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ      for any ρ : Matrix d₁ d₁ ℂ, σ : Matrix d₂ d₂ ℂ
     proof: one entry over pair indices, then `simp` with `ptB`:              R1, then R2, R3, R4
  1. Linearity, as a fact:                                                   have
       hlin : ptB (∑ k, p k • (ρ k ⊗ₖ σ k)) = ∑ k, p k • ptB (ρ k ⊗ₖ σ k)
     proof: `ext a b`, then `simp` with `ptB` and `Matrix.sum_apply`:          R1, then R2, R5, R6
  2. rw [hlin]; reduce PSD of the sum to PSD of term k:                      R7
  3. rw [milestone]; the term is now p k • (ρ k ⊗ₖ (σ k)ᵀ). Close it with hp k, hρ k, hσ k:
                                                                             R8 → R9 → R10
-/
-- BEGIN SPEC
theorem ptB_sep {d₁ d₂ ι : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    [Fintype ι] (p : ι → ℝ) (ρ : ι → Matrix d₁ d₁ ℂ) (σ : ι → Matrix d₂ d₂ ℂ)
    (hp : ∀ k, 0 ≤ p k) (hρ : ∀ k, (ρ k).PosSemidef) (hσ : ∀ k, (σ k).PosSemidef) :
    (ptB (∑ k, p k • (ρ k ⊗ₖ σ k))).PosSemidef :=
-- END SPEC
  by
    have hlin : ptB (∑ k, p k • (ρ k ⊗ₖ σ k)) = ∑ k, p k • ptB (ρ k ⊗ₖ σ k) := by
      ext a b
      simp [ptB, Matrix.sum_apply]
    rw [hlin]
    refine posSemidef_sum _ fun k _ => ?_
    rw [ptB_kron]
    exact ((hρ k).kronecker (hσ k).transpose).smul (hp k)

-- BEGIN SPEC
/-- the Bell vector `(|00⟩ + |11⟩)/√2` -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℂ) else 0
-- END SPEC

/- SKELETON · bell_npt
  1. Assume the partial transpose is PSD; the goal becomes False:            R11
  2. The test vector, the singlet |01⟩ − |10⟩:                               R12
       v : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
  3. PSD on v gives  h1 : 0 ≤ star v ⬝ᵥ ptB (…) *ᵥ v:                         R13
  4. The √2 fact  h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2:                       R14 → R15, then `simp`
  5. The value  hv : star v ⬝ᵥ (ptB (vecMulVec bell (star bell)) *ᵥ v) = -1:
       `simp` with v, ptB, bell and R16, R17, R18, R20, R21 (it applies R2, R19 itself)
       clear the inverses, then close with h2:                               R22, R23
  6. Substitute and refute  0 ≤ -1:                                          R24, R25 → R26
-/
-- BEGIN SPEC
theorem bell_npt : ¬ (ptB (vecMulVec bell (star bell))).PosSemidef :=
-- END SPEC
  by
    intro h
    -- WHY: the singlet `|01⟩ - |10⟩` is an eigenvector of the partially transposed Bell projector with eigenvalue -1/2
    set v : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
    have h1 := h.dotProduct_mulVec_nonneg v
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
    have hv : star v ⬝ᵥ (ptB (vecMulVec bell (star bell)) *ᵥ v) = -1 := by
      simp [v, ptB, bell, dotProduct, mulVec, vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
      field_simp
      linear_combination h2
    rw [hv] at h1
    norm_num [Complex.nonneg_iff] at h1

/- SKELETON · bell_entangled
  1. Assume a decomposition and take it apart:                               R27
       m, p, ρ, σ, hp, hρ, hσ and  h : vecMulVec bell (star bell) = ∑ k, p k • (ρ k ⊗ₖ σ k)
  2. `ptB_sep p ρ σ hp hρ hσ` is PSD of ptB (∑ …); move it to ptB of the Bell matrix with h:   R28
  3. `bell_npt` refutes that:                                                R29
-/
-- BEGIN SPEC
theorem bell_entangled : ¬ ∃ (m : ℕ) (p : Fin m → ℝ) (ρ σ : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ k, 0 ≤ p k) ∧ (∀ k, (ρ k).PosSemidef) ∧ (∀ k, (σ k).PosSemidef) ∧
    vecMulVec bell (star bell) = ∑ k, p k • (ρ k ⊗ₖ σ k) :=
-- END SPEC
  by
    rintro ⟨m, p, ρ, σ, hp, hρ, hσ, h⟩
    exact bell_npt (h ▸ ptB_sep p ρ σ hp hρ hσ)

end M149

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ptB` is linear, and on a product it only transposes the second factor: prove the milestone
    `ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ` first. For the Bell state, PSD fails on a single test vector, the singlet
    `|01⟩ - |10⟩`. The last theorem only combines the first two.
H2. `ptB_sep`: milestone by `ext ⟨a, b⟩ ⟨c, e⟩; simp [ptB]`; linearity by `ext a b; simp [ptB, Matrix.sum_apply]`;
    then `rw [hlin]`, `refine Matrix.posSemidef_sum _ fun k _ => ?_`, `rw [milestone]`, and PSD from
    `.kronecker`, `.transpose`, `.smul`. `bell_npt`: `intro h`, `set v …`, `have h1 := h.dotProduct_mulVec_nonneg v`,
    compute the number (`-1`), then turn `0 ≤ -1` into `False` with `Complex.nonneg_iff`.
H3. Term k: `exact ((hρ k).kronecker (hσ k).transpose).smul (hp k)`.
    `hv` by `simp [v, ptB, bell, dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two]`,
    `field_simp`, `linear_combination h2`; then `rw [hv] at h1; norm_num [Complex.nonneg_iff] at h1`.
    `bell_entangled`: `rintro ⟨m, p, ρ, σ, hp, hρ, hσ, h⟩; exact bell_npt (h ▸ ptB_sep p ρ σ hp hρ hσ)`.
-/
