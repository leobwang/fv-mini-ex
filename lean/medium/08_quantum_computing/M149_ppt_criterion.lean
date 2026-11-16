/- M149 | The PPT (Peres–Horodecki) criterion | 15-20 min | partial transpose, PosSemidef, separability, entanglement witness, mathlib
GOAL
  The partial transpose `ρ^{T_B}` of every separable state `∑ k, p k • (ρ k ⊗ₖ σ k)` is PSD. For the Bell
  state it is not (the singlet vector gives `-1`), so the Bell density matrix is not separable.

REFERENCE
  -- `ρ ⊗ₖ σ` (open scoped Kronecker): (ρ ⊗ₖ σ) (a, b) (c, e) = ρ a c * σ b e. `Mᵀ` is the transpose.
  -- `vecMulVec v (star v)` is the projector |v⟩⟨v|; `M.PosSemidef` needs `open scoped ComplexOrder` on ℂ.
  -- `M *ᵥ v` is matrix·vector; `x ⬝ᵥ y = ∑ i, x i * y i`, so `star x ⬝ᵥ y = ∑ i, conj (x i) * y i`.
  #check Matrix.PosSemidef.kronecker  -- x.PosSemidef → y.PosSemidef → (x ⊗ₖ y).PosSemidef
  #check Matrix.PosSemidef.transpose  -- M.PosSemidef → Mᵀ.PosSemidef
  #check Matrix.PosSemidef.smul       -- x.PosSemidef → 0 ≤ a → (a • x).PosSemidef   (here `a : ℝ`)
  #check Matrix.posSemidef_sum        -- (s) : (∀ i ∈ s, (x i).PosSemidef) → (∑ i ∈ s, x i).PosSemidef
  #check Matrix.PosSemidef.dotProduct_mulVec_nonneg  -- M.PosSemidef → ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x
  #check Complex.nonneg_iff           -- 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im
  #check Matrix.sum_apply             -- (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j
  example : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  -- `ext ⟨a, b⟩ ⟨c, e⟩` proves a matrix equality entry by entry over pair indices.
NOTE: Mathlib defines `PosSemidef` through `Finsupp`; use `dotProduct_mulVec_nonneg` rather than unfolding it.
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

-- BEGIN SPEC
theorem ptB_sep {d₁ d₂ ι : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    [Fintype ι] (p : ι → ℝ) (ρ : ι → Matrix d₁ d₁ ℂ) (σ : ι → Matrix d₂ d₂ ℂ)
    (hp : ∀ k, 0 ≤ p k) (hρ : ∀ k, (ρ k).PosSemidef) (hσ : ∀ k, (σ k).PosSemidef) :
    (ptB (∑ k, p k • (ρ k ⊗ₖ σ k))).PosSemidef :=
-- END SPEC
  sorry

-- BEGIN SPEC
/-- the Bell vector `(|00⟩ + |11⟩)/√2` -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℂ) else 0
-- END SPEC

-- BEGIN SPEC
theorem bell_npt : ¬ (ptB (vecMulVec bell (star bell))).PosSemidef :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem bell_entangled : ¬ ∃ (m : ℕ) (p : Fin m → ℝ) (ρ σ : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ k, 0 ≤ p k) ∧ (∀ k, (ρ k).PosSemidef) ∧ (∀ k, (σ k).PosSemidef) ∧
    vecMulVec bell (star bell) = ∑ k, p k • (ρ k ⊗ₖ σ k) :=
-- END SPEC
  sorry

end M149

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ptB` is linear, and on a product it only transposes the second factor: `ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ`.
    For the Bell state, test PSD on the singlet `v = |01⟩ - |10⟩`. The last theorem combines the first two.
H2. `ptB_sep`: prove `ptB (∑ k, p k • X k) = ∑ k, p k • ptB (X k)` (`ext; simp [ptB, sum_apply]`) and the
    product formula (`ext ⟨a, b⟩ ⟨c, e⟩; simp [ptB]`), then `posSemidef_sum` with `.smul (hp k)` on each term.
    `bell_npt`: `intro h; have := h.dotProduct_mulVec_nonneg v` and compute the number.
H3. `v := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0`; show `star v ⬝ᵥ (ptB … *ᵥ v) = -1` by
    `simp [v, ptB, bell, dotProduct, mulVec, vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two]; field_simp;
    linear_combination h2` (with `h2` the `√2 ^ 2 = 2` line), then `norm_num [Complex.nonneg_iff]`.
    `bell_entangled`: `rintro ⟨m, p, ρ, σ, hp, hρ, hσ, h⟩; exact bell_npt (h ▸ ptB_sep p ρ σ hp hρ hσ)`.
-/
