/- M144 | Kraus maps are trace preserving and positive | 15-20 min | Kraus operators, trace cyclicity, PosSemidef, quadratic forms, simp_rw, mathlib
GOAL
  The Kraus map `kraus K ρ = ∑ i, K i * ρ * (K i)ᴴ` with `∑ i, (K i)ᴴ * K i = 1` preserves the trace of
  every matrix `ρ`; and, proved from the quadratic-form definition, it maps PSD matrices to PSD matrices.

REFERENCE
  -- `Aᴴ`: conjugate transpose; `M *ᵥ v`: matrix·vector; `star x ⬝ᵥ y = ∑ i, conj (x i) * y i`; ℂ's order: `open scoped ComplexOrder`.
  #check Matrix.trace_sum        -- (∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i).trace
  #check Matrix.trace_mul_cycle  -- (A * B * C).trace = (C * A * B).trace
  #check Finset.sum_mul          -- (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
  #check Matrix.posSemidef_sum   -- (s : Finset ι) : (∀ i ∈ s, (x i).PosSemidef) → (∑ i ∈ s, x i).PosSemidef
  #check Matrix.posSemidef_iff_dotProduct_mulVec  -- M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x
  #check Matrix.isHermitian_mul_mul_conjTranspose -- (B) : A.IsHermitian → (B * A * Bᴴ).IsHermitian
  #check Matrix.star_mulVec      -- star (M *ᵥ v) = star v ᵥ* Mᴴ     (`v ᵥ* M` is row vector · matrix)
  #check Matrix.dotProduct_mulVec  -- v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w
  #check Matrix.mulVec_mulVec    -- M *ᵥ N *ᵥ v = (M * N) *ᵥ v
  -- `simp_rw [h]` rewrites under binders such as `∑ i, …` (plain `rw` cannot).
BANNED: mul_mul_conjTranspose_same, conjTranspose_mul_mul_same, star_left_conjugate_nonneg, star_right_conjugate_nonneg, try?
-/
import Mathlib

open Matrix
open scoped ComplexOrder

namespace M144

-- BEGIN SPEC
/-- a channel in Kraus form: `ρ ↦ ∑ i, Kᵢ ρ Kᵢ†` -/
def kraus {d ι : Type} [Fintype ι] [Fintype d] (K : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ
-- END SPEC

-- BEGIN SPEC
theorem kraus_trace {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (K : ι → Matrix d d ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix d d ℂ) :
    (kraus K ρ).trace = ρ.trace :=
-- END SPEC
  sorry

-- BEGIN SPEC
/-- one Kraus term: conjugating a PSD matrix keeps it PSD -/
theorem conj_psd {d : Type} [Fintype d] (B ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) :
    (B * ρ * Bᴴ).PosSemidef :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem kraus_psd {d ι : Type} [Fintype d] [Fintype ι]
    (K : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) :
    (kraus K ρ).PosSemidef :=
-- END SPEC
  sorry

end M144

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Trace: push `trace` inside the sum and use cyclicity to bring `(K i)ᴴ` to the front of each term.
    PSD: `⟨x, B ρ Bᴴ x⟩ = ⟨Bᴴ x, ρ (Bᴴ x)⟩`, so test `ρ` on the vector `Bᴴ *ᵥ x`. A sum of PSD matrices is PSD.
H2. Trace: after `rw [kraus, trace_sum]`, rewrite each term to `((K i)ᴴ * K i * ρ).trace`, fold the sum
    back with `← trace_sum` and `← Finset.sum_mul`, then use `hK`. `conj_psd`: `rw [posSemidef_iff_dotProduct_mulVec] at *`;
    the Hermitian half is one lemma; for the other, `have := hρ.2 (Bᴴ *ᵥ x)` and massage both sides.
H3. `simp_rw [trace_mul_cycle (K _) ρ]; rw [← trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]`.
    `rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec] at this; rwa [← mulVec_mulVec, ← mulVec_mulVec]`.
    `kraus_psd`: `posSemidef_sum _ fun i _ => conj_psd (K i) ρ hρ`.
-/
