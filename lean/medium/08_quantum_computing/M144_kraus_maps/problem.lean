/- M144 | Kraus maps are trace preserving and positive | 15-20 min | Kraus operators, trace cyclicity, PosSemidef, quadratic forms, simp_rw, mathlib
GOAL
  The Kraus map `kraus K ρ = ∑ i, K i * ρ * (K i)ᴴ` with `∑ i, (K i)ᴴ * K i = 1` preserves the trace of
  every matrix `ρ`; and, proved from the quadratic-form definition, it maps PSD matrices to PSD matrices.

BANNED: mul_mul_conjTranspose_same, conjTranspose_mul_mul_same, star_left_conjugate_nonneg, star_right_conjugate_nonneg, try?

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · kraus_trace
  1. Unfold `kraus`, push the trace inside the sum:                      R1, R2
  2. Rotate every term so `(K i)ᴴ` comes first, UNDER the `∑`:            R4  (pinned: `(K _) ρ`; R3 is
       the one-term version). Each term is now `((K i)ᴴ * K i * ρ).trace`.
  3. Fold the sum of traces back into one trace, pull `ρ` out:            R5, R6
  4. The goal now contains `∑ i, (K i)ᴴ * K i` literally:                 rw [hK], R7
       (`rw` closes `ρ.trace = ρ.trace` itself)
-/
-- BEGIN SPEC
theorem kraus_trace {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (K : ι → Matrix d d ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix d d ℂ) :
    (kraus K ρ).trace = ρ.trace :=
-- END SPEC
  sorry

/- SKELETON · conj_psd
  1. Turn `hρ` and the goal into the quadratic-form statement:            R8 (`at *`)
  2. Split the goal; the Hermitian half is one lemma applied to `hρ.1`:   R9 with R10
  3. Test `ρ` on the vector `Bᴴ *ᵥ x`:                                    R11
       this : 0 ≤ star (Bᴴ *ᵥ x) ⬝ᵥ ρ *ᵥ Bᴴ *ᵥ x
  4. Rewrite `this` into  0 ≤ star x ⬝ᵥ B *ᵥ ρ *ᵥ Bᴴ *ᵥ x :               R12 → R13 → R14 (`at this`)
  5. Split the goal's `(B * ρ * Bᴴ) *ᵥ x` the same way, then close with `this`:   R15, R15, R16
-/
-- BEGIN SPEC
/-- one Kraus term: conjugating a PSD matrix keeps it PSD -/
theorem conj_psd {d : Type} [Fintype d] (B ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) :
    (B * ρ * Bᴴ).PosSemidef :=
-- END SPEC
  sorry

/- SKELETON · kraus_psd
  1. (optional) Unfold `kraus` to see the sum:                            R1
  2. A sum of PSD matrices is PSD; take one index:                        R17
  3. That term is `K i * ρ * (K i)ᴴ`: use `conj_psd` (proved above) with `exact`.
-/
-- BEGIN SPEC
theorem kraus_psd {d ι : Type} [Fintype d] [Fintype ι]
    (K : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) (hρ : ρ.PosSemidef) :
    (kraus K ρ).PosSemidef :=
-- END SPEC
  sorry

end M144

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Trace: push `trace` inside the sum and use cyclicity under the `∑` to bring `(K i)ᴴ` to the front of
    each term; then fold the sum back so `hK` applies. PSD: `⟨x, B ρ Bᴴ x⟩ = ⟨Bᴴ x, ρ (Bᴴ x)⟩`, so test `ρ`
    on the vector `Bᴴ *ᵥ x`. A sum of PSD matrices is PSD, and each Kraus term is `conj_psd`.
H2. `kraus_trace`: `rw [kraus, Matrix.trace_sum]` (R1, R2), `simp_rw` with a pinned `trace_mul_cycle` (R4),
    then `rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]` (R5, R6, R7).
    `conj_psd`: `rw [Matrix.posSemidef_iff_dotProduct_mulVec] at *` (R8); `refine ⟨e, fun x => ?_⟩` (R9) with
    R10 as `e` for the Hermitian half; `have := hρ.2 (Bᴴ *ᵥ x)` (R11); rewrite `this` with R12–R14 and the goal
    with R15 until they agree.
H3. `simp_rw [Matrix.trace_mul_cycle (K _) ρ]`.
    `refine ⟨Matrix.isHermitian_mul_mul_conjTranspose B hρ.1, fun x => ?_⟩`;
    `rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec] at this`;
    `rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.
    `kraus_psd`: `Matrix.posSemidef_sum _ fun i _ => conj_psd (K i) ρ hρ`.
-/
